import CERW.Support.LocalTime.KernelFacts
import CERW.Support.LocalTime.IntervalDynkin
import CERW.Support.LocalTime.SourcePacking
import CERW.Support.LocalTime.IntervalMart
import CERW.Support.LocalTime.SourceSum
import CERW.Support.Geometry.CellModulus
import CERW.Generic.Young.Absorb

/-!
# The local-time lemma

`lem:local`, assembled from the kernel facts. For every interval, subtract `eq:dynkin` at its ends
(the interval Dynkin decomposition). The endpoint difference is `O(L)` by the growth of `b`. The
source sum over the `k_{s,t}` new sites is at most `C_d ε k_{s,t}^{1/d}` (`eq:packing-lattice`), and
the martingale increment is at most `C e_n(M_{s,t})` (`eq:interval-mart`). At a site where
`ℓ_{s,t} = M_{s,t}`, Young's inequality absorbs `√M_{s,t}` and proves `eq:interval`. The choice
`s = 0`, `t = n` proves `eq:M`. For `eq:approx`, compare `ℓ̃_n(y) = ℓ_n(z)` at the lattice site
`z` of `y` with `U_{D_n}(z)` through the source-sum comparison. Then compare `U_{D_n}(z)` with
`U_{D_n}(y)` through the cell modulus `eq:cellmodulus`.
-/

universe u

namespace CERW.Support.LocalTime

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law

/-- A measure bound for a set covered by an event of small measure and a null event. -/
private lemma measure_le_of_subset_union {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A N B : Set Ω} {a c : ENNReal} (hsub : B ⊆ A ∪ N) (hA : μ A ≤ a) (hN : μ N = 0)
    (hac : a ≤ c) : μ B ≤ c := by
  refine (measure_mono hsub).trans ((measure_union_le A N).trans ?_)
  rw [hN, add_zero]
  exact hA.trans hac

/-- For `n ≥ 2` the logarithm `log (n + 2)` is at least `1`. -/
private lemma one_le_log_add_two {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Real.log ((n : ℝ) + 2) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_three
  linarith

/-- A logarithm of a positive number at most `4n + 2` is at most `2 log (n + 2)`. -/
private lemma log_le_two_mul_log {a : ℝ} (n : ℕ) (ha : 0 < a) (h : a ≤ 4 * (n : ℝ) + 2) :
    Real.log a ≤ 2 * Real.log ((n : ℝ) + 2) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hle : a ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith
  have := Real.log_le_log ha hle
  rwa [Real.log_pow, Nat.cast_ofNat] at this

/-- The Euclidean norm of a difference of sites is at most the sum of the norms. -/
private lemma euclidNorm_sub_le_add {d : ℕ} (x y : Site d) :
    euclidNorm (x - y) ≤ euclidNorm x + euclidNorm y := by
  have h := CERW.Support.Occupation.euclidNorm_add_le x (-y)
  rwa [← sub_eq_add_neg, CERW.Generic.Lattice.euclidNorm_neg] at h

/-- The error scale `e_n(m) = B √m + L` with `B = L` for `d = 2` and `B = √L` for `d ≥ 3`. -/
private lemma error_scale_eq {m L : ℝ} (d : ℕ) (hm : 0 ≤ m) :
    (if d = 2 then Real.sqrt m * L + L else Real.sqrt (m * L) + L) =
      (if d = 2 then L else Real.sqrt L) * Real.sqrt m + L := by
  by_cases hd : d = 2
  · simp only [hd, if_true]
    ring
  · simp only [hd, if_false]
    rw [Real.sqrt_mul hm]
    ring

/-- The scale `B` of the error, and the scale `λ_n = B²` that dominates `L`. -/
private lemma error_scale_facts {L : ℝ} (d : ℕ) (hL : 1 ≤ L) :
    0 ≤ (if d = 2 then L else Real.sqrt L) ∧
      (if d = 2 then L else Real.sqrt L) ^ 2 = (if d = 2 then L ^ 2 else L) ∧
      L ≤ (if d = 2 then L ^ 2 else L) := by
  split_ifs with hd
  · exact ⟨by linarith, rfl, by nlinarith⟩
  · exact ⟨Real.sqrt_nonneg _, Real.sq_sqrt (by linarith), le_rfl⟩

/-- Some site visited during `[s, t)` attains the interval maximum. -/
private lemma exists_visited_eq_intervalMax {d : ℕ} (x : ℕ → Site d) {s t : ℕ} (hst : s < t) :
    ∃ j, s ≤ j ∧ j < t ∧ intervalLocalTime x s t (x j) = intervalMax x s t := by
  have hne : ((Finset.Ico s t).image x).Nonempty := (Finset.nonempty_Ico.mpr hst).image x
  obtain ⟨y, hy, hsup⟩ := Finset.exists_mem_eq_sup _ hne (intervalLocalTime x s t)
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  exact ⟨j, (Finset.mem_Ico.mp hj).1, (Finset.mem_Ico.mp hj).2, hsup.symm⟩

/-- The pathwise bound of `eq:interval` on one interval: the interval Dynkin decomposition, the
packing bound on the fresh sites and the martingale bound give `M ≤ a + B' √M`, which
Young's inequality absorbs. -/
private lemma interval_bound {d : ℕ} {b : Site d → ℝ}
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0) {CP Cb CI Bn lam ε : ℝ}
    (hCP0 : 0 ≤ CP) (hCb0 : 0 ≤ Cb) (hCI0 : 0 ≤ CI) (hε : 0 ≤ ε) (hBn : 0 ≤ Bn)
    (hBsq : Bn ^ 2 = lam)
    (hCP : ∀ (F : Finset (Site d)) (y : Site d),
      |∑ x ∈ F, inner ℝ (unitDir (toSpace x)) (centralDiff b (x - y))| ≤
        CP * (F.card : ℝ) ^ ((1 : ℝ) / d))
    (hCb : ∀ x : Site d, |b x| ≤ Cb * Real.log (euclidNorm x + 2))
    {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (h0 : X 0 ω = 0)
    (hnorm : ∀ j : ℕ, euclidNorm (X j ω) ≤ j) {n : ℕ} (hn : 2 ≤ n)
    (hLlam : Real.log ((n : ℝ) + 2) ≤ lam)
    (hmart : ∀ (s t : ℕ) (y : Site d), s < t → t ≤ n → euclidNorm y ≤ 3 * n →
      |dynkin ε (fun z => b (z - y)) X t ω - dynkin ε (fun z => b (z - y)) X s ω| ≤
        CI * (Bn * Real.sqrt (intervalMax (fun j => X j ω) s t) + Real.log ((n : ℝ) + 2)))
    (s t : ℕ) (hst : s < t) (htn : t ≤ n) :
    (intervalMax (fun j => X j ω) s t : ℝ) ≤
      (2 * CP + 1) * ε * (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) +
        (8 * Cb + 2 * CI + CI ^ 2) * lam := by
  obtain ⟨j, -, hjt, hjmax⟩ := exists_visited_eq_intervalMax (fun j => X j ω) hst
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have htR : (t : ℝ) ≤ n := by exact_mod_cast htn
  have hsR : (s : ℝ) ≤ n := by exact_mod_cast (hst.le.trans htn)
  have hjR : (j : ℝ) ≤ n := by exact_mod_cast (hjt.le.trans htn)
  have hL1 := one_le_log_add_two hn
  have hyn : euclidNorm (X j ω) ≤ n := (hnorm j).trans hjR
  have hdyn := intervalLocalTime_eq_dynkin hb ε X ω h0 hst.le (X j ω)
  have hM : (intervalLocalTime (fun j => X j ω) s t (X j ω) : ℝ) =
      (intervalMax (fun j => X j ω) s t : ℝ) := by exact_mod_cast hjmax
  have hb1 : |b (X t ω - X j ω)| ≤ Cb * (2 * Real.log ((n : ℝ) + 2)) := by
    refine (hCb _).trans (mul_le_mul_of_nonneg_left ?_ hCb0)
    refine log_le_two_mul_log n (by linarith [euclidNorm_nonneg (X t ω - X j ω)]) ?_
    linarith [euclidNorm_sub_le_add (X t ω) (X j ω), hnorm t]
  have hb2 : |b (X s ω - X j ω)| ≤ Cb * (2 * Real.log ((n : ℝ) + 2)) := by
    refine (hCb _).trans (mul_le_mul_of_nonneg_left ?_ hCb0)
    refine log_le_two_mul_log n (by linarith [euclidNorm_nonneg (X s ω - X j ω)]) ?_
    linarith [euclidNorm_sub_le_add (X s ω) (X j ω), hnorm s]
  have hsum := hCP (departureRange (fun j => X j ω) t \ departureRange (fun j => X j ω) s)
    (X j ω)
  rw [card_departureRange_sdiff _ hst.le] at hsum
  have hk0 : 0 ≤ (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  generalize (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) = k at hsum hk0 ⊢
  have hmt := hmart s t (X j ω) hst htn (by linarith)
  have hεS := mul_le_mul_of_nonneg_left hsum hε
  have hεS' := mul_le_mul_of_nonneg_left (le_abs_self
    (∑ z ∈ departureRange (fun j => X j ω) t \ departureRange (fun j => X j ω) s,
      inner ℝ (unitDir (toSpace z)) (centralDiff b (z - X j ω)))) hε
  rw [hM] at hdyn
  have key : (intervalMax (fun j => X j ω) s t : ℝ) ≤
      Cb * (2 * Real.log ((n : ℝ) + 2)) + Cb * (2 * Real.log ((n : ℝ) + 2)) +
        ε * (CP * k) +
        CI * (Bn * Real.sqrt (intervalMax (fun j => X j ω) s t) +
          Real.log ((n : ℝ) + 2)) := by
    linarith [le_abs_self (b (X t ω - X j ω)), neg_le_abs (b (X s ω - X j ω)),
      neg_le_abs (dynkin ε (fun z => b (z - X j ω)) X t ω -
        dynkin ε (fun z => b (z - X j ω)) X s ω)]
  have ha0 : 0 ≤ Cb * (2 * Real.log ((n : ℝ) + 2)) + Cb * (2 * Real.log ((n : ℝ) + 2)) +
      ε * (CP * k) +
        CI * Real.log ((n : ℝ) + 2) := by positivity
  have hyoung := CERW.Generic.Young.le_two_mul_add_sq_of_le_add_mul_sqrt (Nat.cast_nonneg _)
    ha0 (mul_nonneg hCI0 hBn) (by linarith [key])
  have hBs : (CI * Bn) ^ 2 = CI ^ 2 * lam := by rw [mul_pow, hBsq]
  nlinarith [mul_le_mul_of_nonneg_left hLlam hCb0, mul_le_mul_of_nonneg_left hLlam hCI0,
    mul_nonneg hε hk0]

/-- Combining the five error terms of the approximate local-time bound: if each term is bounded by
its error scale, then their sum is bounded by the summed scale. -/
private lemma approx_error_combination {Cb CS CM CI Bn ε m logn A B C D E : ℝ}
    (hCb0 : 0 ≤ Cb) (hCS0 : 0 ≤ CS) (hCM0 : 0 ≤ CM)
    (hε : 0 ≤ ε) (hBn : 0 ≤ Bn)
    (hA : |A| ≤ Cb * (2 * logn)) (hB : |B| ≤ Cb * (2 * logn))
    (hC : |C| ≤ CS * ε * (2 * logn)) (hD : |D| ≤ CM * ε * (2 * logn))
    (hE : |E| ≤ CI * (Bn * Real.sqrt m + logn)) :
    |A + B + C + D + E| ≤
      (4 * Cb + 2 * CS * ε + 2 * CM * ε + CI) * (Bn * Real.sqrt m + logn) := by
  have hA' := abs_le.mp hA
  have hB' := abs_le.mp hB
  have hC' := abs_le.mp hC
  have hD' := abs_le.mp hD
  have hE' := abs_le.mp hE
  have hK0 : 0 ≤ 4 * Cb + 2 * CS * ε + 2 * CM * ε := by
    have h1 := mul_nonneg hCS0 hε
    have h2 := mul_nonneg hCM0 hε
    linarith
  have hterm : 0 ≤ (4 * Cb + 2 * CS * ε + 2 * CM * ε) * Bn * Real.sqrt m :=
    mul_nonneg (mul_nonneg hK0 hBn) (Real.sqrt_nonneg m)
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> nlinarith [hterm]

/-- The pathwise bound of `eq:approx` at a real point `y`, `|y| ≤ 2n`: at the site `z` of the cell
of `y`, the Dynkin decomposition of `ℓ_n(z)`, the source-sum comparison, the cell modulus and the
martingale bound. -/
private lemma approx_bound {d : ℕ} (hd : 2 ≤ d) {b : Site d → ℝ}
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0) {Cb CS CM CI Bn ε : ℝ}
    (hCb0 : 0 ≤ Cb) (hCS0 : 0 ≤ CS) (hCM0 : 0 ≤ CM) (hCI0 : 0 ≤ CI) (hε : 0 ≤ ε)
    (hBn : 0 ≤ Bn)
    (hCb : ∀ x : Site d, |b x| ≤ Cb * Real.log (euclidNorm x + 2))
    (hCS : ∀ (u : ℕ → Site d) (m : ℕ) (w : Site d) (R' : ℝ), 1 ≤ R' → euclidNorm w ≤ 2 * R' →
      (∀ x ∈ departureRange u m, euclidNorm (x - w) ≤ R' ∧ cell x ⊆ Metric.ball 0 R') →
        |ε * ∑ x ∈ departureRange u m, inner ℝ (unitDir (toSpace x)) (centralDiff b (x - w)) -
            potential d ε (cellSet u m) (toSpace w)| ≤ CS * ε * Real.log (R' + 2))
    (hCM : ∀ R : ℝ, 1 ≤ R → ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D →
      D ⊆ Metric.ball 0 R → ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R →
        ‖y - z‖ ≤ Real.sqrt d →
        |potential d ε D y - potential d ε D z| ≤ CM * ε * Real.log (R + 2))
    {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (h0 : X 0 ω = 0)
    (hnorm : ∀ j : ℕ, euclidNorm (X j ω) ≤ j) {n : ℕ} (hn : 2 ≤ n) (hsq : Real.sqrt d ≤ n)
    (hmart : ∀ (s t : ℕ) (y : Site d), s < t → t ≤ n → euclidNorm y ≤ 3 * n →
      |dynkin ε (fun z => b (z - y)) X t ω - dynkin ε (fun z => b (z - y)) X s ω| ≤
        CI * (Bn * Real.sqrt (intervalMax (fun j => X j ω) s t) + Real.log ((n : ℝ) + 2)))
    (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ 2 * n) :
    |cellLocalTime (fun j => X j ω) n y - potential d ε (cellSet (fun j => X j ω) n) y| ≤
      (4 * Cb + 2 * CS * ε + 2 * CM * ε + CI) *
        (Bn * Real.sqrt (maxLocalTime (fun j => X j ω) n) + Real.log ((n : ℝ) + 2)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL1 := one_le_log_add_two hn
  have hyz : ‖y - toSpace (cellCenter y)‖ ≤ Real.sqrt d / 2 :=
    CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter y)
  have hznorm : euclidNorm (cellCenter y) ≤ 3 * n := by
    have h := norm_le_norm_add_norm_sub' (toSpace (cellCenter y)) y
    rw [norm_toSpace, norm_sub_rev] at h
    linarith
  have hH : CERW.maxRadius (fun j => X j ω) n ≤ n := by
    apply Finset.sup'_le
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact (hnorm j).trans (by exact_mod_cast hjn)
  have hcellSet : cellSet (fun j => X j ω) n ⊆ Metric.ball 0 ((n : ℝ) + Real.sqrt d) :=
    (CERW.Support.Occupation.cellSet_subset_ball (by omega) (fun j => X j ω) n).trans
      (Metric.ball_subset_ball (by linarith))
  have hdyn := localTime_eq_dynkin hb ε X ω h0 n (cellCenter y)
  have hb1 : |b (X n ω - cellCenter y)| ≤ Cb * (2 * Real.log ((n : ℝ) + 2)) := by
    refine (hCb _).trans (mul_le_mul_of_nonneg_left ?_ hCb0)
    refine log_le_two_mul_log n (by linarith [euclidNorm_nonneg (X n ω - cellCenter y)]) ?_
    linarith [euclidNorm_sub_le_add (X n ω) (cellCenter y), hnorm n]
  have hb2 : |b (-cellCenter y)| ≤ Cb * (2 * Real.log ((n : ℝ) + 2)) := by
    refine (hCb _).trans (mul_le_mul_of_nonneg_left ?_ hCb0)
    rw [CERW.Generic.Lattice.euclidNorm_neg]
    exact log_le_two_mul_log n (by linarith [euclidNorm_nonneg (cellCenter y)]) (by linarith)
  have hsrc := hCS (fun j => X j ω) n (cellCenter y) (4 * n) (by linarith) (by linarith) (by
    intro w hw
    rw [departureRange] at hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hj).le
    refine ⟨?_, ?_⟩
    · linarith [euclidNorm_sub_le_add (X j ω) (cellCenter y), hnorm j]
    · intro v hv
      rw [mem_ball_zero_iff]
      have hv' := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hv
      have h := norm_le_norm_add_norm_sub' v (toSpace (X j ω))
      rw [norm_toSpace] at h
      linarith [hnorm j])
  have hmod := hCM ((n : ℝ) + Real.sqrt d) (by linarith [Real.sqrt_nonneg (d : ℝ)])
    (cellSet (fun j => X j ω) n) (CERW.Support.Occupation.measurableSet_cellSet _ _) hcellSet
    y (toSpace (cellCenter y)) (by linarith [Real.sqrt_nonneg (d : ℝ)])
    (by linarith [Real.sqrt_nonneg (d : ℝ)])
  have hmt := hmart 0 n (cellCenter y) (by omega) le_rfl hznorm
  rw [dynkin_zero, sub_zero] at hmt
  have hmono : Real.sqrt (intervalMax (fun j => X j ω) 0 n) ≤
      Real.sqrt (maxLocalTime (fun j => X j ω) n) :=
    Real.sqrt_le_sqrt (Nat.cast_le.mpr
      (CERW.Support.Occupation.intervalMax_le_maxLocalTime _ le_rfl))
  have hmt' : |dynkin ε (fun z => b (z - cellCenter y)) X n ω| ≤
      CI * (Bn * Real.sqrt (maxLocalTime (fun j => X j ω) n) + Real.log ((n : ℝ) + 2)) :=
    hmt.trans (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hmono hBn) le_rfl) hCI0)
  have hlog1 : Real.log (4 * (n : ℝ) + 2) ≤ 2 * Real.log ((n : ℝ) + 2) :=
    log_le_two_mul_log n (by linarith) le_rfl
  have hlog2 : Real.log ((n : ℝ) + Real.sqrt d + 2) ≤ 2 * Real.log ((n : ℝ) + 2) :=
    log_le_two_mul_log n (by linarith [Real.sqrt_nonneg (d : ℝ)]) (by linarith)
  have hsrc' : |ε * ∑ x ∈ departureRange (fun j => X j ω) n,
      inner ℝ (unitDir (toSpace x)) (centralDiff b (x - cellCenter y)) -
        potential d ε (cellSet (fun j => X j ω) n) (toSpace (cellCenter y))| ≤
      CS * ε * (2 * Real.log ((n : ℝ) + 2)) :=
    hsrc.trans (mul_le_mul_of_nonneg_left hlog1 (mul_nonneg hCS0 hε))
  have hmod' : |potential d ε (cellSet (fun j => X j ω) n) y -
      potential d ε (cellSet (fun j => X j ω) n) (toSpace (cellCenter y))| ≤
      CM * ε * (2 * Real.log ((n : ℝ) + 2)) :=
    hmod.trans (mul_le_mul_of_nonneg_left hlog2 (mul_nonneg hCM0 hε))
  have hE : Real.log ((n : ℝ) + 2) ≤
      Bn * Real.sqrt (maxLocalTime (fun j => X j ω) n) + Real.log ((n : ℝ) + 2) := by
    linarith [mul_nonneg hBn (Real.sqrt_nonneg (maxLocalTime (fun j => X j ω) n : ℝ))]
  have hlead : (4 * Cb + 2 * CS * ε + 2 * CM * ε) * Real.log ((n : ℝ) + 2) ≤
      (4 * Cb + 2 * CS * ε + 2 * CM * ε) *
        (Bn * Real.sqrt (maxLocalTime (fun j => X j ω) n) + Real.log ((n : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have hcell : cellLocalTime (fun j => X j ω) n y =
      (localTime (fun j => X j ω) n (cellCenter y) : ℝ) := rfl
  rw [hcell, hdyn]
  have hdecomp : b (X n ω - cellCenter y) - b (-cellCenter y) +
      ε * (∑ z ∈ departureRange (fun j => X j ω) n,
        inner ℝ (unitDir (toSpace z)) (centralDiff b (z - cellCenter y))) -
        dynkin ε (fun z => b (z - cellCenter y)) X n ω -
        potential d ε (cellSet (fun j => X j ω) n) y =
      b (X n ω - cellCenter y) + (-b (-cellCenter y)) +
        (ε * (∑ z ∈ departureRange (fun j => X j ω) n,
          inner ℝ (unitDir (toSpace z)) (centralDiff b (z - cellCenter y))) -
          potential d ε (cellSet (fun j => X j ω) n) (toSpace (cellCenter y))) +
        (potential d ε (cellSet (fun j => X j ω) n) (toSpace (cellCenter y)) -
          potential d ε (cellSet (fun j => X j ω) n) y) +
        (-dynkin ε (fun z => b (z - cellCenter y)) X n ω) := by ring
  rw [hdecomp]
  exact approx_error_combination hCb0 hCS0 hCM0 hε hBn hb1
    (by rwa [abs_neg]) hsrc' (by rwa [abs_sub_comm]) (by rwa [abs_neg])

/-- The bound `1 ≤ C n^{-p}` for `n ≤ n₀` once `C ≥ n₀^p`. -/
private lemma one_le_mul_rpow_neg {C p : ℝ} {n n₀ : ℕ} (hp : 0 < p) (hn : 0 < n)
    (hnn : n ≤ n₀) (hC : (n₀ : ℝ) ^ p ≤ C) : 1 ≤ C * (n : ℝ) ^ (-p) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) ^ p ≤ (n₀ : ℝ) ^ p :=
    Real.rpow_le_rpow hn'.le (Nat.cast_le.mpr hnn) hp.le
  have h2 : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos hn' p
  rw [Real.rpow_neg hn'.le]
  calc (1 : ℝ) = (n : ℝ) ^ p * ((n : ℝ) ^ p)⁻¹ := (mul_inv_cancel₀ h2.ne').symm
    _ ≤ C * ((n : ℝ) ^ p)⁻¹ := mul_le_mul_of_nonneg_right (h1.trans hC) (inv_nonneg.mpr h2.le)

/-- `lem:local`, for any kernel `b` with the kernel facts. -/
theorem local_time_potential_of_kernelFacts {d : ℕ} (hd : 2 ≤ d) {b : Site d → ℝ} {h : ℝ → ℝ}
    (hK : KernelFacts d b h) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) → ∀ p : ℝ, 0 < p →
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        let L : ℝ := Real.log (n + 2)
        let lam : ℝ := if d = 2 then L ^ 2 else L
        let e : ℝ → ℝ := fun m =>
          if d = 2 then Real.sqrt m * L + L else Real.sqrt (m * L) + L
        μ {ω | ¬ ((CERW.maxLocalTime (X · ω) n : ℝ)
                    ≤ Cd * ε * ((CERW.departureRange (X · ω) n).card : ℝ) ^ ((1 : ℝ) / d)
                      + C * lam ∧
                  (∀ s t : ℕ, s < t → t ≤ n →
                    (CERW.intervalMax (X · ω) s t : ℝ)
                      ≤ Cd * ε * (CERW.freshCount (X · ω) s t : ℝ) ^ ((1 : ℝ) / d) + C * lam) ∧
                  ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
                    |CERW.cellLocalTime (X · ω) n y
                        - CERW.potential d ε (CERW.cellSet (X · ω) n) y|
                      ≤ C * e (CERW.maxLocalTime (X · ω) n))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨R, Ca, hR, hgradA⟩ := hK.gradAsymp
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  obtain ⟨Cb, hCb⟩ := hK.growth
  obtain ⟨CP, hCP0, hCP⟩ := exists_abs_sum_inner_centralDiff_le hd hgrad
  obtain ⟨CS, hCS0, hCS⟩ := exists_abs_source_sum_sub_potential_le hd hR hgradA hgrad
  obtain ⟨CM, hCM0, hCM⟩ := CERW.Support.Geometry.exists_potential_cell_modulus hd
  have hCb' : ∀ x : Site d, |b x| ≤ |Cb| * Real.log (euclidNorm x + 2) := fun x =>
    (hCb x).trans (mul_le_mul_of_nonneg_right (le_abs_self Cb)
      (Real.log_nonneg (by linarith [euclidNorm_nonneg x])))
  refine ⟨2 * CP + 1, by linarith, ?_⟩
  intro ε hε hεd p hp
  obtain ⟨CI, hCI0, hCI⟩ := exists_interval_mart.{u} hd hε.le hεd hgrad hp
  set n₀ : ℕ := ⌈Real.sqrt d⌉₊ + 2 with hn₀
  set C₁ : ℝ := 8 * |Cb| + 2 * CI + CI ^ 2 with hC₁
  set C₂ : ℝ := 4 * |Cb| + 2 * CS * ε + 2 * CM * ε + CI with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hnp : 0 ≤ (n₀ : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨C₁ + C₂ + CI + (n₀ : ℝ) ^ p, by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn
  dsimp only
  by_cases hn₀le : n₀ ≤ n
  · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hL1 := one_le_log_add_two hn
    obtain ⟨hBn, hBsq, hLlam⟩ := error_scale_facts d hL1
    have hlam0 : 0 ≤ (if d = 2 then Real.log ((n : ℝ) + 2) ^ 2 else Real.log ((n : ℝ) + 2)) :=
      by linarith
    have hsq : Real.sqrt d ≤ n := by
      have h1 := Nat.le_ceil (Real.sqrt d)
      have h2 : ((⌈Real.sqrt d⌉₊ : ℕ) : ℝ) ≤ n := by
        exact_mod_cast (by omega : ⌈Real.sqrt d⌉₊ ≤ n)
      linarith
    have hnull : μ {ω | ¬ (X 0 ω = 0 ∧ ∀ j : ℕ, euclidNorm (X j ω) ≤ j)} = 0 := by
      refine ae_iff.mp ?_
      filter_upwards [ae_iff.mpr hX.start, ae_euclidNorm_le (by omega) hε.le hεd hX] with ω h0 h1
      exact ⟨h0, h1⟩
    refine measure_le_of_subset_union (fun ω hω => ?_) (hCI hX n hn) hnull
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨hA', hN'⟩ := hcon
    simp only [Set.mem_setOf_eq, not_not] at hN'
    obtain ⟨h0, hnorm⟩ := hN'
    simp only [Set.mem_setOf_eq, not_exists, not_and, not_lt] at hA'
    have hmart : ∀ (s t : ℕ) (y : Site d), s < t → t ≤ n → euclidNorm y ≤ 3 * n →
        |dynkin ε (fun z => b (z - y)) X t ω - dynkin ε (fun z => b (z - y)) X s ω| ≤
          CI * ((if d = 2 then Real.log ((n : ℝ) + 2) else Real.sqrt (Real.log ((n : ℝ) + 2))) *
            Real.sqrt (intervalMax (fun j => X j ω) s t) + Real.log ((n : ℝ) + 2)) := by
      intro s t y hst htn hy
      rw [← error_scale_eq d (Nat.cast_nonneg _)]
      exact hA' s t y hst htn hy
    have hint : ∀ s t : ℕ, s < t → t ≤ n → (intervalMax (fun j => X j ω) s t : ℝ) ≤
        (2 * CP + 1) * ε * (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) +
          C₁ * (if d = 2 then Real.log ((n : ℝ) + 2) ^ 2 else Real.log ((n : ℝ) + 2)) :=
      fun s t hst htn => interval_bound hK.poisson hCP0 (abs_nonneg Cb) hCI0.le hε.le hBn hBsq hCP
        hCb' X ω h0 hnorm hn hLlam hmart s t hst htn
    have hC₁le : C₁ * (if d = 2 then Real.log ((n : ℝ) + 2) ^ 2 else Real.log ((n : ℝ) + 2)) ≤
        (C₁ + C₂ + CI + (n₀ : ℝ) ^ p) *
          (if d = 2 then Real.log ((n : ℝ) + 2) ^ 2 else Real.log ((n : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_right (by linarith) hlam0
    refine hω ⟨?_, fun s t hst htn => (hint s t hst htn).trans (add_le_add le_rfl hC₁le),
      fun y hy => ?_⟩
    · have h1 : maxLocalTime (fun j => X j ω) n ≤ intervalMax (fun j => X j ω) 0 n :=
        Finset.sup_le fun z _ => by
          rw [← CERW.Support.Occupation.intervalLocalTime_zero]
          exact intervalLocalTime_le_intervalMax _ 0 n z
      have h2 := hint 0 n (by omega) le_rfl
      rw [CERW.Support.Occupation.freshCount_zero] at h2
      exact (Nat.cast_le.mpr h1).trans (h2.trans (add_le_add le_rfl hC₁le))
    · have h := approx_bound hd hK.poisson (abs_nonneg Cb) hCS0 hCM0 hCI0.le hε.le hBn hCb'
        (hCS ε hε.le) (hCM ε hε.le) X ω h0 hnorm hn hsq hmart y hy
      rw [error_scale_eq d (Nat.cast_nonneg _)]
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith)
        (add_nonneg (mul_nonneg hBn (Real.sqrt_nonneg _)) (by linarith)))
  · exact (prob_le_one).trans (ENNReal.one_le_ofReal.mpr
      (one_le_mul_rpow_neg hp (by omega) (not_le.mp hn₀le).le (by linarith)))

end CERW.Support.LocalTime
