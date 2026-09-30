import CERW.Support.Law.CoordinateDrift
import CERW.Generic.Martingale.Dyadic
import CERW.Generic.Martingale.Clamp

/-!
# The compensated position

`Z_t = X_t + ε Σ_{j<t} I_j u_{X_j}` (`eq:vector-def`), where `I_j` indicates a first departure from
a nonzero site. Each coordinate of `Z_t - Z_0` is the Dynkin martingale of that coordinate. Its
increments are at most `2` and its conditional variances at most `1`. Freedman's inequality at
dyadic brackets, applied to every interval, every coordinate and every time horizon, gives
`eq:vector`: with probability at least `1 - Cn^{-p}`,
`|Z_t - Z_s| ≤ C √((t - s) L)` for all `0 ≤ s < t ≤ n`.
-/

namespace CERW.Support.Coarse

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law

variable {d : ℕ}

/-- The compensated position `Z_t = X_t + ε Σ_{j<t} I_j u_{X_j}` of `eq:vector-def`. -/
noncomputable def compensated {Ω : Type*} (ε : ℝ) (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  toSpace (X t ω) + ε • ∑ j ∈ range t,
    (if X j ω ≠ 0 ∧ X j ω ∉ (range j).image (fun i => X i ω) then unitDir (toSpace (X j ω))
      else 0)

/-- The `k`-th coordinate of the compensated position is the Dynkin martingale of the `k`-th
coordinate plus the initial coordinate. -/
private lemma compensated_apply (hd : 1 ≤ d) {Ω : Type*} (ε : ℝ) (X : ℕ → Ω → Site d) (t : ℕ)
    (ω : Ω) (k : Fin d) :
    compensated ε X t ω k =
      dynkin ε (fun z : Site d => ((z k : ℤ) : ℝ)) X t ω + ((X 0 ω k : ℤ) : ℝ) := by
  have hterm : ∀ j, nextMean ε (fun z : Site d => ((z k : ℤ) : ℝ)) (fun i => X i ω) j -
      ((X j ω k : ℤ) : ℝ) = -(ε * (if X j ω ≠ 0 ∧ X j ω ∉ (range j).image (fun i => X i ω)
        then unitDir (toSpace (X j ω)) else 0).ofLp k) := by
    intro j
    rw [nextMean_coord hd ε _ j k]
    split_ifs <;> simp
  rw [compensated, dynkin, PiLp.add_apply, PiLp.smul_apply, toSpace_apply, smul_eq_mul,
    WithLp.ofLp_sum, Finset.sum_apply, sum_congr rfl fun j _ => hterm j, sum_neg_distrib,
    ← mul_sum]
  ring

/-- A vector of Euclidean space has norm at most the sum of the absolute values of its
coordinates. -/
private lemma norm_le_sum_abs (w : EuclideanSpace ℝ (Fin d)) : ‖w‖ ≤ ∑ k, |w k| := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  simpa only [Real.norm_eq_abs, sq_abs] using
    sum_sq_le_sq_sum_of_nonneg (s := univ) (f := fun k => |w k|) fun _ _ => abs_nonneg _

/-- A process whose steps are at most `b` moves by at most `k b` in `k` steps. -/
private lemma abs_sub_le_mul_of_increments {M : ℕ → ℝ} {b : ℝ} (h : ∀ i, |M (i + 1) - M i| ≤ b)
    (s k : ℕ) : |M (s + k) - M s| ≤ k * b := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := h (s + k)
    calc |M (s + (k + 1)) - M s|
        = |(M (s + k + 1) - M (s + k)) + (M (s + k) - M s)| := by ring_nf
      _ ≤ |M (s + k + 1) - M (s + k)| + |M (s + k) - M s| := abs_add_le _ _
      _ ≤ ((k + 1 : ℕ) : ℝ) * b := by push_cast; linarith

/-- If `x ≤ c (√(δL) + 2L)` and `x ≤ 2δ`, with `δ ≥ 1`, then `x ≤ (2 + 3c) √(δL)`: the smaller
of `δ` and `L` is at most `√(δL)`. -/
private lemma le_mul_sqrt_of_le {c x δ L : ℝ} (hc : 0 ≤ c) (hδ : 1 ≤ δ) (hL : 0 < L)
    (h1 : x ≤ c * (Real.sqrt (δ * L) + 2 * L)) (h2 : x ≤ 2 * δ) :
    x ≤ (2 + 3 * c) * Real.sqrt (δ * L) := by
  have hδ0 : 0 < δ := by linarith
  set a := Real.sqrt (δ * L) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = δ * L := Real.sq_sqrt (mul_nonneg hδ0.le hL.le)
  rcases le_total δ L with hle | hle
  · have hδa : δ ≤ a := by
      refine le_of_not_gt fun hcon => ?_
      nlinarith
    nlinarith
  · have hLa : L ≤ a := by
      refine le_of_not_gt fun hcon => ?_
      nlinarith
    nlinarith

/-- Freedman's inequality on every interval `[s, t] ⊆ [0, n]`: a martingale with increments at
most `2` and conditional variances at most `1` satisfies `|M_t - M_s| ≤ C √((t - s) L)` except on
an event of probability at most `(n + 1) · 2 e^{-KL}`, where `L = log (n + 2)`. -/
private lemma exists_interval_bound {K : ℝ} (hK : 0 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
      [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ},
      Martingale M ℱ μ → (∀ i ω, |M (i + 1) ω - M i ω| ≤ 2) →
      (∀ j, μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | ℱ j] ≤ᵐ[μ] fun _ => 1) →
      ∀ n : ℕ, 1 ≤ n → ∀ s t : ℕ, s < t → t ≤ n →
        μ {ω | c * Real.sqrt (((t : ℝ) - s) * Real.log (n + 2)) < |M t ω - M s ω|} ≤
          ENNReal.ofReal (((n : ℝ) + 1) * (2 * Real.exp (-(K * Real.log (n + 2))))) := by
  obtain ⟨c, hc1, hc⟩ := CERW.Generic.Martingale.exists_dyadic_bound hK
  refine ⟨2 + 3 * c, by linarith, ?_⟩
  intro Ω m0 μ _ ℱ M hmart hinc hvar n hn s t hst htn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst.le
  have hk : 1 ≤ k := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn : ((s + k : ℕ) : ℝ) - s ≤ n := by
    have : s + k ≤ n := htn
    have h2 : ((s + k : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    have h3 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    linarith
  have hvar' : ∀ j, μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | ℱ j] ≤ᵐ[μ]
      fun ω => ((((j + 1 : ℕ) : ℝ) : ℝ) - (j : ℝ) : ℝ) := by
    intro j
    have h1 : (fun _ : Ω => (((j + 1 : ℕ) : ℝ) - (j : ℝ))) = fun _ => 1 := by
      funext _
      push_cast
      ring
    rw [h1]
    exact hvar j
  have hdy := hc hmart (V := fun j _ => (j : ℝ)) (fun j => stronglyMeasurable_const)
    (fun _ => by simp) (fun j _ => by simp) hvar' (b := 2) (by norm_num) s k
    (fun i _ _ ω => hinc i ω) (W := n) (L := Real.log ((n : ℝ) + 2)) hnR hL (fun _ => hkn)
  have hcast : ((s + k : ℕ) : ℝ) - s = k := by
    push_cast
    ring
  have hmax : max (k : ℝ) 1 = (k : ℝ) := max_eq_left hkR
  refine le_trans (measure_mono fun ω hω => ?_) (hdy.trans ?_)
  · simp only [Set.mem_setOf_eq, hcast, hmax] at hω ⊢
    refine lt_of_not_ge fun hle => absurd hω (not_lt_of_ge ?_)
    have hsteps := abs_sub_le_mul_of_increments (M := fun i => M i ω) (fun i => hinc i ω) s k
    exact le_mul_sqrt_of_le (by linarith) hkR hL hle (by linarith)
  · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [Nat.ceil_natCast]
    have hclog : Nat.clog 2 n ≤ n := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
    have : (Nat.clog 2 n : ℝ) ≤ n := by exact_mod_cast hclog
    linarith

/-- A unit step changes a coordinate of a site by at most one. -/
private lemma abs_coord_add_sub_le (k : Fin d) (x e : Site d) (he : e ∈ unitSteps d) :
    |((((x + e) k : ℤ) : ℝ)) - ((x k : ℤ) : ℝ)| ≤ 1 := by
  obtain ⟨i, rfl | rfl⟩ := mem_unitSteps.mp he
  · simp only [Pi.add_apply, unit_apply_coord]
    split_ifs <;> simp
  · simp only [Pi.add_apply, Pi.neg_apply, unit_apply_coord]
    split_ifs <;> simp

/-- Each coordinate of the walk yields a martingale with increments at most `2` and conditional
variances at most `1` that agrees almost surely with its Dynkin martingale. -/
private lemma exists_clamped_coord (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) (k : Fin d) :
    ∃ M : ℕ → Ω → ℝ, Martingale M (pathFiltration hX.measurable) μ ∧
      (∀ i ω, |M (i + 1) ω - M i ω| ≤ 2) ∧
      (∀ j, μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | pathFiltration hX.measurable j] ≤ᵐ[μ]
        fun _ => 1) ∧
      ∀ᵐ ω ∂μ, ∀ i, M i ω = dynkin ε (fun z : Site d => ((z k : ℤ) : ℝ)) X i ω := by
  set f : Site d → ℝ := fun z => ((z k : ℤ) : ℝ) with hf
  have hmart := martingale_dynkin hd hε hεd hX f
  have hinc : ∀ i, ∀ᵐ ω ∂μ, |dynkin ε f X (i + 1) ω - dynkin ε f X i ω| ≤ 2 := fun i =>
    (ae_abs_dynkin_succ_sub_le hd hε hεd hX f).mono fun ω hω => by
      simpa using hω i 1 fun e he => abs_coord_add_sub_le k (X i ω) e he
  obtain ⟨M, hM, hbd, -, hae⟩ := CERW.Generic.Martingale.exists_martingale_clamp hmart
    (b := 2) (by norm_num) hinc
  refine ⟨M, hM, hbd, fun j => ?_, hae⟩
  have hsq : (fun ω => (M (j + 1) ω - M j ω) ^ 2) =ᵐ[μ]
      fun ω => (dynkin ε f X (j + 1) ω - dynkin ε f X j ω) ^ 2 := by
    filter_upwards [hae] with ω hω
    rw [hω, hω]
  refine (condExp_congr_ae hsq).trans_le ?_
  filter_upwards [condExp_sq_dynkin_succ_sub_le hd hε hεd hX f j] with ω hω
  refine hω.trans ?_
  calc ∑ e ∈ unitSteps d, stepProb d ε (fun i => X i ω) j e * (f (X j ω + e) - f (X j ω)) ^ 2
      ≤ ∑ e ∈ unitSteps d, stepProb d ε (fun i => X i ω) j e * 1 := by
        refine sum_le_sum fun e he => mul_le_mul_of_nonneg_left ?_ (stepProb_nonneg hε hεd _ j e)
        have := abs_coord_add_sub_le k (X j ω) e he
        rw [← sq_abs]
        nlinarith [abs_nonneg (f (X j ω + e) - f (X j ω))]
    _ = 1 := by simp only [mul_one, sum_stepProb hd ε _ j]

/-- If every coordinate of a family of processes that agree with the Dynkin martingales moves by
at most `R` between `s` and `t`, then the compensated position moves by at most `d R`. -/
private lemma norm_compensated_sub_le (hd : 1 ≤ d) {Ω : Type*} (ε : ℝ) (X : ℕ → Ω → Site d)
    (M : Fin d → ℕ → Ω → ℝ) (ω : Ω)
    (hω : ∀ k i, M k i ω = dynkin ε (fun z : Site d => ((z k : ℤ) : ℝ)) X i ω) (s t : ℕ)
    {R : ℝ} (hR : ∀ k, |M k t ω - M k s ω| ≤ R) :
    ‖compensated ε X t ω - compensated ε X s ω‖ ≤ d * R := by
  refine (norm_le_sum_abs _).trans ?_
  calc ∑ k, |(compensated ε X t ω - compensated ε X s ω) k|
      ≤ ∑ _k : Fin d, R := by
        refine sum_le_sum fun k _ => ?_
        have h := hR k
        rw [hω k t, hω k s] at h
        have e : (compensated ε X t ω - compensated ε X s ω) k =
            dynkin ε (fun z : Site d => ((z k : ℤ) : ℝ)) X t ω -
              dynkin ε (fun z : Site d => ((z k : ℤ) : ℝ)) X s ω := by
          rw [PiLp.sub_apply, compensated_apply hd, compensated_apply hd]
          ring
        rw [e]
        exact h
    _ = d * R := by simp

/-- The arithmetic of the union bound: `D (n + 1)² · (n + 1) · 2 e^{-(p+3) log (n+2)}` is at most
`16 D n^{-p}`. -/
private lemma union_bound_arith {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 1 ≤ n) (D : ℕ) :
    ((D : ℝ) * ((n : ℝ) + 1) ^ 2) * (((n : ℝ) + 1) *
      (2 * Real.exp (-((p + 3) * Real.log ((n : ℝ) + 2))))) ≤ (16 * D) * (n : ℝ) ^ (-p) := by
  have h1 := CERW.Generic.Martingale.two_mul_exp_neg_mul_log_le (K := p + 3) (by linarith) hn
  have h2 := CERW.Generic.Martingale.pow_mul_rpow_neg_le hn 3 p
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h3 : (0 : ℝ) ≤ ((D : ℝ) * ((n : ℝ) + 1) ^ 2) * ((n : ℝ) + 1) := by positivity
  calc ((D : ℝ) * ((n : ℝ) + 1) ^ 2) * (((n : ℝ) + 1) *
        (2 * Real.exp (-((p + 3) * Real.log ((n : ℝ) + 2)))))
      = (((D : ℝ) * ((n : ℝ) + 1) ^ 2) * ((n : ℝ) + 1)) *
          (2 * Real.exp (-((p + 3) * Real.log ((n : ℝ) + 2)))) := by ring
    _ ≤ (((D : ℝ) * ((n : ℝ) + 1) ^ 2) * ((n : ℝ) + 1)) * (2 * (n : ℝ) ^ (-(p + 3))) :=
        mul_le_mul_of_nonneg_left h1 h3
    _ = 2 * D * (((n : ℝ) + 1) ^ 3 * (n : ℝ) ^ (-(p + ((3 : ℕ) : ℝ)))) := by
        push_cast
        ring
    _ ≤ 2 * D * (2 ^ 3 * (n : ℝ) ^ (-p)) := by
        refine mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (16 * D) * (n : ℝ) ^ (-p) := by ring

/-- `eq:vector`: for every `p > 0` there is `C` such that, for every `n ≥ 1`, with probability at
least `1 - Cn^{-p}`, `|Z_t - Z_s| ≤ C √((t - s) L)` for all `0 ≤ s < t ≤ n`, where
`L = log(n + 2)`. -/
theorem exists_compensated_bound (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      {X : ℕ → Ω → Site d}, IsCERW μ ε X → ∀ n : ℕ, 1 ≤ n →
        μ {ω | ∃ s t : ℕ, s < t ∧ t ≤ n ∧
          C * Real.sqrt (((t : ℝ) - s) * Real.log (n + 2)) <
            ‖compensated ε X t ω - compensated ε X s ω‖} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨c, hc0, hc⟩ := exists_interval_bound (K := p + 3) (by linarith)
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨d * c + 16 * d, by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn
  choose M hM hbd hvar hae using fun k : Fin d => exists_clamped_coord hd hε hεd hX k
  set P : Finset (ℕ × ℕ) := ((range (n + 1)) ×ˢ (range (n + 1))).filter (fun q => q.1 < q.2)
    with hP
  set B : Fin d → ℕ × ℕ → Set Ω := fun k q =>
    {ω | c * Real.sqrt (((q.2 : ℝ) - q.1) * Real.log (n + 2)) < |M k q.2 ω - M k q.1 ω|}
    with hB
  have hsub : {ω | ∃ s t : ℕ, s < t ∧ t ≤ n ∧
      (d * c + 16 * d) * Real.sqrt (((t : ℝ) - s) * Real.log (n + 2)) <
        ‖compensated ε X t ω - compensated ε X s ω‖} ≤ᵐ[μ] ⋃ k, ⋃ q ∈ P, B k q := by
    filter_upwards [ae_all_iff.mpr hae] with ω hω hE
    obtain ⟨s, t, hst, htn, hlt⟩ := hE
    by_contra hnot
    have hnot' : ω ∉ ⋃ k, ⋃ q ∈ P, B k q := hnot
    simp only [Set.mem_iUnion, not_exists, hB, Set.mem_setOf_eq, not_lt] at hnot'
    
    have hmem : (s, t) ∈ P := by
      simp only [hP, mem_filter, mem_product, mem_range]
      omega
    have hle := norm_compensated_sub_le hd ε X M ω hω s t
      (R := c * Real.sqrt (((t : ℝ) - s) * Real.log (n + 2))) fun k => hnot' k (s, t) hmem
    have hsq := Real.sqrt_nonneg (((t : ℝ) - s) * Real.log (n + 2))
    nlinarith
  set a : ℝ := ((n : ℝ) + 1) * (2 * Real.exp (-((p + 3) * Real.log ((n : ℝ) + 2)))) with ha
  have ha0 : 0 ≤ a := by positivity
  have hbound : ∀ k : Fin d, ∀ q ∈ P, μ (B k q) ≤ ENNReal.ofReal a := by
    intro k q hq
    have hq' := mem_filter.mp hq
    have h2 : q.2 ≤ n := by
      have := mem_range.mp (mem_product.mp hq'.1).2
      omega
    exact hc (hM k) (hbd k) (hvar k) n hn q.1 q.2 hq'.2 h2
  have hPcard : (P.card : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have h1 : P.card ≤ (n + 1) * (n + 1) := by
      refine (card_filter_le _ _).trans ?_
      simp
    exact_mod_cast h1.trans_eq (by ring)
  refine (measure_mono_ae hsub).trans ?_
  calc μ (⋃ k, ⋃ q ∈ P, B k q) ≤ ∑ k, μ (⋃ q ∈ P, B k q) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ k : Fin d, ∑ q ∈ P, μ (B k q) := sum_le_sum fun k _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ _k : Fin d, ∑ _q ∈ P, ENNReal.ofReal a :=
        sum_le_sum fun k _ => sum_le_sum fun q hq => hbound k q hq
    _ = ENNReal.ofReal ((d : ℝ) * P.card * a) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ ≤ ENNReal.ofReal ((d * c + 16 * d) * (n : ℝ) ^ (-p)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (d : ℝ) * P.card * a ≤ ((d : ℝ) * ((n : ℝ) + 1) ^ 2) * a :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPcard (by positivity)) ha0
        have h2 := union_bound_arith hp.le hn d
        have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ d) hc0.le) h3]

end CERW.Support.Coarse
