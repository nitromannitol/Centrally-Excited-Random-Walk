import CERW.Support.Lower.PlanarGap.Clt

/-!
# The width of the planar range is not small

The two radii of the planar range differ by `G_n = R_out(n) − R_in(n)`. The sum of the first
coordinates of the unit directions over the departure range is a sum over the sites between the two
radii, so the first coordinate `Y_n` of the compensated position forces the width to be large when
`|Y_n|` is large (`width_ge_of_abs_dev`, the two-sided form of `width_ge_of_dev`). Since `Y_n / √n`
is asymptotically `N(0, 1/2)` (`PlanarGap.Clt`), portmanteau on closed intervals and the absence of
atoms of the Gaussian give
`limsup P(G_n ≤ a √r_n) ≤ N(0, 1/2)[−a c, a c]`, `c = √(3 ε / π)`, and hence
`P(G_n ≤ a_n √r_n) → 0` for every deterministic `a_n → 0`. Together with the proved upper bound for
the width this places `G_n` between `n^{1/6 − η}` and `n^{1/6 + η}` with probability tending to one.

The constant `c` is the one of the scalar (first-coordinate) estimate; the sharper
two-dimensional constant `1 − exp(−3 ε a² / π)` needs the annulus bound in every direction and the
law of the norm of a planar Gaussian, which are not proved here.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Lower.PlanarGap

open CERW CERW.Support.Law CERW.Support.Lower

/-! ### The width controls the first coordinate of the compensated position -/

/-- The inner radius is nonnegative. -/
private theorem innerRadius_nonneg {d : ℕ} (X : ℕ → Site d) (n : ℕ) :
    0 ≤ innerRadius X n := by
  refine Real.sInf_nonneg ?_
  rintro _ ⟨y, -, rfl⟩
  exact norm_nonneg y

/-- The outer radius is nonnegative. -/
private theorem maxRadius_nonneg {d : ℕ} (X : ℕ → Site d) (n : ℕ) : 0 ≤ maxRadius X n :=
  (LatticeProb.euclidNorm_nonneg (X 0)).trans (euclidNorm_le_maxRadius X (Nat.zero_le n))

/-- A site in the open ball of radius the inner radius belongs to the departure range. -/
private theorem mem_departureRange_of_lt_innerRadius {d : ℕ} {X : ℕ → Site d} {n : ℕ}
    {x : Site d} (h : euclidNorm x < innerRadius X n) : x ∈ departureRange X n := by
  by_contra hx
  have hmem : toSpace x ∈ (cellSet X n)ᶜ := fun hc =>
    hx ((CERW.Support.Occupation.toSpace_mem_cellSet_iff X n x).mp hc)
  have hle : innerRadius X n ≤ ‖toSpace x‖ := by
    refine csInf_le ⟨0, ?_⟩ ⟨toSpace x, hmem, rfl⟩
    rintro _ ⟨y, -, rfl⟩
    exact norm_nonneg y
  rw [norm_toSpace] at hle
  exact absurd h (not_lt.mpr hle)

/-- A site of the departure range is within the outer radius. -/
private theorem euclidNorm_le_maxRadius_of_mem {d : ℕ} {X : ℕ → Site d} {n : ℕ} {x : Site d}
    (hx : x ∈ departureRange X n) : euclidNorm x ≤ maxRadius X n :=
  LatticeProb.mem_ballFinset_iff.mp
    (CERW.Support.Occupation.departureRange_subset_ballFinset X n hx)

/-- **Two-sided width bound.** If the absolute value of the first coordinate of the compensated
position exceeds `T + M` and the outer radius is at most `M`, then the difference of the radii is at
least `T / (ε (2 M + 7)) - 1`. For positive deviations this is `width_ge_of_dev`; for negative
deviations the same argument applies to `-V`, `V` the sum of the first coordinates of the
directions over the range. -/
theorem width_ge_of_abs_dev {x : ℕ → Site 2} {n : ℕ} {ε T M : ℝ} (hε : 0 < ε)
    (hM : maxRadius x n ≤ M)
    (hdev : T + M ≤ |((x n 0 : ℤ) : ℝ) +
      ε * ∑ z ∈ departureRange x n, (unitDir (toSpace z)) 0|) :
    T / (ε * (2 * M + 7)) - 1 ≤ maxRadius x n - innerRadius x n := by
  set V := ∑ z ∈ departureRange x n, (unitDir (toSpace z)) 0 with hV
  rcases le_total 0 (((x n 0 : ℤ) : ℝ) + ε * V) with hsign | hsign
  · rw [abs_of_nonneg hsign] at hdev
    exact width_ge_of_dev hε hM hdev
  · rw [abs_of_nonpos hsign] at hdev
    have hR0 : 0 ≤ maxRadius x n := maxRadius_nonneg x n
    have hρ0 : 0 ≤ innerRadius x n := innerRadius_nonneg x n
    have hG := abs_sum_dir_le (departureRange x n) hρ0 hR0
      (fun z hz => mem_departureRange_of_lt_innerRadius hz)
      (fun z hz => euclidNorm_le_maxRadius_of_mem hz)
    have hx0 : -((x n 0 : ℤ) : ℝ) ≤ maxRadius x n :=
      (neg_le_abs _).trans ((abs_coord_le_euclidNorm (x n) 0).trans
        (euclidNorm_le_maxRadius x le_rfl))
    have hw : 0 ≤ maxRadius x n - innerRadius x n + 1 := by
      by_contra hcon
      have hneg : maxRadius x n - innerRadius x n + 1 < 0 := not_le.mp hcon
      have h1 : (maxRadius x n - innerRadius x n + 1) *
          (maxRadius x n + innerRadius x n + 6) < 0 :=
        mul_neg_of_neg_of_pos hneg (by linarith)
      linarith [abs_nonneg V]
    have hρR : innerRadius x n ≤ maxRadius x n + 1 := by linarith
    have hεV : T ≤ ε * |V| := by
      have h1 : T ≤ -(ε * V) := by linarith
      calc T ≤ -(ε * V) := h1
        _ ≤ ε * |V| := by
          rw [← mul_neg]
          exact mul_le_mul_of_nonneg_left (neg_le_abs V) hε.le
    have h1 : (maxRadius x n - innerRadius x n + 1) * (maxRadius x n + innerRadius x n + 6) ≤
        (maxRadius x n - innerRadius x n + 1) * (2 * M + 7) :=
      mul_le_mul_of_nonneg_left (by linarith) hw
    have h2 : T ≤ (maxRadius x n - innerRadius x n + 1) * (ε * (2 * M + 7)) := by
      calc T ≤ ε * |V| := hεV
        _ ≤ ε * ((maxRadius x n - innerRadius x n + 1) * (2 * M + 7)) :=
            mul_le_mul_of_nonneg_left (hG.trans h1) hε.le
        _ = (maxRadius x n - innerRadius x n + 1) * (ε * (2 * M + 7)) := by ring
    have hM0 : 0 ≤ M := hR0.trans hM
    have hpos : 0 < ε * (2 * M + 7) := mul_pos hε (by linarith)
    have h3 : T / (ε * (2 * M + 7)) ≤ maxRadius x n - innerRadius x n + 1 := by
      rw [div_le_iff₀ hpos]
      exact h2
    linarith

/-- If the width is at most `b` and the outer radius at most `M`, the first coordinate of the
compensated position is at most `M + ε (2 M + 7) (b + 1)` in absolute value. -/
theorem abs_dev_le_of_width_le {x : ℕ → Site 2} {n : ℕ} {ε M b : ℝ} (hε : 0 < ε)
    (hM : maxRadius x n ≤ M) (hb : maxRadius x n - innerRadius x n ≤ b) :
    |((x n 0 : ℤ) : ℝ) + ε * ∑ z ∈ departureRange x n, (unitDir (toSpace z)) 0| ≤
      M + ε * (2 * M + 7) * (b + 1) := by
  have hM0 : 0 ≤ M := (maxRadius_nonneg x n).trans hM
  have hpos : 0 < ε * (2 * M + 7) := mul_pos hε (by linarith)
  have h := width_ge_of_abs_dev (T := |((x n 0 : ℤ) : ℝ) +
    ε * ∑ z ∈ departureRange x n, (unitDir (toSpace z)) 0| - M) hε hM (by linarith)
  have h2 : (|((x n 0 : ℤ) : ℝ) + ε * ∑ z ∈ departureRange x n, (unitDir (toSpace z)) 0| - M) /
      (ε * (2 * M + 7)) ≤ b + 1 := by linarith
  rw [div_le_iff₀ hpos] at h2
  nlinarith

/-! ### Closed intervals under a limit law -/

/-- Continuity from above for symmetric closed intervals: the measures of the intervals
`[-(c + 1/(k+1)), c + 1/(k+1)]` tend to that of `[-c, c]`. -/
theorem tendsto_measure_Icc_add_inv (ν : Measure ℝ) [IsFiniteMeasure ν] (c : ℝ) :
    Tendsto (fun k : ℕ => ν (Set.Icc (-(c + 1 / ((k : ℝ) + 1))) (c + 1 / ((k : ℝ) + 1))))
      atTop (𝓝 (ν (Set.Icc (-c) c))) := by
  have hanti : Antitone
      (fun k : ℕ => Set.Icc (-(c + 1 / ((k : ℝ) + 1))) (c + 1 / ((k : ℝ) + 1))) := by
    intro i j hij x hx
    have h : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hlim := tendsto_measure_iInter_atTop (μ := ν)
    (fun k => measurableSet_Icc.nullMeasurableSet) hanti ⟨0, measure_ne_top ν _⟩
  have hinter : (⋂ k : ℕ, Set.Icc (-(c + 1 / ((k : ℝ) + 1))) (c + 1 / ((k : ℝ) + 1))) =
      Set.Icc (-c) c := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Icc]
    constructor
    · intro h
      constructor
      · by_contra hlt
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < -c - x by linarith [not_le.mp hlt])
        linarith [(h k).1]
      · by_contra hlt
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < x - c by linarith [not_le.mp hlt])
        linarith [(h k).2]
    · rintro ⟨h1, h2⟩ k
      have hk : 0 < 1 / ((k : ℝ) + 1) := by positivity
      exact ⟨by linarith, by linarith⟩
  rw [hinter] at hlim
  exact hlim

/-- A centered Gaussian of positive variance gives small mass to short intervals about the
origin. -/
theorem gaussianReal_Icc_tendsto_zero :
    Tendsto (fun k : ℕ => gaussianReal 0 (1 / 2)
      (Set.Icc (-(1 / ((k : ℝ) + 1))) (1 / ((k : ℝ) + 1)))) atTop (𝓝 0) := by
  have h := tendsto_measure_Icc_add_inv (gaussianReal 0 (1 / 2)) 0
  haveI : NullSingletonClass (gaussianReal 0 (1 / 2)) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have h0 : gaussianReal 0 (1 / 2) (Set.Icc (-(0 : ℝ)) 0) = 0 := by
    rw [neg_zero, Set.Icc_self, measure_singleton]
  rw [h0] at h
  simpa only [zero_add] using h

/-- Portmanteau for symmetric closed intervals: if `f n ⇒ ν` then
`limsup P(|f n| ≤ t) ≤ ν [-t, t]`. -/
theorem limsup_measure_abs_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h : TendstoInDistribution f atTop id (fun _ => μ) ν) (t : ℝ) :
    limsup (fun n => μ {ω | |f n ω| ≤ t}) atTop ≤ ν (Set.Icc (-t) t) := by
  have h1 := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto
    (isClosed_Icc (a := -t) (b := t))
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at h1
  have h2 : ∀ n, μ.map (f n) (Set.Icc (-t) t) = μ {ω | |f n ω| ≤ t} := fun n => by
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) measurableSet_Icc]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_setOf_eq, abs_le]
  simpa only [h2] using h1

/-! ### The scalar small-ball bound -/

/-- If `A n ⊆ F n ∪ B n` eventually, `P(B n) → 0` and `limsup P(F n) ≤ x`, then
`limsup P(A n) ≤ x`. -/
theorem limsup_measure_le_of_eventually_subset {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A F B : ℕ → Set Ω} {x : ℝ≥0∞} (hsub : ∀ᶠ n in atTop, A n ⊆ F n ∪ B n)
    (hB : Tendsto (fun n => μ (B n)) atTop (𝓝 0))
    (hF : limsup (fun n => μ (F n)) atTop ≤ x) : limsup (fun n => μ (A n)) atTop ≤ x := by
  have hmeas : ∀ᶠ n in atTop, μ (A n) ≤ μ (F n) + μ (B n) := by
    filter_upwards [hsub] with n hn
    exact (measure_mono hn).trans (measure_union_le _ _)
  have hlim : limsup (fun n => μ (F n) + μ (B n)) atTop = limsup (fun n => μ (F n)) atTop :=
    ENNReal.limsup_add_of_right_tendsto_zero hB (fun n => μ (F n))
  calc limsup (fun n => μ (A n)) atTop ≤ limsup (fun n => μ (F n) + μ (B n)) atTop :=
        limsup_le_limsup hmeas
    _ = limsup (fun n => μ (F n)) atTop := hlim
    _ ≤ x := hF

/-- The width threshold, divided by `√n`, converges: for `r = K q²`, `q = n^{1/6}`, and the
outer-radius bound `M = (1 + η) r`, the quantity `(M + ε (2 M + 7) (a √r + 1)) / √n` tends to
`2 ε (1 + η) a K √K`. -/
theorem tendsto_width_threshold {K ε : ℝ} (hK : 0 ≤ K) (a η : ℝ) :
    Tendsto (fun n : ℕ =>
      ((1 + η) * (K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2) +
        ε * (2 * ((1 + η) * (K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2)) + 7) *
          (a * Real.sqrt (K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2) + 1)) / Real.sqrt n)
      atTop (𝓝 (2 * ε * (1 + η) * a * (K * Real.sqrt K))) := by
  have h1 := tendsto_inv_rpow_sixth_pow (m := 1) one_ne_zero
  have h2 := tendsto_inv_rpow_sixth_pow (m := 2) two_ne_zero
  have h3 := tendsto_inv_rpow_sixth_pow (m := 3) (by norm_num)
  have hsum := ((((h1.const_mul ((1 + η) * K)).add
    (tendsto_const_nhds (x := 2 * ε * (1 + η) * a * (K * Real.sqrt K)))).add
    (h1.const_mul (2 * ε * (1 + η) * K))).add (h2.const_mul (7 * ε * a * Real.sqrt K))).add
    (h3.const_mul (7 * ε))
  have hlim : (1 + η) * K * 0 + 2 * ε * (1 + η) * a * (K * Real.sqrt K) +
      2 * ε * (1 + η) * K * 0 + 7 * ε * a * Real.sqrt K * 0 + 7 * ε * 0 =
      2 * ε * (1 + η) * a * (K * Real.sqrt K) := by ring
  rw [hlim] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hq0 : 0 < (n : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  rw [sqrt_natCast_eq_rpow_sixth_cube n, Real.sqrt_mul hK, Real.sqrt_sq hq0.le]
  generalize (n : ℝ) ^ ((1 : ℝ) / 6) = q at hq0 ⊢
  field_simp
  ring

/-- The planar radius constant: with `K = (3 / (4 ε π))^{1/3}` one has `2 ε K √K = √(3 ε / π)`. -/
theorem two_mul_eps_mul_radius_const {ε : ℝ} (hε : 0 < ε) :
    2 * ε * ((3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) *
        Real.sqrt ((3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3))) =
      Real.sqrt (3 * ε / Real.pi) := by
  set K : ℝ := (3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) with hKdef
  have hK : 0 < K := by positivity
  have hK3 : K ^ 3 = 3 / (4 * ε * Real.pi) := by
    rw [hKdef, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  symm
  have hsq : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK.le
  calc 2 * ε * (K * Real.sqrt K) * (2 * ε * (K * Real.sqrt K))
      = 4 * ε ^ 2 * K ^ 2 * (Real.sqrt K * Real.sqrt K) := by ring
    _ = 4 * ε ^ 2 * K ^ 3 := by rw [hsq]; ring
    _ = 3 * ε / Real.pi := by
        rw [hK3]
        field_simp

/-- The event on which the proved radius bounds of `planar_radii_rates` fail has probability
tending to zero (here with `p = 1`). -/
theorem planar_radii_bad_tendsto {ε : ℝ} (hε0 : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ)) :
    let r : ℕ → ℝ := fun n =>
      ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal)) ^
        ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site 2), IsCERW μ ε X →
        Tendsto (fun n : ℕ => μ {ω | ¬ (|innerRadius (fun j => X j ω) n - r n| ≤
          C * Real.sqrt (r n * Real.log n) ∧ maxRadius (fun j => X j ω) n - r n ≤
            C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2))}) atTop (𝓝 0) := by
  intro r
  obtain ⟨C, hC, hprob, -⟩ := planar_radii_rates hε0 hεd (p := 1) one_pos
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ X hX
  have hz : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(1 : ℝ))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp
      tendsto_natCast_atTop_atTop).const_mul C
    simpa using this
  have hz' := ENNReal.tendsto_ofReal hz
  rw [ENNReal.ofReal_zero] at hz'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz'
    (Eventually.of_forall fun n => bot_le) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact hprob μ X hX n hn

/-- **Scalar small-ball bound for the width of the planar range.** For `0 < ε < 1/2` and `a ≥ 0`,
`limsup_n P(R_out(n) − R_in(n) ≤ a √r_n) ≤ N(0, 1/2)[−a c, a c]`, `c = √(3 ε / π)`.

The constant is that of the first-coordinate estimate; the two-dimensional bound
`1 − exp(−3 ε a² / π)` is not proved here. -/
theorem gap_limsup_le_gaussian {ε : ℝ} (hε0 : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X) {a : ℝ} (ha : 0 ≤ a) :
    let r : ℕ → ℝ := fun n =>
      ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal)) ^
        ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
    limsup (fun n => μ {ω | maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n ≤
        a * Real.sqrt (r n)}) atTop ≤
      gaussianReal 0 (1 / 2) (Set.Icc (-(a * Real.sqrt (3 * ε / Real.pi)))
        (a * Real.sqrt (3 * ε / Real.pi))) := by
  intro r
  set K : ℝ := (3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) with hKdef
  have hK : 0 < K := by positivity
  have hr : ∀ n : ℕ, r n = K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 := fun n => planar_radius_eq hε0 n
  have hc := two_mul_eps_mul_radius_const hε0
  rw [← hKdef] at hc
  set c : ℝ := Real.sqrt (3 * ε / Real.pi) with hcdef
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hclt := coordinate_clt hε0 hεd μ hX
  obtain ⟨C, hC, hbadT⟩ := planar_radii_bad_tendsto hε0 hεd
  have hk : ∀ k : ℕ, limsup (fun n => μ {ω | maxRadius (fun j => X j ω) n -
        innerRadius (fun j => X j ω) n ≤ a * Real.sqrt (r n)}) atTop ≤
      gaussianReal 0 (1 / 2) (Set.Icc (-(a * c + 1 / ((k : ℝ) + 1)))
        (a * c + 1 / ((k : ℝ) + 1))) := by
    intro k
    set η' : ℝ := 1 / ((k : ℝ) + 1) with hη'
    have hη'0 : 0 < η' := by positivity
    have hac : 0 ≤ a * c := mul_nonneg ha hc0
    set η : ℝ := η' / (2 * (a * c + 1)) with hη
    have hη0 : 0 < η := by positivity
    have hev1 := eventually_sqrt_mul_log_le hK C hη0
    have hlim := tendsto_width_threshold (K := K) (ε := ε) hK.le a η
    have hL : 2 * ε * (1 + η) * a * (K * Real.sqrt K) < a * c + η' := by
      have h1 : 2 * ε * (1 + η) * a * (K * Real.sqrt K) = (1 + η) * (a * c) := by
        rw [← hc]
        ring
      rw [h1]
      have h2 : η * (a * c) ≤ η' / 2 := by
        rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      nlinarith
    have hev2 := Filter.Tendsto.eventually_lt_const hL hlim
    have hincl : ∀ᶠ n : ℕ in atTop,
        {ω | maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n ≤
          a * Real.sqrt (r n)} ⊆
        {ω | |(((X n ω 0 : ℤ) : ℝ) + ε * ∑ x ∈ departureRange (fun j => X j ω) n,
            (unitDir (toSpace x)) 0) / Real.sqrt n| ≤ a * c + η'} ∪
        {ω | ¬ (|innerRadius (fun j => X j ω) n - r n| ≤ C * Real.sqrt (r n * Real.log n) ∧
            maxRadius (fun j => X j ω) n - r n ≤
              C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2))} := by
      filter_upwards [hev1, hev2, eventually_ge_atTop 1] with n h1 h2 hn1
      intro ω hω
      by_cases hgood : |innerRadius (fun j => X j ω) n - r n| ≤ C * Real.sqrt (r n * Real.log n) ∧
          maxRadius (fun j => X j ω) n - r n ≤ C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
      · left
        have hω' : maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n ≤
            a * Real.sqrt (K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2) := by
          rw [← hr n]
          exact hω
        have hM : maxRadius (fun j => X j ω) n ≤
            (1 + η) * (K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2) := by
          have h3 := hgood.2
          rw [hr n] at h3
          linarith
        have hdev := abs_dev_le_of_width_le (x := fun j => X j ω) (n := n) hε0 hM hω'
        have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
        show |(((X n ω 0 : ℤ) : ℝ) + ε * ∑ x ∈ departureRange (fun j => X j ω) n,
            (unitDir (toSpace x)) 0) / Real.sqrt n| ≤ a * c + η'
        rw [abs_div, abs_of_pos hsqrt]
        have h4 := div_le_div_of_nonneg_right hdev hsqrt.le
        exact (h4.trans h2.le)
      · right
        exact hgood
    exact limsup_measure_le_of_eventually_subset μ hincl (hbadT μ X hX)
      (limsup_measure_abs_le μ hclt _)
  exact ge_of_tendsto' (tendsto_measure_Icc_add_inv (gaussianReal 0 (1 / 2)) (a * c)) hk

/-- **The width is not small.** For `0 < ε < 1/2` and every deterministic sequence `a_n → 0`,
`P(R_out(n) − R_in(n) ≤ a_n √r_n) → 0`. -/
theorem gap_probability_tendsto_zero {ε : ℝ} (hε0 : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X) {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) :
    let r : ℕ → ℝ := fun n =>
      ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal)) ^
        ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
    Tendsto (fun n => μ {ω | maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n ≤
        a n * Real.sqrt (r n)}) atTop (𝓝 0) := by
  intro r
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  set c : ℝ := Real.sqrt (3 * ε / Real.pi) with hcdef
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  obtain ⟨k, hk⟩ := (gaussianReal_Icc_tendsto_zero.eventually (gt_mem_nhds hδ)).exists
  set t : ℝ := 1 / ((k : ℝ) + 1) with ht
  have ht0 : 0 < t := by positivity
  set a' : ℝ := t / (c + 1) with ha'
  have ha'0 : 0 < a' := by positivity
  have hac : a' * c ≤ t := by
    rw [ha', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hlim : limsup (fun n => μ {ω | maxRadius (fun j => X j ω) n -
        innerRadius (fun j => X j ω) n ≤ a' * Real.sqrt (r n)}) atTop ≤
      gaussianReal 0 (1 / 2) (Set.Icc (-(a' * c)) (a' * c)) :=
    gap_limsup_le_gaussian hε0 hεd μ hX ha'0.le
  have hlt : limsup (fun n => μ {ω | maxRadius (fun j => X j ω) n -
        innerRadius (fun j => X j ω) n ≤ a' * Real.sqrt (r n)}) atTop < δ :=
    lt_of_le_of_lt (hlim.trans (measure_mono (Set.Icc_subset_Icc (by linarith) hac))) hk
  filter_upwards [eventually_lt_of_limsup_lt hlt, ha.eventually (ge_mem_nhds ha'0)] with n hn han
  refine le_trans (measure_mono fun ω hω => ?_) hn.le
  exact hω.trans (mul_le_mul_of_nonneg_right han (Real.sqrt_nonneg _))

/-- **The planar width lies in a power window with high probability.** For `0 < ε < 1/2` and
every `η > 0` the events `n^{1/6 − η} ≤ R_out(n) − R_in(n) ≤ n^{1/6 + η}` are measurable and have
probability tending to one. The upper bound is the proved fluctuation rate; the lower bound is
`gap_probability_tendsto_zero` with `a_n = n^{-η} / √K`. -/
theorem gap_in_power_window {ε : ℝ} (hε0 : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X) {η : ℝ} (hη : 0 < η) :
    let E : ℕ → Set Ω := fun n =>
      {ω | (n : ℝ) ^ ((1 : ℝ) / 6 - η) ≤
          maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n ∧
        maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n ≤
          (n : ℝ) ^ ((1 : ℝ) / 6 + η)}
    (∀ n, MeasurableSet (E n)) ∧ Tendsto (fun n => μ (E n)) atTop (𝓝 1) := by
  intro E
  have hG : ∀ n : ℕ, Measurable (fun ω => maxRadius (fun j => X j ω) n -
      innerRadius (fun j => X j ω) n) := fun n => measurable_width hX.measurable n
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    (measurableSet_le measurable_const (hG n)).inter (measurableSet_le (hG n) measurable_const)
  refine ⟨hEm, ?_⟩
  set K : ℝ := (3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) with hKdef
  have hK : 0 < K := by positivity
  set r : ℕ → ℝ := fun n =>
    ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal)) ^
      ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1)) with hrdef
  have hr : ∀ n : ℕ, r n = K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 := fun n => planar_radius_eq hε0 n
  obtain ⟨C, hC, hbadT⟩ := planar_radii_bad_tendsto hε0 hεd
  -- the lower side
  set a : ℕ → ℝ := fun n => (n : ℝ) ^ (-η) / Real.sqrt K with hadef
  have ha : Tendsto a atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_neg_atTop hη).comp tendsto_natCast_atTop_atTop
    simpa using h1.div_const (Real.sqrt K)
  have hlow : Tendsto (fun n => μ {ω | maxRadius (fun j => X j ω) n -
      innerRadius (fun j => X j ω) n ≤ a n * Real.sqrt (r n)}) atTop (𝓝 0) :=
    gap_probability_tendsto_zero hε0 hεd μ hX ha
  have hlow' : Tendsto (fun n : ℕ => μ {ω | maxRadius (fun j => X j ω) n -
      innerRadius (fun j => X j ω) n < (n : ℝ) ^ ((1 : ℝ) / 6 - η)}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlow
      (Eventually.of_forall fun n => bot_le) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine measure_mono fun ω hω => ?_
    have hq0 : 0 < (n : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hval : a n * Real.sqrt (r n) = (n : ℝ) ^ ((1 : ℝ) / 6 - η) := by
      rw [hr n, Real.sqrt_mul hK.le, Real.sqrt_sq hq0.le, hadef, sub_eq_add_neg,
        Real.rpow_add hn0, mul_comm ((n : ℝ) ^ ((1 : ℝ) / 6))]
      have hsK : Real.sqrt K ≠ 0 := (Real.sqrt_pos.mpr hK).ne'
      field_simp
    have hω' : maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n <
        (n : ℝ) ^ ((1 : ℝ) / 6 - η) := hω
    show maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n ≤ a n * Real.sqrt (r n)
    rw [hval]
    exact hω'.le
  -- the upper side
  have hup : Tendsto (fun n : ℕ => μ {ω | (n : ℝ) ^ ((1 : ℝ) / 6 + η) <
      maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n}) atTop (𝓝 0) := by
    have hbadT' : Tendsto (fun n : ℕ => μ {ω | ¬ (|innerRadius (fun j => X j ω) n - r n| ≤
        C * Real.sqrt (r n * Real.log n) ∧ maxRadius (fun j => X j ω) n - r n ≤
          C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2))}) atTop (𝓝 0) := hbadT μ X hX
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbadT'
      (Eventually.of_forall fun n => bot_le) ?_
    filter_upwards [eventually_mul_log_rpow_le (2 * C * Real.sqrt K) ((5 : ℝ) / 2) hη
      one_pos, eventually_ge_atTop 3] with n hn hn3
    refine measure_mono fun ω hω hgood => ?_
    have hq0 : 0 < (n : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos (by positivity) _
    have hn0 : (0 : ℝ) < n := by positivity
    have hlog : 1 ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le hn0]
      have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      have := Real.exp_one_lt_d9
      linarith
    obtain ⟨h1, h2⟩ := hgood
    have hsqrt : Real.sqrt (r n * Real.log n) ≤ Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2) := by
      rw [Real.sqrt_mul (by rw [hr n]; positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
    have hgap : maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n ≤
        2 * C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2) := by
      have h3 := (abs_le.mp h1).1
      have h4 : C * Real.sqrt (r n * Real.log n) ≤
          C * (Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hsqrt hC.le
      nlinarith
    have hval : (n : ℝ) ^ ((1 : ℝ) / 6 + η) = (n : ℝ) ^ ((1 : ℝ) / 6) * (n : ℝ) ^ η :=
      Real.rpow_add hn0 _ _
    have hfin : 2 * C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2) ≤
        (n : ℝ) ^ ((1 : ℝ) / 6 + η) := by
      rw [hval, hr n, Real.sqrt_mul hK.le, Real.sqrt_sq hq0.le]
      have h5 : (2 * C * Real.sqrt K) * Real.log n ^ ((5 : ℝ) / 2) ≤ 1 * (n : ℝ) ^ η := hn
      calc 2 * C * (Real.sqrt K * (n : ℝ) ^ ((1 : ℝ) / 6)) * Real.log n ^ ((5 : ℝ) / 2)
          = ((2 * C * Real.sqrt K) * Real.log n ^ ((5 : ℝ) / 2)) * (n : ℝ) ^ ((1 : ℝ) / 6) := by
            ring
        _ ≤ (1 * (n : ℝ) ^ η) * (n : ℝ) ^ ((1 : ℝ) / 6) :=
            mul_le_mul_of_nonneg_right h5 hq0.le
        _ = (n : ℝ) ^ ((1 : ℝ) / 6) * (n : ℝ) ^ η := by ring
    exact absurd (lt_of_lt_of_le hω (hgap.trans hfin)) (lt_irrefl _)
  -- the complement of `E n`
  have hcompl : Tendsto (fun n => μ (E n)ᶜ) atTop (𝓝 0) := by
    have hsum := hlow'.add hup
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun n => bot_le) ?_
    refine Eventually.of_forall fun n => ?_
    refine le_trans (measure_mono fun ω hω => ?_) (measure_union_le _ _)
    simp only [E, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_le] at hω
    rcases hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hE : ∀ n, μ (E n) = 1 - μ (E n)ᶜ := fun n => by
    have h := prob_compl_eq_one_sub (μ := μ) (hEm n).compl
    rw [compl_compl] at h
    exact h
  have h1 : Tendsto (fun n => 1 - μ (E n)ᶜ) atTop (𝓝 (1 - 0)) :=
    ENNReal.Tendsto.sub tendsto_const_nhds hcompl (Or.inl ENNReal.one_ne_top)
  rw [tsub_zero] at h1
  exact h1.congr fun n => (hE n).symm

end CERW.Support.Lower.PlanarGap
