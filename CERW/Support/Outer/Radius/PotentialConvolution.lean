module

public import CERW.Support.Outer.Radius.OccupationKernel

@[expose] public section

/-!
# Potential Convolution

The potential splits into the contribution of the inner ball and the exterior set. Radial
convolution and cell comparison bound the weighted sum of these potentials.
The retained labels `eq:potential-convolution`
refer to the earlier source `paper/limit-shapes.tex`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- The potential of a measurable set of finite volume is continuous. -/
lemma ev_continuous_potential (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) :
    Continuous (potential d ε E) := by
  obtain ⟨C, hC0, hC⟩ := CERW.Support.Geometry.exists_potential_holder hd
  exact CERW.Support.Geometry.continuous_of_holder_half (by positivity)
    fun y z => hC ε hε E hE hEfin y z

/-- For `d ≥ 3` and a measurable set `E` of finite volume, `ζ ↦ χ(|ζ|) U_E(y - ζ)` is
integrable. -/
lemma ev_integrable_chi_mul_potential (hd : 3 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => ev_chi d ‖ζ‖ * potential d ε E (y - ζ)) := by
  have hcont := ev_continuous_potential (by omega) hε hE hEfin
  have hbd := fun ζ : EuclideanSpace ℝ (Fin d) =>
    CERW.Support.Geometry.abs_potential_le (by omega) hε hE hEfin (y - ζ)
  exact (ev_integrable_chi_norm hd).mul_bdd
    (hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ζ => (Real.norm_eq_abs _).trans_le (hbd ζ))

/-- The potential is at most its positive part `U_E^+`. -/
lemma ev_potential_le_positivePotential (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) : potential d ε E y ≤ positivePotential d ε E y := by
  have hint := CERW.Support.Geometry.integrableOn_potentialIntegrand hd hE hEfin y
  have hω := unitBallVolume_pos d
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  unfold potential positivePotential
  exact mul_le_mul_of_nonneg_left
    (integral_mono hint hint.pos_part fun v => le_max_left _ _) hc

/-- The positive part `U_E^+` of the potential is nonnegative. -/
lemma ev_positivePotential_nonneg {ε : ℝ} (hε : 0 ≤ ε)
    (E : Set (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d)) :
    0 ≤ positivePotential d ε E y := by
  have hω := unitBallVolume_pos d
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  exact mul_nonneg hc (integral_nonneg fun v => le_max_right _ _)

/-- The decomposition `U_D = 2dε (b - |·|)_+ + U_{D ∖ B(0,b)}`, including the degenerate radius
`b = 0`. -/
lemma ev_potential_split (hd : 2 ≤ d) (ε : ℝ) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDb : Bornology.IsBounded D) {b : ℝ} (hb : 0 ≤ b)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ D) (y : EuclideanSpace ℝ (Fin d)) :
    potential d ε D y =
      2 * d * ε * max (b - ‖y‖) 0 + potential d ε (D \ Metric.ball 0 b) y := by
  rcases hb.lt_or_eq with hb | hb
  · exact potential_split hd ε hD hDb hb hball y
  · subst hb
    rw [Metric.ball_zero, Set.sdiff_empty,
      max_eq_right (by linarith [norm_nonneg y] : (0 : ℝ) - ‖y‖ ≤ 0), mul_zero, zero_add]

/-- `eq:potential-convolution` beyond the inner ball: for `|y| ≥ b` and `B(0,b) ⊆ D`,
`∫ χ(|ζ|) U_D(y - ζ) dζ ≤ 2dε ∫ χ(|ζ|) min(b, |ζ|) dζ + ‖χ‖₁ U_E^+(y)` with `E = D ∖ B(0,b)`. -/
lemma ev_integral_chi_mul_potential_le (hd : 3 ≤ d) (hN : NewtonConv d) {ε : ℝ}
    (hε : 0 < ε) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) {b : ℝ} (hb : 0 ≤ b)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ D) {y : EuclideanSpace ℝ (Fin d)}
    (hy : b ≤ ‖y‖) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * potential d ε D (y - ζ) ≤
      2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖) +
        (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖) *
          positivePotential d ε (D \ Metric.ball 0 b) y := by
  have hE : MeasurableSet (D \ Metric.ball 0 b) := hD.diff measurableSet_ball
  have hEb : Bornology.IsBounded (D \ Metric.ball 0 b) := hDb.subset Set.sdiff_subset
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hEfin : volume (D \ Metric.ball 0 b) ≠ ⊤ := hEb.measure_lt_top.ne
  have hχ := ev_integrable_chi_norm hd
  have hint0 := ev_integrable_chi_mul_potential hd hε.le hD hDfin y
  have hint2 := ev_integrable_chi_mul_potential hd hε.le hE hEfin y
  have hint1 : Integrable
      (fun ζ : EuclideanSpace ℝ (Fin d) => ev_chi d ‖ζ‖ * min b ‖ζ‖) := by
    refine hχ.mul_bdd (c := b) (continuous_const.min continuous_norm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hb (norm_nonneg ζ))]
    exact min_le_left _ _
  have hP : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  have hpt : ∀ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * potential d ε D (y - ζ) ≤
      2 * d * ε * (ev_chi d ‖ζ‖ * min b ‖ζ‖) +
        ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ) := by
    intro ζ
    have hcone : max (b - ‖y - ζ‖) 0 ≤ min b ‖ζ‖ := by
      refine max_le (le_min (by linarith [norm_nonneg (y - ζ)]) ?_) (le_min hb (norm_nonneg ζ))
      have h1 : ‖y‖ ≤ ‖y - ζ‖ + ‖ζ‖ := by
        calc ‖y‖ = ‖(y - ζ) + ζ‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - ζ‖ + ‖ζ‖ := norm_add_le _ _
      linarith
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcone hP)
      (ev_chi_nonneg (d := d) ‖ζ‖)
    rw [ev_potential_split (by omega) ε hD hDb hb hball (y - ζ)]
    calc ev_chi d ‖ζ‖ * (2 * d * ε * max (b - ‖y - ζ‖) 0 +
          potential d ε (D \ Metric.ball 0 b) (y - ζ))
        = ev_chi d ‖ζ‖ * (2 * d * ε * max (b - ‖y - ζ‖) 0) +
            ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ) := by ring
      _ ≤ ev_chi d ‖ζ‖ * (2 * d * ε * min b ‖ζ‖) +
            ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ) := by linarith
      _ = 2 * d * ε * (ev_chi d ‖ζ‖ * min b ‖ζ‖) +
            ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ) := by ring
  have hNE := hN hε.le hE hEb y
  simp only [← ev_chi_norm] at hNE
  calc ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * potential d ε D (y - ζ)
      ≤ ∫ ζ : EuclideanSpace ℝ (Fin d), (2 * d * ε * (ev_chi d ‖ζ‖ * min b ‖ζ‖) +
          ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ)) :=
        integral_mono hint0 ((hint1.const_mul _).add hint2) hpt
    _ = 2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖) +
          ∫ ζ : EuclideanSpace ℝ (Fin d),
            ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ) := by
        rw [integral_add (hint1.const_mul _) hint2, integral_const_mul]
    _ ≤ 2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖) +
          (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖) *
            positivePotential d ε (D \ Metric.ball 0 b) y := by linarith

/-- The potential step: the `a`-weighted sum of the potential over the lattice ball of radius
`2n` is at most `β L + m U_E^+(y₀)`, where `m = ∫ χ(|ζ|) dζ`, `E = D_n ∖ B(0,b)`, `|y₀| ≥ b`,
and `β` depends only on `d, ε, C₃`. -/
lemma ev_sum_cellWeight_mul_potential_le (hd : 3 ≤ d) (hN : NewtonConv d) {ε : ℝ}
    (hε : 0 < ε) {C₃ : ℝ} (hC₃ : 0 ≤ C₃) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ (X : ℕ → Site d) (n : ℕ), 2 ≤ n → 4 * Real.sqrt d ≤ n →
      (∀ j, euclidNorm (X j) ≤ j) →
      (∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * ((n : ℝ) + Real.sqrt d) →
        ‖y - z‖ ≤ Real.sqrt d →
        |potential d ε (cellSet X n) y - potential d ε (cellSet X n) z| ≤
          C₃ * Real.log ((n : ℝ) + 2)) →
      ∀ (b : ℝ) (y₀ : EuclideanSpace ℝ (Fin d)), 0 ≤ b →
        Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ cellSet X n →
        b ≤ ‖y₀‖ → ‖y₀‖ ≤ 2 * n →
        ∑ y ∈ LatticeProb.ballFinset d (2 * n),
            ev_cellWeight d y₀ y * potential d ε (cellSet X n) (toSpace y) ≤
          β * Real.log ((n : ℝ) + 2) +
            (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖) *
              positivePotential d ε (cellSet X n \ Metric.ball 0 b) y₀ := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hω := unitBallVolume_pos d
  set m : ℝ := ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun ζ => ev_chi_nonneg _
  set Cf : ℝ := 2 * ε / unitBallVolume d * 2 with hCf
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  set CT : ℝ := 1 + Real.log (1 + max 1 (2 * 1)) with hCT
  have hCT0 : 0 ≤ CT := by
    rw [hCT]
    have : 0 ≤ Real.log (1 + max 1 (2 * 1 : ℝ)) :=
      Real.log_nonneg (by linarith [le_max_left (1 : ℝ) (2 * 1)])
    linarith
  refine ⟨2 * d * ε * (d * unitBallVolume d * (CT + 1)) + (C₃ + Cf) * m, by positivity, ?_⟩
  intro X n hn hn4 hXn hmod b y₀ hb hball hby hyn
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hL1 : 1 ≤ L := CERW.Support.Law.one_le_log_add_two hn
  have hsd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hDmeas : MeasurableSet (cellSet X n) := CERW.Support.Occupation.measurableSet_cellSet X n
  have hDbdd : Bornology.IsBounded (cellSet X n) :=
    (Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin d)))
      (r := maxRadius X n + Real.sqrt d)).subset
      (CERW.Support.Occupation.cellSet_subset_ball hd1 X n)
  have hDfin : volume (cellSet X n) ≠ ⊤ := hDbdd.measure_lt_top.ne
  set G : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => ev_chi d ‖y₀ - ζ‖ with hG
  set Uf : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => potential d ε (cellSet X n) ζ with hUf
  have hG0 : ∀ ζ, 0 ≤ G ζ := fun ζ => ev_chi_nonneg _
  have hGint : Integrable G := (ev_integrable_chi_norm hd).comp_sub_left y₀
  have hGU : Integrable (fun ζ => G ζ * Uf ζ) := by
    have := (ev_integrable_chi_mul_potential hd hε.le hDmeas hDfin y₀).comp_sub_left y₀
    simpa only [sub_sub_cancel] using this
  have hGUint : ∫ ζ, G ζ * Uf ζ =
      ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * potential d ε (cellSet X n) (y₀ - ζ) := by
    have := integral_sub_left_eq_self
      (fun ζ : EuclideanSpace ℝ (Fin d) =>
        ev_chi d ‖ζ‖ * potential d ε (cellSet X n) (y₀ - ζ)) volume y₀
    simpa only [sub_sub_cancel] using this
  have hGm : ∫ ζ, G ζ = m :=
    integral_sub_left_eq_self (fun ζ : EuclideanSpace ℝ (Fin d) => ev_chi d ‖ζ‖) volume y₀
  have hmod' : ∀ y ∈ LatticeProb.ballFinset d (2 * n), ∀ ζ ∈ cell y,
      Uf (toSpace y) ≤ Uf ζ + C₃ * L := by
    intro y hy ζ hζ
    rw [LatticeProb.mem_ballFinset_iff] at hy
    have h1 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hζ
    have h2 := hmod (toSpace y) ζ (by rw [norm_toSpace]; linarith) (by
      rw [norm_sub_rev]; linarith)
    have := (abs_le.mp h2).2
    simp only [hUf]
    linarith
  have hfar : ∀ ζ ∉ ⋃ y ∈ LatticeProb.ballFinset d (2 * n), cell y, -Cf ≤ Uf ζ := fun ζ hζ =>
    ev_neg_le_potential_of_not_mem hd2 hε.le hn hn4 hXn hζ
  have hsum := ev_sum_setIntegral_mul_le (S := LatticeProb.ballFinset d (2 * n)) (M := C₃ * L)
    (Cf := Cf) hG0 hGint hGU (mul_nonneg hC₃ (by linarith)) hCf0 hmod' hfar
  have hb2 : b ≤ 1 * (2 * n) := by linarith
  have hlog := ev_log_one_add_max_le hn hb2
  have hIB := ev_integral_chi_mul_min_le hd hb
  have hIB' : ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖ ≤
      d * unitBallVolume d * ((CT + 1) * L) := by
    refine hIB.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    linarith
  have hconv := ev_integral_chi_mul_potential_le hd hN hε hDmeas hDbdd hb hball hby
  have hP : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  have hstep : 2 * (d : ℝ) * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖) ≤
      2 * d * ε * (d * unitBallVolume d * (CT + 1)) * L := by
    calc 2 * (d : ℝ) * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖)
        ≤ 2 * d * ε * (d * unitBallVolume d * ((CT + 1) * L)) :=
          mul_le_mul_of_nonneg_left hIB' hP
      _ = 2 * d * ε * (d * unitBallVolume d * (CT + 1)) * L := by ring
  have hCfm : Cf * m ≤ Cf * m * L := by
    have := mul_nonneg (mul_nonneg hCf0 hm0) (sub_nonneg.mpr hL1)
    linarith
  calc ∑ y ∈ LatticeProb.ballFinset d (2 * n),
          ev_cellWeight d y₀ y * potential d ε (cellSet X n) (toSpace y)
      ≤ (∫ ζ, G ζ * Uf ζ) + (C₃ * L + Cf) * ∫ ζ, G ζ := hsum
    _ ≤ (2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖) +
          m * positivePotential d ε (cellSet X n \ Metric.ball 0 b) y₀) +
          (C₃ * L + Cf) * m := by
        rw [hGm, hGUint]
        linarith
    _ ≤ (2 * d * ε * (d * unitBallVolume d * (CT + 1)) + (C₃ + Cf) * m) * L +
          m * positivePotential d ε (cellSet X n \ Metric.ball 0 b) y₀ := by linarith

end CERW.Support.Outer.Radius
