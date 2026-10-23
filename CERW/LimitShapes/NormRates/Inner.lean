import CERW.LimitShapes.Frozen.NormBallPotential
import CERW.LimitShapes.NormRates.Arithmetic

/-!
# Inner radius and cone profile from the quadratic event

The excess and layer geometry of Proposition `prop:norm-shape` controls the volume
outside the inner ball. The stopped quadratic radius-volume estimate determines
the radius used to shift the cone profile.
-/

open MeasureTheory Topology
open LatticeProb (Site)
open CERW CERW.Support.Norm
open CERW.Support.Norm.ContactEvent (scale PathTyping)
open private rateQ rateQ_nonneg approx_error_le profile_arith
  RateInequalities.mass_bound RateInequalities.ev_bound
  RateInequalities.rateQ_pos RateInequalities.rateQ_le_one RateInequalities.rpow_half_sq
  from CERW.Support.Norm.ShapeRates

namespace CERW.LimitShapes.NormRates

/-- The inner radius and cone profile of Proposition `prop:norm-shape` from the quadratic event. -/
theorem inner_rates_of_quadratic_event {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (K : EventConstants) (hCo : 0 < K.CCo) (hLoc : 0 < K.CLoc)
    (hQuad : 0 < K.CQuad) {C_c : ℝ} (hC_c : 0 < C_c) :
    ∃ C_in C_lt r₀ M : ℝ, ∃ n₀ : ℕ,
      0 < C_in ∧ 0 < C_lt ∧ 0 < M ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) →
        ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n → PathTyping d X →
          r₀ ≤ scale d Ψ ε n → 1 ≤ Real.log n →
          M * Real.log n ^ (d + 5) ≤ scale d Ψ ε n →
          (K.CCo + 1) * scale d Ψ ε n ≤ 2 * n →
          EventEstimates Ψ ε ξ K X n →
          (∀ y₀ : EuclideanSpace ℝ (Fin d), Ψ y₀ = normInnerRadius Ψ X n →
            y₀ ∈ closure (cellSet X n)ᶜ → normPotential d ε Ψ (cellSet X n) y₀ ≤
              C_c * scale d Ψ ε n * rateQ d (scale d Ψ ε n) (Real.log n)) →
          |normInnerRadius Ψ X n - scale d Ψ ε n| ≤
            C_in * (scale d Ψ ε n * rateQ d (scale d Ψ ε n) (Real.log n) ^ ((1 : ℝ) / 2)) ∧
          ∀ y : EuclideanSpace ℝ (Fin d),
            |cellLocalTime X n y - 2 * d * ε * max (scale d Ψ ε n - Ψ y) 0| ≤
              C_lt * (scale d Ψ ε n *
                rateQ d (scale d Ψ ε n) (Real.log n) ^ ((1 : ℝ) / (d + 1))) := by
  have hd1 : 1 ≤ d := by omega
  have hV : 0 < normBallVolume Ψ := ContactAssembly.normBallVolume_pos' hd1 hΨ
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  obtain ⟨hc0, _⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hΛ : 0 < normMax Ψ :=
    lt_of_lt_of_le hc0 (ContactAssembly.normMin_le_normMax hd1 hΨ)
  obtain ⟨C_L, hCL, hgeoC⟩ := inner_geometry hd hΨ hε
    CERW.LimitShapes.norm_ball_potential CERW.Support.Norm.layer_potential
    CERW.Support.Norm.norm_potential_geometry
  obtain ⟨C_RV, hCRV, n_RV, _, hRV⟩ := radius_volume_of_event hd hΨ hε K hCo hQuad
  let κ : ℝ := K.CCo + 1
  have hκ0 : 0 < κ := by dsimp [κ]; linarith
  let C_δ := K.CLoc * (1 + Real.sqrt K.CCo)
  have hCδ0 : 0 < C_δ := by dsimp [C_δ]; positivity
  let C_I := unitBallVolume d / (2 * ε) * ((1 + normMax Ψ / normMin Ψ) * κ) ^ d
  have hCI0 : 0 < C_I := by dsimp [C_I]; positivity
  let C_Ev := normBallVolume Ψ * d * (normMax Ψ * κ + 1) ^ (d - 1) + C_I * C_c
  have hCEv : 0 < C_Ev := by dsimp [C_Ev]; positivity
  let C₁ := C_RV * (2 + C_Ev)
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  obtain ⟨C₂, r₂, M₂, hC₂, _, hprof⟩ :=
    profile_arith hd hε hCL (mul_pos hCI0 hC_c) hC₁ hCδ0
  refine ⟨C₁, C₂, max r₂ (max 1 (Real.sqrt d)), max M₂ 1, max n_RV 2,
    hC₁, hC₂, lt_max_of_lt_right one_pos, ?_⟩
  intro ξ hξ X n hn hpath hr hℓ hMℓ hK2n hE hcon
  let r := scale d Ψ ε n
  have hX0 := hpath.1
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hH := hE.1.2.2.2.2.2
  have hMloc := hE.1.2.2.2.1
  have happrox := hE.2.1
  set ℓ : ℝ := Real.log n with hℓdef
  have hr1 : 1 ≤ r :=
    le_trans (le_trans (le_max_left 1 _) (le_max_right _ _)) hr
  have hrd : Real.sqrt d ≤ r :=
    le_trans (le_trans (le_max_right 1 _) (le_max_right _ _)) hr
  have hr₂ : r₂ ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 < r := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hpowℓ : 0 ≤ ℓ ^ (d + 5) := pow_nonneg hℓ0 _
  have hℓpow : ℓ ^ (d + 5) ≤ r :=
    calc ℓ ^ (d + 5) = 1 * ℓ ^ (d + 5) := (one_mul _).symm
      _ ≤ max M₂ 1 * ℓ ^ (d + 5) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpowℓ
      _ ≤ r := hMℓ
  have hℓr : ℓ ≤ r := (le_self_pow₀ hℓ (by omega)).trans hℓpow
  have hM₂ℓ : M₂ * ℓ ^ (d + 5) ≤ r :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpowℓ) hMℓ
  have hDR : cellSet X n ⊆ Metric.ball 0 (κ * r) :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 X n).trans
      (Metric.ball_subset_ball (by
        have : κ * r = K.CCo * r + 1 * r := by dsimp [κ]; ring
        linarith))
  set δ : ℝ := K.CLoc * ℓ + K.CLoc * (if d = 2
      then Real.sqrt (maxLocalTime X n) * ℓ else Real.sqrt (maxLocalTime X n * ℓ)) with hδdef
  have hδapp : ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (κ * r),
      |cellLocalTime X n y - normPotential d ε Ψ (cellSet X n) y| ≤ δ := by
    intro y hy
    rw [mem_ball_zero_iff] at hy
    exact happrox y (by linarith)
  have hδ0 : 0 ≤ δ := by
    refine add_nonneg (mul_nonneg hLoc.le hℓ0) (mul_nonneg hLoc.le ?_)
    split_ifs
    · exact mul_nonneg (Real.sqrt_nonneg _) hℓ0
    · exact Real.sqrt_nonneg _
  have hδle : δ ≤ C_δ * (if d = 2 then Real.sqrt r * ℓ else Real.sqrt (r * ℓ)) :=
    approx_error_le d hLoc.le hCo.le hMloc hr1 hℓ hℓr
  have hqnn : 0 ≤ rateQ d r ℓ := rateQ_nonneg d hr0 hℓ0
  obtain ⟨hb0, hbR, hI0, hexc, hshell, _, hprof'⟩ :=
    hgeoC X n hX0 (by omega) (R := κ * r) (δ := δ) (H := C_c * r * rateQ d r ℓ) hDR hδapp hcon
  set b : ℝ := normInnerRadius Ψ X n with hb
  set E : Set (EuclideanSpace ℝ (Fin d)) := cellSet X n \ {v | Ψ v < b} with hEdef
  set I : ℝ := ∫ v in E, (Ψ v - b) with hI
  set Ev : ℝ := (volume E).toReal with hEv
  have hbR' : b ≤ normMax Ψ * κ * r := by
    calc b ≤ normMax Ψ * (κ * r) := hbR
      _ = normMax Ψ * κ * r := by ring
  have hexc' : I ≤ unitBallVolume d / (2 * ε) * ((1 + normMax Ψ / normMin Ψ) * κ) ^ d * r ^ d *
      (C_c * r * rateQ d r ℓ) := by
    calc I ≤ unitBallVolume d / (2 * ε) * ((1 + normMax Ψ / normMin Ψ) * (κ * r)) ^ d *
          (C_c * r * rateQ d r ℓ) := hexc
      _ = unitBallVolume d / (2 * ε) * ((1 + normMax Ψ / normMin Ψ) * κ) ^ d * r ^ d *
          (C_c * r * rateQ d r ℓ) := by
          rw [show (1 + normMax Ψ / normMin Ψ) * (κ * r) =
            ((1 + normMax Ψ / normMin Ψ) * κ) * r by ring, mul_pow]
          ring
  have hIrate : I ≤ C_I * C_c * (r ^ (d + 1) * rateQ d r ℓ) :=
    RateInequalities.mass_bound hCI0 hr0 hexc' le_rfl
  have hqpos := RateInequalities.rateQ_pos d hr0 (by linarith : 0 < ℓ)
  have hp0 : 0 < rateQ d r ℓ ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hqpos _
  have hp1 : rateQ d r ℓ ^ ((1 : ℝ) / 2) ≤ 1 := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_one.mpr (RateInequalities.rateQ_le_one d hr0 hℓr)
  have hIsq : I ≤ C_I * C_c * (r ^ (d + 1) *
      (rateQ d r ℓ ^ ((1 : ℝ) / 2)) ^ 2) := by
    rw [RateInequalities.rpow_half_sq d hr0 (by linarith : 0 < ℓ)]
    exact hIrate
  have hEvb : Ev ≤ C_Ev * (r ^ d * rateQ d r ℓ ^ ((1 : ℝ) / 2)) :=
    RateInequalities.ev_bound hd1 hV hr0 hp0 hp1 hb0 hbR' hIsq
      (hshell (r * rateQ d r ℓ ^ ((1 : ℝ) / 2)) (mul_pos hr0 hp0))
  have hrv := hRV ξ hξ X n ((le_max_left _ _).trans hn) hpath hE
  have hbrate : |b - r| ≤ C₁ * (r * rateQ d r ℓ ^ ((1 : ℝ) / 2)) :=
    inner_radius_rate_of_radius_volume hd hr1 hb0.le hℓ hℓr hCRV.le hEvb hrv
  have hprofC := hprof r ℓ b I δ hr₂ hℓ hM₂ℓ hI0 hIrate hbrate hδ0 hδle
  refine ⟨hbrate, fun y => ?_⟩
  have h1 := hprof' y
  have hmx : |max (b - Ψ y) 0 - max (r - Ψ y) 0| ≤ |b - r| := by
    have := abs_max_sub_max_le_abs (b - Ψ y) (r - Ψ y) 0
    rwa [show (b - Ψ y) - (r - Ψ y) = b - r by ring] at this
  have hcoef : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  have hsplit : cellLocalTime X n y - 2 * d * ε * max (r - Ψ y) 0 =
      (cellLocalTime X n y - 2 * d * ε * max (b - Ψ y) 0) +
        2 * d * ε * (max (b - Ψ y) 0 - max (r - Ψ y) 0) := by ring
  rw [hsplit]
  calc |(cellLocalTime X n y - 2 * d * ε * max (b - Ψ y) 0) +
        2 * d * ε * (max (b - Ψ y) 0 - max (r - Ψ y) 0)|
      ≤ |cellLocalTime X n y - 2 * d * ε * max (b - Ψ y) 0| +
        |2 * d * ε * (max (b - Ψ y) 0 - max (r - Ψ y) 0)| := abs_add_le _ _
    _ ≤ (δ + C_L * I ^ ((1 : ℝ) / (d + 1))) + 2 * d * ε * |b - r| := by
        refine add_le_add h1 ?_
        rw [abs_mul, abs_of_nonneg hcoef]
        exact mul_le_mul_of_nonneg_left hmx hcoef
    _ ≤ C₂ * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) := by linarith


end CERW.LimitShapes.NormRates
