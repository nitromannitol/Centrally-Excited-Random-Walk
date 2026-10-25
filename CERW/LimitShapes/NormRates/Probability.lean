module

public import CERW.LimitShapes.NormRates.Outer
public import CERW.LimitShapes.NormRates.Inner
public import CERW.LimitShapes.CommonEvent
public import CERW.LimitShapes.Energy.Contact

@[expose] public section

/-!
# Norm limit-shape rates on the common event

Proposition `prop:norm-shape` follows from the excess and cone estimates of
`inner_geometry`, the stopped quadratic radius-volume comparison, and distance
crossing at the predicted radius. The probability bound uses the literal event
of `sec:norm-event`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open LatticeProb (Site)
open CERW CERW.Support.Norm
open CERW.Support.Norm.ContactEvent (scale contactRate PathTyping)
open private rateQ rateQ_nonneg rate_inner_eq rate_local_eq rate_outer_eq
  tendsto_scale tendsto_log_rpow_div_scale tendsto_scale_div_self
  from CERW.Support.Norm.ShapeRates

namespace CERW.LimitShapes

/-- Proposition `prop:norm-shape`, with all estimates taken on the literal common event. -/
theorem norm_shape_rates_from_common_event :
    CERW.Support.Statements.norm_shape_rates.{u} := by
  intro d hd Ψ hΨ ε hε hell r p hp
  have hd1 : 1 ≤ d := by omega
  have hV : 0 < normBallVolume Ψ := ContactAssembly.normBallVolume_pos' hd1 hΨ
  obtain ⟨hc0, hcle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hΛ : 0 < normMax Ψ :=
    lt_of_lt_of_le hc0 (ContactAssembly.normMin_le_normMax hd1 hΨ)
  obtain ⟨K, hc, hCo, hLoc, hQuad, hSquare, hMart, hCross,
    C_prob, hCprob0, n_prob, hnprob, hprob⟩ :=
    CommonEvent.exists_common_event.{u} hd hΨ hε hell p hp
  obtain ⟨C_c, hC_c, n_c, hn_c, hcon⟩ :=
    Energy.contact_potential_from_energy hd Ψ hΨ ε hε hell K hCo.le hLoc.le hMart.le
  let C_co := K.CCo
  have hC_co : 0 < C_co := hCo
  obtain ⟨C_in, C_lt, r_in, M_in, n_in, hC_in, hC_lt, hM_in, hin⟩ :=
    NormRates.inner_rates_of_quadratic_event hd hΨ hε K hCo hLoc hQuad hC_c
  let C_ob := normMax Ψ * K.CCross * (1 + C_lt)
  have hC_ob : 0 < C_ob := by dsimp [C_ob]; positivity
  set X₀ : ℝ := 2 * d * ε * normBallVolume Ψ with hX₀
  have hX₀pos : 0 < X₀ := by positivity
  set M₀ : ℝ := max M_in 1 with hM₀
  have hM₀pos : 0 < M₀ := lt_max_of_lt_left hM_in
  have hreg : ∀ᶠ n : ℕ in atTop, max (max (max n_c n_in) n_prob) 3 ≤ n ∧ max r_in 1 ≤ r n ∧
      M₀ * Real.log n ^ (d + 5) ≤ r n ∧ (C_co + 1) * r n ≤ 2 * n := by
    have h1 : ∀ᶠ n : ℕ in atTop, max (max (max n_c n_in) n_prob) 3 ≤ n := eventually_ge_atTop _
    have hrt := tendsto_scale d hX₀pos
    have h2 : ∀ᶠ n : ℕ in atTop, max r_in 1 ≤ r n := hrt.eventually_ge_atTop _
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < r n := hrt.eventually_gt_atTop 0
    have h3 : ∀ᶠ n : ℕ in atTop, M₀ * Real.log n ^ (d + 5) ≤ r n := by
      have ht := tendsto_log_rpow_div_scale d hX₀pos ((d + 5 : ℕ) : ℝ)
      have ht' := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / M₀ by positivity))
      filter_upwards [ht', hpos] with n hn hrn
      have hn' : Real.log n ^ ((d + 5 : ℕ) : ℝ) / r n < 1 / M₀ := hn
      rw [Real.rpow_natCast, div_lt_iff₀ hrn] at hn'
      calc M₀ * Real.log n ^ (d + 5) ≤ M₀ * (1 / M₀ * r n) :=
            mul_le_mul_of_nonneg_left hn'.le hM₀pos.le
        _ = r n := by field_simp
    have h4 : ∀ᶠ n : ℕ in atTop, (C_co + 1) * r n ≤ 2 * n := by
      have ht := tendsto_scale_div_self d hd1 hX₀pos
      have hK : 0 < C_co + 1 := by linarith
      have ht' := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 2 / (C_co + 1) by positivity))
      filter_upwards [ht', eventually_ge_atTop 1] with n hn hn1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hn' : r n / n < 2 / (C_co + 1) := hn
      rw [div_lt_div_iff₀ hn0 hK] at hn'
      linarith
    filter_upwards [h1, h2, h3, h4] with n a b c' d'
    exact ⟨a, b, c', d'⟩
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hreg
  set C₀ : ℝ := max (max (max C_in C_lt) C_ob) C_prob with hC₀
  refine ⟨max C₀ ((N₁ : ℝ) ^ p), lt_max_of_lt_left (lt_max_of_lt_right hCprob0), ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg hnpos.le _
  by_cases hnN : N₁ ≤ n
  · obtain ⟨hnmax, hrr, hMlog, hK2n⟩ := hN₁ n hnN
    have hncontact : n_c ≤ n :=
      (le_max_left n_c n_in).trans
        (((le_max_left _ _).trans (le_max_left _ _)).trans hnmax)
    have hninner : n_in ≤ n :=
      (le_max_right n_c n_in).trans
        (((le_max_left _ _).trans (le_max_left _ _)).trans hnmax)
    have hnprob' : n_prob ≤ n := ((le_max_right _ _).trans (le_max_left _ _)).trans hnmax
    have hn3 : 3 ≤ n := (le_max_right _ _).trans hnmax
    have hℓ1 : (1 : ℝ) ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le hnpos]
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      linarith [Real.exp_one_lt_three]
    have hℓ0 : 0 < Real.log n := by linarith
    have hr_in : r_in ≤ r n := (le_max_left _ _).trans hrr
    have hr1 : 1 ≤ r n := (le_max_right _ _).trans hrr
    have hrpos : 0 < r n := by linarith
    have hpowℓ : 0 ≤ Real.log n ^ (d + 5) := pow_nonneg hℓ0.le _
    have hM_in' : M_in * Real.log n ^ (d + 5) ≤ r n :=
      le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpowℓ) hMlog
    have hℓr : Real.log n ≤ r n := by
      calc Real.log n ≤ Real.log n ^ (d + 5) := le_self_pow₀ hℓ1 (by omega)
        _ ≤ M₀ * Real.log n ^ (d + 5) :=
          le_mul_of_one_le_left hpowℓ (le_max_right _ _)
        _ ≤ r n := hMlog
    have hξ' := ContactAssembly.drift_coord_le hΨ hε hell hξ hξ0
    have hpath : ∀ᵐ ω ∂μ, PathTyping d (X · ω) := by
      have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
        rw [ae_iff]
        exact hX.start
      filter_upwards [h0, ae_all_iff.mpr
        (CERW.Support.Drift.ae_sub_mem_unitSteps_drift hd1 hε.le hξ' hX)] with ω h0 hs
      exact ⟨h0, hs⟩
    apply le_trans (measure_mono_ae ?_) ((hprob ξ hξ hξ0 μ X hX n hnprob').trans ?_)
    · filter_upwards [hpath] with ω hpathω
      intro hbad
      show ω ∈ (section5Event Ψ ε ξ K X n)ᶜ
      intro hE
      have hconω := hcon ξ hξ hξ0 (X · ω) n hncontact hpathω hE
      have hcontact : ∀ y₀ : EuclideanSpace ℝ (Fin d),
          Ψ y₀ = normInnerRadius Ψ (X · ω) n →
          y₀ ∈ closure (cellSet (X · ω) n)ᶜ →
          normPotential d ε Ψ (cellSet (X · ω) n) y₀ ≤
            C_c * r n * rateQ d (r n) (Real.log n) := by
        simpa only [contactRate, scale, rateQ] using hconω
      obtain ⟨hinner, hprofile⟩ := hin ξ hξ (X · ω) n hninner hpathω hr_in hℓ1 hM_in'
        hK2n hE hcontact
      have hfin := norm_outer_rate_of_distance_crossing hΨ hr1 hCross.le hC_lt.le
        hℓ1 hℓr hE.2.2.2.2.2 hprofile
      have hCin : C_in ≤ max C₀ ((N₁ : ℝ) ^ p) :=
        ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans
          (le_max_left _ _)
      have hClt : C_lt ≤ max C₀ ((N₁ : ℝ) ^ p) :=
        ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans
          (le_max_left _ _)
      have hCob : C_ob ≤ max C₀ ((N₁ : ℝ) ^ p) :=
        ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
      have hq := rateQ_nonneg d hrpos hℓ0.le
      apply hbad
      refine ⟨?_, ?_, ?_⟩
      · calc |normInnerRadius Ψ (X · ω) n - r n|
            ≤ C_in * (r n * rateQ d (r n) (Real.log n) ^ ((1 : ℝ) / 2)) := hinner
          _ ≤ max C₀ ((N₁ : ℝ) ^ p) *
              (r n * rateQ d (r n) (Real.log n) ^ ((1 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_right hCin
              (mul_nonneg hrpos.le (Real.rpow_nonneg hq _))
          _ = _ := by rw [rate_inner_eq hrpos hℓ0]
      · calc normMaxRadius Ψ (X · ω) n - r n
            ≤ C_ob *
              (r n * rateQ d (r n) (Real.log n) ^ ((1 : ℝ) / (d + 1)) * Real.log n) := hfin
          _ ≤ max C₀ ((N₁ : ℝ) ^ p) *
              (r n * rateQ d (r n) (Real.log n) ^ ((1 : ℝ) / (d + 1)) * Real.log n) :=
            mul_le_mul_of_nonneg_right hCob
              (mul_nonneg (mul_nonneg hrpos.le (Real.rpow_nonneg hq _)) hℓ0.le)
          _ = _ := by rw [rate_outer_eq hrpos hℓ0]
      · intro x
        have h := hprofile (toSpace x)
        rw [cellLocalTime_of_mem_cell _ _ (toSpace_mem_cell x)] at h
        calc |(localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - Ψ (toSpace x)) 0|
            ≤ C_lt * (r n * rateQ d (r n) (Real.log n) ^ ((1 : ℝ) / (d + 1))) := h
          _ ≤ max C₀ ((N₁ : ℝ) ^ p) *
              (r n * rateQ d (r n) (Real.log n) ^ ((1 : ℝ) / (d + 1))) :=
            mul_le_mul_of_nonneg_right hClt
              (mul_nonneg hrpos.le (Real.rpow_nonneg hq _))
          _ = _ := by rw [rate_local_eq hrpos hℓ0]
    · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_left _ _)) hnp)
  · have hnN' : n < N₁ := not_le.mp hnN
    calc _ ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal (max C₀ ((N₁ : ℝ) ^ p) * (n : ℝ) ^ (-p)) := by
          rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (n : ℝ) ^ p ≤ (N₁ : ℝ) ^ p :=
            Real.rpow_le_rpow hnpos.le (by exact_mod_cast hnN'.le) hp.le
          have h2 : (1 : ℝ) ≤ (N₁ : ℝ) ^ p * (n : ℝ) ^ (-p) := by
            rw [Real.rpow_neg hnpos.le, ← div_eq_mul_inv]
            exact (one_le_div (Real.rpow_pos_of_pos hnpos p)).mpr h1
          exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hnp)

end CERW.LimitShapes
