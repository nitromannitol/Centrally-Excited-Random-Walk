module

public import CERW.LimitShapes.BulkProfileProbability.Event
public import CERW.LimitShapes.Curvature.FluctuationTheorem

@[expose] public section

/-!
# The bulk potential from the excess set

The display `eq:bulk-potential-only` follows from the excess-set potential estimate
and the radius and volume clauses of Theorem `thm:fluctuations`.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes

open CERW
open CERW.Support.Norm.ContactEvent (scale contactRate)
open private exists_contact_setup_core from CERW.Support.Contact.ContactSetup
open private InnerVolume innerVolume_of_clauses from CERW.Support.Lower.BulkProfile

/-- The excess-set estimate gives the potential display on the inner-volume event. -/
theorem bulk_potential_on_inner_volume {d : ℕ} (hd : 2 ≤ d) {ε κ A : ℝ}
    (hε : 0 < ε) (hκ : 0 < κ) (hA : 0 < A)
    (r : ℕ → ℝ) (hr : ∀ n, r n = (κ * n) ^ ((1 : ℝ) / (d + 1)))
    (hrscale : ∀ n, scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n = r n) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ Y : ℕ → Site d,
      InnerVolume d r A Y n → CERW.Support.Norm.ContactEvent.PathTyping d Y →
      ∀ y : Site d, euclidNorm y ≤ r n / 2 →
        |potential d ε (cellSet Y n) (toSpace y) -
          2 * d * ε * (r n - euclidNorm y)| ≤
          C * (if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n) := by
  let θ : ℝ := 1 / 2
  have hθ : 0 < θ := by norm_num [θ]
  have hθ1 : θ < 1 := by norm_num [θ]
  let V := A + unitBallVolume d * A * d * 2 ^ (d - 1)
  let C := (2 * ε / unitBallVolume d) *
    (((1 - θ) / 2) ^ (d - 1))⁻¹ * V + 2 * d * ε * A
  have hω := unitBallVolume_pos d
  have ht : 0 < (1 - θ) / 2 := by linarith
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hC : 0 < C := by
    have hlast : 0 < 2 * (d : ℝ) * ε * A := by positivity
    have hmid : 0 ≤ (2 * ε / unitBallVolume d) *
        (((1 - θ) / 2) ^ (d - 1))⁻¹ * V := by positivity
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  filter_upwards [bulk_scales_eventually hd hκ hA hθ hθ1 r hr] with n hn
  obtain ⟨hn2, hr1, hl1, hlr, hlog, hs, hyn⟩ := hn
  intro Y hIV hlegal y hy
  have hrp : 0 < r n := by linarith
  have hq : 0 ≤ (if d = 2 then Real.sqrt (Real.log n / r n)
      else Real.log n / r n) := by split_ifs <;> positivity
  have he : r n * (if d = 2 then Real.sqrt (Real.log n / r n)
      else Real.log n / r n) =
      if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n := by
    have h := Energy.scale_mul_contactRate
      (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n (by rw [hrscale]; exact hrp)
    simpa only [contactRate, hrscale] using h
  have hin : |innerRadius Y n - r n| ≤
      A * r n * (if d = 2 then Real.sqrt (Real.log n / r n)
        else Real.log n / r n) := by
    rw [mul_assoc, he]
    exact hIV.1
  have hb : 0 < innerRadius Y n := by
    have hR := CERW.Support.Outer.Radius.gd_maxRadius_nonneg Y n
    have hsq := Real.sqrt_nonneg (d : ℝ)
    have hsub := CERW.Support.Occupation.cellSet_subset_ball (by omega : 1 ≤ d) Y n
    exact (exists_contact_setup_core hd Y n (maxRadius Y n + 2 * Real.sqrt d + 1)
      (by omega) hlegal.1 (by linarith)
      (hsub.trans (Metric.ball_subset_ball (by linarith)))).1
  have hs1 : A * (if d = 2 then Real.sqrt (Real.log n / r n)
      else Real.log n / r n) ≤ 1 := hs.trans (by linarith)
  have hvol := bulk_excess_volume_le (by omega : 1 ≤ d) hrp hb.le hA.le hq hs1
    hin hIV.2
  have hys : ‖toSpace y‖ ≤ θ * r n := by
    rw [norm_toSpace]
    simpa only [θ, one_div, inv_mul_eq_div] using hy
  have hp := bulk_potential_from_excess hd hε.le hb hrp hθ1
    (CERW.Support.Occupation.measurableSet_cellSet Y n)
    (Metric.isBounded_ball.subset
      (CERW.Support.Occupation.cellSet_subset_ball (by omega : 1 ≤ d) Y n))
    (CERW.Support.Outer.Radius.ball_innerRadius_subset (by omega) Y n)
    hin hs hvol hys
  simpa only [C, V, mul_assoc, he, norm_toSpace] using hp

/-- The potential-only display `eq:bulk-potential-only`, with polynomial tail of exponent ten,
obtained by bounding the actual potential through the separated excess set. -/
theorem bulk_potential_only_from_excess {d : ℕ} (hd : 2 ≤ d) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / (d : ℝ)) :
    let r : ℕ → ℝ := fun n =>
      (((d : ℝ) + 1) * n / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))
    ∃ C : ℝ, 0 < C ∧ ∃ n₁ : ℕ, ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, n₁ ≤ n →
      μ {ω | ¬ ∀ y : Site d, euclidNorm y ≤ r n / 2 →
          |potential d ε (cellSet (fun j => X j ω) n) (toSpace y) -
              2 * d * ε * (r n - euclidNorm y)| ≤
            C * (if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n)} ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (-(10 : ℝ))) := by
  intro r
  obtain ⟨A, hA, hfluct, _⟩ :=
    Curvature.fluctuation_rates_via_curvature.{u} hd ε hε0 hε1 10 (by norm_num)
  have hω := unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  let κ : ℝ := (d + 1) / (2 * d * ε * unitBallVolume d)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hrκ : ∀ n : ℕ, r n = (κ * n) ^ ((1 : ℝ) / (d + 1)) := by
    intro n
    dsimp only [r, κ]
    rw [mul_div_right_comm]
  have hrs : ∀ n, scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n = r n := by
    intro n
    simp only [scale, CERW.Support.Norm.Section5Localization.normBallVolume_norm]
    rfl
  obtain ⟨Cb, hCb, hev⟩ := bulk_potential_on_inner_volume hd hε0 hκ hA r hrκ hrs
  obtain ⟨nb, hnb⟩ := eventually_atTop.mp hev
  let C := Cb + A
  have hC : 0 < C := add_pos hCb hA
  have hbC : Cb ≤ C := le_add_of_nonneg_right hA.le
  have hAC : A ≤ C := le_add_of_nonneg_left hCb.le
  refine ⟨C, hC, max nb 2, ?_⟩
  intro Ω _ μ _ X hX n hn
  have hn2 : 2 ≤ n := (le_max_right nb 2).trans hn
  have hlegal := CERW.Support.Norm.Section5Localization.ae_legal_of_isDriftCERW
    ((CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).mp hX)
  have hnull : μ {ω | ¬ CERW.Support.Norm.ContactEvent.PathTyping d (X · ω)} = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr (by simpa only [Set.mem_setOf_eq, not_not,
      CERW.Support.Norm.Section5Localization.legalSet,
      CERW.Support.Norm.ContactEvent.PathTyping] using hlegal)
  have hsub : {ω | ¬ ∀ y : Site d, euclidNorm y ≤ r n / 2 →
      |potential d ε (cellSet (X · ω) n) (toSpace y) -
        2 * d * ε * (r n - euclidNorm y)| ≤
        C * (if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n)} ⊆
      {ω | ¬ InnerVolume d r A (X · ω) n} ∪
      {ω | ¬ CERW.Support.Norm.ContactEvent.PathTyping d (X · ω)} := by
    intro ω hbad
    by_cases hi : InnerVolume d r A (X · ω) n
    · by_cases hl : CERW.Support.Norm.ContactEvent.PathTyping d (X · ω)
      · exfalso
        apply hbad
        intro y hy
        apply (hnb n ((le_max_left nb 2).trans hn) (X · ω) hi hl y hy).trans
        apply mul_le_mul_of_nonneg_right hbC
        split_ifs
        · exact Real.sqrt_nonneg _
        · exact Real.log_natCast_nonneg n
      · exact Or.inr hl
    · exact Or.inl hi
  have hIV : μ {ω | ¬ InnerVolume d r A (X · ω) n} ≤
      ENNReal.ofReal (A * (n : ℝ) ^ (-(10 : ℝ))) := by
    apply (measure_mono ?_).trans (hfluct μ X hX n hn2)
    intro ω hbad hg
    exact hbad (innerVolume_of_clauses (r := r) hg)
  calc
    _ ≤ μ ({ω | ¬ InnerVolume d r A (X · ω) n} ∪
        {ω | ¬ CERW.Support.Norm.ContactEvent.PathTyping d (X · ω)}) :=
      measure_mono hsub
    _ ≤ μ {ω | ¬ InnerVolume d r A (X · ω) n} +
        μ {ω | ¬ CERW.Support.Norm.ContactEvent.PathTyping d (X · ω)} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-(10 : ℝ))) := by
      rw [hnull, add_zero]
      exact hIV
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hAC (Real.rpow_nonneg (Nat.cast_nonneg n) _))

end CERW.LimitShapes
