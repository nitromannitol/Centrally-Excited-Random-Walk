module

public import CERW.LimitShapes.BulkProfileProbability.Event
public import CERW.LimitShapes.EuclideanEvent
public import CERW.LimitShapes.Curvature.FluctuationTheorem

@[expose] public section

/-!
# Probability and almost sure bulk profiles

Proposition `prop:bulk-profile` follows by intersecting the common event of
`sec:norm-event` and Theorem `thm:fluctuations`, and applying the excess-set estimate.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes

open CERW
open private InnerVolume innerVolume_of_clauses measure_not_le_add
  from CERW.Support.Lower.BulkProfile

/-- The exact bulk profile, with polynomial tails and almost sure eventual validity, from
the common event and the excess-set potential bound of Proposition `prop:bulk-profile`. -/
theorem bulk_profile_from_common_event : CERW.Support.Statements.bulk_profile.{u} := by
  intro d hd ωd ε hε hεd r θ hθ hθ1 p hp
  let ps := max p 2
  have hps : 0 < ps := lt_max_of_lt_right two_pos
  have hps1 : 1 < ps := lt_max_of_lt_right one_lt_two
  obtain ⟨A, hA, hfluct, _⟩ :=
    Curvature.fluctuation_rates_via_curvature.{u} hd ε hε hεd ps hps
  obtain ⟨K, _, hCo, hLoc, _, _, _, _, Cp, hCp, np, hnp, hprob⟩ :=
    EuclideanEvent.exists_euclidean_event.{u} hd hε hεd ps hps
  have hIV : ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d), IsCERW μ ε X →
      ∀ n : ℕ, 2 ≤ n → μ {ω | ¬ InnerVolume d r A (X · ω) n} ≤
        ENNReal.ofReal (A * (n : ℝ) ^ (-ps)) := by
    intro Ω _ μ _ X hX n hn
    refine (measure_mono ?_).trans (hfluct μ X hX n hn)
    intro ω hbad hg
    exact hbad (innerVolume_of_clauses (r := r) hg)
  have hω : 0 < ωd := unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  let κ : ℝ := (d + 1) / (2 * d * ε * ωd)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hrκ : ∀ n : ℕ, r n = (κ * n) ^ ((1 : ℝ) / (d + 1)) := by
    intro n
    change (((d : ℝ) + 1) * n / (2 * d * ε * ωd)) ^ _ = _
    dsimp only [κ]
    rw [mul_div_right_comm]
  have hrs : ∀ n, CERW.Support.Norm.ContactEvent.scale d
      (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n = r n := by
    intro n
    simp only [CERW.Support.Norm.ContactEvent.scale,
      CERW.Support.Norm.Section5Localization.normBallVolume_norm]
    rfl
  obtain ⟨Cb, hCb, hev⟩ := bulk_profile_on_intersection hd hε hκ hA hθ hθ1
    K hCo.le hLoc.le r hrκ hrs
  obtain ⟨nb, hnb⟩ := eventually_atTop.mp hev
  let N := max np nb
  let C := Cb + A + Cp + (N : ℝ) ^ ps
  have hpowN : 0 ≤ (N : ℝ) ^ ps := Real.rpow_nonneg (Nat.cast_nonneg N) ps
  have hC : 0 < C := by dsimp only [C]; positivity
  have hbC : Cb ≤ C := by dsimp only [C]; linarith
  have hpC : A + Cp ≤ C := by dsimp only [C]; linarith
  have hnC : (N : ℝ) ^ ps ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro Good
  have hgood : ∀ (Y : ℕ → Site d) (n : ℕ), nb ≤ n →
      InnerVolume d r A Y n → CERW.Support.Norm.ContactEvent.PathTyping d Y →
      EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε
        (fun x => unitDir (toSpace x)) K Y n → Good Y n := by
    intro Y n hn hi hlegal he y hy
    apply (hnb n hn Y hi hlegal he y hy).trans
    apply mul_le_mul_of_nonneg_right hbC
    split_ifs
    · exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_natCast_nonneg n)
    · exact Real.sqrt_nonneg _
  have htail : ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d), IsCERW μ ε X →
      ∀ n : ℕ, 2 ≤ n → μ {ω | ¬ Good (X · ω) n} ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (-ps)) := by
    intro Ω _ μ _ X hX n hn2
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    by_cases hn : N ≤ n
    · have hlegal := CERW.Support.Norm.Section5Localization.ae_legal_of_isDriftCERW
        ((CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).mp hX)
      have hnull : μ {ω | ¬ CERW.Support.Norm.ContactEvent.PathTyping d (X · ω)} = 0 :=
        measure_eq_zero_iff_ae_notMem.mpr (by simpa only [Set.mem_setOf_eq, not_not,
          CERW.Support.Norm.Section5Localization.legalSet,
          CERW.Support.Norm.ContactEvent.PathTyping] using hlegal)
      have hu := measure_not_le_add μ
        (P₁ := fun ω => InnerVolume d r A (X · ω) n)
        (P₂ := fun ω => EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε
          (fun x => unitDir (toSpace x)) K (X · ω) n)
        (P₃ := fun ω => CERW.Support.Norm.ContactEvent.PathTyping d (X · ω))
        (Q := fun ω => Good (X · ω) n)
        (fun ω hi he hl => hgood (X · ω) n (by dsimp [N] at hn; omega) hi hl he)
      rw [hnull, add_zero] at hu
      have he := hprob μ X hX n (by dsimp [N] at hn; omega)
      have hu' := hu.trans (add_le_add (hIV μ X hX n hn2) he)
      apply hu'.trans
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = (A + Cp) * (n : ℝ) ^ (-ps) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hpC (Real.rpow_nonneg hnpos.le _)
    · have hnN : (n : ℝ) ≤ N := by exact_mod_cast (by omega : n ≤ N)
      have hnp : (n : ℝ) ^ ps ≤ C :=
        (Real.rpow_le_rpow hnpos.le hnN hps.le).trans hnC
      apply prob_le_one.trans
      rw [ENNReal.one_le_ofReal]
      calc
        (1 : ℝ) = (n : ℝ) ^ ps * (n : ℝ) ^ (-ps) := by
          rw [← Real.rpow_add hnpos]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hnp (Real.rpow_nonneg hnpos.le _)
  constructor
  · intro Ω _ μ _ X hX n hn
    apply (htail μ X hX n hn).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (by omega : 1 ≤ n)) (neg_le_neg (le_max_left p 2))
  · intro Ω _ μ _ X hX
    exact Curvature.ae_eventually_of_polynomial_bound μ
      (fun n ω => Good (X · ω) n) hps1 (htail μ X hX)

end CERW.LimitShapes
