import CERW.LimitShapes.SharpRadii.Transfer
import CERW.Support.Lower.SharpWidth

/-!
# Two signs of the coarse quadratic deviation

The martingale furnished by the coarse bracket is rescaled, then Lemma 9.1(i)
is applied on a measurable subset of the common event. The radius transfer
retains the general coarse ball constant of Theorem 1.3(i).
-/

universe u

open MeasureTheory LatticeProb ProbabilityTheory

namespace CERW.LimitShapes.SharpRadii

open CERW CERW.Support.Law CERW.Support.Norm.ContactEvent
open private DeviationBound scale_sq_mul one_sub_le_measureReal
  from CERW.Support.Lower.SharpRadii

open private CERW.Support.Lower.predBracket_smul from CERW.Support.Lower.SharpWidth

/-- At one time the common event gives both radius probability bounds, from the
single-martingale form of Lemma 9.1(i). All numeric premises are deterministic. -/
theorem coarse_radii_deviation
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (2 : ℝ))
    (hX : IsCERW μ ε X) (K : EventConstants) (n : ℕ)
    {r R θ a α β c₁ C₁ B CS CI : ℝ}
    (hr : 0 < r) (hR : 1 ≤ R) (hθ : 0 < θ)
    (hscale : R = K.CCo * scale 2 (fun v => ‖v‖) ε n)
    (hRr : R = K.CCo * r) (hn : (n : ℝ) = a * R ^ 3)
    (hrn : r ^ 3 = 3 * n / (4 * ε * unitBallVolume 2))
    (hhalf : R * (2 * θ * R + 1) ^ 2 ≤ (n : ℝ) / 2)
    (herror : 4 * R ^ 2 * (4 * R + 1) ^ 2 ≤ θ ^ 2 * R ^ 2 * (n : ℝ) / 4)
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hEc : μ (section5Event (fun v => ‖v‖) ε
      (fun x => unitDir (toSpace x)) K X n)ᶜ ≤ ENNReal.ofReal α)
    (hβ : C₁ ≤ β)
    (hb : β * ((Real.sqrt (r ^ 5))⁻¹ * (2 * (2 * R + 1))) ≤ c₁)
    (hq : 0 < c₁ * β / (Real.sqrt (r ^ 5))⁻¹)
    (hqR : 2 * R ^ 2 ≤ c₁ * β / (Real.sqrt (r ^ 5))⁻¹)
    (hB : 0 ≤ B) (hCSr : K.CCo * r + CS ≤ B * r)
    (hCS : ∀ Y : ℕ → Site 2, momentRadius Y n ≤ maxRadius Y n + CS)
    (hCI : ∀ Y : ℕ → Site 2, innerRadius Y n ≤ momentRadius Y n + CI)
    (hdev : DeviationBound μ (pathFiltration hX.measurable) n
      ((θ ^ 2 * a / 2) * K.CCo ^ 5)
      (max ((θ ^ 2 * a / 2) * K.CCo ^ 5) (25 * a * K.CCo ^ 5)) c₁ C₁) :
    Real.exp (-(C₁ * β ^ 2)) / 4 - 2 * α ≤ μ.real {ω |
      3 * (c₁ * β / (Real.sqrt (r ^ 5))⁻¹) /
          (8 * ε * unitBallVolume 2 * (B ^ 2 + B + 1) * r ^ 2) - CS ≤
        maxRadius (X · ω) n - r} ∧
    Real.exp (-(C₁ * β ^ 2)) / 4 - 2 * α ≤ μ.real {ω |
      (c₁ * β / (Real.sqrt (r ^ 5))⁻¹) / (4 * ε * unitBallVolume 2 * r ^ 2) - CI ≤
        r - innerRadius (X · ω) n} := by
  obtain ⟨S, hS, hzero, hinc, hbr⟩ := exists_martingale_coarse_bracket hε hεd hX K n
    hR hθ hscale hn hhalf herror
  let κ := (Real.sqrt (r ^ 5))⁻¹
  have hκ : 0 < κ := inv_pos.mpr (Real.sqrt_pos.mpr (pow_pos hr 5))
  have hκ2 : κ ^ 2 * R ^ 5 = K.CCo ^ 5 := by
    rw [hRr, mul_pow]
    calc
      _ = K.CCo ^ 5 * (κ ^ 2 * r ^ 5) := by ring
      _ = K.CCo ^ 5 := by rw [scale_sq_mul hr, mul_one]
  let F := section5Event (fun v => ‖v‖) ε (fun x => unitDir (toSpace x)) K X n
  let E := (toMeasurable μ Fᶜ)ᶜ
  have hE : MeasurableSet E := (measurableSet_toMeasurable μ Fᶜ).compl
  have hEF : E ⊆ F := by
    intro ω hω
    by_contra hf
    exact hω (subset_toMeasurable μ Fᶜ hf)
  have hEc' : μ Eᶜ ≤ ENNReal.ofReal α := by
    simpa only [E, compl_compl, measure_toMeasurable] using hEc
  have hEα := one_sub_le_measureReal hα hE hEc'
  have hEcReal : μ.real Eᶜ ≤ α := ENNReal.toReal_le_of_le_ofReal hα hEc'
  have hnorm : ∀ᵐ ω ∂μ, ω ∈ E →
      (θ ^ 2 * a / 2) * K.CCo ^ 5 ≤
        predBracket μ (pathFiltration hX.measurable) (κ • S) (κ • S) n ω ∧
      predBracket μ (pathFiltration hX.measurable) (κ • S) (κ • S) n ω ≤
        max ((θ ^ 2 * a / 2) * K.CCo ^ 5) (25 * a * K.CCo ^ 5) := by
    filter_upwards [hbr, CERW.Support.Lower.predBracket_smul μ (pathFiltration hX.measurable) S κ n]
      with ω hω hnorm hωE
    obtain ⟨_, hlo, hup⟩ := hω (hEF hωE)
    rw [hnorm]
    have hl := mul_le_mul_of_nonneg_left hlo (sq_nonneg κ)
    have hu := mul_le_mul_of_nonneg_left hup (sq_nonneg κ)
    have he (c : ℝ) : κ ^ 2 * (c * R ^ 5) = c * K.CCo ^ 5 := by
      calc
        _ = c * (κ ^ 2 * R ^ 5) := by ring
        _ = _ := by rw [hκ2]
    rw [he] at hl hu
    exact ⟨hl, hu.trans (le_max_right _ _)⟩
  have hbpos : 0 < κ * (2 * (2 * R + 1)) := by positivity
  have hscaled : ∀ t < n, ∀ ω,
      |(κ • S) (t + 1) ω - (κ • S) t ω| ≤ κ * (2 * (2 * R + 1)) := by
    intro t _ ω
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, abs_mul, abs_of_pos hκ]
    exact mul_le_mul_of_nonneg_left (hinc t ω) hκ.le
  obtain ⟨hp, hm⟩ := hdev _ α (κ • S) E hbpos hα hα1 (hS.smul κ)
    (by intro ω; simp only [Pi.smul_apply, smul_eq_mul, hzero, mul_zero]) hscaled hE hEα
    hnorm β hβ hb
  have hp' : Real.exp (-(C₁ * β ^ 2)) / 4 - α ≤
      μ.real {ω | c₁ * β / κ ≤ S n ω} := by
    simpa only [Pi.smul_apply, smul_eq_mul, div_le_iff₀ hκ, mul_comm] using hp
  have hm' : Real.exp (-(C₁ * β ^ 2)) / 4 - α ≤
      μ.real {ω | S n ω ≤ -(c₁ * β / κ)} := by
    have he : {ω | (κ • S) n ω ≤ -(c₁ * β)} =
        {ω | S n ω ≤ -(c₁ * β / κ)} := by
      ext ω
      simp only [Pi.smul_apply, smul_eq_mul, ← neg_div, le_div_iff₀ hκ, mul_comm]
    rwa [he] at hm
  have hag : ∀ᵐ ω ∂μ, ω ∈ E → S n ω = quadraticMart ε (X · ω) n ∧
      maxRadius (X · ω) n ≤ K.CCo * r := by
    filter_upwards [hbr] with ω hω hωE
    have hωF := hEF hωE
    refine ⟨(hω hωF).1, ?_⟩
    have ho := hωF.1.2.2.2.2.2
    rw [← hscale, hRr] at ho
    exact ho
  have ht := radii_of_quadratic_deviations hε hr hB hrn hE hEcReal hag hCS hCI hCSr
    hq (by simpa only [← hRr] using hqR) hp' hm'
  constructor <;> linarith [ht.1, ht.2]

end CERW.LimitShapes.SharpRadii
