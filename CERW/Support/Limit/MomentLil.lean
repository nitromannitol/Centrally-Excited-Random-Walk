import CERW.Support.Statements
import CERW.Support.Contact.Quadratic
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellVolume
import CERW.Support.Occupation.FreshSum
import CERW.Support.Occupation.Facts
import CERW.Generic.Kernel.RadialPacking
import CERW.Support.Main.ScaleLimits
import CERW.Support.Lower.SharpRadii
import CERW.Support.Limit.MomentCommon

/-!
# The iterated logarithm law for the moment radius in the plane

`CERW.Support.Limit.moment_radius_lil_of_stout` proves the law of the iterated logarithm for the
moment radius (Theorem 8.1(ii) of the paper for `d = 2`) from the limit shape and fluctuation
theorems and the cited law of the iterated logarithm for martingales (`StoutLIL`) alone; no
central limit theorem is used. Combined with `sharp_radii_lil_of_moment_lil` it gives
`CERW.Support.Lower.sharp_radii_lil_holds_of`.

The argument is the one for the iterated logarithm law in the proof of the limit laws for the sum
of the distances from the origin. The Dynkin martingale `𝒬` of `|x|²` equals
`2ε Σ_{x ∈ A_n} |x| - n + |X_n|²`. Its bracket is asymptotic to `r_n^{d+3}` times an explicit
constant by comparing the local times with the limit profile, its increments are bounded by the
predictable quantity `4 |X_{n-1}| + 2`, so the cited law applies to `𝒬` and `-𝒬`, and the sum
and the moment radius follow by a perturbation argument and a delta-method argument.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Limit

open CERW.Support.Statements

open LatticeProb CERW CERW.Support.Occupation CERW.Support.Law CERW.Support.Contact

/-- The law of the iterated logarithm for the Dynkin martingale of `|x|²`, normalized by
`r_n^{(d+3)/2}`. -/
private theorem dynkin_sq_lil {d : ℕ} (hd : 2 ≤ d) (hLIL : StoutLIL.{u})
    {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d)
    (hX : IsCERW μ ε X) {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
    (hloc : ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ y : Site d,
      |(localTime (fun j => X j ω) n y : ℝ) - 2 * d * ε * max (r n - euclidNorm y) 0|
        ≤ η * r n)
    (hmax : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, maxRadius (fun j => X j ω) n ≤ 2 * r n) :
    ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      (∀ᶠ n : ℕ in atTop,
        σ * dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n
          ≤ (Real.sqrt (bracketLimit d ε) + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
      (∃ᶠ n : ℕ in atTop,
        (Real.sqrt (bracketLimit d ε) - δ) * Real.sqrt (2 * Real.log (Real.log n))
          ≤ σ * dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n) := by
  have hd1 : 1 ≤ d := by omega
  have hε0 : 0 ≤ ε := hε.le
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hVpos : 0 < bracketLimit d ε := by
    unfold bracketLimit
    positivity
  set ℱ := pathFiltration hX.measurable with hℱ
  set Q : ℕ → Ω → ℝ := dynkin ε (fun z : Site d => euclidNorm z ^ 2) X with hQ
  have hmart : Martingale Q ℱ μ := martingale_dynkin hd1 hε0 hεd hX _
  have hL2 : ∀ n, MemLp (Q n) 2 μ := memLp_dynkin_sq hd1 hε0 hεd hX
  have hQ0 : ∀ ω, Q 0 ω = 0 := fun ω => dynkin_zero ε _ X ω
  set B : ℕ → Ω → ℝ := fun n ω => 4 * euclidNorm (X (n - 1) ω) + 2 with hB
  have hB0 : ∀ n ω, 0 ≤ B n ω := fun n ω => by
    have := euclidNorm_nonneg (X (n - 1) ω)
    simp only [hB]
    linarith
  have hBm : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1)) := fun n =>
    stronglyMeasurable_comp_pastPath hX.measurable n
      (fun p : (i : Finset.Iic n) → Site d =>
        4 * euclidNorm (p ⟨n, Finset.mem_Iic.2 le_rfl⟩) + 2)
  have hBb : ∀ᵐ ω ∂μ, ∀ n, |Q (n + 1) ω - Q n ω| ≤ B (n + 1) ω :=
    ae_abs_dynkin_sq_succ_sub_le hd1 hε0 hεd hX
  have hs := norming_pos ha hr
  have hs' := tendsto_norming_atTop ha hr
  have hrtend := tendsto_scale_atTop ha hr
  have hbr : ∀ᵐ ω ∂μ, Tendsto (fun n => predBracket μ ℱ Q Q n ω / norming d r n ^ 2) atTop
      (𝓝 (bracketLimit d ε)) := by
    filter_upwards [ae_predBracket_dynkin_sq hd1 hε0 hεd hX, hloc, hmax] with ω hbrω hlocω hmaxω
    have := tendsto_bracket_quotient hd1 hε hrtend (fun j => X j ω) hlocω hmaxω
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [hbrω n, norming_sq ha hr hn]
  have hBs : ∀ᵐ ω ∂μ, Tendsto (fun n => B n ω ^ 2 / norming d r n) atTop (𝓝 0) := by
    filter_upwards [hmax] with ω hmaxω
    have hlim : Tendsto (fun n => 100 * (r n ^ 2 / norming d r n)) atTop (𝓝 0) := by
      simpa using (tendsto_scale_sq_div hd ha hr).const_mul 100
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => ?_) ?_ hlim
    · exact div_nonneg (sq_nonneg _) (hs n).le
    · filter_upwards [hmaxω, hrtend.eventually_ge_atTop 1] with n h1 h2
      have hX1 : euclidNorm (X (n - 1) ω) ≤ maxRadius (fun j => X j ω) n :=
        euclidNorm_le_maxRadius (fun j => X j ω) (Nat.sub_le n 1)
      have hBn : B n ω ≤ 10 * r n := by
        simp only [hB]
        linarith
      have hsn := hs n
      calc B n ω ^ 2 / norming d r n ≤ (10 * r n) ^ 2 / norming d r n :=
            div_le_div_of_nonneg_right (pow_le_pow_left₀ (hB0 n ω) hBn 2) hsn.le
        _ = 100 * (r n ^ 2 / norming d r n) := by ring
  have hκ : 0 < ((d : ℝ) + 3) / ((d : ℝ) + 1) := by positivity
  have hlog := tendsto_log_norming_sq ha hr
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ →
      (∀ᶠ n : ℕ in atTop, σ * Q n ω / norming d r n
        ≤ (Real.sqrt (bracketLimit d ε) + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
      (∃ᶠ n : ℕ in atTop, (Real.sqrt (bracketLimit d ε) - δ) *
        Real.sqrt (2 * Real.log (Real.log n)) ≤ σ * Q n ω / norming d r n) := by
    intro σ hσ
    have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    set M : ℕ → Ω → ℝ := fun n ω => σ * Q n ω with hM
    have hMmart : Martingale M ℱ μ := hmart.smul σ
    have hML2 : ∀ n, MemLp (M n) 2 μ := fun n => (hL2 n).const_mul σ
    have hM0 : ∀ ω, M 0 ω = 0 := fun ω => by simp [hM, hQ0]
    have hMBb : ∀ᵐ ω ∂μ, ∀ n, |M (n + 1) ω - M n ω| ≤ B (n + 1) ω := by
      filter_upwards [hBb] with ω h n
      have : M (n + 1) ω - M n ω = σ * (Q (n + 1) ω - Q n ω) := by simp only [hM]; ring
      rw [this, abs_mul, hσabs, one_mul]
      exact h n
    have hbrM : ∀ n, predBracket μ ℱ M M n = predBracket μ ℱ Q Q n := by
      intro n
      unfold predBracket
      refine Finset.sum_congr rfl fun t _ => ?_
      congr 1
      funext ω
      have h1 : (M (t + 1) ω - M t ω) * (M (t + 1) ω - M t ω)
          = (σ * σ) * ((Q (t + 1) ω - Q t ω) * (Q (t + 1) ω - Q t ω)) := by
        simp only [hM]
        ring
      rw [h1, hσ2, one_mul]
    have hMbr : ∀ᵐ ω ∂μ, Tendsto (fun n => predBracket μ ℱ M M n ω / norming d r n ^ 2)
        atTop (𝓝 (bracketLimit d ε)) := by
      filter_upwards [hbr] with ω h
      simpa only [hbrM] using h
    exact lil_normalized hLIL μ ℱ M hMmart hML2 hM0 B hB0 hBm hMBb hs hs' hVpos hκ hMbr hBs hlog
  filter_upwards [key 1 (Or.inl rfl), key (-1) (Or.inr rfl)] with ω h1 h2 δ hδ σ hσ
  rcases hσ with rfl | rfl
  · exact h1 δ hδ
  · exact h2 δ hδ

/-- The iterated logarithm law for the moment radius in the plane, from the limit shape theorem,
the fluctuation theorem and the cited iterated logarithm law for martingales. -/
theorem moment_radius_lil_of_stout (hshape : limit_shape.{u})
    (hfluct : fluctuation_rates.{u}) : CERW.Support.Lower.moment_radius_lil.{u} := by
  intro d hd2 hLIL ωd ε hε hεd r v₂ Ω _ μ _ X hX R
  have hd : 2 ≤ d := hd2.symm.le
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hω : 0 < ωd := unitBallVolume_pos d
  have hc : 0 < ((d : ℝ) + 1) / (2 * d * ε * ωd) := by positivity
  set a : ℝ := (((d : ℝ) + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hc _
  have hr : ∀ n : ℕ, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := fun n => by
    show (((d : ℝ) + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) = _
    rw [show ((d : ℝ) + 1) * n / (2 * d * ε * ωd) =
      (((d : ℝ) + 1) / (2 * d * ε * ωd)) * n by ring]
    exact Real.mul_rpow hc.le (Nat.cast_nonneg n)
  have hrdef : ∀ n : ℕ, r n =
      ((d + 1) * n / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1)) := fun n => rfl
  have hrpow : ∀ n : ℕ, r n ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d) :=
    fun n => by
    rw [hrdef n, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have : ((1 : ℝ) / (d + 1)) * ((d + 1 : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  have hsh := hshape hd hε hεd μ X hX
  have hloc : ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ y : Site d,
      |(localTime (fun j => X j ω) n y : ℝ) - 2 * d * ε * max (r n - euclidNorm y) 0|
        ≤ η * r n := by
    filter_upwards [hsh] with ω h using h.2.1
  have hmax : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, maxRadius (fun j => X j ω) n ≤ 2 * r n := by
    obtain ⟨C, hC, -, hae⟩ := hfluct hd ε hε hεd 1 one_pos
    filter_upwards [hae μ X hX] with ω hω
    filter_upwards [hω, eventually_excess_le hd ha hr hC] with n hn hle
    have hex : maxRadius (fun j => X j ω) n - r n ≤ (if d = 2 then
        C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
        else C * Real.log n ^ ((d : ℝ) + 1)) := by
      have h1 := hn.1
      by_cases h2 : d = 2
      · rw [if_pos h2] at h1 ⊢
        exact h1.2
      · rw [if_neg h2] at h1 ⊢
        exact h1.2
    linarith
  have hQ2 := dynkin_sq_lil hd hLIL hε hεd μ X hX ha hr hloc hmax
  have hSlil := sum_lil hd hε μ X hX ha hr hmax hQ2
  have hAx := ae_tendsto_radiusFactor hd hε μ X hX ha hr hrdef hrpow hmax hQ2
  have hRlil := radius_lil hd hε μ X ha hr hrpow hSlil hAx
  filter_upwards [hRlil] with ω h δ hδ σ hσ
  exact (h δ hδ σ hσ).2

end CERW.Support.Limit

namespace CERW.Support.Lower

open CERW.Support.Statements

/-- Theorem 1.3(ii): the iterated logarithm law for the radii in the plane, from the limit shape
theorem, the fluctuation theorem and the cited iterated logarithm law for martingales. -/
theorem sharp_radii_lil_holds_of (hshape : limit_shape.{u}) (hfluct : fluctuation_rates.{u}) :
    sharp_radii_lil.{u} :=
  sharp_radii_lil_of_moment_lil (CERW.Support.Limit.moment_radius_lil_of_stout hshape hfluct)

end CERW.Support.Lower
