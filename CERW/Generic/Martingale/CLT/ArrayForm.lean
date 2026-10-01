import CERW.External.MartingaleCLT
import Mathlib.MeasureTheory.Measure.LevyConvergence
import CERW.Generic.Martingale.CLT.Interfaces

/-!
# The array form of the martingale central limit theorem

Convergence of characteristic functions to the Gaussian one gives convergence in distribution to
`gaussianReal 0 v`. The array form `ArrayCLT` of the martingale central limit theorem, for rows
`M n` that are square-integrable martingales started at `0`, implies the form carried by
`CERW.External.MartingaleCLT`, which has one martingale `S` and normalizers `s n`.
-/

universe u

namespace CERW.Generic.Martingale.CLT

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal

/-- If the characteristic functions of measurable real random variables converge pointwise to
that of the centered Gaussian of variance `v`, the variables converge in distribution to it. -/
theorem tendstoInDistribution_gaussianReal_of_tendsto_integral_cexp
    {Ω : Type*} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (v : ℝ≥0) (hX : ∀ n, AEMeasurable (X n) μ)
    (h : ∀ t : ℝ, Tendsto (fun n => ∫ ω, Complex.exp (t * X n ω * Complex.I) ∂μ) atTop
      (𝓝 (Complex.exp (-(t ^ 2 * v / 2 : ℝ))))) :
    TendstoInDistribution X atTop id (fun _ => μ) (gaussianReal 0 v) := by
  refine ⟨hX, aemeasurable_id, ?_⟩
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
  have hmap : ∀ n, charFun (μ.map (X n)) t = ∫ ω, Complex.exp (t * X n ω * Complex.I) ∂μ :=
    fun n => by
      rw [charFun_apply_real, integral_map (hX n)]
      exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  simp only [ProbabilityMeasure.coe_mk, hmap, Measure.map_id, charFun_gaussianReal]
  have harg : (↑t * ↑0 * Complex.I - ↑↑v * ↑t ^ 2 / 2 : ℂ)
      = -(Complex.ofReal (t ^ 2 * (v : ℝ) / 2)) := by
    push_cast
    ring
  simp only [Complex.ofReal_zero] at harg ⊢
  rw [harg]
  exact h t
/-- The array form of the martingale central limit theorem: for rows `M n` of square-integrable
martingales started at `0`, whose conditional Lindeberg sums tend to `0` in measure and whose
predictable brackets tend to `v` in measure, the last terms `M n n` converge in distribution to
the centered Gaussian of variance `v`. -/
def ArrayCLT : Prop :=
  ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (M : ℕ → ℕ → Ω → ℝ) (v : ℝ≥0),
    (∀ n, Martingale (M n) ℱ μ) → (∀ n k, MemLp (M n k) 2 μ) → (∀ n ω, M n 0 ω = 0) →
    (∀ δ : ℝ, 0 < δ → TendstoInMeasure μ
      (fun n ω => ∑ i ∈ Finset.range n,
        μ[fun ω => (M n (i + 1) ω - M n i ω) ^ 2 *
          (if δ < |M n (i + 1) ω - M n i ω| then 1 else 0) | ℱ i] ω)
      atTop (fun _ => 0)) →
    TendstoInMeasure μ (fun n => CERW.predBracket μ ℱ (M n) (M n) n) atTop
      (fun _ => (v : ℝ)) →
    TendstoInDistribution (fun n => M n n) atTop id (fun _ => μ) (gaussianReal 0 v)

/-- Dividing a process by a constant `c` divides its predictable bracket by `c ^ 2`, up to a null
set. -/
private theorem predBracket_div_const_ae_eq {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ) (c : ℝ) (n : ℕ) :
    CERW.predBracket μ ℱ (fun k ω => S k ω / c) (fun k ω => S k ω / c) n =ᵐ[μ]
      fun ω => CERW.predBracket μ ℱ S S n ω / c ^ 2 := by
  have hterm : ∀ t : ℕ,
      μ[fun ω => (S (t + 1) ω / c - S t ω / c) * (S (t + 1) ω / c - S t ω / c) | ℱ t] =ᵐ[μ]
        fun ω => (c ^ 2)⁻¹ *
          μ[fun ω => (S (t + 1) ω - S t ω) * (S (t + 1) ω - S t ω) | ℱ t] ω := by
    intro t
    have e : (fun ω => (S (t + 1) ω / c - S t ω / c) * (S (t + 1) ω / c - S t ω / c)) =
        (c ^ 2)⁻¹ • fun ω => (S (t + 1) ω - S t ω) * (S (t + 1) ω - S t ω) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    filter_upwards [condExp_smul ((c ^ 2)⁻¹)
      (fun ω => (S (t + 1) ω - S t ω) * (S (t + 1) ω - S t ω)) (ℱ t)] with ω hω
    simpa using hω
  filter_upwards [ae_all_iff.2 hterm] with ω hω
  simp only [CERW.predBracket, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun t _ => hω t, ← Finset.mul_sum, div_eq_inv_mul]

/-- The array form of the martingale central limit theorem implies the form with a single
martingale `S`, normalizers `s n` and the rows `S k / s n`. -/
theorem martingaleCLT_of_arrayCLT (h : ArrayCLT.{u}) : CERW.External.MartingaleCLT.{u} := by
  intro Ω m0 μ hμ ℱ S hS hL hS0 s hs v hLind hBr
  have hrow : ∀ n, (fun k ω => S k ω / s n) = (s n)⁻¹ • S := fun n => by
    funext k ω
    simp [div_eq_inv_mul]
  refine h μ ℱ (fun n k ω => S k ω / s n) v ?_ ?_ ?_ ?_ ?_
  · intro n
    rw [hrow n]
    exact hS.smul _
  · intro n k
    have := (hL k).const_mul (s n)⁻¹
    simpa [div_eq_inv_mul] using this
  · intro n ω
    simp [hS0]
  · intro δ hδ
    refine (hLind δ hδ).congr_left (fun n => ae_of_all _ fun ω => ?_)
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← sub_div, abs_div, abs_of_pos, hs]
  · exact hBr.congr (fun n => (predBracket_div_const_ae_eq μ ℱ S (s n) n).symm) EventuallyEq.rfl

end CERW.Generic.Martingale.CLT
