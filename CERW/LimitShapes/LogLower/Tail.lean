import CERW.LimitShapes.LogLower.Azuma
import CERW.Support.Lower.LogLower

/-!
# Azuma for the stopped quadratic process

The path-space law permits conditional Hoeffding without imposing any regularity assumption
on the original probability space. The bounded representative of the stopped quadratic
martingale transfers the resulting tail back to the quadratic event in Proposition 9.4.
-/

open MeasureTheory ProbabilityTheory Filter
open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes.LogLower

open CERW CERW.Support.Law
open private exists_clamped_stopped_quadratic from CERW.Support.Lower.LogLower

/-- The coordinate process under the path law satisfies the same walk law. -/
theorem isCERW_path_law {d : ℕ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) :
    IsCERW (μ.map (fun ω j => X j ω)) ε (fun j x => x j) := by
  have hP : Measurable (fun ω j => X j ω) := measurable_pi_lambda _ hX.measurable
  have hc (s : ℕ) (y : ℕ → Site d) :
      MeasurableSet {x : ℕ → Site d | ∀ j ≤ s, x j = y j} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    have hj : Measurable (fun x : ℕ → Site d => x j) := measurable_pi_apply j
    exact measurableSet_eq_fun hj measurable_const
  constructor
  · exact fun j => measurable_pi_apply j
  · have hs : MeasurableSet {x : ℕ → Site d | x 0 ≠ 0} :=
      (measurableSet_eq_fun
        (show Measurable (fun x : ℕ → Site d => x 0) from measurable_pi_apply 0)
        measurable_const).compl
    rw [Measure.map_apply hP hs]
    exact hX.start
  · intro n y
    rw [Measure.map_apply hP (hc (n + 1) y), Measure.map_apply hP (hc n y)]
    exact hX.step n y

/-- The lower quadratic event has the Azuma exponent for the actual stopped martingale. -/
theorem quadratic_lower_tail {d : ℕ} (hd : 2 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X)
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (n : ℕ) :
    μ {ω | (∀ j ≤ n, euclidNorm (X j ω) ≤ R) ∧
        quadraticMart ε (fun j => X j ω) n ≤ -t} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * n * (2 * (2 * R + 1)) ^ 2)))) := by
  have hP : Measurable (fun ω j => X j ω) := measurable_pi_lambda _ hX.measurable
  let ν := μ.map (fun ω j => X j ω)
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hP.aemeasurable
  have hpath : IsCERW ν ε (fun j x => x j) := isCERW_path_law hX
  obtain ⟨M, hM, hinc, _, hzero, hae⟩ :=
    exists_clamped_stopped_quadratic hd hε.le hεd hR n hpath
  have htail := martingale_lower_tail hM hzero
    (by positivity : 0 ≤ 2 * (2 * R + 1)) hinc ht n
  have hstart : ∀ᵐ x ∂ν, x 0 = 0 := ae_iff.mpr hpath.start
  have hsub : {x : ℕ → Site d | (∀ j ≤ n, euclidNorm (x j) ≤ R) ∧
      quadraticMart ε x n ≤ -t} ≤ᵐ[ν] {x | M n x ≤ -t} := by
    filter_upwards [hae, hstart] with x hx hx0 hevent
    have hsq := CERW.Support.Contact.sq_euclidNorm_eq (by omega : 1 ≤ d)
      ε (fun j x => x j) x hx0 n
    have hQ : quadraticMart ε x n =
        dynkin ε (fun z : Site d => euclidNorm z ^ 2) (fun j x => x j) n x := by
      unfold quadraticMart
      linarith
    change M n x ≤ -t
    rw [hx hevent.1, ← hQ]
    exact hevent.2
  have htail' : ν {x | M n x ≤ -t} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * n * (2 * (2 * R + 1)) ^ 2)))) :=
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr htail
  exact (Measure.le_map_apply hP.aemeasurable _).trans
    ((measure_mono_ae hsub).trans htail')

end CERW.LimitShapes.LogLower
