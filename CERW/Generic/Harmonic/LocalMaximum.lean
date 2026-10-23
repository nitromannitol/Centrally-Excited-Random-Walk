import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-! # Calculus at local maxima

Second derivatives along lines give the sign of the Laplacian at a local maximum.
-/

open MeasureTheory Filter Topology
open InnerProductSpace Laplacian

namespace CERW.Generic.Harmonic

/-- The second derivative at a local maximum of a continuous real function is nonpositive. -/
theorem deriv_deriv_nonpos_of_localMax {g : ℝ → ℝ} {a : ℝ}
    (hm : IsLocalMax g a) (hc : ContinuousAt g a) : deriv (deriv g) a ≤ 0 := by
  by_contra h
  have hp : 0 < deriv (deriv g) a := lt_of_not_ge h
  have hn := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : g =ᶠ[𝓝 a] fun _ => g a := by
    filter_upwards [hm, hn] with x hx hy
    exact le_antisymm hx hy
  have hz : deriv (deriv g) a = 0 := by
    simpa using he.deriv.deriv_eq
  exact hp.ne' hz

/-- At a local maximum, every diagonal entry of the Hessian is nonpositive. -/
theorem fderiv_fderiv_nonpos_of_localMax
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) (v : E) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ 0 := by
  let c : ℝ → E := fun t => x + t • v
  have hc : ∀ t, HasDerivAt c v t := by
    intro t
    simpa [c] using (hasDerivAt_id t).smul_const v |>.const_add x
  have hcx : c 0 = x := by simp [c]
  have hg : IsLocalMax (f ∘ c) 0 := by
    apply IsLocalMax.comp_continuous (g := c)
    · simpa [hcx] using hm
    · exact (hc 0).continuousAt
  have he : deriv (f ∘ c) =ᶠ[𝓝 0] fun t => fderiv ℝ f (c t) v := by
    have hd := hf.eventually (by norm_num) |>.mono fun y hy =>
      hy.differentiableAt (by norm_num)
    have ht : Tendsto c (𝓝 0) (𝓝 x) := by
      simpa only [hcx] using (hc 0).continuousAt.tendsto
    filter_upwards [ht.eventually hd] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hc t)).deriv
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hd' : DifferentiableAt ℝ (fderiv ℝ f) (c 0) := by simpa [hcx] using hd
  have hh := (hd'.hasFDerivAt.comp_hasDerivAt 0 (hc 0)).clm_apply
    (hasDerivAt_const 0 v)
  have hv : deriv (deriv (f ∘ c)) 0 = fderiv ℝ (fderiv ℝ f) x v v := by
    rw [he.deriv_eq]
    simpa [hcx] using hh.deriv
  rw [← hv]
  apply deriv_deriv_nonpos_of_localMax hg
  have hfc : ContinuousAt f (c 0) := by simpa only [hcx] using hf.continuousAt
  exact hfc.comp (hc 0).continuousAt

/-- A twice continuously differentiable function has nonpositive Laplacian at a local maximum. -/
theorem laplacian_nonpos_of_localMax
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) :
    laplacian f x ≤ 0 := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_nonpos
  intro i _
  simpa [iteratedFDeriv_two_apply] using
    fderiv_fderiv_nonpos_of_localMax hf hm ((stdOrthonormalBasis ℝ E) i)

/-- The squared norm has constant Laplacian twice the dimension. -/
theorem laplacian_norm_sq {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    laplacian (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖ ^ 2) x = 2 * (d : ℝ) := by
  have he : fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖ ^ 2)) x =
      2 • innerSL ℝ := by
    rw [fderiv_norm_sq]
    exact ((innerSL ℝ (E := EuclideanSpace ℝ (Fin d))).hasFDerivAt.const_smul (2 : ℕ)).fderiv
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, he]
  simp only [two_smul, add_apply]
  change (∑ i : Fin d,
    (inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i)
      ((EuclideanSpace.basisFun (Fin d) ℝ) i) +
    inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i)
      ((EuclideanSpace.basisFun (Fin d) ℝ) i))) = 2 * (d : ℝ)
  simp [two_mul]

end CERW.Generic.Harmonic
