import CERW.Support.Statements
import CERW.Support.Drift
import CERW.Support.LocalTime.KernelAsymptotics
import CERW.Support.LocalTime.KernelFacts
import CERW.Generic.Kernel.NewtonField
import CERW.Support.Contact.ContactCell
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellSetVolume
import CERW.Generic.Norm.Sphere
import CERW.Generic.Norm.Gradient
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral
import CERW.Generic.Norm
import CERW.Support.Occupation.CellVolume
import CERW.Model
import CERW.Generic.Kernel.Integrable
import CERW.Generic.Kernel.LogRadial
import CERW.Support.Geometry.Newton
import CERW.Generic.Kernel.Modulus
import CERW.Generic.Newton.Polar
import CERW.Model.NormPotential
import CERW.Model.Norm
import CERW.Support.Geometry.Bound
import CERW.Support.LocalTime.DynkinLocal
import CERW.Support.LocalTime.LocalMart
import CERW.Support.LocalTime.ReplaceGradient
import CERW.Support.LocalTime.ReplaceCell
import CERW.Support.Occupation.CellIntegral
import CERW.Support.Occupation.SiteArith
import CERW.Support.Occupation.Facts
import CERW.Generic.Lattice.Centered
import CERW.Generic.Kernel.RadialPower
import CERW.Support.LocalTime.Bracket
import CERW.Support.Law.ScaleArith
import CERW.Support.Occupation.Cells
import CERW.Generic.Norm.Subgradient
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import CERW.Support.Main.ScaleLimits
import CERW.Support.Norm.DriftSite

/-!
# The contact bound for the centrally excited random walk with a norm

`lem:contact` (Lemma 5.2 of the revised paper, lines 724-864) in its probabilistic closure: for
every `p` there are `C` and `n₀` such that, for `n ≥ n₀`, with probability at least `1 - C n^{-p}`
every contact point `y₀` (`Ψ(y₀) = inf_{y ∉ D_n} Ψ(y)`, `y₀` in the closure of the complement of
`D_n`) has `U_{D_n}(y₀) ≤ C r_n q_n`.

The proof follows the paper. The Dynkin decomposition of the local time at a site for the walk
with a drift field and `eq:cellmodulus` (`ContactModulus`) are in `CERW.Support.Norm.DriftSite`;
the local martingale bound is in `ContactDynkin`. `lem:cell` is proved
without the distributional Laplacian measure (`ContactWeakLap`, `ContactCellTest`,
`ContactBregman`): the sum of `|∇Ψ - ξ(x)|` over the cells is controlled by pairings of `∇Ψ` with
test functions. It gives `eq:pointwise` for a norm (`ContactPointwise`).
`ContactConv` is Newton's theorem for a radial weight
(`eq:radial-convolution`) with the convolution bound, and `ContactShared` is the contact setup
(`eq:bm`). `ContactPlanar` and `ContactHigh` are the deterministic contact arguments (Step 1,
respectively Steps 2-4, of the proof of the lemma), and the final theorem assembles them on the
intersection of the events of `lem:local`, `prop:coarse` and the local martingale bounds.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.ContactShared

open CERW CERW.Generic.Kernel CERW.Support.Statements
open scoped ContDiff

variable {d : ℕ}

/-- (†) The Bregman sum bound: the weighted `L¹` distance between the gradient of a norm on a cell
and a subgradient at the cell's site, summed over the cells of a finite set, is logarithmic. -/
def BregmanSumBound (d : ℕ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
    (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
    ∀ (S : Finset (Site d)) (y : EuclideanSpace ℝ (Fin d)) (R : ℝ), 1 ≤ R →
      (∀ x ∈ S, cell x ⊆ Metric.ball 0 R) → ‖y‖ ≤ 2 * R →
      ∑ x ∈ S, ∫ v in cell x, ‖gradient Ψ v - ξ x‖ * ‖v - y‖ ^ (1 - (d : ℝ)) ≤
        C * Real.log (R + 2)

/-- The convolution bound: the convolution of the potential of a set containing the sublevel ball
`{Ψ < b}`, against a radial weight, at a point `y₀` with `Ψ(y₀) = b`. -/
def ConvBound (d : ℕ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ) : Prop :=
  ∀ χ : ℝ → ℝ, Measurable χ → (∀ s, 0 ≤ χ s) → (∃ M : ℝ, ∀ s, χ s ≤ M) →
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖) →
    ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
    ∀ b : ℝ, 0 < b → {v | Ψ v < b} ⊆ D → ∀ y₀ : EuclideanSpace ℝ (Fin d), Ψ y₀ = b →
      Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * normPotential d ε Ψ D (y₀ - ζ)) ∧
      ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * normPotential d ε Ψ D (y₀ - ζ) ≤
        2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * min b (Ψ ζ)) +
          (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) * normPotential d ε Ψ D y₀

/-- The per-cell bound by a test function. -/
def CellTestBound (d : ℕ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∃ (φ₀ : EuclideanSpace ℝ (Fin d) → ℝ) (A C : ℝ), ContDiff ℝ ∞ φ₀ ∧ HasCompactSupport φ₀ ∧
    (∀ v, 0 ≤ φ₀ v) ∧ 0 < A ∧ (∀ v, A ≤ ‖v‖ → φ₀ v = 0) ∧ 0 ≤ C ∧
    ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ x : Site d, ∫ v in cell x, ‖gradient Ψ v - ξ x‖ ≤
        C * (-∫ v, inner ℝ (gradient Ψ v) (gradient (fun w => φ₀ (w - toSpace x)) v))

end CERW.Support.Norm.ContactShared

namespace CERW.Support.Norm.ContactShared

open LatticeProb CERW CERW.Support.Occupation CERW.Support.Contact

variable {d : ℕ}

/-- If the origin is a departure site, every point outside `D_n` lies at distance at least
`1/2` from the origin. -/
private theorem half_le_norm_of_not_mem_cellSet {X : ℕ → Site d} {n : ℕ} (hn : 1 ≤ n)
    (hX0 : X 0 = 0) {y : EuclideanSpace ℝ (Fin d)} (hy : y ∉ cellSet X n) :
    (1 / 2 : ℝ) ≤ ‖y‖ := by
  by_contra h
  rw [not_le] at h
  have h0 : (0 : Site d) ∈ departureRange X n := by
    rw [mem_departureRange_iff, localTime, Finset.card_pos]
    exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hX0⟩⟩
  have hy_cell : y ∈ cell (0 : Site d) := by
    intro i
    have hi : |y i| < 1 / 2 := by
      have hle : ‖y i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
      rw [Real.norm_eq_abs] at hle
      linarith
    constructor <;> simp only [Pi.zero_apply, Int.cast_zero] <;>
      linarith [(abs_lt.mp hi).1, (abs_lt.mp hi).2]
  exact hy (by rw [cellSet]; exact Set.mem_iUnion₂.mpr ⟨0, h0, hy_cell⟩)

/-- A path with `|X_j| ≤ j` has `H_n ≤ n`. -/
theorem maxRadius_le_nat (X : ℕ → Site d) (n : ℕ) (hXn : ∀ j, euclidNorm (X j) ≤ j) :
    maxRadius X n ≤ n := by
  unfold maxRadius
  refine Finset.sup'_le _ _ fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact (hXn j).trans (by exact_mod_cast hjn)

/-- The contact setup for a norm: the inradius `b` is positive and at most `Λ_Ψ (n + √d)`, the
sublevel set `{Ψ < b}` lies in `D_n`, every contact point lies within `n + √d` of the origin, and
the closure of the cell of some unvisited site `z` contains it. The radius `H_n = maxRadius X n`
replaces `n` in the bounds. -/
theorem contact_setup (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (X : ℕ → Site d) (n : ℕ) (hn : 1 ≤ n) (hX0 : X 0 = 0)
    {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : Ψ y₀ = normInnerRadius Ψ X n)
    (hcl : y₀ ∈ closure (cellSet X n)ᶜ) :
    0 < normInnerRadius Ψ X n ∧ {v | Ψ v < normInnerRadius Ψ X n} ⊆ cellSet X n ∧
      normInnerRadius Ψ X n ≤ normMax Ψ * (maxRadius X n + Real.sqrt d) ∧
      ‖y₀‖ ≤ maxRadius X n + Real.sqrt d ∧
      ∃ z : Site d, localTime X n z = 0 ∧ ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2 ∧
        euclidNorm z ≤ maxRadius X n + 2 * Real.sqrt d := by
  have hd1 : 1 ≤ d := by omega
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  set D := cellSet X n with hD
  set b := normInnerRadius Ψ X n with hb
  have hDball : D ⊆ Metric.ball 0 (maxRadius X n + Real.sqrt d) := cellSet_subset_ball hd1 X n
  have hRpos : 0 < maxRadius X n + Real.sqrt d := by
    have h1 : 0 ≤ maxRadius X n :=
      (euclidNorm_nonneg (X 0)).trans (euclidNorm_le_maxRadius X (Nat.zero_le n))
    have : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
    linarith
  obtain ⟨y₁, hy₁⟩ := (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin d)))
    (r := maxRadius X n + Real.sqrt d)).mpr hRpos.le
  have hy₁norm : ‖y₁‖ = maxRadius X n + Real.sqrt d := by simpa using (mem_sphere_iff_norm.mp hy₁)
  have hy₁c : y₁ ∉ D := by
    intro hyD
    have hmem := hDball hyD
    rw [Metric.mem_ball, dist_zero_right] at hmem
    linarith
  have hne : (Ψ '' Dᶜ).Nonempty := ⟨Ψ y₁, ⟨y₁, hy₁c, rfl⟩⟩
  have hnonneg : ∀ y, 0 ≤ Ψ y := (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1
  have hbdd : BddBelow (Ψ '' Dᶜ) := ⟨0, by rintro _ ⟨y, -, rfl⟩; exact hnonneg y⟩
  obtain ⟨hcpos, hcle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hb_ge : normMin Ψ / 2 ≤ b := by
    refine le_csInf hne ?_
    rintro _ ⟨y, hyc, rfl⟩
    have h1 := half_le_norm_of_not_mem_cellSet hn hX0 hyc
    have h2 := hcle y
    nlinarith
  have hbpos : 0 < b := lt_of_lt_of_le (by linarith) hb_ge
  have hball : {v | Ψ v < b} ⊆ D := by
    intro v hv
    by_contra hvD
    exact absurd (csInf_le hbdd ⟨v, hvD, rfl⟩) (not_le.mpr hv)
  have hb_le : b ≤ normMax Ψ * (maxRadius X n + Real.sqrt d) := by
    calc b ≤ Ψ y₁ := csInf_le hbdd ⟨y₁, hy₁c, rfl⟩
      _ ≤ normMax Ψ * ‖y₁‖ := CERW.Generic.Norm.le_normMax_mul hΨ y₁
      _ = normMax Ψ * (maxRadius X n + Real.sqrt d) := by rw [hy₁norm]
  have hy₀norm : ‖y₀‖ ≤ maxRadius X n + Real.sqrt d := by
    by_contra hcon
    rw [not_le] at hcon
    set R : ℝ := maxRadius X n + Real.sqrt d with hR
    have hy₀pos : 0 < ‖y₀‖ := lt_trans hRpos hcon
    set t : ℝ := (R + ‖y₀‖) / (2 * ‖y₀‖) with ht
    have ht1 : t < 1 := by
      rw [ht, div_lt_one (by positivity)]
      linarith
    have ht0 : 0 < t := by
      rw [ht]
      positivity
    have hΨt : Ψ (t • y₀) < b := by
      rw [hΨ.smul, abs_of_pos ht0, hy₀]
      nlinarith
    have hmem : t • y₀ ∈ D := hball hΨt
    have hlt := hDball hmem
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hlt
    have : t * ‖y₀‖ = (R + ‖y₀‖) / 2 := by
      rw [ht]
      field_simp
    linarith
  obtain ⟨z, hzA, hzcl⟩ := exists_unvisited_mem_closure_cell X n hcl
  have hzy := norm_sub_toSpace_le_of_mem_closure_cell hzcl
  refine ⟨hbpos, hball, hb_le, hy₀norm, z, ?_, ?_, ?_⟩
  · rwa [mem_departureRange_iff, not_lt, Nat.le_zero] at hzA
  · rw [norm_sub_rev]
    exact hzy
  · rw [← norm_toSpace]
    calc ‖toSpace z‖ ≤ ‖y₀‖ + ‖toSpace z - y₀‖ := norm_le_norm_add_norm_sub' (toSpace z) y₀
      _ ≤ (maxRadius X n + Real.sqrt d) + Real.sqrt d / 2 := by
          rw [norm_sub_rev] at hzy
          linarith
      _ ≤ maxRadius X n + 2 * Real.sqrt d := by linarith [Real.sqrt_nonneg (d : ℝ)]

end CERW.Support.Norm.ContactShared

namespace CERW.Support.Norm.ContactWeakLap

open CERW
open scoped ContDiff

/-- The midpoint inequality of a norm: `2 Ψ v ≤ Ψ (v + a) + Ψ (v - a)`. -/
private lemma two_mul_le_add_sub {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (v a : EuclideanSpace ℝ (Fin d)) : 2 * Ψ v ≤ Ψ (v + a) + Ψ (v - a) := by
  have h1 : (2 : ℝ) • v = (v + a) + (v - a) := by module
  have h := hΨ.add_le (v + a) (v - a)
  rw [← h1, hΨ.smul 2 v, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  exact h

/-- A norm is Lipschitz with constant `Σ_i Ψ(e_i)`. -/
private lemma lipschitzWith_of_isNorm {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) : LipschitzWith (Real.toNNReal (∑ i, Ψ (coordVec i))) Ψ := by
  apply LipschitzWith.of_dist_le'
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  exact CERW.Generic.Norm.abs_sub_le_sum_mul hΨ x y

/-- The difference quotient of a Lipschitz function along `e` is bounded by `C ‖e‖`. -/
private lemma abs_quotient_le {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (e v : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 < t) :
    |t⁻¹ * (f (v + t • e) - f v)| ≤ C * ‖e‖ := by
  have h := hf.dist_le_mul (v + t • e) v
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht] at h
  rw [abs_mul, abs_inv, abs_of_pos ht, inv_mul_le_iff₀ ht]
  calc |f (v + t • e) - f v| ≤ C * (t * ‖e‖) := h
    _ = t * (C * ‖e‖) := by ring

/-- Where `f` is differentiable, the right difference quotient along `e` converges to
`fderiv f v e`. -/
private lemma tendsto_quotient {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {v : EuclideanSpace ℝ (Fin d)} (hv : DifferentiableAt ℝ f v) (e : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun t : ℝ => t⁻¹ * (f (v + t • e) - f v)) (𝓝[>] 0) (𝓝 (fderiv ℝ f v e)) := by
  have hpath : HasDerivAt (fun t : ℝ => v + t • e) e 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const e).const_add v
  have hd : HasDerivAt (fun t : ℝ => f (v + t • e)) (fderiv ℝ f v e) 0 :=
    hv.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp)
  simpa using hd.tendsto_slope_zero_right

/-- A continuous function times a continuous compactly supported function is integrable. -/
private lemma integrable_mul_of_hasCompactSupport {d : ℕ}
    {g ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) : Integrable (fun v => g v * ψ v) := by
  refine Continuous.integrable_of_hasCompactSupport (hg.mul hψ) ?_
  exact hc.mul_left

/-- Translating a compactly supported function keeps it compactly supported. -/
private lemma hasCompactSupport_shift {d : ℕ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : HasCompactSupport ψ) (a : EuclideanSpace ℝ (Fin d)) :
    HasCompactSupport (fun v => ψ (v + a)) :=
  hc.comp_homeomorph (Homeomorph.addRight a)

/-- The integral of the product of the increments of a norm `Ψ` and of a nonnegative compactly
supported function `φ` along a translation `a` is nonpositive. -/
private lemma integral_increment_mul_nonpos {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) (hcont : Continuous Ψ) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (h0 : ∀ v, 0 ≤ φ v)
    (a : EuclideanSpace ℝ (Fin d)) :
    ∫ v, (Ψ (v + a) - Ψ v) * (φ (v + a) - φ v) ≤ 0 := by
  have hφa : Continuous (fun v => φ (v + a)) := hφ.comp (continuous_id.add continuous_const)
  have hΨa : Continuous (fun v => Ψ (v + a)) := hcont.comp (continuous_id.add continuous_const)
  have hΨb : Continuous (fun v => Ψ (v - a)) := hcont.comp (continuous_id.sub continuous_const)
  have iA : Integrable (fun v => Ψ (v + a) * φ (v + a)) :=
    integrable_mul_of_hasCompactSupport hΨa hφa (hasCompactSupport_shift hc a)
  have iB : Integrable (fun v => Ψ (v + a) * φ v) :=
    integrable_mul_of_hasCompactSupport hΨa hφ hc
  have iC : Integrable (fun v => Ψ v * φ (v + a)) :=
    integrable_mul_of_hasCompactSupport hcont hφa (hasCompactSupport_shift hc a)
  have iD : Integrable (fun v => Ψ v * φ v) := integrable_mul_of_hasCompactSupport hcont hφ hc
  have iE : Integrable (fun v => Ψ (v - a) * φ v) :=
    integrable_mul_of_hasCompactSupport hΨb hφ hc
  have hA : ∫ v, Ψ (v + a) * φ (v + a) = ∫ v, Ψ v * φ v :=
    integral_add_right_eq_self (μ := volume) (fun v => Ψ v * φ v) a
  have hC : ∫ v, Ψ v * φ (v + a) = ∫ v, Ψ (v - a) * φ v := by
    have h := integral_add_right_eq_self (μ := volume) (fun v => Ψ (v - a) * φ v) a
    simpa using h
  have iAB : Integrable (fun v => Ψ (v + a) * φ (v + a) - Ψ (v + a) * φ v) := iA.sub iB
  have iABC : Integrable (fun v => Ψ (v + a) * φ (v + a) - Ψ (v + a) * φ v - Ψ v * φ (v + a)) :=
    iAB.sub iC
  have iD2 : Integrable (fun v => 2 * (Ψ v * φ v)) := iD.const_mul 2
  have iD2B : Integrable (fun v => 2 * (Ψ v * φ v) - Ψ (v + a) * φ v) := iD2.sub iB
  have hL : ∫ v, (Ψ (v + a) - Ψ v) * (φ (v + a) - φ v) =
      (∫ v, Ψ (v + a) * φ (v + a)) - (∫ v, Ψ (v + a) * φ v) - (∫ v, Ψ v * φ (v + a))
        + ∫ v, Ψ v * φ v := by
    have hfun : (fun v => (Ψ (v + a) - Ψ v) * (φ (v + a) - φ v)) =
        fun v => Ψ (v + a) * φ (v + a) - Ψ (v + a) * φ v - Ψ v * φ (v + a) + Ψ v * φ v := by
      funext v
      ring
    rw [hfun, integral_add iABC iD, integral_sub iAB iC, integral_sub iA iB]
  have hR : ∫ v, (2 * Ψ v - Ψ (v + a) - Ψ (v - a)) * φ v =
      2 * (∫ v, Ψ v * φ v) - (∫ v, Ψ (v + a) * φ v) - ∫ v, Ψ (v - a) * φ v := by
    have hfun : (fun v => (2 * Ψ v - Ψ (v + a) - Ψ (v - a)) * φ v) =
        fun v => 2 * (Ψ v * φ v) - Ψ (v + a) * φ v - Ψ (v - a) * φ v := by
      funext v
      ring
    rw [hfun, integral_sub iD2B iE, integral_sub iD2 iB, integral_const_mul]
  have hnonpos : ∫ v, (2 * Ψ v - Ψ (v + a) - Ψ (v - a)) * φ v ≤ 0 := by
    refine integral_nonpos fun v => ?_
    have h := two_mul_le_add_sub hΨ v a
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (h0 v)
  rw [hL, hA, hC]
  linarith

/-- Outside a large ball the difference quotient of a compactly supported function vanishes. -/
private lemma quotient_eq_zero_of_notMem {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ} {R : ℝ}
    (hR : tsupport φ ⊆ Metric.closedBall 0 R) (e v : EuclideanSpace ℝ (Fin d)) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hv : v ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d))
      (R + ‖e‖)) : t⁻¹ * (φ (v + t • e) - φ v) = 0 := by
  have hv0 : φ v = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun hmem => hv ?_
    exact Metric.closedBall_subset_closedBall (by linarith [norm_nonneg e]) (hR hmem)
  have hv1 : φ (v + t • e) = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun hmem => hv ?_
    have h1 : ‖v + t • e‖ ≤ R := by simpa using hR hmem
    have h2 : ‖t • e‖ ≤ ‖e‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      exact mul_le_of_le_one_left (norm_nonneg e) ht1
    have h3 : ‖v‖ ≤ ‖v + t • e‖ + ‖t • e‖ := by
      calc ‖v‖ = ‖(v + t • e) - t • e‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖v + t • e‖ + ‖t • e‖ := norm_sub_le _ _
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  rw [hv0, hv1]
  simp

/-- For a norm `Ψ` and a smooth compactly supported `φ ≥ 0`, the weak directional second
derivative `∫ ∂_eΨ ∂_eφ` is nonpositive. -/
private lemma integral_fderiv_mul_nonpos {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (h0 : ∀ v, 0 ≤ φ v) (e : EuclideanSpace ℝ (Fin d)) :
    ∫ v, fderiv ℝ Ψ v e * fderiv ℝ φ v e ≤ 0 := by
  have hlipΨ := lipschitzWith_of_isNorm hΨ
  have hcΨ : Continuous Ψ := hlipΨ.continuous
  have hcφ : Continuous φ := hφ.continuous
  obtain ⟨C₂, hlipφ⟩ := hφ.lipschitzWith_of_hasCompactSupport hc (by simp)
  obtain ⟨R, hR⟩ := (show IsCompact (tsupport φ) from hc).isBounded.subset_closedBall
    (0 : EuclideanSpace ℝ (Fin d))
  have hKfin : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + ‖e‖)) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  let F : ℝ → EuclideanSpace ℝ (Fin d) → ℝ := fun t v =>
    (t⁻¹ * (Ψ (v + t • e) - Ψ v)) * (t⁻¹ * (φ (v + t • e) - φ v))
  let bound : EuclideanSpace ℝ (Fin d) → ℝ :=
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + ‖e‖)).indicator
      (fun _ => ((Real.toNNReal (∑ i, Ψ (coordVec i)) : ℝ) * ‖e‖) * ((C₂ : ℝ) * ‖e‖))
  have hbound_int : Integrable bound :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hKfin)
  have hmeas : ∀ t, AEStronglyMeasurable (F t) volume := fun t => by
    have : Continuous (F t) := by fun_prop
    exact this.aestronglyMeasurable
  have hdom : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      ‖F t v‖ ≤ bound v := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    refine Eventually.of_forall fun v => ?_
    by_cases hv : v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + ‖e‖)
    · rw [show bound v = _ from Set.indicator_of_mem hv _]
      simp only [F]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (abs_quotient_le hlipΨ e v ht.1) (abs_quotient_le hlipφ e v ht.1)
        (abs_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg e))
    · have h := quotient_eq_zero_of_notMem hR e v ht.1 ht.2.le hv
      simp [bound, Set.indicator_of_notMem hv, F, h]
  have hlim : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      Tendsto (fun t => F t v) (𝓝[>] (0 : ℝ)) (𝓝 (fderiv ℝ Ψ v e * fderiv ℝ φ v e)) := by
    filter_upwards [CERW.Generic.Norm.ae_differentiableAt hΨ] with v hv
    exact (tendsto_quotient hv e).mul (tendsto_quotient ((hφ.differentiable (by simp)) v) e)
  have hT := tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall hmeas) hdom hbound_int hlim
  refine le_of_tendsto hT (Eventually.of_forall fun t => ?_)
  have hfun : F t = fun v =>
      (t⁻¹ * t⁻¹) * ((Ψ (v + t • e) - Ψ v) * (φ (v + t • e) - φ v)) := by
    funext v
    simp only [F]
    ring
  rw [hfun, integral_const_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _)
    (integral_increment_mul_nonpos hΨ hcΨ hcφ hc h0 (t • e))

/-- The product of the directional derivatives of a norm and of a smooth compactly supported
function is integrable. -/
private lemma integrable_fderiv_mul {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (e : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun v => fderiv ℝ Ψ v e * fderiv ℝ φ v e) := by
  have hlip := lipschitzWith_of_isNorm hΨ
  have hcont : Continuous (fun v => fderiv ℝ φ v e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsupp : HasCompactSupport (fun v => fderiv ℝ φ v e) :=
    (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => L e)
      (by simp)
  refine Integrable.bdd_mul (c := ((Real.toNNReal (∑ i, Ψ (coordVec i)) : ℝ) * ‖e‖))
    (hcont.integrable_of_hasCompactSupport hsupp)
    (measurable_fderiv_apply_const ℝ Ψ e).aestronglyMeasurable ?_
  refine Eventually.of_forall fun v => ?_
  calc ‖fderiv ℝ Ψ v e‖ ≤ ‖fderiv ℝ Ψ v‖ * ‖e‖ := (fderiv ℝ Ψ v).le_opNorm e
    _ ≤ (Real.toNNReal (∑ i, Ψ (coordVec i)) : ℝ) * ‖e‖ :=
        mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hlip) (norm_nonneg e)

/-- The pairing of the gradient of `f` with a vector is the Fréchet derivative applied to it. -/
private lemma inner_gradient_eq_fderiv {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (v w : EuclideanSpace ℝ (Fin d)) : inner ℝ (gradient f v) w = fderiv ℝ f v w := by
  rw [← toDual_gradient]
  rfl

/-- The pairing of two gradients is the sum of the products of the partial derivatives. -/
private lemma inner_gradient_eq_sum {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : inner ℝ (gradient f v) (gradient g v) =
      ∑ i, fderiv ℝ f v (coordVec i) * fderiv ℝ g v (coordVec i) := by
  rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_inner_mul_inner (gradient f v) (gradient g v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hb : (EuclideanSpace.basisFun (Fin d) ℝ) i = coordVec i := by simp [coordVec]
  rw [hb, real_inner_comm (gradient g v) (coordVec i), inner_gradient_eq_fderiv,
    inner_gradient_eq_fderiv]

/-- The weak Laplacian of a norm is nonnegative: `∫ ⟪∇Ψ, ∇φ⟫ ≤ 0` for every smooth compactly
supported `φ ≥ 0`. -/
theorem inner_gradient_integral_nonpos {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (h0 : ∀ v, 0 ≤ φ v) :
    ∫ v, inner ℝ (gradient Ψ v) (gradient φ v) ≤ 0 := by
  simp_rw [inner_gradient_eq_sum]
  rw [integral_finsetSum _ fun i _ => integrable_fderiv_mul hΨ hφ hc (coordVec i)]
  exact Finset.sum_nonpos fun i _ => integral_fderiv_mul_nonpos hΨ hφ hc h0 (coordVec i)

end CERW.Support.Norm.ContactWeakLap

namespace CERW.Support.Norm.ContactCellTest

open scoped ContDiff

/-- A smooth radial cut-off profile: values in `[0, 1]`, equal to `1` up to `a ^ 2` and
vanishing from `r ^ 2` on. -/
private structure Cutoff (a r : ℝ) (b : ℝ → ℝ) : Prop where
  /-- The profile is smooth. -/
  smooth : ContDiff ℝ ∞ b
  /-- The profile is nonnegative. -/
  nonneg : ∀ s, 0 ≤ b s
  /-- The profile is at most one. -/
  le_one : ∀ s, b s ≤ 1
  /-- The profile equals one up to `a ^ 2`. -/
  eq_one : ∀ s, s ≤ a ^ 2 → b s = 1
  /-- The profile vanishes from `r ^ 2` on. -/
  eq_zero : ∀ s, r ^ 2 ≤ s → b s = 0

/-- For `0 ≤ a < r` there is a smooth cut-off profile. -/
private lemma exists_cutoff {a r : ℝ} (ha : 0 ≤ a) (h : a < r) : ∃ b, Cutoff a r b := by
  have hpos : 0 < r ^ 2 - a ^ 2 := by nlinarith
  have hsm : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition ((r ^ 2 - s) / (r ^ 2 - a ^ 2))) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  refine ⟨fun s => Real.smoothTransition ((r ^ 2 - s) / (r ^ 2 - a ^ 2)), hsm, ?_, ?_, ?_, ?_⟩
  · intro s
    exact Real.smoothTransition.nonneg _
  · intro s
    exact Real.smoothTransition.le_one _
  · intro s hs
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hpos]
    linarith
  · intro s hs
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le

/-- The primitive `E(s) = ∫_0^s b`. -/
private noncomputable def prim (b : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, b t

/-- The primitive of a continuous function has the function as derivative. -/
private lemma hasDerivAt_prim {b : ℝ → ℝ} (hb : Continuous b) (s : ℝ) :
    HasDerivAt (prim b) (b s) s :=
  (hb.integral_hasStrictDerivAt 0 s).hasDerivAt

/-- The primitive of a smooth function is smooth. -/
private lemma contDiff_prim {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (prim b) := by
  rw [contDiff_infty_iff_deriv]
  have hd : deriv (prim b) = b := funext fun s => (hasDerivAt_prim hb.continuous s).deriv
  exact ⟨fun s => (hasDerivAt_prim hb.continuous s).differentiableAt, by rw [hd]; exact hb⟩

variable {d : ℕ}

/-- The radial test function `φ(v) = (E(r²) - E(|v - x|²)) / 2`. -/
private noncomputable def testFn (b : ℝ → ℝ) (r : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2) * (prim b (r ^ 2) - prim b (‖v - x‖ ^ 2))

/-- The derivative of the radial test function is `-b(|v - x|²) (v - x)`. -/
private lemma hasFDerivAt_testFn {b : ℝ → ℝ} (hb : Continuous b) (r : ℝ)
    (x v : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (testFn b r x) ((-b (‖v - x‖ ^ 2)) • innerSL ℝ (v - x)) v := by
  have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin d) => ‖w - x‖ ^ 2)
      (2 • innerSL ℝ (v - x)) v := by
    have := (hasStrictFDerivAt_norm_sq (v - x)).hasFDerivAt.comp v
      ((hasFDerivAt_id v).sub_const x)
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  have h2 := (hasDerivAt_prim hb (‖v - x‖ ^ 2)).comp_hasFDerivAt v h1
  have h3 := ((hasFDerivAt_const (prim b (r ^ 2)) v).sub h2).const_mul (1 / 2 : ℝ)
  refine HasFDerivAt.congr_fderiv (h3 : HasFDerivAt (testFn b r x) _ v) ?_
  ext w
  simp
  ring

/-- The gradient of the radial test function is `-b(|v - x|²) (v - x)`. -/
private lemma gradient_testFn {b : ℝ → ℝ} (hb : Continuous b) (r : ℝ)
    (x v : EuclideanSpace ℝ (Fin d)) :
    gradient (testFn b r x) v = (-b (‖v - x‖ ^ 2)) • (v - x) := by
  have h := hasFDerivAt_testFn hb r x v
  have hg : HasGradientAt (testFn b r x) ((-b (‖v - x‖ ^ 2)) • (v - x)) v := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have he : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)))
        ((-b (‖v - x‖ ^ 2)) • (v - x)) = (-b (‖v - x‖ ^ 2)) • innerSL ℝ (v - x) := by
      ext w
      simp [InnerProductSpace.toDual_apply_apply]
    rw [he]
    exact h
  exact hg.gradient

/-- Beyond `r ^ 2` the primitive of a cut-off profile is constant. -/
private lemma prim_eq_of_le {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) {s : ℝ} (hs : r ^ 2 ≤ s) :
    prim b s = prim b (r ^ 2) := by
  have hint : ∀ t u : ℝ, IntervalIntegrable b volume t u := fun t u =>
    (hb.smooth.continuous.intervalIntegrable t u)
  have h := intervalIntegral.integral_interval_sub_left (hint 0 s) (hint 0 (r ^ 2))
  have h0 : ∫ t in (r ^ 2)..s, b t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le hs] at ht
      exact hb.eq_zero t ht.1
  rw [h0] at h
  unfold prim
  linarith

/-- The primitive of a cut-off profile drops by between `0` and `r ^ 2` from any `s ≥ 0` to
`r ^ 2`. -/
private lemma prim_sub_bounds {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ prim b (r ^ 2) - prim b s ∧ prim b (r ^ 2) - prim b s ≤ r ^ 2 := by
  rcases le_total s (r ^ 2) with h | h
  · have hint : ∀ t u : ℝ, IntervalIntegrable b volume t u := fun t u =>
      (hb.smooth.continuous.intervalIntegrable t u)
    have hsub := intervalIntegral.integral_interval_sub_left (hint 0 (r ^ 2)) (hint 0 s)
    have hrs : prim b (r ^ 2) - prim b s = ∫ t in s..(r ^ 2), b t := hsub
    rw [hrs]
    refine ⟨intervalIntegral.integral_nonneg h fun t _ => hb.nonneg t, ?_⟩
    calc ∫ t in s..(r ^ 2), b t ≤ ∫ _ in s..(r ^ 2), (1 : ℝ) :=
          intervalIntegral.integral_mono_on h (hint _ _) (by simp)
            fun t _ => hb.le_one t
      _ = r ^ 2 - s := by simp
      _ ≤ r ^ 2 := by linarith
  · rw [prim_eq_of_le hb h]
    have : 0 ≤ r ^ 2 := sq_nonneg r
    constructor <;> simp [this]

/-- The radial test function is smooth. -/
private lemma contDiff_testFn {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ContDiff ℝ ∞ (testFn b r x) := by
  unfold testFn
  have h1 : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin d) => ‖v - x‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  exact contDiff_const.mul (contDiff_const.sub ((contDiff_prim hb).comp h1))

/-- The radial test function vanishes outside the ball of radius `r`. -/
private lemma testFn_eq_zero {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b)
    {x v : EuclideanSpace ℝ (Fin d)} (hv : r ≤ ‖v - x‖) (hr : 0 ≤ r) : testFn b r x v = 0 := by
  unfold testFn
  have : r ^ 2 ≤ ‖v - x‖ ^ 2 := by nlinarith
  rw [prim_eq_of_le hb this]
  ring

/-- The radial test function is nonnegative. -/
private lemma testFn_nonneg {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b)
    (x v : EuclideanSpace ℝ (Fin d)) : 0 ≤ testFn b r x v := by
  have h := prim_sub_bounds hb (sq_nonneg ‖v - x‖)
  unfold testFn
  nlinarith [h.1]

/-- The radial test function has compact support. -/
private lemma hasCompactSupport_testFn {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) (hr : 0 ≤ r)
    (x : EuclideanSpace ℝ (Fin d)) : HasCompactSupport (testFn b r x) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x r) ?_
  intro v hv
  by_contra hnot
  rw [Metric.mem_closedBall, dist_eq_norm] at hnot
  exact hv (testFn_eq_zero hb (le_of_lt (not_le.mp hnot)) hr)

/-- The excess `Ψ(v) - Ψ(x) - ξ · (v - x)` of `Ψ` over its tangent plane at `x` with slope
`ξ`. -/
private noncomputable def excess (Ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (x ξ v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Ψ v - Ψ x - inner ℝ ξ (v - x)

/-- The excess over a tangent plane of a subgradient is nonnegative. -/
private lemma excess_nonneg {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} {x ξ : EuclideanSpace ℝ (Fin d)}
    (hξ : CERW.IsSubgradient Ψ x ξ) (v : EuclideanSpace ℝ (Fin d)) : 0 ≤ excess Ψ x ξ v := by
  have h := hξ v
  unfold excess
  linarith

/-- The excess is continuous when `Ψ` is. -/
private lemma continuous_excess {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : Continuous Ψ)
    (x ξ : EuclideanSpace ℝ (Fin d)) : Continuous (excess Ψ x ξ) := by
  unfold excess
  fun_prop

/-- The Euclidean norm is at most the sum of the absolute values of the coordinates. -/
private lemma norm_le_sum_abs (w : EuclideanSpace ℝ (Fin d)) : ‖w‖ ≤ ∑ i, |w i| := by
  have hw : ∑ i, w i • CERW.coordVec i = w := by
    simpa [CERW.coordVec] using (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr w
  calc ‖w‖ = ‖∑ i, w i • CERW.coordVec i‖ := by rw [hw]
    _ ≤ ∑ i, ‖w i • CERW.coordVec i‖ := norm_sum_le _ _
    _ = ∑ i, |w i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [CERW.coordVec, norm_smul, PiLp.norm_single]

/-- At a point of differentiability, the gradient of a norm differs from a subgradient at `x` by
at most the sum of the excesses at the `2d` neighbours of the point. -/
private lemma norm_gradient_sub_le_sum {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {x ξ v : EuclideanSpace ℝ (Fin d)} (hξ : CERW.IsSubgradient Ψ x ξ)
    (hv : DifferentiableAt ℝ Ψ v) :
    ‖gradient Ψ v - ξ‖ ≤ ∑ i : Fin d, (excess Ψ x ξ (v + CERW.coordVec i) +
      excess Ψ x ξ (v - CERW.coordVec i)) := by
  have hsub := CERW.Generic.Norm.gradient_isSubgradient hΨ hv
  have hexc := excess_nonneg hξ v
  have key : ∀ (i : Fin d) (σ : ℝ),
      σ * (gradient Ψ v - ξ) i ≤ excess Ψ x ξ (v + σ • CERW.coordVec i) := by
    intro i σ
    have h1 := hsub (v + σ • CERW.coordVec i)
    have hcoord : inner ℝ (gradient Ψ v - ξ) (CERW.coordVec i) = (gradient Ψ v - ξ) i := by
      simp [CERW.coordVec, EuclideanSpace.inner_single_right]
    have h2 : inner ℝ (gradient Ψ v) (σ • CERW.coordVec i) - inner ℝ ξ (σ • CERW.coordVec i) =
        σ * (gradient Ψ v - ξ) i := by
      rw [← inner_sub_left, real_inner_smul_right, hcoord]
    unfold excess at hexc ⊢
    have h3 : inner ℝ ξ (v + σ • CERW.coordVec i - x) =
        inner ℝ ξ (v - x) + inner ℝ ξ (σ • CERW.coordVec i) := by
      rw [← inner_add_right]
      congr 1
      abel
    have h4 : v + σ • CERW.coordVec i - v = σ • CERW.coordVec i := by abel
    rw [h4] at h1
    rw [h3]
    linarith
  refine (norm_le_sum_abs _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hp := key i 1
  have hn := key i (-1)
  have hp0 := excess_nonneg hξ (v + CERW.coordVec i)
  have hn0 := excess_nonneg hξ (v - CERW.coordVec i)
  simp only [one_smul, neg_smul, one_mul, neg_one_mul, ← sub_eq_add_neg] at hp hn
  rw [abs_le]
  constructor <;> linarith

/-- A continuous function is integrable on a bounded set. -/
private lemma integrableOn_of_isBounded {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f)
    {S : Set (EuclideanSpace ℝ (Fin d))} (hS : Bornology.IsBounded S) :
    IntegrableOn f S volume :=
  (hf.continuousOn.integrableOn_compact hS.isCompact_closure).mono_set subset_closure

/-- For a nonnegative continuous `f` and bounded measurable sets with `S + e ⊆ T`,
`∫_S f(v + e) dv ≤ ∫_T f`. -/
private lemma setIntegral_add_le {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f)
    (hf0 : ∀ v, 0 ≤ f v) {S T : Set (EuclideanSpace ℝ (Fin d))} (e : EuclideanSpace ℝ (Fin d))
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hSb : Bornology.IsBounded S)
    (hTb : Bornology.IsBounded T) (hsub : ∀ v ∈ S, v + e ∈ T) :
    ∫ v in S, f (v + e) ≤ ∫ v in T, f v := by
  rw [← integral_indicator hS, ← integral_indicator hT]
  have hTint : Integrable (T.indicator f) volume :=
    (integrable_indicator_iff hT).2 (integrableOn_of_isBounded hf hTb)
  have hSint : Integrable (S.indicator fun v => f (v + e)) volume :=
    (integrable_indicator_iff hS).2
      (integrableOn_of_isBounded (hf.comp (continuous_id.add_const e)) hSb)
  calc ∫ v, S.indicator (fun v => f (v + e)) v ≤ ∫ v, T.indicator f (v + e) := by
        refine integral_mono hSint (hTint.comp_add_right e) fun v => ?_
        by_cases hv : v ∈ S
        · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (hsub v hv)]
        · rw [Set.indicator_of_notMem hv]
          exact Set.indicator_nonneg (fun w _ => hf0 w) _
    _ = ∫ v, T.indicator f v := integral_add_right_eq_self (T.indicator f) e

/-- The cell `C_x` is bounded. -/
private lemma isBounded_cell (x : Site d) : Bornology.IsBounded (CERW.cell x) := by
  refine (Metric.isBounded_closedBall (x := CERW.toSpace x) (r := Real.sqrt d / 2)).subset ?_
  intro v hv
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hv

/-- A unit translate of a point of the cell `C_x` lies in the ball of radius `2 √d` about `x`. -/
private lemma add_mem_ball_of_mem_cell (hd : 1 ≤ d) (x : Site d)
    {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ CERW.cell x) : v + e ∈ Metric.ball (CERW.toSpace x) (2 * Real.sqrt d) := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hd
  rw [Metric.mem_ball, dist_eq_norm]
  have h1 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hv
  have h2 : ‖v + e - CERW.toSpace x‖ ≤ ‖v - CERW.toSpace x‖ + ‖e‖ := by
    calc ‖v + e - CERW.toSpace x‖ = ‖(v - CERW.toSpace x) + e‖ := by
          congr 1
          abel
      _ ≤ ‖v - CERW.toSpace x‖ + ‖e‖ := norm_add_le _ _
  rw [he] at h2
  linarith

/-- The integral of the gradient's distance to a subgradient over a cell is at most `2d` times
the integral of the excess over the ball of radius `2 √d` about the site. -/
private lemma cell_integral_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    (hd : 1 ≤ d) {ξ : EuclideanSpace ℝ (Fin d)} (x : Site d)
    (hξ : CERW.IsSubgradient Ψ (CERW.toSpace x) ξ) :
    ∫ v in CERW.cell x, ‖gradient Ψ v - ξ‖ ≤
      2 * d * ∫ v in Metric.ball (CERW.toSpace x) (2 * Real.sqrt d),
        excess Ψ (CERW.toSpace x) ξ v := by
  set f : EuclideanSpace ℝ (Fin d) → ℝ := excess Ψ (CERW.toSpace x) ξ with hf
  have hfc : Continuous f := continuous_excess (CERW.Generic.Norm.norm_continuous hΨ) _ _
  have hf0 : ∀ v, 0 ≤ f v := excess_nonneg hξ
  have hS := CERW.Support.Occupation.measurableSet_cell x
  have hSb := isBounded_cell x
  have hTb : Bornology.IsBounded
      (Metric.ball (CERW.toSpace x) (2 * Real.sqrt d)) := Metric.isBounded_ball
  have hnear : ∀ (e : EuclideanSpace ℝ (Fin d)), ‖e‖ = 1 → ∀ v ∈ CERW.cell x,
      v + e ∈ Metric.ball (CERW.toSpace x) (2 * Real.sqrt d) :=
    fun e he v hv => add_mem_ball_of_mem_cell hd x he hv
  have hone : ∀ i : Fin d, ‖CERW.coordVec (d := d) i‖ = 1 := by
    intro i
    simp [CERW.coordVec, PiLp.norm_single]
  have hplus : ∀ i : Fin d, ∫ v in CERW.cell x, f (v + CERW.coordVec i) ≤
      ∫ v in Metric.ball (CERW.toSpace x) (2 * Real.sqrt d), f v := fun i =>
    setIntegral_add_le hfc hf0 _ hS Metric.isOpen_ball.measurableSet hSb hTb
      (hnear _ (hone i))
  have hminus : ∀ i : Fin d, ∫ v in CERW.cell x, f (v - CERW.coordVec i) ≤
      ∫ v in Metric.ball (CERW.toSpace x) (2 * Real.sqrt d), f v := by
    intro i
    have := setIntegral_add_le hfc hf0 (-CERW.coordVec i) hS Metric.isOpen_ball.measurableSet hSb
      hTb (hnear _ (by rw [norm_neg]; exact hone i))
    simpa [sub_eq_add_neg] using this
  have hint : ∀ e : EuclideanSpace ℝ (Fin d), IntegrableOn (fun v => f (v + e))
      (CERW.cell x) volume := fun e =>
    integrableOn_of_isBounded (hfc.comp (continuous_id.add_const e)) hSb
  have hint' : ∀ e : EuclideanSpace ℝ (Fin d), IntegrableOn (fun v => f (v - e))
      (CERW.cell x) volume := fun e =>
    integrableOn_of_isBounded (hfc.comp (continuous_id.sub continuous_const)) hSb
  have hae : ∀ᵐ v ∂(volume.restrict (CERW.cell x)), ‖gradient Ψ v - ξ‖ ≤
      ∑ i : Fin d, (f (v + CERW.coordVec i) + f (v - CERW.coordVec i)) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [CERW.Generic.Norm.ae_differentiableAt hΨ] with v hv
    exact norm_gradient_sub_le_sum hΨ hξ hv
  have hsumint : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      IntegrableOn (fun v => f (v + CERW.coordVec i) + f (v - CERW.coordVec i))
        (CERW.cell x) volume := fun i _ => (hint _).add (hint' _)
  calc ∫ v in CERW.cell x, ‖gradient Ψ v - ξ‖
      ≤ ∫ v in CERW.cell x, ∑ i : Fin d, (f (v + CERW.coordVec i) + f (v - CERW.coordVec i)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _)
          (integrable_finsetSum _ hsumint) hae
    _ = ∑ i : Fin d, ((∫ v in CERW.cell x, f (v + CERW.coordVec i)) +
          ∫ v in CERW.cell x, f (v - CERW.coordVec i)) := by
        refine (integral_finsetSum Finset.univ hsumint).trans ?_
        exact Finset.sum_congr rfl fun i _ => integral_add (hint _) (hint' _)
    _ ≤ ∑ _i : Fin d, (2 * ∫ v in Metric.ball (CERW.toSpace x) (2 * Real.sqrt d), f v) := by
        refine Finset.sum_le_sum fun i _ => ?_
        linarith [hplus i, hminus i]
    _ = 2 * d * ∫ v in Metric.ball (CERW.toSpace x) (2 * Real.sqrt d), f v := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The gradient of a function on `ℝ^d` is measurable. -/
private lemma measurable_gradient (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measurable (gradient Ψ) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ Ψ)

/-- A norm is Lipschitz, with constant the positive part of `Σ_i Ψ(e_i)`. -/
private lemma lipschitzWith_isNorm {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ) :
    LipschitzWith (Real.toNNReal (∑ i, Ψ (CERW.coordVec i))) Ψ := by
  apply LipschitzWith.of_dist_le'
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  exact CERW.Generic.Norm.abs_sub_le_sum_mul hΨ x y

/-- The gradient of a norm has norm at most the Lipschitz constant of the norm. -/
private lemma norm_gradient_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    (v : EuclideanSpace ℝ (Fin d)) :
    ‖gradient Ψ v‖ ≤ (Real.toNNReal (∑ i, Ψ (CERW.coordVec i)) : ℝ) := by
  have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := v) (lipschitzWith_isNorm hΨ)
  have h' : ‖gradient Ψ v‖ = ‖fderiv ℝ Ψ v‖ := by
    unfold gradient
    exact LinearIsometryEquiv.norm_map _ _
  rwa [h']

/-- A continuous function vanishing outside a ball is integrable. -/
private lemma integrable_of_zero_outside {r : ℝ} {c : EuclideanSpace ℝ (Fin d)}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) (h : ∀ u, r < ‖u - c‖ → f u = 0) :
    Integrable f volume := by
  refine hf.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r) ?_
  intro u hu
  by_contra hnot
  rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hnot
  exact hu (h u hnot)

/-- The profile of the squared distance to a point, times a linear function of the displacement,
integrates to zero, by oddness about the point. -/
private lemma integral_profile_inner (b : ℝ → ℝ) (x ξ : EuclideanSpace ℝ (Fin d)) :
    ∫ v, b (‖v - x‖ ^ 2) * inner ℝ ξ (v - x) = 0 := by
  rw [← integral_add_left_eq_self (fun v => b (‖v - x‖ ^ 2) * inner ℝ ξ (v - x)) x]
  simp only [add_sub_cancel_left]
  have h := integral_neg_eq_self (fun u : EuclideanSpace ℝ (Fin d) =>
    b (‖u‖ ^ 2) * inner ℝ ξ u) volume
  simp only [norm_neg, inner_neg_right, mul_neg, integral_neg] at h
  linarith

/-- The integrand `b(|v - x|²) ∇Ψ(v) · (v - x)` pairing the gradient of a norm with the radial
field of a cut-off profile is integrable. -/
private lemma integrable_profile_gradient_inner {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : CERW.IsNorm Ψ) {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) (hr : 0 ≤ r)
    (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun v => b (‖v - x‖ ^ 2) * inner ℝ (gradient Ψ v) (v - x)) volume := by
  set L : ℝ := (Real.toNNReal (∑ i, Ψ (CERW.coordVec i)) : ℝ) with hL
  have hL0 : 0 ≤ L := NNReal.coe_nonneg _
  have hmeas : Measurable fun v : EuclideanSpace ℝ (Fin d) =>
      b (‖v - x‖ ^ 2) * inner ℝ (gradient Ψ v) (v - x) := by
    have h1 : Measurable fun v : EuclideanSpace ℝ (Fin d) => b (‖v - x‖ ^ 2) :=
      hb.smooth.continuous.measurable.comp (by fun_prop)
    exact h1.mul ((measurable_gradient Ψ).inner (measurable_id.sub_const x))
  have hbound : Integrable ((Metric.closedBall x r).indicator fun _ => L * r) volume :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (isCompact_closedBall x r).measure_lt_top.ne)
  refine hbound.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  by_cases hv : r ≤ ‖v - x‖
  · have h0 : b (‖v - x‖ ^ 2) = 0 := hb.eq_zero _ (by nlinarith)
    rw [h0, zero_mul, norm_zero]
    exact Set.indicator_nonneg (fun w _ => mul_nonneg hL0 hr) _
  · have hmem : v ∈ Metric.closedBall x r := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact (not_le.mp hv).le
    rw [Set.indicator_of_mem hmem, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (hb.nonneg _)]
    calc b (‖v - x‖ ^ 2) * ‖inner ℝ (gradient Ψ v) (v - x)‖
        ≤ 1 * (‖gradient Ψ v‖ * ‖v - x‖) :=
          mul_le_mul (hb.le_one _) (norm_inner_le_norm _ _) (norm_nonneg _) zero_le_one
      _ ≤ L * r := by
          rw [one_mul]
          exact mul_le_mul (norm_gradient_le hΨ v) (not_le.mp hv).le (norm_nonneg _) hL0

/-- The integral of the excess over a ball on which the profile equals one is at most the pairing
of the gradient of a norm with the radial field of the profile. -/
private lemma setIntegral_excess_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {x ξ : EuclideanSpace ℝ (Fin d)} (hξ : CERW.IsSubgradient Ψ x ξ) {a r : ℝ} {b : ℝ → ℝ}
    (hb : Cutoff a r b) (hr : 0 ≤ r) :
    ∫ v in Metric.ball x a, excess Ψ x ξ v ≤
      ∫ v, b (‖v - x‖ ^ 2) * inner ℝ (gradient Ψ v) (v - x) := by
  have hfc : Continuous (excess Ψ x ξ) :=
    continuous_excess (CERW.Generic.Norm.norm_continuous hΨ) x ξ
  have hU := integrable_profile_gradient_inner hΨ hb hr x
  have hwc : Continuous fun v : EuclideanSpace ℝ (Fin d) => b (‖v - x‖ ^ 2) * inner ℝ ξ (v - x) :=
    (hb.smooth.continuous.comp (by fun_prop)).mul (by fun_prop)
  have hw : Integrable (fun v : EuclideanSpace ℝ (Fin d) =>
      b (‖v - x‖ ^ 2) * inner ℝ ξ (v - x)) volume := by
    refine integrable_of_zero_outside (r := r) (c := x) hwc fun u hu => ?_
    rw [hb.eq_zero _ (by nlinarith), zero_mul]
  have hind : Integrable ((Metric.ball x a).indicator (excess Ψ x ξ)) volume :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).2
      (integrableOn_of_isBounded hfc Metric.isBounded_ball)
  have hsplit : ∫ v, b (‖v - x‖ ^ 2) * inner ℝ (gradient Ψ v) (v - x) =
      ∫ v, (b (‖v - x‖ ^ 2) * inner ℝ (gradient Ψ v) (v - x) -
        b (‖v - x‖ ^ 2) * inner ℝ ξ (v - x)) := by
    rw [integral_sub hU hw, integral_profile_inner b x ξ, sub_zero]
  rw [hsplit, ← integral_indicator Metric.isOpen_ball.measurableSet]
  refine integral_mono_ae hind (hU.sub hw) ?_
  filter_upwards [CERW.Generic.Norm.ae_differentiableAt hΨ] with v hv
  have hsub := CERW.Generic.Norm.gradient_isSubgradient hΨ hv x
  have hneg : x - v = -(v - x) := (neg_sub v x).symm
  rw [hneg, inner_neg_right] at hsub
  have hexc := excess_nonneg hξ v
  have hkey : excess Ψ x ξ v ≤
      inner ℝ (gradient Ψ v) (v - x) - inner ℝ ξ (v - x) := by
    unfold excess at hexc ⊢
    linarith
  rw [← mul_sub]
  by_cases hball : v ∈ Metric.ball x a
  · rw [Set.indicator_of_mem hball]
    rw [Metric.mem_ball, dist_eq_norm] at hball
    have h1 : b (‖v - x‖ ^ 2) = 1 :=
      hb.eq_one _ (pow_le_pow_left₀ (norm_nonneg _) hball.le 2)
    rw [h1, one_mul]
    exact hkey
  · rw [Set.indicator_of_notMem hball]
    exact mul_nonneg (hb.nonneg _) (hexc.trans hkey)

/-- The cell integral is at most `2d` times the pairing of the gradient of a norm with the radial
field of a cut-off profile that equals one on the ball of radius `2 √d` about the site. -/
private lemma cell_integral_le_pairing {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    (hd : 1 ≤ d) {ξ : EuclideanSpace ℝ (Fin d)} (x : Site d)
    (hξ : CERW.IsSubgradient Ψ (CERW.toSpace x) ξ) {r : ℝ} {b : ℝ → ℝ}
    (hb : Cutoff (2 * Real.sqrt d) r b) (hr : 0 ≤ r) :
    ∫ v in CERW.cell x, ‖gradient Ψ v - ξ‖ ≤
      2 * d * ∫ v, b (‖v - CERW.toSpace x‖ ^ 2) *
        inner ℝ (gradient Ψ v) (v - CERW.toSpace x) :=
  (cell_integral_le hΨ hd x hξ).trans
    (mul_le_mul_of_nonneg_left (setIntegral_excess_le hΨ hξ hb hr) (by positivity))

/-- The negative pairing of the gradient of a norm with the gradient of the translated radial test
function is the integral of the profile times `∇Ψ(v) · (v - x)`. -/
private lemma neg_integral_inner_gradient_testFn {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {b : ℝ → ℝ} (hb : Continuous b) (r : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    -∫ v, inner ℝ (gradient Ψ v) (gradient (fun w => testFn b r 0 (w - x)) v) =
      ∫ v, b (‖v - x‖ ^ 2) * inner ℝ (gradient Ψ v) (v - x) := by
  have hfun : (fun w : EuclideanSpace ℝ (Fin d) => testFn b r 0 (w - x)) = testFn b r x := by
    funext w
    simp [testFn]
  rw [hfun, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [gradient_testFn hb r x v, real_inner_smul_right]
  ring

/-- The per-cell bound by a test function: for a norm `Ψ` on `ℝ^d`, `d ≥ 2`, the integral of
`|∇Ψ - ξ(x)|` over the cell `C_x` is at most `2d` times the pairing of `∇Ψ` with the gradient of a
fixed radial bump translated to `x`. -/
theorem cellTestBound {d : ℕ} (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) :
    CERW.Support.Norm.ContactShared.CellTestBound d Ψ := by
  have hd1 : 1 ≤ d := by omega
  have hsqrt : (1 : ℝ) ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hd1
  obtain ⟨b, hb⟩ := exists_cutoff (a := 2 * Real.sqrt d) (r := 3 * Real.sqrt d)
    (by linarith) (by linarith)
  have hr : 0 ≤ 3 * Real.sqrt d := by linarith
  refine ⟨testFn b (3 * Real.sqrt d) 0, 3 * Real.sqrt d, 2 * (d : ℝ),
    contDiff_testFn hb.smooth _ _, hasCompactSupport_testFn hb hr 0, testFn_nonneg hb 0,
    by linarith, ?_, by positivity, ?_⟩
  · intro v hv
    exact testFn_eq_zero hb (by rwa [sub_zero]) hr
  · intro ξ hξ hξ0 x
    have hsub : CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x) := by
      by_cases hx : x = 0
      · subst hx
        have h0 : CERW.toSpace (0 : Site d) = 0 := by
          ext i
          simp
        rw [h0, hξ0]
        exact CERW.Generic.Norm.subgradient_zero hΨ
      · exact hξ x hx
    rw [neg_integral_inner_gradient_testFn hb.smooth.continuous]
    exact cell_integral_le_pairing hΨ hd1 x hsub hb hr

end CERW.Support.Norm.ContactCellTest

namespace CERW.Support.Norm.ContactBregman

open CERW CERW.Generic.Norm CERW.Support.Occupation CERW.Support.Norm.ContactShared
open scoped ContDiff

variable {d : ℕ}

/-- The gradient of a function on `ℝ^d` is measurable. -/
private lemma measurable_gradient (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measurable (gradient Ψ) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ Ψ)

/-- For `d ≥ 1`, `Λ_Ψ ≥ 0`. -/
private lemma normMax_nonneg {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d) :
    0 ≤ normMax Ψ := by
  have h1 := normMin_pos_mul_le hΨ hd
  have hn : ‖coordVec (⟨0, by omega⟩ : Fin d)‖ = 1 := by
    simp [coordVec, PiLp.norm_single]
  have h2 := le_normMax_mul hΨ (coordVec (⟨0, by omega⟩ : Fin d))
  have h3 := h1.2 (coordVec (⟨0, by omega⟩ : Fin d))
  rw [hn] at h2 h3
  linarith [h1.1]

/-- A subgradient of a norm at any point has Euclidean norm at most `Λ_Ψ`. -/
private lemma norm_subgradient_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (hd : 1 ≤ d) {x ξ : EuclideanSpace ℝ (Fin d)} (h : IsSubgradient Ψ x ξ) :
    ‖ξ‖ ≤ normMax Ψ := by
  have h1 := (subgradient_euler hΨ h).2 ξ
  have h2 := le_normMax_mul hΨ ξ
  rw [real_inner_self_eq_norm_mul_norm] at h1
  have h3 : ‖ξ‖ * ‖ξ‖ ≤ normMax Ψ * ‖ξ‖ := h1.trans h2
  rcases eq_or_lt_of_le (norm_nonneg ξ) with h0 | h0
  · rw [← h0]
    exact normMax_nonneg hΨ hd
  · exact le_of_mul_le_mul_right h3 h0

/-- The gradient of a norm has Euclidean norm at most `Λ_Ψ` everywhere: where `Ψ` is
differentiable it is a subgradient, and elsewhere it is `0`. -/
private lemma norm_gradient_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d)
    (v : EuclideanSpace ℝ (Fin d)) : ‖gradient Ψ v‖ ≤ normMax Ψ := by
  by_cases hv : DifferentiableAt ℝ Ψ v
  · exact norm_subgradient_le hΨ hd (gradient_isSubgradient hΨ hv)
  · have h0 : gradient Ψ v = 0 := by
      rw [gradient, fderiv_zero_of_not_differentiableAt hv]
      simp
    rw [h0, norm_zero]
    exact normMax_nonneg hΨ hd

/-- The difference of the gradient and a subgradient (or `0`) has norm at most `2 Λ_Ψ`. -/
private lemma norm_gradient_sub_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (hd : 1 ≤ d) {ξ : EuclideanSpace ℝ (Fin d)} (hξ : ‖ξ‖ ≤ normMax Ψ)
    (v : EuclideanSpace ℝ (Fin d)) : ‖gradient Ψ v - ξ‖ ≤ 2 * normMax Ψ := by
  have h := norm_sub_le (gradient Ψ v) ξ
  have h1 := norm_gradient_le hΨ hd v
  linarith

/-- A test function is smooth with compact support. -/
private def IsTest (φ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

/-- The pairing `∫ ⟪∇Ψ, ∇φ⟫` of the gradient of `Ψ` with the gradient of `φ`. -/
private noncomputable def pairing (Ψ φ : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  ∫ v, inner ℝ (gradient Ψ v) (gradient φ v)

/-- A test function is differentiable. -/
private lemma IsTest.differentiable {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTest φ) :
    Differentiable ℝ φ :=
  h.1.differentiable (by simp)

/-- The gradient of a test function is continuous. -/
private lemma IsTest.continuous_gradient {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTest φ) :
    Continuous (gradient φ) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.comp
    (h.1.continuous_fderiv (by simp))

/-- The gradient of a test function has compact support. -/
private lemma IsTest.hasCompactSupport_gradient {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTest φ) : HasCompactSupport (gradient φ) :=
  (h.2.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm)
    (map_zero _)

/-- The norm of the gradient of a test function is integrable. -/
private lemma IsTest.integrable_norm_gradient {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTest φ) : Integrable (fun v => ‖gradient φ v‖) :=
  h.continuous_gradient.norm.integrable_of_hasCompactSupport h.hasCompactSupport_gradient.norm

/-- The pairing integrand of a bounded-gradient function with a test function is integrable. -/
private lemma IsTest.integrable_inner {Ψ φ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (hd : 1 ≤ d) (h : IsTest φ) :
    Integrable (fun v => inner ℝ (gradient Ψ v) (gradient φ v)) := by
  refine (h.integrable_norm_gradient.const_mul (normMax Ψ)).mono' ?_ ?_
  · exact ((measurable_gradient Ψ).inner h.continuous_gradient.measurable).aestronglyMeasurable
  · filter_upwards with v
    rw [Real.norm_eq_abs]
    calc |inner ℝ (gradient Ψ v) (gradient φ v)| ≤ ‖gradient Ψ v‖ * ‖gradient φ v‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ normMax Ψ * ‖gradient φ v‖ :=
          mul_le_mul_of_nonneg_right (norm_gradient_le hΨ hd v) (norm_nonneg _)

/-- The pairing of `∇Ψ` with a test function is at most `Λ_Ψ ∫ |∇φ|` in absolute value. -/
private lemma IsTest.abs_pairing_le {Ψ φ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (hd : 1 ≤ d) (h : IsTest φ) :
    |pairing Ψ φ| ≤ normMax Ψ * ∫ v, ‖gradient φ v‖ := by
  have hb : ∀ v, ‖inner ℝ (gradient Ψ v) (gradient φ v)‖ ≤ normMax Ψ * ‖gradient φ v‖ := by
    intro v
    rw [Real.norm_eq_abs]
    calc |inner ℝ (gradient Ψ v) (gradient φ v)| ≤ ‖gradient Ψ v‖ * ‖gradient φ v‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ normMax Ψ * ‖gradient φ v‖ :=
          mul_le_mul_of_nonneg_right (norm_gradient_le hΨ hd v) (norm_nonneg _)
  have := norm_integral_le_of_norm_le (h.integrable_norm_gradient.const_mul (normMax Ψ))
    (Eventually.of_forall hb)
  rw [integral_const_mul, Real.norm_eq_abs] at this
  exact this

/-- The inner product with the gradient is the derivative applied to the vector. -/
private lemma inner_gradient_eq (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (v g : EuclideanSpace ℝ (Fin d)) : inner ℝ g (gradient φ v) = fderiv ℝ φ v g := by
  rw [real_inner_comm, inner_gradient_left]

/-- Test functions are closed under subtraction. -/
private lemma IsTest.sub {f g : EuclideanSpace ℝ (Fin d) → ℝ} (hf : IsTest f) (hg : IsTest g) :
    IsTest (fun v => f v - g v) :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

/-- Test functions are closed under multiplication by constants. -/
private lemma IsTest.const_mul {f : EuclideanSpace ℝ (Fin d) → ℝ} (c : ℝ) (hf : IsTest f) :
    IsTest (fun v => c * f v) :=
  ⟨contDiff_const.mul hf.1, hf.2.comp_left (g := fun t : ℝ => c * t) (mul_zero c)⟩

/-- A finite sum of functions with compact support has compact support. -/
private lemma hasCompactSupport_finset_sum (T : Finset (Site d))
    (g : Site d → EuclideanSpace ℝ (Fin d) → ℝ) (hg : ∀ x ∈ T, HasCompactSupport (g x)) :
    HasCompactSupport (fun v => ∑ x ∈ T, g x v) := by
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert a T ha ih =>
    have h1 := hg a (Finset.mem_insert_self a T)
    have h2 := ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))
    have hsum : (fun v => ∑ x ∈ insert a T, g x v) = g a + fun v => ∑ x ∈ T, g x v := by
      funext v
      simp [Finset.sum_insert ha]
    rw [hsum]
    exact h1.add h2

/-- Test functions are closed under finite weighted sums. -/
private lemma IsTest.sum (T : Finset (Site d)) (w : Site d → ℝ)
    (f : Site d → EuclideanSpace ℝ (Fin d) → ℝ) (hf : ∀ x ∈ T, IsTest (f x)) :
    IsTest (fun v => ∑ x ∈ T, w x * f x v) :=
  ⟨ContDiff.sum fun x hx => contDiff_const.mul (hf x hx).1,
    hasCompactSupport_finset_sum T (fun x v => w x * f x v) fun x hx =>
      (hf x hx).const_mul (w x) |>.2⟩

/-- The pairing is additive in the test function (difference form). -/
private lemma pairing_sub {Ψ f g : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d)
    (hf : IsTest f) (hg : IsTest g) :
    pairing Ψ (fun v => f v - g v) = pairing Ψ f - pairing Ψ g := by
  unfold pairing
  rw [← integral_sub (hf.integrable_inner hΨ hd) (hg.integrable_inner hΨ hd)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [inner_gradient_eq, fderiv_fun_sub (hf.differentiable v) (hg.differentiable v),
    _root_.sub_apply]

/-- The pairing is homogeneous in the test function. -/
private lemma pairing_const_mul {Ψ f : EuclideanSpace ℝ (Fin d) → ℝ} (c : ℝ) (hf : IsTest f) :
    pairing Ψ (fun v => c * f v) = c * pairing Ψ f := by
  unfold pairing
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [inner_gradient_eq, fderiv_const_mul (hf.differentiable v) c,
    _root_.smul_apply, smul_eq_mul]

/-- The pairing of a finite weighted sum of test functions is the weighted sum of the pairings. -/
private lemma pairing_sum {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d)
    (T : Finset (Site d)) (w : Site d → ℝ) (f : Site d → EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ∀ x ∈ T, IsTest (f x)) :
    pairing Ψ (fun v => ∑ x ∈ T, w x * f x v) = ∑ x ∈ T, w x * pairing Ψ (f x) := by
  unfold pairing
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum T (fun x hx => ((hf x hx).integrable_inner hΨ hd).const_mul (w x))]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  have hdiff : ∀ x ∈ T, DifferentiableAt ℝ (fun v => w x * f x v) v := fun x hx =>
    ((hf x hx).differentiable v).const_mul (w x)
  beta_reduce
  rw [inner_gradient_eq, fderiv_fun_sum hdiff, _root_.sum_apply]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [fderiv_const_mul ((hf x hx).differentiable v), inner_gradient_eq]
  simp

/-- A function that is locally constant at `t` has zero derivative there. -/
private lemma deriv_eq_zero_of_eventually_const {κ : ℝ → ℝ} {t c : ℝ}
    (h : ∀ᶠ s in 𝓝 t, κ s = c) : deriv κ t = 0 := by
  have h' : κ =ᶠ[𝓝 t] fun _ => c := h
  rw [h'.deriv_eq]
  simp

/-- The properties of the smooth cut-off profile used for the radial majorant: values in
`[0, 1]`, equal to `1` on `(-∞, 1]`, equal to `0` on `[4, ∞)`, with a derivative bounded by `K`
that vanishes off `[1, 4]`. -/
private structure Profile (κ : ℝ → ℝ) (K : ℝ) : Prop where
  /-- The profile is smooth. -/
  smooth : ContDiff ℝ ∞ κ
  /-- The profile is nonnegative. -/
  nonneg : ∀ t, 0 ≤ κ t
  /-- The profile is at most one. -/
  le_one : ∀ t, κ t ≤ 1
  /-- The profile equals one on `(-∞, 1]`. -/
  eq_one : ∀ t, t ≤ 1 → κ t = 1
  /-- The profile vanishes on `[4, ∞)`. -/
  eq_zero : ∀ t, 4 ≤ t → κ t = 0
  /-- The derivative vanishes below `1`. -/
  deriv_lt : ∀ t, t < 1 → deriv κ t = 0
  /-- The derivative vanishes above `4`. -/
  deriv_gt : ∀ t, 4 < t → deriv κ t = 0
  /-- The derivative is bounded by `K`. -/
  deriv_le : ∀ t, |deriv κ t| ≤ K

/-- There is a smooth cut-off profile on the line with a bounded derivative. -/
private lemma exists_profile : ∃ (κ : ℝ → ℝ) (K : ℝ), Profile κ K := by
  set κ : ℝ → ℝ := fun t => Real.smoothTransition ((4 - t) / 3) with hκdef
  have hsm : ContDiff ℝ ∞ κ := Real.smoothTransition.contDiff.comp (by fun_prop)
  have h1 : ∀ t, t ≤ 1 → κ t = 1 := by
    intro t ht
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have h0 : ∀ t, 4 ≤ t → κ t = 0 := by
    intro t ht
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)
  have hd1 : ∀ t, t < 1 → deriv κ t = 0 := fun t ht =>
    deriv_eq_zero_of_eventually_const (c := 1)
      (by filter_upwards [Iio_mem_nhds ht] with s hs using h1 s (le_of_lt hs))
  have hd0 : ∀ t, 4 < t → deriv κ t = 0 := fun t ht =>
    deriv_eq_zero_of_eventually_const (c := 0)
      (by filter_upwards [Ioi_mem_nhds ht] with s hs using h0 s (le_of_lt hs))
  have hsupp : HasCompactSupport (deriv κ) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 1) (b := 4)) ?_
    intro t ht
    by_contra hnot
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
    rcases hnot with h | h
    · exact ht (hd1 t h)
    · exact ht (hd0 t h)
  obtain ⟨K, hK⟩ := (hsm.continuous_deriv (by simp)).bounded_above_of_compact_support hsupp
  exact ⟨κ, K, ⟨hsm, fun t => Real.smoothTransition.nonneg _,
    fun t => Real.smoothTransition.le_one _, h1, h0, hd1, hd0, fun t => by simpa using hK t⟩⟩

/-- For `r ≥ 0` and `t ≥ 0`: `(1 + t²)^{-r} ≤ 2^r (1 + t)^{-2r}`. -/
private lemma rpow_one_add_sq_le {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    (1 + t ^ 2) ^ (-r) ≤ (2 : ℝ) ^ r * (1 + t) ^ (-(2 * r)) := by
  have hB : 0 < 1 + t := by linarith
  have hA : 0 < 1 + t ^ 2 := by positivity
  have hle : (1 + t) ^ 2 / 2 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
  have hpos : 0 < (1 + t) ^ 2 / 2 := by positivity
  calc (1 + t ^ 2) ^ (-r) ≤ ((1 + t) ^ 2 / 2) ^ (-r) :=
        Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
    _ = (2 : ℝ) ^ r * (1 + t) ^ (-(2 * r)) := by
        rw [Real.div_rpow (by positivity) (by norm_num),
          Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2)]
        have h2 : ((1 + t) ^ 2) ^ (-r) = (1 + t) ^ (-(2 * r)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]
          congr 1
          push_cast
          ring
        rw [h2, div_inv_eq_mul, mul_comm]

/-- The derivative of the radial profile `s ↦ (1 + s)^{-p} κ(s/ρ²)` at `s ≥ 0`. -/
private lemma hasDerivAt_profile {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) (p ρ : ℝ) {s : ℝ}
    (hs : 0 ≤ s) :
    HasDerivAt (fun s : ℝ => (1 + s) ^ (-p) * κ (s / ρ ^ 2))
      (-p * (1 + s) ^ (-p - 1) * κ (s / ρ ^ 2) +
        (1 + s) ^ (-p) * (deriv κ (s / ρ ^ 2) / ρ ^ 2)) s := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 s := (hasDerivAt_id' s).const_add 1
  have h2 : HasDerivAt (fun s : ℝ => (1 + s) ^ (-p)) (1 * (-p) * (1 + s) ^ (-p - 1)) s :=
    h1.rpow_const (Or.inl (by linarith))
  have h3 : HasDerivAt (fun s : ℝ => s / ρ ^ 2) (1 / ρ ^ 2) s := (hasDerivAt_id' s).div_const _
  have h4 : HasDerivAt (fun s : ℝ => κ (s / ρ ^ 2)) (deriv κ (s / ρ ^ 2) * (1 / ρ ^ 2)) s :=
    ((hκ.differentiable (by simp)) (s / ρ ^ 2)).hasDerivAt.comp s h3
  have h5 := h2.mul h4
  exact h5.congr_deriv (by ring)

/-- The derivative of `w ↦ |w - y|²`. -/
private lemma hasFDerivAt_sqNorm (y v : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun w : EuclideanSpace ℝ (Fin d) => ‖w - y‖ ^ 2)
      (2 • innerSL ℝ (v - y)) v := by
  have := (hasStrictFDerivAt_norm_sq (v - y)).hasFDerivAt.comp v
    ((hasFDerivAt_id v).sub_const y)
  rw [ContinuousLinearMap.comp_id] at this
  exact this

/-- The norm of the derivative of a radial function `w ↦ F(|w - y|²)` is at most
`2 |F'(|v - y|²)| |v - y|`. -/
private lemma norm_fderiv_radial_le {F : ℝ → ℝ} {F' : ℝ} (y v : EuclideanSpace ℝ (Fin d))
    (h : HasDerivAt F F' (‖v - y‖ ^ 2)) :
    ‖fderiv ℝ (fun w : EuclideanSpace ℝ (Fin d) => F (‖w - y‖ ^ 2)) v‖ ≤
      |F'| * (2 * ‖v - y‖) := by
  have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin d) => F (‖w - y‖ ^ 2))
      (F' • (2 • innerSL ℝ (v - y))) v := h.comp_hasFDerivAt v (hasFDerivAt_sqNorm y v)
  rw [h1.fderiv, norm_smul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc ‖(2 : ℕ) • innerSL ℝ (v - y)‖ ≤ (2 : ℕ) * ‖innerSL ℝ (v - y)‖ := norm_nsmul_le
    _ = 2 * ‖v - y‖ := by rw [innerSL_apply_norm]; norm_num

/-- The decaying part of the derivative of the radial profile:
`p (1 + t²)^{-p-1} · 2t ≤ 2p · 2^{p+1} (1 + t)^{-(2p+1)}`. -/
private lemma term_decay_le {p t : ℝ} (hp : 0 ≤ p) (ht : 0 ≤ t) :
    p * (1 + t ^ 2) ^ (-p - 1) * (2 * t) ≤
      2 * p * (2 : ℝ) ^ (p + 1) * (1 + t) ^ (-(2 * p + 1)) := by
  have hB : 0 < 1 + t := by linarith
  have h1 := rpow_one_add_sq_le (r := p + 1) (by linarith) ht
  have h2 : (1 + t) ^ (-(2 * (p + 1))) = (1 + t) ^ (-(2 * p + 1)) * (1 + t)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hB]
    congr 1
    ring
  have h3 : t * (1 + t)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hB]
    linarith
  have h4 : (1 + t ^ 2) ^ (-p - 1) ≤
      (2 : ℝ) ^ (p + 1) * ((1 + t) ^ (-(2 * p + 1)) * (1 + t)⁻¹) := by
    have h5 : -p - 1 = -(p + 1) := by ring
    rw [h5, ← h2]
    exact h1
  have hpos : 0 ≤ (1 + t) ^ (-(2 * p + 1)) := Real.rpow_nonneg hB.le _
  have h2p : 0 ≤ (2 : ℝ) ^ (p + 1) := Real.rpow_nonneg (by norm_num) _
  calc p * (1 + t ^ 2) ^ (-p - 1) * (2 * t)
      ≤ p * ((2 : ℝ) ^ (p + 1) * ((1 + t) ^ (-(2 * p + 1)) * (1 + t)⁻¹)) * (2 * t) := by
        gcongr
    _ = 2 * p * (2 : ℝ) ^ (p + 1) * (1 + t) ^ (-(2 * p + 1)) * (t * (1 + t)⁻¹) := by ring
    _ ≤ 2 * p * (2 : ℝ) ^ (p + 1) * (1 + t) ^ (-(2 * p + 1)) * 1 := by
        gcongr
    _ = 2 * p * (2 : ℝ) ^ (p + 1) * (1 + t) ^ (-(2 * p + 1)) := mul_one _

/-- The cut-off part of the derivative of the radial profile, on the annulus `ρ ≤ t ≤ 2ρ`:
`(1 + t²)^{-p} (K/ρ²) · 2t ≤ 12 K 2^p (1 + t)^{-(2p+1)}`. -/
private lemma term_cutoff_le {p t ρ K : ℝ} (hp : 0 ≤ p) (hρ : 1 ≤ ρ) (hK : 0 ≤ K)
    (ht1 : ρ ≤ t) (ht2 : t ≤ 2 * ρ) :
    (1 + t ^ 2) ^ (-p) * (K / ρ ^ 2 * (2 * t)) ≤
      12 * K * (2 : ℝ) ^ p * (1 + t) ^ (-(2 * p + 1)) := by
  have ht : 0 ≤ t := by linarith
  have hB : 0 < 1 + t := by linarith
  have hρ0 : 0 < ρ := by linarith
  have h1 := rpow_one_add_sq_le (r := p) hp ht
  have h2 : (1 + t) ^ (-(2 * p + 1)) = (1 + t) ^ (-(2 * p)) * (1 + t)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hB]
    congr 1
    ring
  have h3 : K / ρ ^ 2 * (2 * t) ≤ 12 * K * (1 + t)⁻¹ := by
    have h4 : 2 * t * (1 + t) ≤ 12 * ρ ^ 2 := by nlinarith
    rw [← div_eq_mul_inv, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hB]
    calc K * (2 * t) * (1 + t) = K * (2 * t * (1 + t)) := by ring
      _ ≤ K * (12 * ρ ^ 2) := mul_le_mul_of_nonneg_left h4 hK
      _ = 12 * K * ρ ^ 2 := by ring
  have hB0 : 0 ≤ (1 + t) ^ (-(2 * p)) := Real.rpow_nonneg hB.le _
  have h2p : 0 ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) _
  calc (1 + t ^ 2) ^ (-p) * (K / ρ ^ 2 * (2 * t))
      ≤ ((2 : ℝ) ^ p * (1 + t) ^ (-(2 * p))) * (12 * K * (1 + t)⁻¹) := by
        apply mul_le_mul h1 h3 (by positivity) (by positivity)
    _ = 12 * K * (2 : ℝ) ^ p * ((1 + t) ^ (-(2 * p)) * (1 + t)⁻¹) := by ring
    _ = 12 * K * (2 : ℝ) ^ p * (1 + t) ^ (-(2 * p + 1)) := by rw [h2]

/-- The radial bump `(1 + |v - y|²)^{-p} κ(|v - y|² / ρ²)`. -/
private noncomputable def bump (p ρ : ℝ) (κ : ℝ → ℝ) (y v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 + ‖v - y‖ ^ 2) ^ (-p) * κ (‖v - y‖ ^ 2 / ρ ^ 2)

/-- The gradient of the radial bump is at most `c (1 + |v - y|)^{-(2p+1)}` in norm and vanishes
outside the ball of radius `2ρ`. -/
private lemma norm_gradient_bump_le {κ : ℝ → ℝ} {K : ℝ} (hκ : Profile κ K) {p ρ : ℝ}
    (hp : 0 ≤ p) (hρ : 1 ≤ ρ) (y v : EuclideanSpace ℝ (Fin d)) :
    ‖gradient (bump p ρ κ y) v‖ ≤
      if ‖v - y‖ ≤ 2 * ρ then
        (2 * p * (2 : ℝ) ^ (p + 1) + 12 * K * (2 : ℝ) ^ p) * (1 + ‖v - y‖) ^ (-(2 * p + 1))
      else 0 := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hκ.deriv_le 0)
  have hρ0 : 0 < ρ := by linarith
  have hnorm : ‖gradient (bump p ρ κ y) v‖ = ‖fderiv ℝ (bump p ρ κ y) v‖ :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.norm_map _
  rw [hnorm]
  have hD := hasDerivAt_profile hκ.smooth p ρ (sq_nonneg ‖v - y‖)
  have hF := norm_fderiv_radial_le y v hD
  set t := ‖v - y‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  set q := t ^ 2 / ρ ^ 2 with hq
  set D := -p * (1 + t ^ 2) ^ (-p - 1) * κ q +
    (1 + t ^ 2) ^ (-p) * (deriv κ q / ρ ^ 2) with hDdef
  have hF' : ‖fderiv ℝ (bump p ρ κ y) v‖ ≤ |D| * (2 * t) := hF
  have hA : 0 ≤ (1 + t ^ 2) ^ (-p - 1) := Real.rpow_nonneg (by positivity) _
  have hA' : 0 ≤ (1 + t ^ 2) ^ (-p) := Real.rpow_nonneg (by positivity) _
  split_ifs with h2
  · have hT1 : |-p * (1 + t ^ 2) ^ (-p - 1) * κ q| ≤ p * (1 + t ^ 2) ^ (-p - 1) := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hp, abs_of_nonneg hA,
        abs_of_nonneg (hκ.nonneg q)]
      calc p * (1 + t ^ 2) ^ (-p - 1) * κ q ≤ p * (1 + t ^ 2) ^ (-p - 1) * 1 :=
            mul_le_mul_of_nonneg_left (hκ.le_one q) (by positivity)
        _ = p * (1 + t ^ 2) ^ (-p - 1) := mul_one _
    have hT2 : |(1 + t ^ 2) ^ (-p) * (deriv κ q / ρ ^ 2)| ≤
        (if ρ ≤ t then (1 + t ^ 2) ^ (-p) * (K / ρ ^ 2) else 0) := by
      split_ifs with h3
      · rw [abs_mul, abs_of_nonneg hA', abs_div, abs_of_nonneg (sq_nonneg ρ)]
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (hκ.deriv_le q) (sq_nonneg ρ)) hA'
      · have hlt : q < 1 := by
          rw [hq, div_lt_one (by positivity)]
          nlinarith [not_le.mp h3]
        rw [hκ.deriv_lt q hlt]
        simp
    have hDle : |D| ≤ p * (1 + t ^ 2) ^ (-p - 1) +
        (if ρ ≤ t then (1 + t ^ 2) ^ (-p) * (K / ρ ^ 2) else 0) :=
      (abs_add_le _ _).trans (add_le_add hT1 hT2)
    have hfin : |D| * (2 * t) ≤
        (2 * p * (2 : ℝ) ^ (p + 1) + 12 * K * (2 : ℝ) ^ p) * (1 + t) ^ (-(2 * p + 1)) := by
      have hc := term_decay_le hp ht0
      have hpos : 0 ≤ 12 * K * (2 : ℝ) ^ p * (1 + t) ^ (-(2 * p + 1)) :=
        mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _))
          (Real.rpow_nonneg (by linarith) _)
      calc |D| * (2 * t) ≤ (p * (1 + t ^ 2) ^ (-p - 1) +
            (if ρ ≤ t then (1 + t ^ 2) ^ (-p) * (K / ρ ^ 2) else 0)) * (2 * t) :=
            mul_le_mul_of_nonneg_right hDle (by positivity)
        _ = p * (1 + t ^ 2) ^ (-p - 1) * (2 * t) +
            (if ρ ≤ t then (1 + t ^ 2) ^ (-p) * (K / ρ ^ 2) * (2 * t) else 0) := by
            split_ifs <;> ring
        _ ≤ 2 * p * (2 : ℝ) ^ (p + 1) * (1 + t) ^ (-(2 * p + 1)) +
            12 * K * (2 : ℝ) ^ p * (1 + t) ^ (-(2 * p + 1)) := by
            refine add_le_add hc ?_
            split_ifs with h3
            · have := term_cutoff_le hp hρ hK h3 h2
              calc (1 + t ^ 2) ^ (-p) * (K / ρ ^ 2) * (2 * t)
                  = (1 + t ^ 2) ^ (-p) * (K / ρ ^ 2 * (2 * t)) := by ring
                _ ≤ _ := this
            · exact hpos
        _ = _ := by ring
    exact hF'.trans hfin
  · have hq4 : 4 < q := by
      rw [hq, lt_div_iff₀ (by positivity)]
      nlinarith [not_le.mp h2]
    have hD0 : D = 0 := by
      rw [hDdef, hκ.eq_zero q hq4.le, hκ.deriv_gt q hq4]
      simp
    rw [hD0] at hF'
    simpa using hF'

/-- The radial bump is smooth. -/
private lemma contDiff_bump {κ : ℝ → ℝ} {K : ℝ} (hκ : Profile κ K) (p ρ : ℝ)
    (y : EuclideanSpace ℝ (Fin d)) : ContDiff ℝ ∞ (bump p ρ κ y) := by
  have hq : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin d) => ‖v - y‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have h1 : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin d) => 1 + ‖v - y‖ ^ 2) :=
    contDiff_const.add hq
  exact (h1.rpow_const_of_ne (fun v => by positivity)).mul (hκ.smooth.comp (hq.div_const _))

/-- The radial bump vanishes outside the ball of radius `2ρ`. -/
private lemma bump_eq_zero {κ : ℝ → ℝ} {K : ℝ} (hκ : Profile κ K) {p ρ : ℝ} (hρ : 0 < ρ)
    {y v : EuclideanSpace ℝ (Fin d)} (h : 2 * ρ ≤ ‖v - y‖) : bump p ρ κ y v = 0 := by
  have h4 : 4 ≤ ‖v - y‖ ^ 2 / ρ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rw [bump, hκ.eq_zero _ h4, mul_zero]

/-- The radial bump is `(1 + |v - y|²)^{-p}` inside the ball of radius `ρ`. -/
private lemma bump_eq {κ : ℝ → ℝ} {K : ℝ} (hκ : Profile κ K) {p ρ : ℝ} (hρ : 0 < ρ)
    {y v : EuclideanSpace ℝ (Fin d)} (h : ‖v - y‖ ≤ ρ) :
    bump p ρ κ y v = (1 + ‖v - y‖ ^ 2) ^ (-p) := by
  have h1 : ‖v - y‖ ^ 2 / ρ ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [norm_nonneg (v - y)]
  rw [bump, hκ.eq_one _ h1, mul_one]

/-- The radial bump is nonnegative. -/
private lemma bump_nonneg {κ : ℝ → ℝ} {K : ℝ} (hκ : Profile κ K) (p ρ : ℝ)
    (y v : EuclideanSpace ℝ (Fin d)) : 0 ≤ bump p ρ κ y v :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) (hκ.nonneg _)

/-- The radial bump is a test function. -/
private lemma isTest_bump {κ : ℝ → ℝ} {K : ℝ} (hκ : Profile κ K) (p : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (y : EuclideanSpace ℝ (Fin d)) : IsTest (bump p ρ κ y) := by
  refine ⟨contDiff_bump hκ p ρ y, ?_⟩
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall y (2 * ρ)) ?_
  intro v hv
  by_contra hnot
  rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hnot
  exact hv (bump_eq_zero hκ hρ hnot.le)

/-- Translating by `y` carries integrals over `B(0, r)` to integrals over `B(y, r)`. -/
private lemma integrableOn_ball_comp_sub {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (y : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hf : IntegrableOn f (Metric.ball 0 r)) :
    IntegrableOn (fun v => f (v - y)) (Metric.ball y r) ∧
      ∫ v in Metric.ball y r, f (v - y) = ∫ w in Metric.ball 0 r, f w := by
  have hmp := measurePreserving_sub_right (volume : Measure (EuclideanSpace ℝ (Fin d))) y
  have hemb := measurableEmbedding_subRight y
  rw [CERW.Generic.Kernel.ball_eq_preimage_sub y r]
  exact ⟨(hmp.integrableOn_comp_preimage hemb (f := f)).mpr hf,
    hmp.setIntegral_preimage_emb hemb f _⟩

/-- The radial majorant: there is a constant `c` such that for every centre `y` and radius
`ρ ≥ 1` there is a test function `Θ ≥ 0`, equal to `(1 + |v - y|²)^{-(d-1)/2}` on `B(y, ρ)`,
whose gradient has mass at most `c log (2ρ + 2)`. -/
private lemma exists_majorant (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (y : EuclideanSpace ℝ (Fin d)) (ρ : ℝ), 1 ≤ ρ →
      ∃ Θ : EuclideanSpace ℝ (Fin d) → ℝ, IsTest Θ ∧ (∀ v, 0 ≤ Θ v) ∧
        (∀ v, ‖v - y‖ ≤ ρ → Θ v = (1 + ‖v - y‖ ^ 2) ^ (-(((d : ℝ) - 1) / 2))) ∧
        ∫ v, ‖gradient Θ v‖ ≤ c * Real.log (2 * ρ + 2) := by
  obtain ⟨κ, K, hκ⟩ := exists_profile
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  set p : ℝ := ((d : ℝ) - 1) / 2 with hpdef
  have hp : 0 ≤ p := by rw [hpdef]; linarith
  have hK : 0 ≤ K := (abs_nonneg _).trans (hκ.deriv_le 0)
  have hω := CERW.unitBallVolume_pos d
  have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) _
  have h2p1 : (0 : ℝ) ≤ (2 : ℝ) ^ (p + 1) := Real.rpow_nonneg (by norm_num) _
  set c₂ : ℝ := 2 * p * (2 : ℝ) ^ (p + 1) + 12 * K * (2 : ℝ) ^ p with hc₂def
  have hc₂ : 0 ≤ c₂ := by positivity
  have hexp : 2 * p + 1 = (d : ℝ) := by rw [hpdef]; ring
  refine ⟨c₂ * (d * CERW.unitBallVolume d), by positivity, fun y ρ hρ => ?_⟩
  have hρ0 : 0 < ρ := by linarith
  refine ⟨bump p ρ κ y, isTest_bump hκ p hρ0 y, bump_nonneg hκ p ρ y,
    fun v hv => bump_eq hκ hρ0 hv, ?_⟩
  set f : EuclideanSpace ℝ (Fin d) → ℝ := fun w => (1 + ‖w‖) ^ (-(d : ℝ)) with hfdef
  set G : EuclideanSpace ℝ (Fin d) → ℝ :=
    (Metric.ball y (2 * ρ + 1)).indicator (fun v => c₂ * f (v - y)) with hGdef
  obtain ⟨hfint, hfval⟩ := CERW.Generic.Kernel.integrableOn_ball_one_add_norm_rpow_and_integral_le
    (d := d) hd1 (R := 2 * ρ + 1) (by linarith)
  obtain ⟨hGint', hGval⟩ := integrableOn_ball_comp_sub y (2 * ρ + 1) hfint
  have hGint : Integrable G := by
    rw [hGdef, integrable_indicator_iff Metric.isOpen_ball.measurableSet]
    exact hGint'.const_mul c₂
  have hGnn : ∀ v, 0 ≤ G v :=
    Set.indicator_nonneg fun v _ => mul_nonneg hc₂ (Real.rpow_nonneg (by positivity) _)
  have hle : ∀ v, ‖gradient (bump p ρ κ y) v‖ ≤ G v := by
    intro v
    refine (norm_gradient_bump_le hκ hp hρ y v).trans ?_
    split_ifs with h2
    · have hmem : v ∈ Metric.ball y (2 * ρ + 1) := by
        rw [mem_ball_iff_norm]
        linarith
      rw [hGdef, Set.indicator_of_mem hmem, hfdef, hexp]
    · exact hGnn v
  calc ∫ v, ‖gradient (bump p ρ κ y) v‖ ≤ ∫ v, G v :=
        integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _) hGint
          (Eventually.of_forall hle)
    _ = c₂ * ∫ v in Metric.ball y (2 * ρ + 1), f (v - y) := by
        rw [hGdef, integral_indicator Metric.isOpen_ball.measurableSet, integral_const_mul]
    _ = c₂ * ∫ w in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (2 * ρ + 1), f w := by
        rw [hGval]
    _ ≤ c₂ * (d * CERW.unitBallVolume d * Real.log (1 + (2 * ρ + 1))) :=
        mul_le_mul_of_nonneg_left hfval hc₂
    _ = c₂ * (d * CERW.unitBallVolume d) * Real.log (2 * ρ + 2) := by
        rw [show 1 + (2 * ρ + 1) = 2 * ρ + 2 by ring]
        ring

/-- Near sites: the sum over finitely many disjoint cells inside `B(y, ρ₀)` of the integral of a
function bounded by `M` against the Newtonian kernel `|v - y|^{1-d}` is at most `M d ω_d ρ₀`. -/
private lemma sum_cells_kernel_le (hd : 1 ≤ d) (T : Finset (Site d))
    (y : EuclideanSpace ℝ (Fin d)) {ρ₀ M : ℝ} (hρ₀ : 0 < ρ₀) (hM : 0 ≤ M)
    (hT : ∀ x ∈ T, cell x ⊆ Metric.ball y ρ₀)
    (f : Site d → EuclideanSpace ℝ (Fin d) → ℝ) (hf0 : ∀ x ∈ T, ∀ v, 0 ≤ f x v)
    (hfM : ∀ x ∈ T, ∀ v, f x v ≤ M) :
    ∑ x ∈ T, ∫ v in cell x, f x v * ‖v - y‖ ^ (1 - (d : ℝ)) ≤
      M * (d * CERW.unitBallVolume d * ρ₀) := by
  obtain ⟨hint, hval⟩ := CERW.Generic.Kernel.integrableOn_ball_and_integral_eq hd y hρ₀
  have hK0 : ∀ v : EuclideanSpace ℝ (Fin d), 0 ≤ ‖v - y‖ ^ (1 - (d : ℝ)) :=
    fun v => Real.rpow_nonneg (norm_nonneg _) _
  have hMK : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => M * ‖v - y‖ ^ (1 - (d : ℝ)))
      (Metric.ball y ρ₀) := hint.const_mul M
  have hdisj : Set.PairwiseDisjoint (↑T : Set (Site d)) cell :=
    fun x _ x' _ hxx' => cell_disjoint hxx'
  calc ∑ x ∈ T, ∫ v in cell x, f x v * ‖v - y‖ ^ (1 - (d : ℝ))
      ≤ ∑ x ∈ T, ∫ v in cell x, M * ‖v - y‖ ^ (1 - (d : ℝ)) := by
        refine Finset.sum_le_sum fun x hx => ?_
        refine setIntegral_mono_of_nonneg (fun v _ => mul_nonneg (hf0 x hx v) (hK0 v))
          (fun v _ => mul_le_mul_of_nonneg_right (hfM x hx v) (hK0 v)) ?_
        exact hMK.mono_set (hT x hx)
    _ = ∫ v in ⋃ x ∈ T, cell x, M * ‖v - y‖ ^ (1 - (d : ℝ)) :=
        (integral_biUnion_finset T (fun x _ => measurableSet_cell x) hdisj
          (fun x hx => hMK.mono_set (hT x hx))).symm
    _ ≤ ∫ v in Metric.ball y ρ₀, M * ‖v - y‖ ^ (1 - (d : ℝ)) := by
        refine setIntegral_mono_set hMK (Eventually.of_forall fun v => mul_nonneg hM (hK0 v)) ?_
        exact (Set.iUnion₂_subset hT).eventuallyLE
    _ = M * (d * CERW.unitBallVolume d * ρ₀) := by rw [integral_const_mul, hval]

/-- The number of sites of a finite set within distance `A` of a point `v` is at most the volume
of the ball of radius `A + √d / 2`: the corresponding unit cells are disjoint and lie in it. -/
private lemma card_filter_le (T : Finset (Site d)) (v : EuclideanSpace ℝ (Fin d)) (A : ℝ) :
    ((T.filter (fun x => ‖v - toSpace x‖ < A)).card : ℝ) ≤
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (A + Real.sqrt d / 2))).toReal := by
  set T' := T.filter (fun x => ‖v - toSpace x‖ < A) with hT'
  have hdisj : Set.PairwiseDisjoint (↑T' : Set (Site d)) cell :=
    fun x _ x' _ hxx' => cell_disjoint hxx'
  have hunion : (⋃ x ∈ T', cell x) ⊆ Metric.ball v (A + Real.sqrt d / 2) := by
    refine Set.iUnion₂_subset fun x hx w hw => ?_
    have hxA : ‖v - toSpace x‖ < A := (Finset.mem_filter.mp hx).2
    have hw' := norm_sub_toSpace_le_of_mem_cell hw
    rw [mem_ball_iff_norm]
    calc ‖w - v‖ = ‖(w - toSpace x) + (toSpace x - v)‖ := by congr 1; abel
      _ ≤ ‖w - toSpace x‖ + ‖toSpace x - v‖ := norm_add_le _ _
      _ < A + Real.sqrt d / 2 := by rw [norm_sub_rev (toSpace x) v]; linarith
  have hsum : (T'.card : ENNReal) =
      volume (⋃ x ∈ T', cell x) := by
    rw [measure_biUnion_finset hdisj (fun x _ => measurableSet_cell x)]
    simp [volume_cell]
  have hle : (T'.card : ENNReal) ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d))
      (A + Real.sqrt d / 2)) := by
    rw [hsum, ← Measure.addHaar_ball_center volume v]
    exact measure_mono hunion
  have := ENNReal.toReal_mono measure_ball_lt_top.ne hle
  simpa using this

/-- Geometry of the far bump: if `m ≥ 1` and `t ≤ m + A` then
`m^{-2p} ≤ (1 + (1 + A)²)^p (1 + t²)^{-p}`. -/
private lemma rpow_le_bump {p m t A : ℝ} (hp : 0 ≤ p) (hA : 0 ≤ A) (hm : 1 ≤ m) (ht : 0 ≤ t)
    (htm : t ≤ m + A) :
    m ^ (-(2 * p)) ≤ (1 + (1 + A) ^ 2) ^ p * (1 + t ^ 2) ^ (-p) := by
  have hm0 : 0 < m := by linarith
  have hb : 0 < 1 + (1 + A) ^ 2 := by positivity
  have h1 : t ≤ (1 + A) * m := by nlinarith
  have h2 : 1 + t ^ 2 ≤ (1 + (1 + A) ^ 2) * m ^ 2 := by
    have h3 : t ^ 2 ≤ ((1 + A) * m) ^ 2 := pow_le_pow_left₀ ht h1 2
    nlinarith
  have h4 : ((1 + (1 + A) ^ 2) * m ^ 2) ^ (-p) ≤ (1 + t ^ 2) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
  have h5 : ((1 + (1 + A) ^ 2) * m ^ 2) ^ (-p) =
      ((1 + (1 + A) ^ 2) ^ p)⁻¹ * m ^ (-(2 * p)) := by
    have h6 : (m ^ 2) ^ (-p) = m ^ (-(2 * p)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
      congr 1
      push_cast
      ring
    rw [Real.mul_rpow hb.le (by positivity), Real.rpow_neg hb.le, h6]
  have hbp : 0 < (1 + (1 + A) ^ 2) ^ p := Real.rpow_pos_of_pos hb _
  rw [h5] at h4
  calc m ^ (-(2 * p)) = (1 + (1 + A) ^ 2) ^ p * (((1 + (1 + A) ^ 2) ^ p)⁻¹ * m ^ (-(2 * p))) := by
        field_simp
    _ ≤ (1 + (1 + A) ^ 2) ^ p * (1 + t ^ 2) ^ (-p) := mul_le_mul_of_nonneg_left h4 hbp.le

/-- A pointwise bound on a weighted sum of translated bumps over sites at distance at least `1`
from `y`: at most `N c M₀ b^p (1 + |v - y|²)^{-p}`, where `N` bounds the number of sites within
distance `A` of a point. -/
private lemma sum_translate_le {φ₀ : EuclideanSpace ℝ (Fin d) → ℝ} {A M₀ c : ℝ} (hd : 1 ≤ d)
    (hA : 0 < A) (hφ0 : ∀ v, 0 ≤ φ₀ v) (hM₀ : ∀ v, φ₀ v ≤ M₀)
    (hsupp : ∀ v, A ≤ ‖v‖ → φ₀ v = 0) (hc : 0 ≤ c) (y : EuclideanSpace ℝ (Fin d))
    (T : Finset (Site d)) (hT : ∀ x ∈ T, 1 ≤ ‖toSpace x - y‖) (v : EuclideanSpace ℝ (Fin d)) :
    ∑ x ∈ T, c * ‖toSpace x - y‖ ^ (1 - (d : ℝ)) * φ₀ (v - toSpace x) ≤
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (A + Real.sqrt d / 2))).toReal *
        (c * M₀ * (1 + (1 + A) ^ 2) ^ (((d : ℝ) - 1) / 2)) *
          (1 + ‖v - y‖ ^ 2) ^ (-(((d : ℝ) - 1) / 2)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set p : ℝ := ((d : ℝ) - 1) / 2 with hpdef
  have hp : 0 ≤ p := by rw [hpdef]; linarith
  have hM0 : 0 ≤ M₀ := (hφ0 0).trans (hM₀ 0)
  have hbd : 0 ≤ c * M₀ * (1 + (1 + A) ^ 2) ^ p * (1 + ‖v - y‖ ^ 2) ^ (-p) :=
    mul_nonneg (mul_nonneg (mul_nonneg hc hM0) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by positivity) _)
  have hexp : (1 - (d : ℝ)) = -(2 * p) := by rw [hpdef]; ring
  rw [← Finset.sum_filter_of_ne (p := fun x => ‖v - toSpace x‖ < A)]
  · calc ∑ x ∈ T.filter (fun x => ‖v - toSpace x‖ < A),
          c * ‖toSpace x - y‖ ^ (1 - (d : ℝ)) * φ₀ (v - toSpace x)
        ≤ (T.filter (fun x => ‖v - toSpace x‖ < A)).card •
            (c * M₀ * (1 + (1 + A) ^ 2) ^ p * (1 + ‖v - y‖ ^ 2) ^ (-p)) := by
          refine Finset.sum_le_card_nsmul _ _ _ fun x hx => ?_
          obtain ⟨hxT, hxA⟩ := Finset.mem_filter.mp hx
          have hm := hT x hxT
          have ht : ‖v - y‖ ≤ ‖toSpace x - y‖ + A := by
            calc ‖v - y‖ = ‖(v - toSpace x) + (toSpace x - y)‖ := by congr 1; abel
              _ ≤ ‖v - toSpace x‖ + ‖toSpace x - y‖ := norm_add_le _ _
              _ ≤ ‖toSpace x - y‖ + A := by linarith
          have hk := rpow_le_bump hp hA.le hm (norm_nonneg _) ht
          rw [hexp]
          calc c * ‖toSpace x - y‖ ^ (-(2 * p)) * φ₀ (v - toSpace x)
              ≤ c * ‖toSpace x - y‖ ^ (-(2 * p)) * M₀ :=
                mul_le_mul_of_nonneg_left (hM₀ _)
                  (mul_nonneg hc (Real.rpow_nonneg (by linarith) _))
            _ ≤ c * ((1 + (1 + A) ^ 2) ^ p * (1 + ‖v - y‖ ^ 2) ^ (-p)) * M₀ := by
                gcongr
            _ = c * M₀ * (1 + (1 + A) ^ 2) ^ p * (1 + ‖v - y‖ ^ 2) ^ (-p) := by ring
      _ = ((T.filter (fun x => ‖v - toSpace x‖ < A)).card : ℝ) *
            (c * M₀ * (1 + (1 + A) ^ 2) ^ p * (1 + ‖v - y‖ ^ 2) ^ (-p)) := nsmul_eq_mul _ _
      _ ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d))
            (A + Real.sqrt d / 2))).toReal *
            (c * M₀ * (1 + (1 + A) ^ 2) ^ p * (1 + ‖v - y‖ ^ 2) ^ (-p)) :=
          mul_le_mul_of_nonneg_right (card_filter_le T v A) hbd
      _ = _ := by ring
  · intro x _ hne
    by_contra hlt
    exact hne (by rw [hsupp (v - toSpace x) (not_lt.mp hlt), mul_zero])

/-- For a site at distance at least `2√d` from `y`, every point of its cell is at distance at
least half that from `y`. -/
private lemma half_le_dist_of_mem_cell {x : Site d} {v y : EuclideanSpace ℝ (Fin d)}
    (hx : 2 * Real.sqrt d ≤ ‖toSpace x - y‖) (hv : v ∈ cell x) :
    ‖toSpace x - y‖ / 2 ≤ ‖v - y‖ := by
  have h1 := norm_sub_toSpace_le_of_mem_cell hv
  have h2 : ‖toSpace x - y‖ ≤ ‖v - toSpace x‖ + ‖v - y‖ := by
    calc ‖toSpace x - y‖ = ‖(toSpace x - v) + (v - y)‖ := by congr 1; abel
      _ ≤ ‖toSpace x - v‖ + ‖v - y‖ := norm_add_le _ _
      _ = ‖v - toSpace x‖ + ‖v - y‖ := by rw [norm_sub_rev (toSpace x) v]
  have h3 := Real.sqrt_nonneg (d : ℝ)
  linarith

/-- The Newtonian kernel on a far cell is comparable to its value at the cell's site. -/
private lemma kernel_le_of_far {x : Site d} {v y : EuclideanSpace ℝ (Fin d)}
    (hd : 1 ≤ d) (hx : 2 * Real.sqrt d ≤ ‖toSpace x - y‖) (hv : v ∈ cell x) :
    ‖v - y‖ ^ (1 - (d : ℝ)) ≤ (2 : ℝ) ^ ((d : ℝ) - 1) * ‖toSpace x - y‖ ^ (1 - (d : ℝ)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by linarith)
  have hm : 0 < ‖toSpace x - y‖ := by linarith
  have hhalf := half_le_dist_of_mem_cell hx hv
  have h1 : ‖v - y‖ ^ (1 - (d : ℝ)) ≤ (‖toSpace x - y‖ / 2) ^ (1 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (by linarith)
  have h2 : (2 : ℝ) ^ (1 - (d : ℝ)) = ((2 : ℝ) ^ ((d : ℝ) - 1))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  rw [Real.div_rpow hm.le (by norm_num), h2, div_inv_eq_mul, mul_comm] at h1
  exact h1

/-- A bounded multiple of `|∇Ψ - ξ|` is integrable on a cell. -/
private lemma integrableOn_cell_norm_sub {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (hd : 1 ≤ d) {ξ : EuclideanSpace ℝ (Fin d)} (hξ : ‖ξ‖ ≤ normMax Ψ) (x : Site d) (c : ℝ) :
    IntegrableOn (fun v => c * ‖gradient Ψ v - ξ‖) (cell x) := by
  refine Measure.integrableOn_of_bounded (M := |c| * (2 * normMax Ψ))
    (by rw [volume_cell]; exact ENNReal.one_ne_top) ?_ ?_
  · exact (((measurable_gradient Ψ).sub_const ξ).norm.const_mul c).aestronglyMeasurable
  · refine Eventually.of_forall fun v => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left (norm_gradient_sub_le hΨ hd hξ v) (abs_nonneg c)

/-- Far sites: the weighted integral over a far cell is at most `2^{d-1} |x - y|^{1-d}` times the
unweighted integral bound. -/
private lemma far_cell_integral_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (hd : 1 ≤ d) {ξ : EuclideanSpace ℝ (Fin d)} (hξ : ‖ξ‖ ≤ normMax Ψ) {x : Site d}
    {y : EuclideanSpace ℝ (Fin d)} (hx : 2 * Real.sqrt d ≤ ‖toSpace x - y‖) {B : ℝ}
    (hB : ∫ v in cell x, ‖gradient Ψ v - ξ‖ ≤ B) :
    ∫ v in cell x, ‖gradient Ψ v - ξ‖ * ‖v - y‖ ^ (1 - (d : ℝ)) ≤
      (2 : ℝ) ^ ((d : ℝ) - 1) * ‖toSpace x - y‖ ^ (1 - (d : ℝ)) * B := by
  have hw : 0 ≤ (2 : ℝ) ^ ((d : ℝ) - 1) * ‖toSpace x - y‖ ^ (1 - (d : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (norm_nonneg _) _)
  calc ∫ v in cell x, ‖gradient Ψ v - ξ‖ * ‖v - y‖ ^ (1 - (d : ℝ))
      ≤ ∫ v in cell x, ((2 : ℝ) ^ ((d : ℝ) - 1) * ‖toSpace x - y‖ ^ (1 - (d : ℝ))) *
          ‖gradient Ψ v - ξ‖ := by
        refine setIntegral_mono_of_nonneg
          (fun v _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
          (fun v hv => ?_) (integrableOn_cell_norm_sub hΨ hd hξ x _)
        calc ‖gradient Ψ v - ξ‖ * ‖v - y‖ ^ (1 - (d : ℝ))
            ≤ ‖gradient Ψ v - ξ‖ * ((2 : ℝ) ^ ((d : ℝ) - 1) * ‖toSpace x - y‖ ^ (1 - (d : ℝ))) :=
              mul_le_mul_of_nonneg_left (kernel_le_of_far hd hx hv) (norm_nonneg _)
          _ = _ := mul_comm _ _
    _ = (2 : ℝ) ^ ((d : ℝ) - 1) * ‖toSpace x - y‖ ^ (1 - (d : ℝ)) *
          ∫ v in cell x, ‖gradient Ψ v - ξ‖ := integral_const_mul _ _
    _ ≤ (2 : ℝ) ^ ((d : ℝ) - 1) * ‖toSpace x - y‖ ^ (1 - (d : ℝ)) * B :=
        mul_le_mul_of_nonneg_left hB hw

/-- Translates of a bump are test functions. -/
private lemma isTest_translate {φ₀ : EuclideanSpace ℝ (Fin d) → ℝ} {A : ℝ}
    (hφsm : ContDiff ℝ ∞ φ₀) (hφsupp : ∀ v, A ≤ ‖v‖ → φ₀ v = 0) (x : Site d) :
    IsTest (fun w => φ₀ (w - toSpace x)) := by
  refine ⟨hφsm.comp (contDiff_id.sub contDiff_const), ?_⟩
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (toSpace x) A) ?_
  intro v hv
  by_contra hnot
  rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hnot
  exact hv (hφsupp _ hnot.le)

/-- The far sum is at most the negative pairing of `∇Ψ` with the weighted sum of bumps. -/
private lemma far_sum_le_neg_pairing {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (hd : 1 ≤ d) {φ₀ : EuclideanSpace ℝ (Fin d) → ℝ} {A Cc : ℝ} (hφsm : ContDiff ℝ ∞ φ₀)
    (hφsupp : ∀ v, A ≤ ‖v‖ → φ₀ v = 0) {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξb : ∀ x, ‖ξ x‖ ≤ normMax Ψ)
    (hcellb : ∀ x : Site d, ∫ v in cell x, ‖gradient Ψ v - ξ x‖ ≤
      Cc * (-∫ v, inner ℝ (gradient Ψ v) (gradient (fun w => φ₀ (w - toSpace x)) v)))
    (y : EuclideanSpace ℝ (Fin d)) (T : Finset (Site d))
    (hT : ∀ x ∈ T, 2 * Real.sqrt d ≤ ‖toSpace x - y‖) :
    ∑ x ∈ T, ∫ v in cell x, ‖gradient Ψ v - ξ x‖ * ‖v - y‖ ^ (1 - (d : ℝ)) ≤
      -pairing Ψ (fun v => ∑ x ∈ T,
        ((2 : ℝ) ^ ((d : ℝ) - 1) * Cc * ‖toSpace x - y‖ ^ (1 - (d : ℝ))) *
          φ₀ (v - toSpace x)) := by
  rw [pairing_sum hΨ hd T _ (fun x w => φ₀ (w - toSpace x))
    (fun x _ => isTest_translate hφsm hφsupp x), ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun x hx => ?_
  calc ∫ v in cell x, ‖gradient Ψ v - ξ x‖ * ‖v - y‖ ^ (1 - (d : ℝ))
      ≤ (2 : ℝ) ^ ((d : ℝ) - 1) * ‖toSpace x - y‖ ^ (1 - (d : ℝ)) *
          (Cc * (-∫ v, inner ℝ (gradient Ψ v) (gradient (fun w => φ₀ (w - toSpace x)) v))) :=
        far_cell_integral_le hΨ hd (hξb x) (hT x hx) (hcellb x)
    _ = -((2 : ℝ) ^ ((d : ℝ) - 1) * Cc * ‖toSpace x - y‖ ^ (1 - (d : ℝ)) *
          pairing Ψ (fun w => φ₀ (w - toSpace x))) := by
        unfold pairing
        ring

/-- The negative pairing of `∇Ψ` with a weighted sum of bumps over far sites is logarithmic:
the sum is dominated by a radial majorant, and `∇Ψ` pairs positively with the difference. -/
private lemma neg_pairing_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hd : 1 ≤ d) (hΨ : IsNorm Ψ)
    (hpos : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ v, 0 ≤ φ v) → ∫ v, inner ℝ (gradient Ψ v) (gradient φ v) ≤ 0)
    {φ₀ : EuclideanSpace ℝ (Fin d) → ℝ} {A M₀ c c₃ R : ℝ} (hφsm : ContDiff ℝ ∞ φ₀)
    (hφnn : ∀ v, 0 ≤ φ₀ v) (hA : 0 < A) (hφsupp : ∀ v, A ≤ ‖v‖ → φ₀ v = 0)
    (hM₀ : ∀ v, φ₀ v ≤ M₀) (hc : 0 ≤ c) (hR : 1 ≤ R)
    (hmaj : ∀ (y : EuclideanSpace ℝ (Fin d)) (ρ : ℝ), 1 ≤ ρ →
      ∃ Θ : EuclideanSpace ℝ (Fin d) → ℝ, IsTest Θ ∧ (∀ v, 0 ≤ Θ v) ∧
        (∀ v, ‖v - y‖ ≤ ρ → Θ v = (1 + ‖v - y‖ ^ 2) ^ (-(((d : ℝ) - 1) / 2))) ∧
        ∫ v, ‖gradient Θ v‖ ≤ c₃ * Real.log (2 * ρ + 2))
    (y : EuclideanSpace ℝ (Fin d)) (T : Finset (Site d))
    (hT : ∀ x ∈ T, 1 ≤ ‖toSpace x - y‖ ∧ ‖toSpace x - y‖ < 3 * R) :
    -pairing Ψ (fun v => ∑ x ∈ T, (c * ‖toSpace x - y‖ ^ (1 - (d : ℝ))) * φ₀ (v - toSpace x)) ≤
      normMax Ψ * ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d))
        (A + Real.sqrt d / 2))).toReal * (c * M₀ * (1 + (1 + A) ^ 2) ^ (((d : ℝ) - 1) / 2))) *
        (c₃ * Real.log (2 * (3 * R + A) + 2)) := by
  have hρ : 1 ≤ 3 * R + A := by linarith
  obtain ⟨Θ, hΘt, hΘnn, hΘeq, hΘint⟩ := hmaj y (3 * R + A) hρ
  set c₁ : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d))
      (A + Real.sqrt d / 2))).toReal * (c * M₀ * (1 + (1 + A) ^ 2) ^ (((d : ℝ) - 1) / 2)) with hc₁
  have hM0 : 0 ≤ M₀ := (hφnn 0).trans (hM₀ 0)
  have hc₁ : 0 ≤ c₁ :=
    mul_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (mul_nonneg hc hM0) (Real.rpow_nonneg (by positivity) _))
  have hΦt : IsTest (fun v => ∑ x ∈ T, (c * ‖toSpace x - y‖ ^ (1 - (d : ℝ))) *
      φ₀ (v - toSpace x)) :=
    IsTest.sum T _ (fun x w => φ₀ (w - toSpace x)) fun x _ => isTest_translate hφsm hφsupp x
  have hdom : ∀ v, ∑ x ∈ T, (c * ‖toSpace x - y‖ ^ (1 - (d : ℝ))) * φ₀ (v - toSpace x) ≤
      c₁ * Θ v := by
    intro v
    by_cases hv : ‖v - y‖ ≤ 3 * R + A
    · rw [hΘeq v hv]
      exact sum_translate_le hd hA hφnn hM₀ hφsupp hc y T (fun x hx => (hT x hx).1) v
    · have hzero : ∀ x ∈ T, (c * ‖toSpace x - y‖ ^ (1 - (d : ℝ))) * φ₀ (v - toSpace x) = 0 := by
        intro x hx
        have hlt : A ≤ ‖v - toSpace x‖ := by
          by_contra hlt
          apply hv
          calc ‖v - y‖ = ‖(v - toSpace x) + (toSpace x - y)‖ := by congr 1; abel
            _ ≤ ‖v - toSpace x‖ + ‖toSpace x - y‖ := norm_add_le _ _
            _ ≤ 3 * R + A := by linarith [not_le.mp hlt, (hT x hx).2]
        rw [hφsupp _ hlt, mul_zero]
      rw [Finset.sum_eq_zero hzero]
      exact mul_nonneg hc₁ (hΘnn v)
  have hnn : ∀ v, 0 ≤ c₁ * Θ v - ∑ x ∈ T, (c * ‖toSpace x - y‖ ^ (1 - (d : ℝ))) *
      φ₀ (v - toSpace x) := fun v => sub_nonneg.mpr (hdom v)
  have hdiff := hΘt.const_mul c₁ |>.sub hΦt
  have h0 := hpos _ hdiff.1 hdiff.2 hnn
  have h1 : pairing Ψ (fun v => c₁ * Θ v - ∑ x ∈ T, (c * ‖toSpace x - y‖ ^ (1 - (d : ℝ))) *
      φ₀ (v - toSpace x)) ≤ 0 := h0
  rw [pairing_sub hΨ hd (hΘt.const_mul c₁) hΦt, pairing_const_mul c₁ hΘt] at h1
  have h2 := hΘt.abs_pairing_le hΨ hd
  have h3 : |pairing Ψ Θ| ≤ normMax Ψ * (c₃ * Real.log (2 * (3 * R + A) + 2)) :=
    h2.trans (mul_le_mul_of_nonneg_left hΘint (normMax_nonneg hΨ hd))
  calc _ ≤ -(c₁ * pairing Ψ Θ) := by linarith
    _ ≤ c₁ * |pairing Ψ Θ| := by
        rw [← mul_neg]
        exact mul_le_mul_of_nonneg_left (neg_le_abs _) hc₁
    _ ≤ c₁ * (normMax Ψ * (c₃ * Real.log (2 * (3 * R + A) + 2))) :=
        mul_le_mul_of_nonneg_left h3 hc₁
    _ = _ := by ring

/-- **The Bregman sum bound (†).** For a weakly subharmonic norm `Ψ` on `ℝ^d` (`d ≥ 2`) satisfying
the per-cell test bound, the weighted `L¹` distance `Σ_{x ∈ S} ∫_{C_x} |∇Ψ - ξ(x)| |v - y|^{1-d}`
between the gradient and a subgradient selection, over any finite set of cells in `B(0, R)`, is at
most `C log (R + 2)`. -/
theorem bregmanSumBound_of {d : ℕ} (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (hpos : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ v, 0 ≤ φ v) → ∫ v, inner ℝ (gradient Ψ v) (gradient φ v) ≤ 0)
    (hcell : CERW.Support.Norm.ContactShared.CellTestBound d Ψ) :
    CERW.Support.Norm.ContactShared.BregmanSumBound d Ψ := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  obtain ⟨φ₀, A, Cc, hφsm, hφcs, hφnn, hA, hφsupp, hCc, hcellb⟩ := hcell
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, ∀ v, φ₀ v ≤ M₀ := by
    obtain ⟨M, hM⟩ := hφsm.continuous.bounded_above_of_compact_support hφcs
    exact ⟨M, fun v => (le_abs_self _).trans (by simpa using hM v)⟩
  obtain ⟨c₃, hc₃, hmaj⟩ := exists_majorant hd
  have hΛ : 0 ≤ normMax Ψ := normMax_nonneg hΨ hd1
  have hω : 0 < CERW.unitBallVolume d := CERW.unitBallVolume_pos d
  have hs1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hdR
  have hM0 : 0 ≤ M₀ := (hφnn 0).trans (hM₀ 0)
  have hlogM : 0 ≤ Real.log (6 + 2 * A) := Real.log_nonneg (by linarith)
  set c : ℝ := (2 : ℝ) ^ ((d : ℝ) - 1) * Cc with hcdef
  have hc : 0 ≤ c := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hCc
  set c₁ : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d))
      (A + Real.sqrt d / 2))).toReal * (c * M₀ * (1 + (1 + A) ^ 2) ^ (((d : ℝ) - 1) / 2))
    with hc₁def
  have hc₁ : 0 ≤ c₁ :=
    mul_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (mul_nonneg hc hM0) (Real.rpow_nonneg (by positivity) _))
  have hnearC : 0 ≤ 2 * normMax Ψ * (d * CERW.unitBallVolume d * (3 * Real.sqrt d)) := by
    positivity
  have hfarC : 0 ≤ normMax Ψ * c₁ * c₃ * (Real.log (6 + 2 * A) + 1) := by positivity
  refine ⟨2 * normMax Ψ * (d * CERW.unitBallVolume d * (3 * Real.sqrt d)) +
    normMax Ψ * c₁ * c₃ * (Real.log (6 + 2 * A) + 1), add_nonneg hnearC hfarC, ?_⟩
  intro ξ hξ hξ0 S y R hR hS hy
  have hξb : ∀ x, ‖ξ x‖ ≤ normMax Ψ := by
    intro x
    by_cases hx : x = 0
    · rw [hx, hξ0, norm_zero]
      exact hΛ
    · exact norm_subgradient_le hΨ hd1 (hξ x hx)
  have hxR : ∀ x ∈ S, ‖toSpace x - y‖ < 3 * R := by
    intro x hx
    have h1 : toSpace x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R :=
      hS x hx (toSpace_mem_cell x)
    rw [mem_ball_zero_iff] at h1
    calc ‖toSpace x - y‖ ≤ ‖toSpace x‖ + ‖y‖ := norm_sub_le _ _
      _ < 3 * R := by linarith
  have hL : 1 ≤ Real.log (R + 2) := by
    have h3 : Real.exp 1 < R + 2 := by
      have := Real.exp_one_lt_d9
      linarith
    exact ((Real.lt_log_iff_exp_lt (by linarith)).mpr h3).le
  rw [← Finset.sum_filter_add_sum_filter_not S (fun x => ‖toSpace x - y‖ < 2 * Real.sqrt d)]
  have hnear : ∑ x ∈ S.filter (fun x => ‖toSpace x - y‖ < 2 * Real.sqrt d),
      ∫ v in cell x, ‖gradient Ψ v - ξ x‖ * ‖v - y‖ ^ (1 - (d : ℝ)) ≤
        2 * normMax Ψ * (d * CERW.unitBallVolume d * (3 * Real.sqrt d)) := by
    refine sum_cells_kernel_le hd1 _ y (by positivity) (by positivity) ?_
      (fun x v => ‖gradient Ψ v - ξ x‖) (fun x _ v => norm_nonneg _)
      (fun x _ v => norm_gradient_sub_le hΨ hd1 (hξb x) v)
    intro x hx w hw
    have hxP := (Finset.mem_filter.mp hx).2
    have hw' := norm_sub_toSpace_le_of_mem_cell hw
    rw [mem_ball_iff_norm]
    calc ‖w - y‖ = ‖(w - toSpace x) + (toSpace x - y)‖ := by congr 1; abel
      _ ≤ ‖w - toSpace x‖ + ‖toSpace x - y‖ := norm_add_le _ _
      _ < 3 * Real.sqrt d := by linarith
  have hfar : ∑ x ∈ S.filter (fun x => ¬ ‖toSpace x - y‖ < 2 * Real.sqrt d),
      ∫ v in cell x, ‖gradient Ψ v - ξ x‖ * ‖v - y‖ ^ (1 - (d : ℝ)) ≤
        normMax Ψ * c₁ * (c₃ * Real.log (2 * (3 * R + A) + 2)) := by
    have hT : ∀ x ∈ S.filter (fun x => ¬ ‖toSpace x - y‖ < 2 * Real.sqrt d),
        2 * Real.sqrt d ≤ ‖toSpace x - y‖ := fun x hx => not_lt.mp (Finset.mem_filter.mp hx).2
    refine (far_sum_le_neg_pairing hΨ hd1 hφsm hφsupp hξb (fun x => hcellb ξ hξ hξ0 x) y _
      hT).trans ?_
    refine neg_pairing_le hd1 hΨ hpos hφsm hφnn hA hφsupp hM₀ hc hR hmaj y _ fun x hx => ?_
    obtain ⟨hxS, hxP⟩ := Finset.mem_filter.mp hx
    exact ⟨by linarith [not_lt.mp hxP], hxR x hxS⟩
  have hlog : Real.log (2 * (3 * R + A) + 2) ≤ (Real.log (6 + 2 * A) + 1) * Real.log (R + 2) := by
    have hAR : 0 ≤ A * R := mul_nonneg hA.le (by linarith)
    have hle : 2 * (3 * R + A) + 2 ≤ (6 + 2 * A) * (R + 2) := by linarith
    calc Real.log (2 * (3 * R + A) + 2) ≤ Real.log ((6 + 2 * A) * (R + 2)) :=
          Real.log_le_log (by linarith) hle
      _ = Real.log (6 + 2 * A) + Real.log (R + 2) :=
          Real.log_mul (by linarith) (by linarith)
      _ ≤ (Real.log (6 + 2 * A) + 1) * Real.log (R + 2) := by
          have := mul_le_mul_of_nonneg_left hL hlogM
          linarith
  have hfar' : normMax Ψ * c₁ * (c₃ * Real.log (2 * (3 * R + A) + 2)) ≤
      normMax Ψ * c₁ * c₃ * (Real.log (6 + 2 * A) + 1) * Real.log (R + 2) := by
    calc normMax Ψ * c₁ * (c₃ * Real.log (2 * (3 * R + A) + 2))
        ≤ normMax Ψ * c₁ * (c₃ * ((Real.log (6 + 2 * A) + 1) * Real.log (R + 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hc₃)
            (mul_nonneg hΛ hc₁)
      _ = _ := by ring
  calc _ ≤ 2 * normMax Ψ * (d * CERW.unitBallVolume d * (3 * Real.sqrt d)) +
        normMax Ψ * c₁ * c₃ * (Real.log (6 + 2 * A) + 1) * Real.log (R + 2) :=
        add_le_add hnear (hfar.trans hfar')
    _ ≤ 2 * normMax Ψ * (d * CERW.unitBallVolume d * (3 * Real.sqrt d)) * Real.log (R + 2) +
        normMax Ψ * c₁ * c₃ * (Real.log (6 + 2 * A) + 1) * Real.log (R + 2) :=
        add_le_add (le_mul_of_one_le_right hnearC hL) le_rfl
    _ = _ := by ring

end CERW.Support.Norm.ContactBregman

namespace CERW.Support.Norm.ContactConv

open CERW CERW.Generic.Kernel CERW.Generic.Norm CERW.Generic.Newton
  CERW.Support.Geometry CERW.Support.Statements

variable {d : ℕ}

/-- A measurable field weighted by the Newtonian kernel has a measurable integrand. -/
private lemma measurable_fieldIntegrand {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hg : Measurable g) (y : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun v : EuclideanSpace ℝ (Fin d) => inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) := by
  have hsub : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v - y) :=
    measurable_id.sub measurable_const
  exact (hg.inner hsub).div (hsub.norm.pow_const d)

/-- The integrand of the field potential is at most `Λ` times the Newtonian kernel `|v - y|^{1-d}`
when the field has norm at most `Λ`. -/
private lemma abs_fieldIntegrand_le {Λ : ℝ} {ξ : EuclideanSpace ℝ (Fin d)} (hξ : ‖ξ‖ ≤ Λ)
    (v y : EuclideanSpace ℝ (Fin d)) :
    |inner ℝ ξ (v - y) / ‖v - y‖ ^ d| ≤ Λ * ‖v - y‖ ^ (1 - (d : ℝ)) := by
  have hΛ : 0 ≤ Λ := (norm_nonneg ξ).trans hξ
  rcases eq_or_ne v y with rfl | hne
  · simp only [sub_self, inner_zero_right, zero_div, abs_zero]
    exact mul_nonneg hΛ (Real.rpow_nonneg (norm_nonneg _) _)
  · have hw : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hden : 0 < ‖v - y‖ ^ d := pow_pos hw d
    have h1 : |inner ℝ ξ (v - y)| ≤ ‖ξ‖ * ‖v - y‖ := abs_real_inner_le_norm _ _
    have h2 : ‖ξ‖ * ‖v - y‖ ≤ Λ * ‖v - y‖ := mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
    calc |inner ℝ ξ (v - y) / ‖v - y‖ ^ d|
        = |inner ℝ ξ (v - y)| / ‖v - y‖ ^ d := by rw [abs_div, abs_of_nonneg hden.le]
      _ ≤ (Λ * ‖v - y‖) / ‖v - y‖ ^ d :=
          div_le_div_of_nonneg_right (h1.trans h2) hden.le
      _ = Λ * ‖v - y‖ ^ (1 - (d : ℝ)) := by
          rw [mul_div_assoc, div_pow_eq_rpow_sub hw d]

/-- On a set of finite volume the integrand of a bounded measurable field potential is
integrable. -/
private lemma integrableOn_fieldIntegrand (hd : 1 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) D := by
  obtain ⟨hint, _⟩ := integrableOn_and_setIntegral_le (d := d) hd hD hDfin y
  refine (hint.const_mul Λ).mono' (measurable_fieldIntegrand hg y).aestronglyMeasurable ?_
  filter_upwards with v
  rw [Real.norm_eq_abs]
  exact abs_fieldIntegrand_le (hΛ v) v y


/-- A linear isometry of `ℝ^d` acts on the Euclidean unit sphere. -/
private noncomputable def sphereMap (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
  ⟨A θ, by simp⟩

/-- The action of a linear isometry on the unit sphere is measurable. -/
private lemma measurable_sphereMap (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Measurable (sphereMap A) :=
  ((A.continuous.comp continuous_subtype_val).subtype_mk _).measurable

/-- Surface measure on the unit sphere is invariant under linear isometries. -/
private lemma map_sphereMap_toSphere
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Measure.map (sphereMap A) (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  ext S hS
  rw [Measure.map_apply (measurable_sphereMap A) hS,
    Measure.toSphere_apply' _ ((measurable_sphereMap A) hS), Measure.toSphere_apply' _ hS]
  congr 1
  have hset : Set.Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap A ⁻¹' S) : Set (EuclideanSpace ℝ (Fin d))) =
      A ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' S)) := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨t, ht, _, ⟨θ, hθ, rfl⟩, rfl⟩
      refine ⟨t, ht, _, ⟨sphereMap A θ, hθ, rfl⟩, ?_⟩
      simp [sphereMap]
    · rintro ⟨t, ht, _, ⟨θ, hθ, rfl⟩, h⟩
      refine ⟨t, ht, _, ⟨⟨A.symm θ, by simp⟩, ?_, rfl⟩, ?_⟩
      · simpa [sphereMap] using hθ
      · have h' : t • (θ : EuclideanSpace ℝ (Fin d)) = A x := h
        show t • A.symm (θ : EuclideanSpace ℝ (Fin d)) = x
        rw [← A.symm.map_smul, h', A.symm_apply_apply]
  rw [hset]
  exact (LinearIsometryEquiv.measurePreserving A).measure_preimage_equiv
    (f := A.toMeasurableEquiv) _

/-- Integrals over the unit sphere are invariant under linear isometries. -/
private lemma integral_sphereMap (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    {f : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ} (hf : Measurable f) :
    ∫ θ, f (sphereMap A θ) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      ∫ θ, f θ ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  have h := integral_map (measurable_sphereMap A).aemeasurable
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) (f := f)
    (by rw [map_sphereMap_toSphere]; exact hf.aestronglyMeasurable)
  rw [map_sphereMap_toSphere] at h
  exact h.symm

/-- The Newtonian field commutes with linear isometries. -/
private lemma newtonField_map (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : newtonField (A x) = A (newtonField x) := by
  simp only [newtonField, A.norm_map, LinearIsometryEquiv.map_smul]

/-- The sphere integrand `θ ↦ ⟨ξ, K(v - sθ)⟩` is measurable. -/
private lemma measurable_inner_newtonField (ξ v : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    Measurable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))) :=
  measurable_const.inner (measurable_newtonField.comp
    (measurable_const.sub (measurable_subtype_coe.const_smul s)))

/-- The component of the spherical average of the Newtonian field orthogonal to `v` vanishes:
a reflection fixing `v` and reversing `w ⟂ v` preserves surface measure. -/
private lemma integral_sphere_inner_newtonField_perp {v w : EuclideanSpace ℝ (Fin d)}
    (hvw : inner ℝ w v = 0) (s : ℝ) :
    ∫ θ, inner ℝ w (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere = 0 := by
  set R := Submodule.reflection (ℝ ∙ w)ᗮ with hR
  have hRv : R v = v :=
    Submodule.reflection_mem_subspace_eq_self
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hvw)
  have hRw : R w = -w := Submodule.reflection_orthogonalComplement_singleton_eq_neg w
  have h := integral_sphereMap R (measurable_inner_newtonField w v s)
  have hpt : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ w (newtonField (v - s • (sphereMap R θ : EuclideanSpace ℝ (Fin d)))) =
        -inner ℝ w (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) := by
    intro θ
    have h1 : v - s • (sphereMap R θ : EuclideanSpace ℝ (Fin d)) =
        R (v - s • (θ : EuclideanSpace ℝ (Fin d))) := by
      rw [R.map_sub, R.map_smul, hRv]
      rfl
    rw [h1, newtonField_map, ← R.inner_map_map w, hRw, hR, Submodule.reflection_reflection,
      inner_neg_left]
  simp_rw [hpt, integral_neg] at h
  linarith

/-- The Newtonian field is continuous away from the origin. -/
private lemma continuousAt_newtonField_of_ne {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    ContinuousAt (newtonField : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) x :=
  ((continuous_norm.pow d).continuousAt.inv₀
    (pow_ne_zero d (norm_ne_zero_iff.mpr hx))).smul continuousAt_id

/-- For `|v| ≠ s` the sphere integrand `θ ↦ ⟨ξ, K(v - sθ)⟩` is integrable, being continuous on a
compact space. -/
private lemma integrable_inner_newtonField (ξ : EuclideanSpace ℝ (Fin d))
    {v : EuclideanSpace ℝ (Fin d)} {s : ℝ} (hs : 0 < s) (hvs : ‖v‖ ≠ s) :
    Integrable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))))
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  haveI : CompactSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hcont : Continuous (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hθ : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
      simp
    have hne : v - s • (θ : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
      intro h
      have hv : v = s • (θ : EuclideanSpace ℝ (Fin d)) := sub_eq_zero.mp h
      apply hvs
      rw [hv, norm_smul, hθ, Real.norm_eq_abs, abs_of_pos hs, mul_one]
    have hc : ContinuousAt (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        v - s • (θ : EuclideanSpace ℝ (Fin d))) θ :=
      continuousAt_const.sub (continuousAt_subtype_val.const_smul s)
    exact ContinuousAt.comp_of_eq (g := newtonField)
      (f := fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        v - s • (θ : EuclideanSpace ℝ (Fin d))) (continuousAt_newtonField_of_ne hne) hc rfl
  exact Continuous.integrable_of_hasCompactSupport (continuous_const.inner hcont)
    (HasCompactSupport.of_compactSpace _)

/-- The kernel average `eq:kernel-average` against an arbitrary vector `ξ`: for `v ≠ 0`, `s > 0` and
`|v| ≠ s`, `∫_S ξ · K(v - sθ) dσ(θ) = σ_d |v|^{-d} (ξ · v) 1{s < |v|}`. -/
private lemma integral_sphere_inner_newtonField_vec (hd : 2 ≤ d)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) {s : ℝ} (hs : 0 < s) (hvs : ‖v‖ ≠ s)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    ∫ θ, inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      if s < ‖v‖ then d * unitBallVolume d * (inner ℝ ξ v / ‖v‖ ^ d) else 0 := by
  have hrpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hvv : inner ℝ v v = ‖v‖ * ‖v‖ := real_inner_self_eq_norm_mul_norm v
  set a : ℝ := inner ℝ ξ (unitDir v) with ha_def
  have ha : a = ‖v‖⁻¹ * inner ℝ ξ v := by
    rw [ha_def, unitDir, real_inner_smul_right]
  set w : EuclideanSpace ℝ (Fin d) := ξ - a • unitDir v with hw_def
  have hperp : inner ℝ w v = 0 := by
    rw [hw_def, inner_sub_left, real_inner_smul_left, unitDir, real_inner_smul_left, hvv, ha]
    field_simp
    ring
  have hdecomp : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) =
        a * inner ℝ (unitDir v) (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) +
          inner ℝ w (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) := by
    intro θ
    rw [hw_def, inner_sub_left, real_inner_smul_left]
    ring
  simp_rw [hdecomp]
  rw [integral_add ((integrable_inner_newtonField (unitDir v) hs hvs).const_mul a)
    (integrable_inner_newtonField w hs hvs), integral_const_mul,
    integral_sphere_inner_newtonField hd hv hs hvs, integral_sphere_inner_newtonField_perp hperp,
    add_zero]
  split_ifs
  · rw [ha, ← div_pow_eq_rpow_sub hrpos d]
    field_simp
  · simp


/-- The gradient of a function on `ℝ^d` is measurable. -/
private lemma measurable_gradient (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measurable (gradient Ψ) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ Ψ)

/-- For `d ≥ 1`, `Λ_Ψ ≥ 0`. -/
private lemma normMax_nonneg {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d) :
    0 ≤ normMax Ψ := by
  have h1 := normMin_pos_mul_le hΨ hd
  have hn : ‖coordVec (⟨0, by omega⟩ : Fin d)‖ = 1 := by
    simp [coordVec, PiLp.norm_single]
  have h2 := le_normMax_mul hΨ (coordVec (⟨0, by omega⟩ : Fin d))
  have h3 := h1.2 (coordVec (⟨0, by omega⟩ : Fin d))
  rw [hn] at h2 h3
  linarith [h1.1]

/-- The gradient of a norm has Euclidean norm at most `Λ_Ψ` everywhere: where `Ψ` is
differentiable it is a subgradient, and elsewhere it is `0`. -/
private lemma norm_gradient_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d)
    (v : EuclideanSpace ℝ (Fin d)) : ‖gradient Ψ v‖ ≤ normMax Ψ := by
  by_cases hv : DifferentiableAt ℝ Ψ v
  · have h := (subgradient_euler hΨ (gradient_isSubgradient hΨ hv)).2 (gradient Ψ v)
    have h2 := le_normMax_mul hΨ (gradient Ψ v)
    rw [real_inner_self_eq_norm_mul_norm] at h
    have h3 : ‖gradient Ψ v‖ * ‖gradient Ψ v‖ ≤ normMax Ψ * ‖gradient Ψ v‖ := h.trans h2
    rcases eq_or_lt_of_le (norm_nonneg (gradient Ψ v)) with h0 | h0
    · rw [← h0]
      exact normMax_nonneg hΨ hd
    · exact le_of_mul_le_mul_right h3 h0
  · have h0 : gradient Ψ v = 0 := by
      rw [gradient, fderiv_zero_of_not_differentiableAt hv]
      simp
    rw [h0, norm_zero]
    exact normMax_nonneg hΨ hd



/-- The weight `χ(|ζ|)` times the kernel `|a - ζ|^{1-d}` is integrable, with integral at most
`M d ω_d + ∫ χ(|ζ|) dζ`: inside the unit ball around `a` the weight is at most `M` and the kernel
has integral `d ω_d`, outside the kernel is at most one. -/
private lemma integrable_weight_mul_kernel (hd : 1 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    (a : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))) ∧
      ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤
        M * (d * unitBallVolume d) + ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ := by
  obtain ⟨hint, hval⟩ := integrableOn_ball_and_integral_eq hd a one_pos
  have hind := hint.integrable_indicator (Metric.isOpen_ball.measurableSet)
  have hGi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      M * (Metric.ball a 1).indicator (fun v => ‖v - a‖ ^ (1 - (d : ℝ))) ζ + χ ‖ζ‖) :=
    (hind.const_mul M).add hχi
  have hmeas : Measurable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))) :=
    (hχm.comp measurable_norm).mul ((measurable_const.sub measurable_id).norm.pow_const _)
  have hle : ∀ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤
      M * (Metric.ball a 1).indicator (fun v => ‖v - a‖ ^ (1 - (d : ℝ))) ζ + χ ‖ζ‖ := by
    intro ζ
    have hk : 0 ≤ ‖a - ζ‖ ^ (1 - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have hsw : ‖a - ζ‖ = ‖ζ - a‖ := norm_sub_rev a ζ
    by_cases hζ : ζ ∈ Metric.ball a 1
    · rw [Set.indicator_of_mem hζ, ← hsw]
      have h1 : χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤ M * ‖a - ζ‖ ^ (1 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_right (hM _) hk
      linarith [hχ0 ‖ζ‖]
    · rw [Set.indicator_of_notMem hζ]
      have hge : 1 ≤ ‖a - ζ‖ := by
        rw [hsw]
        simpa [Metric.mem_ball, dist_eq_norm] using hζ
      have hk1 : ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hge (by
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd
          linarith)
      have h1 : χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤ χ ‖ζ‖ * 1 :=
        mul_le_mul_of_nonneg_left hk1 (hχ0 _)
      linarith
  have hfi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))) := by
    refine hGi.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hχ0 _) (Real.rpow_nonneg (norm_nonneg _) _))]
    exact hle ζ
  refine ⟨hfi, ?_⟩
  calc ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))
      ≤ ∫ ζ : EuclideanSpace ℝ (Fin d),
          (M * (Metric.ball a 1).indicator (fun v => ‖v - a‖ ^ (1 - (d : ℝ))) ζ + χ ‖ζ‖) :=
        integral_mono hfi hGi hle
    _ = M * (d * unitBallVolume d) + ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ := by
        rw [integral_add (hind.const_mul M) hχi, integral_const_mul,
          integral_indicator Metric.isOpen_ball.measurableSet, hval, mul_one]


/-- Pointwise bound of the radial weight times the field `⟨ξ, K(w - ζ)⟩` by `|ξ|` times the
weighted kernel `χ(|ζ|) |w - ζ|^{1-d}`. -/
private lemma norm_weight_inner_le (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ0 : ∀ s, 0 ≤ χ s)
    (w ξ ζ : EuclideanSpace ℝ (Fin d)) :
    ‖χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ))‖ ≤ ‖ξ‖ * (χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ0 _), Real.norm_eq_abs]
  have h1 : |inner ℝ ξ (newtonField (w - ζ))| ≤ ‖ξ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ)) := by
    rw [← norm_newtonField hd]
    exact abs_real_inner_le_norm _ _
  calc χ ‖ζ‖ * |inner ℝ ξ (newtonField (w - ζ))|
      ≤ χ ‖ζ‖ * (‖ξ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := mul_le_mul_of_nonneg_left h1 (hχ0 _)
    _ = ‖ξ‖ * (χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := by ring

/-- The radial weight times the field `⟨ξ, K(w - ζ)⟩` is integrable. -/
private lemma integrable_weight_inner_newtonField (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    (w ξ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ))) := by
  have hk := (integrable_weight_mul_kernel (by omega) hχm hχ0 hM hχi w).1
  have hmeas : Measurable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ))) :=
    (hχm.comp measurable_norm).mul
      (measurable_const.inner (measurable_newtonField.comp (measurable_const.sub measurable_id)))
  exact (hk.const_mul ‖ξ‖).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ζ => norm_weight_inner_le hd hχ0 w ξ ζ)

/-- The mass of a radial weight in a centred ball, in polar coordinates:
`∫_{B(0,s)} χ(|ζ|) dζ = d ω_d ∫_0^s r^{d-1} χ(r) dr`. -/
private lemma integral_ball_weight (hd : 1 ≤ d) (χ : ℝ → ℝ) (s : ℝ) :
    ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ =
      d * unitBallVolume d * ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * (Set.Iio s).indicator χ r := by
  haveI : NeZero d := ⟨by omega⟩
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hind : (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s).indicator (fun ζ => χ ‖ζ‖) =
      fun ζ => (Set.Iio s).indicator χ ‖ζ‖ := by
    funext ζ
    by_cases hζ : ‖ζ‖ < s <;> simp [Set.indicator, hζ]
  rw [← integral_indicator Metric.isOpen_ball.measurableSet, hind,
    integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d))), hfin]
  simp only [unitBallVolume, Measure.real, nsmul_eq_mul, smul_eq_mul]
  ring


/-- Newton's theorem for a radial weight: for `w ≠ 0` and any vector `ξ`,
`∫ χ(|ζ|) ⟨ξ, K(w - ζ)⟩ dζ = (∫_{B(0,|w|)} χ(|ζ|) dζ) ⟨ξ, w⟩ / |w|^d`. -/
private lemma integral_weight_inner_newtonField (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {w : EuclideanSpace ℝ (Fin d)} (hw : w ≠ 0) (ξ : EuclideanSpace ℝ (Fin d)) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ)) =
      (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖w‖, χ ‖ζ‖) *
        (inner ℝ ξ w / ‖w‖ ^ d) := by
  have hint := integrable_weight_inner_newtonField hd hχm hχ0 hM hχi w ξ
  rw [integral_eq_integral_Ioi_sphere (by omega) hint, integral_ball_weight (by omega)]
  have hae : ∀ᵐ r : ℝ ∂(volume : Measure ℝ), r ≠ ‖w‖ := by
    rw [ae_iff]
    simp
  have hpt : ∀ᵐ r : ℝ ∂(volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)),
      r ^ (d - 1) * ∫ θ, χ ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ *
          inner ℝ ξ (newtonField (w - r • (θ : EuclideanSpace ℝ (Fin d))))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
        d * unitBallVolume d * (inner ℝ ξ w / ‖w‖ ^ d) *
          (r ^ (d - 1) * (Set.Iio ‖w‖).indicator χ r) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hae] with r hr hr0
    have hr0' : 0 < r := hr0
    have hθ : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ = r := fun θ => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0', mem_sphere_zero_iff_norm.mp θ.2, mul_one]
    simp_rw [hθ]
    rw [integral_const_mul, integral_sphere_inner_newtonField_vec hd hw hr0' hr.symm ξ]
    by_cases hlt : r < ‖w‖
    · simp only [hlt, if_true, Set.indicator_of_mem (Set.mem_Iio.mpr hlt)]
      ring
    · simp only [hlt, if_false, Set.indicator_of_notMem (mt Set.mem_Iio.mp hlt)]
      ring
  rw [integral_congr_ae hpt, integral_const_mul]
  ring


/-- For each position `v`, the radial weight times the field `⟨g(v), K(v - y₀ - ζ)⟩` is integrable
in `ζ`, uniformly in `v`, and jointly integrable in `(v, ζ)` over `F × ℝ^d` for a set `F` of finite
volume. -/
private lemma integrable_weight_fieldPair (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {F : Set (EuclideanSpace ℝ (Fin d))} (hFfin : volume F ≠ ⊤)
    (y₀ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      χ ‖p.2‖ * inner ℝ (g p.1) (newtonField (p.1 - y₀ - p.2)))
      (((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict F).prod volume) := by
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hmeas : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      χ ‖p.2‖ * inner ℝ (g p.1) (newtonField (p.1 - y₀ - p.2))) :=
    (hχm.comp measurable_snd.norm).mul ((hg.comp measurable_fst).inner
      (measurable_newtonField.comp ((measurable_fst.sub_const y₀).sub measurable_snd)))
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun v =>
    integrable_weight_inner_newtonField hd hχm hχ0 hM hχi (v - y₀) (g v), ?_⟩
  refine Integrable.mono' (integrableOn_const hFfin (C := Λ * (M * (d * unitBallVolume d) +
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖)))
    hmeas.norm.aestronglyMeasurable.integral_prod_right' (Filter.Eventually.of_forall fun v => ?_)
  obtain ⟨hki, hkle⟩ := integrable_weight_mul_kernel (by omega) hχm hχ0 hM hχi (v - y₀)
  have hfi := integrable_weight_inner_newtonField hd hχm hχ0 hM hχi (v - y₀) (g v)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ζ => norm_nonneg _)]
  calc ∫ ζ : EuclideanSpace ℝ (Fin d), ‖χ ‖ζ‖ * inner ℝ (g v) (newtonField (v - y₀ - ζ))‖
      ≤ ∫ ζ : EuclideanSpace ℝ (Fin d), Λ * (χ ‖ζ‖ * ‖v - y₀ - ζ‖ ^ (1 - (d : ℝ))) := by
        refine integral_mono hfi.norm (hki.const_mul Λ) fun ζ => ?_
        exact (norm_weight_inner_le hd hχ0 (v - y₀) (g v) ζ).trans
          (mul_le_mul_of_nonneg_right (hΛ v) (mul_nonneg (hχ0 _) (Real.rpow_nonneg
            (norm_nonneg _) _)))
    _ = Λ * ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖v - y₀ - ζ‖ ^ (1 - (d : ℝ)) :=
        integral_const_mul _ _
    _ ≤ Λ * (M * (d * unitBallVolume d) + ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) :=
        mul_le_mul_of_nonneg_left hkle hΛ0


/-- The mass of a radial weight in a centred ball lies between `0` and the total mass. -/
private lemma ball_weight_bounds {χ : ℝ → ℝ} (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖)) (s : ℝ) :
    0 ≤ ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ ∧
      ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ ≤
        ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ :=
  ⟨integral_nonneg fun _ => hχ0 _,
    setIntegral_le_integral hχi (Filter.Eventually.of_forall fun _ => hχ0 _)⟩

/-- Fubini and Newton's theorem for the radial weight: for a field `g` of norm at most `Λ` whose
pairing `⟨g(v), v - y₀⟩` is nonnegative on `F`, the weighted field potential of `F` is integrable
and its integral is at most the total weight times the field potential at `y₀`. -/
private lemma weighted_fieldPotential_le (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {F : Set (EuclideanSpace ℝ (Fin d))} (hF : MeasurableSet F)
    (hFfin : volume F ≠ ⊤) (y₀ : EuclideanSpace ℝ (Fin d))
    (hpos : ∀ v ∈ F, 0 ≤ inner ℝ (g v) (v - y₀)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * ∫ v in F, inner ℝ (g v) (newtonField (v - y₀ - ζ))) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d),
        χ ‖ζ‖ * ∫ v in F, inner ℝ (g v) (newtonField (v - y₀ - ζ)) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
        ∫ v in F, inner ℝ (g v) (newtonField (v - y₀)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hI := integrable_weight_fieldPair hd hχm hχ0 hM hχi hg hΛ hFfin y₀
  have hcm : ∀ ζ : EuclideanSpace ℝ (Fin d),
      χ ‖ζ‖ * ∫ v in F, inner ℝ (g v) (newtonField (v - y₀ - ζ)) =
        ∫ v in F, χ ‖ζ‖ * inner ℝ (g v) (newtonField (v - y₀ - ζ)) := fun ζ =>
    (integral_const_mul _ _).symm
  simp_rw [hcm]
  refine ⟨hI.integral_prod_right, ?_⟩
  rw [← integral_integral_swap (f := fun (v ζ : EuclideanSpace ℝ (Fin d)) =>
    χ ‖ζ‖ * inner ℝ (g v) (newtonField (v - y₀ - ζ))) hI]
  have hgi : Integrable (fun v : EuclideanSpace ℝ (Fin d) =>
      (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) * inner ℝ (g v) (newtonField (v - y₀)))
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict F) := by
    refine Integrable.const_mul ?_ _
    simp_rw [inner_newtonField]
    exact integrableOn_fieldIntegrand (by omega) hg hΛ hF hFfin y₀
  rw [← integral_const_mul]
  refine integral_mono_ae hI.integral_prod_left hgi ?_
  have hne : ∀ᵐ v : EuclideanSpace ℝ (Fin d), v ≠ y₀ := by
    rw [ae_iff]
    simp
  rw [Filter.EventuallyLE, ae_restrict_iff' hF]
  filter_upwards [hne] with v hv hvF
  have hw : v - y₀ ≠ 0 := sub_ne_zero.mpr hv
  rw [integral_weight_inner_newtonField hd hχm hχ0 hM hχi hw (g v), inner_newtonField]
  have hq : 0 ≤ inner ℝ (g v) (v - y₀) / ‖v - y₀‖ ^ d :=
    div_nonneg (hpos v hvF) (pow_nonneg (norm_nonneg _) _)
  exact mul_le_mul_of_nonneg_right (ball_weight_bounds hχ0 hχi _).2 hq


/-- The field potential of `F` weighted by the radial weight, in the normalisation of
`normPotential`: if `⟨∇Ψ(v), v - y₀⟩ ≥ 0` on `F`, it is integrable with integral at most the total
weight times the potential of `F` at `y₀`. -/
private lemma weighted_normPotential_le (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {F : Set (EuclideanSpace ℝ (Fin d))} (hF : MeasurableSet F) (hFfin : volume F ≠ ⊤)
    (y₀ : EuclideanSpace ℝ (Fin d))
    (hpos : ∀ v ∈ F, 0 ≤ inner ℝ (gradient Ψ v) (v - y₀)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * normPotential d ε Ψ F (y₀ - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * normPotential d ε Ψ F (y₀ - ζ) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) * normPotential d ε Ψ F y₀ := by
  obtain ⟨hint, hle⟩ := weighted_fieldPotential_le hd hχm hχ0 hM hχi (measurable_gradient Ψ)
    (norm_gradient_le hΨ (by omega)) hF hFfin y₀ hpos
  have hω := unitBallVolume_pos d
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  set h : EuclideanSpace ℝ (Fin d) → ℝ := fun t =>
    χ ‖t‖ * ∫ v in F, inner ℝ (gradient Ψ v) (newtonField (v - y₀ - t)) with hh
  have hfun : (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * normPotential d ε Ψ F (y₀ - ζ)) =
      fun ζ => (2 * ε / unitBallVolume d) * h (-ζ) := by
    funext ζ
    have hv : ∀ v : EuclideanSpace ℝ (Fin d), v - y₀ - -ζ = v - (y₀ - ζ) := fun v => by abel
    simp only [hh, normPotential, norm_neg, hv, inner_newtonField]
    ring
  rw [hfun]
  refine ⟨(hint.comp_neg).const_mul _, ?_⟩
  rw [integral_const_mul, integral_neg_eq_self h volume]
  calc (2 * ε / unitBallVolume d) * ∫ t : EuclideanSpace ℝ (Fin d), h t
      ≤ (2 * ε / unitBallVolume d) * ((∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
          ∫ v in F, inner ℝ (gradient Ψ v) (newtonField (v - y₀))) :=
        mul_le_mul_of_nonneg_left hle hc
    _ = (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) * normPotential d ε Ψ F y₀ := by
        simp only [normPotential, inner_newtonField]
        ring


/-- If `Ψ(y₀) ≤ Ψ(v)`, then `⟨∇Ψ(v), v - y₀⟩ ≥ 0`: Euler's relation `⟨∇Ψ(v), v⟩ = Ψ(v)` and the
subgradient bound `⟨∇Ψ(v), y₀⟩ ≤ Ψ(y₀)` where `Ψ` is differentiable, and `∇Ψ(v) = 0` elsewhere. -/
private lemma inner_gradient_sub_nonneg {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {v y₀ : EuclideanSpace ℝ (Fin d)} (h : Ψ y₀ ≤ Ψ v) :
    0 ≤ inner ℝ (gradient Ψ v) (v - y₀) := by
  by_cases hv : DifferentiableAt ℝ Ψ v
  · have h1 := subgradient_euler hΨ (gradient_isSubgradient hΨ hv)
    rw [inner_sub_right, h1.1]
    have := h1.2 y₀
    linarith
  · have h0 : gradient Ψ v = 0 := by
      rw [gradient, fderiv_zero_of_not_differentiableAt hv]
      simp
    rw [h0, inner_zero_left]

/-- A function with a Hölder bound of exponent `1/2` is continuous. -/
private lemma continuous_of_holder {f : EuclideanSpace ℝ (Fin d) → ℝ} {K : ℝ}
    (h : ∀ y z, |f y - f z| ≤ K * ‖y - z‖ ^ ((1 : ℝ) / 2)) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro z
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin d) => K * ‖y - z‖ ^ ((1 : ℝ) / 2)) :=
    continuous_const.mul ((continuous_norm.comp (continuous_id.sub continuous_const)).rpow_const
      (fun _ => Or.inr (by norm_num)))
  have hlim : Tendsto (fun y : EuclideanSpace ℝ (Fin d) => K * ‖y - z‖ ^ ((1 : ℝ) / 2)) (𝓝 z)
      (𝓝 0) := by
    have h0 := hcont.tendsto z
    simpa using h0
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun y => by simpa [Real.norm_eq_abs] using h y z) hlim

/-- The radial weight times the potential of a bounded measurable set is integrable, by the
boundedness and the Hölder continuity of the potential. -/
private lemma integrable_weight_normPotential (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε) (hgeom : norm_potential_geometry) {χ : ℝ → ℝ}
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    (y₀ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * normPotential d ε Ψ D (y₀ - ζ)) := by
  obtain ⟨C, -, hC⟩ := hgeom hd Ψ hΨ
  obtain ⟨hbound, hholder, -⟩ := hC ε hε D hD hDb
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin d) => normPotential d ε Ψ D y) :=
    continuous_of_holder hholder
  have hcont' : Continuous (fun ζ : EuclideanSpace ℝ (Fin d) => normPotential d ε Ψ D (y₀ - ζ)) :=
    hcont.comp (continuous_const.sub continuous_id)
  exact hχi.mul_bdd hcont'.aestronglyMeasurable (Filter.Eventually.of_forall fun ζ => by
    rw [Real.norm_eq_abs]
    exact hbound (y₀ - ζ))


/-- The sublevel-ball part: if the potential of `B` is `2dε (b - Ψ(y))_+`, then, at a point `y₀`
with `Ψ(y₀) = b`, the radial weight times the potential of `B` around `y₀` is integrable and its
integral is at most `2dε ∫ χ(|ζ|) min(b, Ψ(ζ)) dζ`. -/
private lemma weighted_ballPotential_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε) {χ : ℝ → ℝ} (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖)) {b : ℝ}
    {B : Set (EuclideanSpace ℝ (Fin d))}
    (hU : ∀ y, normPotential d ε Ψ B y = 2 * d * ε * max (b - Ψ y) 0)
    {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : Ψ y₀ = b) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * normPotential d ε Ψ B (y₀ - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * normPotential d ε Ψ B (y₀ - ζ) ≤
      2 * d * ε * ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * min b (Ψ ζ) := by
  have hnn : ∀ x, 0 ≤ Ψ x := (map_zero_nonneg_neg hΨ).2.1
  have hΨc := norm_continuous hΨ
  have hb : 0 ≤ b := by rw [← hy₀]; exact hnn y₀
  have hc : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  have hmaxle : ∀ ζ : EuclideanSpace ℝ (Fin d), max (b - Ψ (y₀ - ζ)) 0 ≤ b := fun ζ =>
    max_le (by linarith [hnn (y₀ - ζ)]) hb
  have hmaxc : Continuous (fun ζ : EuclideanSpace ℝ (Fin d) => max (b - Ψ (y₀ - ζ)) 0) :=
    (continuous_const.sub (hΨc.comp (continuous_const.sub continuous_id))).max continuous_const
  have hint : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * normPotential d ε Ψ B (y₀ - ζ)) := by
    simp_rw [hU]
    refine hχi.mul_bdd (c := 2 * d * ε * b) (hmaxc.const_mul _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc (le_max_right _ _))]
    exact mul_le_mul_of_nonneg_left (hmaxle ζ) hc
  have hminc : Continuous (fun ζ : EuclideanSpace ℝ (Fin d) => min b (Ψ ζ)) :=
    continuous_const.min hΨc
  have hmini : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * min b (Ψ ζ)) :=
    hχi.mul_bdd (c := b) hminc.aestronglyMeasurable (Filter.Eventually.of_forall fun ζ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hb (hnn ζ))]
      exact min_le_left _ _)
  refine ⟨hint, ?_⟩
  rw [← integral_const_mul]
  refine integral_mono hint (hmini.const_mul _) fun ζ => ?_
  have h1 : max (b - Ψ (y₀ - ζ)) 0 ≤ min b (Ψ ζ) := by
    refine max_le (le_min (by linarith [hnn (y₀ - ζ)]) ?_) (le_min hb (hnn ζ))
    have h := hΨ.add_le (y₀ - ζ) ζ
    rw [sub_add_cancel, hy₀] at h
    linarith
  rw [hU, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (hχ0 _)) hc

/-- The potential of a set splits over a measurable subset `B`: `U_D = U_B + U_{D \ B}`. -/
private lemma normPotential_union_diff {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (hd : 1 ≤ d) (ε : ℝ) {D B : Set (EuclideanSpace ℝ (Fin d))} (hBD : B ⊆ D)
    (hBm : MeasurableSet B) (hDm : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε Ψ D y = normPotential d ε Ψ B y + normPotential d ε Ψ (D \ B) y := by
  have hg := measurable_gradient Ψ
  have hΛ := norm_gradient_le hΨ hd
  have hBfin : volume B ≠ ⊤ := (measure_mono hBD).trans_lt hDfin.lt_top |>.ne
  have hDBfin : volume (D \ B) ≠ ⊤ := (measure_mono Set.sdiff_subset).trans_lt hDfin.lt_top |>.ne
  unfold normPotential
  rw [← mul_add, ← setIntegral_union Set.disjoint_sdiff_right (hDm.diff hBm)
    (integrableOn_fieldIntegrand hd hg hΛ hBm hBfin y)
    (integrableOn_fieldIntegrand hd hg hΛ (hDm.diff hBm) hDBfin y), Set.union_sdiff_cancel hBD]

/-- `convBound`: the convolution bound for a radial weight. -/
theorem convBound {d : ℕ} (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {ε : ℝ}
    (hε : 0 < ε) (hgeom : norm_potential_geometry) (hball : norm_ball_potential) :
    CERW.Support.Norm.ContactShared.ConvBound d Ψ ε := by
  intro χ hχm hχ0 hMex hχi D hD hDb b hb hBD y₀ hy₀
  obtain ⟨M, hM⟩ := hMex
  have hBm : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | Ψ v < b} :=
    measurableSet_lt (norm_continuous hΨ).measurable measurable_const
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hFfin : volume (D \ {v : EuclideanSpace ℝ (Fin d) | Ψ v < b}) ≠ ⊤ :=
    ((measure_mono Set.sdiff_subset).trans_lt hDfin.lt_top).ne
  have hsplit := normPotential_union_diff hΨ (by omega) ε hBD hBm hD hDfin
  have hU : ∀ y, normPotential d ε Ψ {v : EuclideanSpace ℝ (Fin d) | Ψ v < b} y =
      2 * d * ε * max (b - Ψ y) 0 := fun y => hball hd hΨ ε hb y
  have hU0 : normPotential d ε Ψ {v : EuclideanSpace ℝ (Fin d) | Ψ v < b} y₀ = 0 := by
    rw [hU, hy₀]
    simp
  obtain ⟨hBi, hBle⟩ := weighted_ballPotential_le hΨ hε hχ0 hχi hU hy₀
  obtain ⟨hFi, hFle⟩ := weighted_normPotential_le hd hΨ hε hχm hχ0 hM hχi (hD.diff hBm) hFfin y₀
    (fun v hv => inner_gradient_sub_nonneg hΨ (by
      have : ¬ Ψ v < b := hv.2
      rw [hy₀]
      exact not_lt.mp this))
  refine ⟨integrable_weight_normPotential hd hΨ hε hgeom hχi hD hDb y₀, ?_⟩
  have hfun : ∀ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * normPotential d ε Ψ D (y₀ - ζ) =
      χ ‖ζ‖ * normPotential d ε Ψ {v : EuclideanSpace ℝ (Fin d) | Ψ v < b} (y₀ - ζ) +
        χ ‖ζ‖ * normPotential d ε Ψ (D \ {v : EuclideanSpace ℝ (Fin d) | Ψ v < b}) (y₀ - ζ) :=
    fun ζ => by rw [hsplit, mul_add]
  simp_rw [hfun]
  rw [integral_add hBi hFi, hsplit y₀, hU0, zero_add]
  linarith

end CERW.Support.Norm.ContactConv

namespace CERW.Support.Norm.ContactDynkin

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law CERW.Support.Drift
  CERW.Support.LocalTime

variable {d : ℕ}

/-- The Freedman threshold `c (√(max (C_g² B) 1 · L) + (2C_g+1) L)` is at most
`C (√(B L) + L)`. -/
private lemma threshold_arith {Cg c : ℝ} (hCg : 0 ≤ Cg) (hc : 1 ≤ c) :
    ∃ Cdet : ℝ, 0 < Cdet ∧ ∀ S L : ℝ, 0 ≤ S → 1 ≤ L →
      c * (Real.sqrt (max (Cg ^ 2 * S) 1 * L) + (2 * Cg + 1) * L) ≤
        Cdet * (Real.sqrt (S * L) + L) := by
  refine ⟨c * (3 * Cg + 2), by positivity, ?_⟩
  intro S L hS hL
  have hc0 : 0 ≤ c := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hmax : max (Cg ^ 2 * S) 1 ≤ Cg ^ 2 * S + 1 :=
    max_le (by linarith) (by nlinarith [sq_nonneg Cg, hS])
  have hsqrt : Real.sqrt (max (Cg ^ 2 * S) 1 * L) ≤ Cg * Real.sqrt (S * L) + Real.sqrt L := by
    calc Real.sqrt (max (Cg ^ 2 * S) 1 * L)
        ≤ Real.sqrt ((Cg ^ 2 * S + 1) * L) :=
            Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hmax hL0)
      _ = Real.sqrt (Cg ^ 2 * (S * L) + L) := by
            congr 1
            ring
      _ ≤ Real.sqrt (Cg ^ 2 * (S * L)) + Real.sqrt L :=
            sqrt_add_le_add (by positivity) hL0
      _ = Cg * Real.sqrt (S * L) + Real.sqrt L := by
            rw [Real.sqrt_mul (sq_nonneg Cg), Real.sqrt_sq hCg]
  have hsqrtL : Real.sqrt L ≤ L := by
    rw [Real.sqrt_le_left hL0]
    nlinarith
  have hg : 0 ≤ Real.sqrt (S * L) := Real.sqrt_nonneg _
  have hsum : Cg * Real.sqrt (S * L) + Real.sqrt L + (2 * Cg + 1) * L ≤
      (3 * Cg + 2) * (Real.sqrt (S * L) + L) := by
    have h1 : Cg * Real.sqrt (S * L) ≤ (3 * Cg + 2) * Real.sqrt (S * L) :=
      mul_le_mul_of_nonneg_right (by linarith) hg
    have h2 : Real.sqrt L ≤ (Cg + 1) * L :=
      hsqrtL.trans (le_mul_of_one_le_left hL0 (by linarith))
    nlinarith [h1, h2]
  calc c * (Real.sqrt (max (Cg ^ 2 * S) 1 * L) + (2 * Cg + 1) * L)
      ≤ c * (Cg * Real.sqrt (S * L) + Real.sqrt L + (2 * Cg + 1) * L) := by
          refine mul_le_mul_of_nonneg_left ?_ hc0
          linarith [hsqrt]
    _ ≤ c * ((3 * Cg + 2) * (Real.sqrt (S * L) + L)) :=
          mul_le_mul_of_nonneg_left hsum hc0
    _ = c * (3 * Cg + 2) * (Real.sqrt (S * L) + L) := by ring

/-- One target: Freedman's inequality at dyadic brackets, followed by the deterministic step,
bounds the probability that `|𝓜^y_n|` exceeds the threshold. -/
private lemma exists_event_bound_drift (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ Cdet : ℝ, 0 < Cdet ∧ ∀ {ξ : Site d → EuclideanSpace ℝ (Fin d)},
      (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
      ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d}, IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        ∀ y : Site d,
        μ {ω | Cdet * (Real.sqrt ((∑ j ∈ range n,
            (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) *
              Real.log (n + 2)) + Real.log (n + 2)) <
            |driftDynkin ε ξ (fun z => b (z - y)) X n ω|} ≤
          ENNReal.ofReal (((Nat.clog 2 ⌈max (Cg ^ 2 * n) 1⌉₊ : ℕ) + 1) *
            (2 * Real.exp (-(K * Real.log (n + 2))))) := by
  have hd1 : 1 ≤ d := by omega
  have hCg := cg_nonneg hd1 hgrad
  obtain ⟨c, hc1, hc⟩ := CERW.Generic.Martingale.exists_dyadic_bound hK
  obtain ⟨Cdet, hCdet0, hCdet⟩ := threshold_arith hCg hc1
  refine ⟨Cdet, hCdet0, ?_⟩
  intro ξ hξ Ω _ μ _ X hX n hn y
  obtain ⟨M, hM, hbd, hvar, hae⟩ := exists_clamped_translate_drift hd1 hε hξ hX hgrad y
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  have hL1 : 1 ≤ Real.log ((n : ℝ) + 2) := one_le_log_add_two hn
  have hW : (1 : ℝ) ≤ max (Cg ^ 2 * n) 1 := le_max_right _ _
  have hVW : ∀ ω, bracket Cg y X (0 + n) ω - bracket Cg y X 0 ω ≤ max (Cg ^ 2 * n) 1 := by
    intro ω
    rw [zero_add]
    exact (bracket_sub_le hd1 Cg y X (Nat.zero_le n) le_rfl ω).trans (le_max_left _ _)
  have hdy := hc hM (V := bracket Cg y X) (stronglyMeasurable_bracket_succ hX.measurable Cg y)
    (bracket_zero Cg y X) (bracket_mono Cg y X) hvar (b := 2 * Cg + 1) (by linarith) 0 n
    (fun i _ _ ω => hbd i ω) hW hL hVW
  refine le_trans (measure_mono_ae ?_) hdy
  filter_upwards [hae] with ω hω hE
  change _ < _ at hE
  change _ < _
  rw [zero_add, bracket_zero, sub_zero, hω n, hω 0, driftDynkin_zero, sub_zero]
  have hS0 : 0 ≤ ∑ j ∈ range n, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ)) :=
    sum_nonneg fun j _ => Real.rpow_nonneg (by linarith [euclidNorm_nonneg (X j ω - y)]) _
  have hthr := hCdet _ _ hS0 hL1
  simp only [bracket]
  exact lt_of_le_of_lt hthr hE

/-- The arithmetic of the union bound: `(7(n+1))^D · (G + 3)(n + 1) · 2 e^{-(p + D + 2)L}` is at
most `(7^D (G + 3) 2^{D+2}) n^{-p}`. -/
private lemma union_bound_arith_drift {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 1 ≤ n) (D : ℕ) {G : ℝ}
    (hG : 0 ≤ G) :
    (7 * ((n : ℝ) + 1)) ^ D * (((G + 3) * ((n : ℝ) + 1)) *
      (2 * Real.exp (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))) ≤
    (7 ^ D * (G + 3) * 2 ^ (D + 3)) * (n : ℝ) ^ (-p) := by
  have h1 := CERW.Generic.Martingale.two_mul_exp_neg_mul_log_le
    (K := p + ((D + 2 : ℕ) : ℝ)) (by positivity) hn
  have h2 := CERW.Generic.Martingale.pow_mul_rpow_neg_le hn (D + 2) p
  have h3 : (0 : ℝ) ≤ 7 ^ D * (G + 3) * ((n : ℝ) + 1) ^ (D + 2) := by positivity
  calc (7 * ((n : ℝ) + 1)) ^ D * (((G + 3) * ((n : ℝ) + 1)) *
        (2 * Real.exp (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))))
      = (7 ^ D * (G + 3) * ((n : ℝ) + 1) ^ (D + 1)) *
          (2 * Real.exp (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) := by
        rw [mul_pow]
        ring
    _ ≤ (7 ^ D * (G + 3) * ((n : ℝ) + 1) ^ (D + 2)) *
          (2 * Real.exp (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) := by
        have hpow : ((n : ℝ) + 1) ^ (D + 1) ≤ ((n : ℝ) + 1) ^ (D + 2) :=
          pow_le_pow_right₀
            (show (1 : ℝ) ≤ (n : ℝ) + 1 by
              have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
              linarith) (by omega)
        have hC : (0 : ℝ) ≤ 7 ^ D * (G + 3) := by positivity
        have he : (0 : ℝ) ≤ 2 * Real.exp
            (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))) := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) he
    _ ≤ (7 ^ D * (G + 3) * ((n : ℝ) + 1) ^ (D + 2)) *
          (2 * (n : ℝ) ^ (-(p + ((D + 2 : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left h1 h3
    _ = 2 * (7 ^ D * (G + 3)) * (((n : ℝ) + 1) ^ (D + 2) *
          (n : ℝ) ^ (-(p + ((D + 2 : ℕ) : ℝ)))) := by ring
    _ ≤ 2 * (7 ^ D * (G + 3)) * (2 ^ (D + 2) * (n : ℝ) ^ (-p)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (7 ^ D * (G + 3) * 2 ^ (D + 3)) * (n : ℝ) ^ (-p) := by ring

/-- `eq:localmart` for the walk with a drift field: with probability at least `1 - Cn^{-p}`,
`|𝓜^y_n| ≤ C (√(B_y L) + L)` for all lattice `|y| ≤ 3n`, with `C` independent of the drift
field. -/
theorem exists_drift_local_mart (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ξ : Site d → EuclideanSpace ℝ (Fin d)},
      (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
      ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        {X : ℕ → Ω → Site d}, IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ∃ y : Site d, euclidNorm y ≤ 3 * n ∧
          C * (Real.sqrt ((∑ j ∈ range n, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) *
              Real.log (n + 2)) + Real.log (n + 2)) <
            |driftDynkin ε ξ (fun z => b (z - y)) X n ω|} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨Cdet, hCdet0, hCdet⟩ := exists_event_bound_drift hd hε hgrad
    (K := p + ((d + 2 : ℕ) : ℝ)) (by positivity)
  refine ⟨Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 3), by positivity, ?_⟩
  intro ξ hξ Ω _ μ _ X hX n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  set Y : Finset (Site d) := ballFinset d (3 * (n : ℝ)) with hY
  set B : Site d → Set Ω := fun y =>
    {ω | Cdet * (Real.sqrt ((∑ j ∈ range n, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) *
        Real.log (n + 2)) + Real.log (n + 2)) <
      |driftDynkin ε ξ (fun z => b (z - y)) X n ω|} with hB
  have hbound : ∀ y ∈ Y, μ (B y) ≤ ENNReal.ofReal (((Cg ^ 2 + 3) * ((n : ℝ) + 1)) *
      (2 * Real.exp (-((p + ((d + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))) := by
    intro y _
    refine (hCdet hξ hX n hn y).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (clog_ceil_add_one_le Cg n) (by positivity)
  have hYcard : (Y.card : ℝ) ≤ (7 * ((n : ℝ) + 1)) ^ d :=
    (card_ballFinset_le d (R := 3 * (n : ℝ)) (by positivity)).trans
      (pow_le_pow_left₀ (by positivity) (by linarith) d)
  set a : ℝ := ((Cg ^ 2 + 3) * ((n : ℝ) + 1)) *
    (2 * Real.exp (-((p + ((d + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) with ha
  have ha0 : 0 ≤ a := by positivity
  refine (measure_mono (t := ⋃ y ∈ Y, B y) ?_).trans ?_
  · rintro ω ⟨y, hy3, hlt⟩
    simp only [Set.mem_iUnion]
    refine ⟨y, ?_, ?_⟩
    · rw [hY, mem_ballFinset_iff]
      exact hy3
    · have hlog : 0 ≤ Real.log (n + 2) := by
        apply Real.log_nonneg
        exact_mod_cast (by omega : 1 ≤ n + 2)
      have hterm : 0 ≤ Real.sqrt ((∑ j ∈ range n,
          (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) *
          Real.log (n + 2)) + Real.log (n + 2) :=
        add_nonneg (Real.sqrt_nonneg _) hlog
      have hconst : 0 ≤ 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 3) := by positivity
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hconst) hterm) hlt
  · calc μ (⋃ y ∈ Y, B y) ≤ ∑ y ∈ Y, μ (B y) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _y ∈ Y, ENNReal.ofReal a := sum_le_sum hbound
      _ = ENNReal.ofReal ((Y.card : ℝ) * a) := by
          simp only [sum_const, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul (p := (Y.card : ℝ)) (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 3)) *
            (n : ℝ) ^ (-p)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (Y.card : ℝ) * a ≤ (7 * ((n : ℝ) + 1)) ^ d * a :=
            mul_le_mul_of_nonneg_right hYcard ha0
          have h2 := union_bound_arith_drift hp.le (by omega : 1 ≤ n) d
            (G := Cg ^ 2) (sq_nonneg Cg)
          have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
          nlinarith [mul_nonneg hCdet0.le h3]

end CERW.Support.Norm.ContactDynkin

namespace CERW.Support.Norm.ContactPointwise

open CERW.Generic.Kernel CERW.Generic.Norm CERW.Support.Occupation

variable {d : ℕ}

/-- For `d ≥ 1`, `Λ_Ψ > 0`. -/
private lemma normMax_pos {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d) :
    0 < normMax Ψ := by
  obtain ⟨hcpos, hcle⟩ := normMin_pos_mul_le hΨ hd
  have hn : ‖coordVec (⟨0, by omega⟩ : Fin d)‖ = 1 := by
    simp [coordVec, PiLp.norm_single]
  have h2 := le_normMax_mul hΨ (coordVec (⟨0, by omega⟩ : Fin d))
  have h3 := hcle (coordVec (⟨0, by omega⟩ : Fin d))
  rw [hn] at h2 h3
  linarith

/-- A subgradient of a norm has Euclidean norm at most `Λ_Ψ`. -/
private lemma norm_le_normMax_of_isSubgradient {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) (hd : 1 ≤ d) {x ξ : EuclideanSpace ℝ (Fin d)} (hξ : IsSubgradient Ψ x ξ) :
    ‖ξ‖ ≤ normMax Ψ := by
  have h := (subgradient_euler hΨ hξ).2 ξ
  have h2 := le_normMax_mul hΨ ξ
  rw [real_inner_self_eq_norm_mul_norm] at h
  have h3 : ‖ξ‖ * ‖ξ‖ ≤ normMax Ψ * ‖ξ‖ := h.trans h2
  rcases eq_or_lt_of_le (norm_nonneg ξ) with h0 | h0
  · rw [← h0]
    exact (normMax_pos hΨ hd).le
  · exact le_of_mul_le_mul_right h3 h0

/-- The gradient of a norm has Euclidean norm at most `Λ_Ψ` everywhere: where `Ψ` is
differentiable it is a subgradient, and elsewhere it is `0`. -/
private lemma norm_gradient_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d)
    (v : EuclideanSpace ℝ (Fin d)) : ‖gradient Ψ v‖ ≤ normMax Ψ := by
  by_cases hv : DifferentiableAt ℝ Ψ v
  · exact norm_le_normMax_of_isSubgradient hΨ hd (gradient_isSubgradient hΨ hv)
  · have h0 : gradient Ψ v = 0 := by
      rw [gradient, fderiv_zero_of_not_differentiableAt hv]
      simp
    rw [h0, norm_zero]
    exact (normMax_pos hΨ hd).le

/-- The gradient of a function on `ℝ^d` is measurable. -/
private lemma measurable_gradient (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measurable (gradient Ψ) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ Ψ)

/-- A subgradient selection with `ξ 0 = 0` has norm at most `Λ_Ψ` at every site. -/
private lemma norm_selection_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    (x : Site d) : ‖ξ x‖ ≤ normMax Ψ := by
  by_cases hx : x = 0
  · rw [hx, hξ0, norm_zero]
    exact (normMax_pos hΨ hd).le
  · exact norm_le_normMax_of_isSubgradient hΨ hd (hξ x hx)

/-- For a measurable field `g` of norm at most `Λ`, `v ↦ ⟪g v, K(v - z)⟫` is integrable on a
measurable set of finite volume. -/
private lemma integrableOn_inner_field_newtonField (hd : 2 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (z : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => inner ℝ (g v) (newtonField (v - z))) D volume := by
  have hbase : IntegrableOn (fun v => ‖v - z‖ ^ (1 - (d : ℝ))) D volume :=
    (integrableOn_and_setIntegral_le (d := d) (by omega : 1 ≤ d) hD hDfin z).1
  have hcomp : Measurable (fun v : EuclideanSpace ℝ (Fin d) => newtonField (v - z)) :=
    measurable_newtonField.comp (measurable_id.sub measurable_const)
  refine (hbase.const_mul Λ).mono' (hg.inner hcomp).aestronglyMeasurable ?_
  filter_upwards with v
  calc ‖inner ℝ (g v) (newtonField (v - z))‖
      ≤ ‖g v‖ * ‖newtonField (v - z)‖ := norm_inner_le_norm _ _
    _ = ‖g v‖ * ‖v - z‖ ^ (1 - (d : ℝ)) := by rw [norm_newtonField hd]
    _ ≤ Λ * ‖v - z‖ ^ (1 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_right (hΛ v) (Real.rpow_nonneg (norm_nonneg _) _)

/-- The Bregman integrand `‖∇Ψ v - ξ₀‖ ‖v - z‖^{1-d}` is integrable on a measurable set of finite
volume when `‖ξ₀‖ ≤ Λ_Ψ`. -/
private lemma integrableOn_norm_gradient_sub_mul {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) (hd : 1 ≤ d) {ξ₀ : EuclideanSpace ℝ (Fin d)} (hξ₀ : ‖ξ₀‖ ≤ normMax Ψ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (z : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => ‖gradient Ψ v - ξ₀‖ * ‖v - z‖ ^ (1 - (d : ℝ))) D volume := by
  have hbase : IntegrableOn (fun v => ‖v - z‖ ^ (1 - (d : ℝ))) D volume :=
    (integrableOn_and_setIntegral_le (d := d) hd hD hDfin z).1
  have hmeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
      ‖gradient Ψ v - ξ₀‖ * ‖v - z‖ ^ (1 - (d : ℝ))) :=
    ((measurable_gradient Ψ).sub measurable_const).norm.mul
      ((measurable_id.sub measurable_const).norm.pow_const _)
  refine (hbase.const_mul (2 * normMax Ψ)).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with v
  have hnn : 0 ≤ ‖gradient Ψ v - ξ₀‖ * ‖v - z‖ ^ (1 - (d : ℝ)) :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  rw [Real.norm_of_nonneg hnn]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _)
  calc ‖gradient Ψ v - ξ₀‖ ≤ ‖gradient Ψ v‖ + ‖ξ₀‖ := norm_sub_le _ _
    _ ≤ normMax Ψ + normMax Ψ := add_le_add (norm_gradient_le hΨ hd v) hξ₀
    _ = 2 * normMax Ψ := by ring


/-- If `‖w x‖ ≤ Λ`, the sum `Σ ⟪w x, F x⟫` is at most `Λ` times the sum of the norms of `F x`. -/
private lemma abs_sum_inner_le {Λ : ℝ} (S : Finset (Site d))
    (w F : Site d → EuclideanSpace ℝ (Fin d)) (hw : ∀ x, ‖w x‖ ≤ Λ) :
    |∑ x ∈ S, inner ℝ (w x) (F x)| ≤ Λ * ∑ x ∈ S, ‖F x‖ := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  calc |inner ℝ (w x) (F x)| ≤ ‖w x‖ * ‖F x‖ := abs_real_inner_le_norm _ _
    _ ≤ Λ * ‖F x‖ := mul_le_mul_of_nonneg_right (hw x) (norm_nonneg _)

/-- Replacing the gradient of the kernel by the Newtonian field costs `Λ` times the error of the
unit-vector version. -/
private lemma abs_sum_inner_centralDiff_sub_le {Λ c : ℝ} (S : Finset (Site d))
    (w : Site d → EuclideanSpace ℝ (Fin d)) (hw : ∀ x, ‖w x‖ ≤ Λ)
    (F G : Site d → EuclideanSpace ℝ (Fin d)) :
    |∑ x ∈ S, inner ℝ (w x) (F x) - c * ∑ x ∈ S, inner ℝ (w x) (G x)| ≤
      Λ * ∑ x ∈ S, ‖F x - c • G x‖ := by
  have hrew : ∑ x ∈ S, inner ℝ (w x) (F x) - c * ∑ x ∈ S, inner ℝ (w x) (G x) =
      ∑ x ∈ S, inner ℝ (w x) (F x - c • G x) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [inner_sub_right, inner_smul_right]
  rw [hrew]
  exact abs_sum_inner_le S w (fun x => F x - c • G x) hw

/-- The pointwise error of replacing the kernel value at a site by its cell average, for a vector
`w` of norm at most `Λ`, is `Λ` times the error for the normalized vector `Λ⁻¹ w`. -/
private lemma abs_inner_sub_setIntegral_eq {Λ : ℝ} (hΛ : 0 < Λ) (w a : EuclideanSpace ℝ (Fin d))
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (A : Set (EuclideanSpace ℝ (Fin d))) :
    |inner ℝ w a - ∫ v in A, inner ℝ w (f v)| =
      Λ * |inner ℝ (Λ⁻¹ • w) a - ∫ v in A, inner ℝ (Λ⁻¹ • w) (f v)| := by
  obtain ⟨w', rfl⟩ : ∃ w' : EuclideanSpace ℝ (Fin d), w = Λ • w' :=
    ⟨Λ⁻¹ • w, by rw [smul_inv_smul₀ hΛ.ne']⟩
  rw [inv_smul_smul₀ hΛ.ne']
  simp only [real_inner_smul_left]
  rw [integral_const_mul, ← mul_sub, abs_mul, abs_of_pos hΛ]

/-- The kernel values at the sites of a finite set differ from their cell averages by a
logarithmic sum, for vectors of norm at most `Λ`. -/
private lemma exists_sum_abs_inner_sub_setIntegral_le (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Finset (Site d)) (w : Site d → EuclideanSpace ℝ (Fin d))
      (y : Site d) (R' : ℝ), 1 ≤ R' → (∀ x, ‖w x‖ ≤ Λ) →
      (∀ x ∈ E, euclidNorm (x - y) ≤ R') →
        ∑ x ∈ E, |inner ℝ (w x) (newtonField (toSpace x - toSpace y)) -
            ∫ v in cell x, inner ℝ (w x) (newtonField (v - toSpace y))|
          ≤ C * Real.log (R' + 2) := by
  obtain ⟨Cb, hCb0, hCb⟩ :=
    CERW.Support.LocalTime.exists_sum_abs_newtonField_sub_setIntegral_le (d := d) hd
  refine ⟨Λ * Cb, mul_nonneg hΛ.le hCb0, fun E w y R' hR' hw hE => ?_⟩
  have hw1 : ∀ x, ‖Λ⁻¹ • w x‖ ≤ 1 := by
    intro x
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hΛ.le]
    calc Λ⁻¹ * ‖w x‖ ≤ Λ⁻¹ * Λ := mul_le_mul_of_nonneg_left (hw x) (inv_nonneg.mpr hΛ.le)
      _ = 1 := inv_mul_cancel₀ hΛ.ne'
  have hsum := hCb E (fun x => Λ⁻¹ • w x) y R' hR' hw1 hE
  calc ∑ x ∈ E, |inner ℝ (w x) (newtonField (toSpace x - toSpace y)) -
          ∫ v in cell x, inner ℝ (w x) (newtonField (v - toSpace y))|
      = Λ * ∑ x ∈ E, |inner ℝ (Λ⁻¹ • w x) (newtonField (toSpace x - toSpace y)) -
          ∫ v in cell x, inner ℝ (Λ⁻¹ • w x) (newtonField (v - toSpace y))| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ =>
          abs_inner_sub_setIntegral_eq hΛ (w x) _ (fun v => newtonField (v - toSpace y)) _
    _ ≤ Λ * (Cb * Real.log (R' + 2)) := mul_le_mul_of_nonneg_left hsum hΛ.le
    _ = Λ * Cb * Real.log (R' + 2) := by ring


/-- On one cell, replacing a fixed vector `ξ₀` by the gradient of the norm inside the kernel
integral costs at most the Bregman integral `∫ ‖∇Ψ v - ξ₀‖ ‖v - z‖^{1-d}`. -/
private lemma abs_setIntegral_inner_sub_gradient_le (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {ξ₀ : EuclideanSpace ℝ (Fin d)}
    (hξ₀ : ‖ξ₀‖ ≤ normMax Ψ) (x : Site d) (z : EuclideanSpace ℝ (Fin d)) :
    |(∫ v in cell x, inner ℝ ξ₀ (newtonField (v - z))) -
        ∫ v in cell x, inner ℝ (gradient Ψ v) (newtonField (v - z))| ≤
      ∫ v in cell x, ‖gradient Ψ v - ξ₀‖ * ‖v - z‖ ^ (1 - (d : ℝ)) := by
  have hcellmeas : MeasurableSet (cell x) := measurableSet_cell x
  have hcellfin : volume (cell x) ≠ ⊤ := by
    rw [volume_cell]
    exact ENNReal.one_ne_top
  have hleft := integrableOn_inner_field_newtonField hd (g := fun _ => ξ₀) measurable_const
    (fun _ => hξ₀) hcellmeas hcellfin z
  have hright := integrableOn_inner_field_newtonField hd (measurable_gradient Ψ)
    (norm_gradient_le hΨ (by omega)) hcellmeas hcellfin z
  rw [← integral_sub hleft hright, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le
    (integrableOn_norm_gradient_sub_mul hΨ (by omega) hξ₀ hcellmeas hcellfin z) ?_
  filter_upwards with v
  calc ‖inner ℝ ξ₀ (newtonField (v - z)) - inner ℝ (gradient Ψ v) (newtonField (v - z))‖
      = ‖inner ℝ (ξ₀ - gradient Ψ v) (newtonField (v - z))‖ := by rw [inner_sub_left]
    _ ≤ ‖ξ₀ - gradient Ψ v‖ * ‖newtonField (v - z)‖ := norm_inner_le_norm _ _
    _ = ‖gradient Ψ v - ξ₀‖ * ‖v - z‖ ^ (1 - (d : ℝ)) := by
        rw [norm_sub_rev, norm_newtonField hd]

/-- Replacing the subgradients `ξ x` by the gradient of the norm in the sum of cell integrals of
the Newtonian field costs at most the Bregman sum. -/
private lemma abs_sum_setIntegral_sub_gradient_le (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ : ∀ x, ‖ξ x‖ ≤ normMax Ψ)
    (S : Finset (Site d)) (z : EuclideanSpace ℝ (Fin d)) {C : ℝ}
    (hC : ∑ x ∈ S, ∫ v in cell x, ‖gradient Ψ v - ξ x‖ * ‖v - z‖ ^ (1 - (d : ℝ)) ≤ C) :
    |(∑ x ∈ S, ∫ v in cell x, inner ℝ (ξ x) (newtonField (v - z))) -
        ∑ x ∈ S, ∫ v in cell x, inner ℝ (gradient Ψ v) (newtonField (v - z))| ≤ C := by
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum fun x _ => abs_setIntegral_inner_sub_gradient_le hd hΨ (hξ x) x z).trans hC)

/-- The norm potential of the set of cells of a finite set of sites is `2ε/ω_d` times the sum
of the cell integrals of `⟪∇Ψ v, K(v - z)⟫`. -/
private lemma normPotential_cellSet_eq (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) (ε : ℝ) (X : ℕ → Site d) (n : ℕ) (z : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε Ψ (cellSet X n) z =
      2 * ε / unitBallVolume d *
        ∑ x ∈ departureRange X n, ∫ v in cell x, inner ℝ (gradient Ψ v) (newtonField (v - z)) := by
  have hD : ∫ v in cellSet X n, inner ℝ (gradient Ψ v) (newtonField (v - z)) =
      ∑ x ∈ departureRange X n, ∫ v in cell x, inner ℝ (gradient Ψ v) (newtonField (v - z)) := by
    rw [cellSet]
    exact integral_biUnion_finset (departureRange X n) (fun x _ => measurableSet_cell x)
      (fun x _ y _ hxy => cell_disjoint hxy)
      (fun x _ => integrableOn_inner_field_newtonField hd (measurable_gradient Ψ)
        (norm_gradient_le hΨ (by omega)) (measurableSet_cell x)
        (by rw [volume_cell]; exact ENNReal.one_ne_top) z)
  have hcongr : ∫ v in cellSet X n, inner ℝ (gradient Ψ v) (v - z) / ‖v - z‖ ^ d =
      ∫ v in cellSet X n, inner ℝ (gradient Ψ v) (newtonField (v - z)) :=
    setIntegral_congr_fun (measurableSet_cellSet X n)
      (fun v _ => (inner_newtonField (gradient Ψ v) (v - z)).symm)
  rw [normPotential, hcongr, hD]


/-- Scaling inside an absolute difference by a nonnegative constant. -/
private lemma abs_mul_sub_mul_eq {c : ℝ} (hc : 0 ≤ c) (a b : ℝ) :
    |c * a - c * b| = c * |a - b| := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hc]

/-- The absolute difference of two finite sums is at most the sum of the absolute differences. -/
private lemma abs_sum_sub_sum_le {ι : Type*} (S : Finset ι) (f g : ι → ℝ) :
    |∑ x ∈ S, f x - ∑ x ∈ S, g x| ≤ ∑ x ∈ S, |f x - g x| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-- Triangle inequality along a chain of three steps. -/
private lemma abs_sub_le_add_add {a b c e p q r : ℝ} (h1 : |a - b| ≤ p) (h2 : |b - c| ≤ q)
    (h3 : |c - e| ≤ r) : |a - e| ≤ p + (q + r) :=
  calc |a - e| ≤ |a - b| + |b - e| := abs_sub_le _ _ _
    _ ≤ |a - b| + (|b - c| + |c - e|) := add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ p + (q + r) := add_le_add h1 (add_le_add h2 h3)

open CERW.Support.Law CERW.Support.LocalTime in
/-- The source sum of the Dynkin formula for a subgradient selection `ξ` differs from the norm
potential of the cell set by `O(ε log(R' + 2))`, uniformly in `ε`, `ξ` and the path. -/
theorem exists_abs_source_sum_sub_normPotential_le {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (hB : CERW.Support.Norm.ContactShared.BregmanSumBound d Ψ)
    {b : Site d → ℝ} {Ca R Cg : ℝ} (hR : 1 ≤ R)
    (hgradA : ∀ x, R ≤ euclidNorm x →
      ‖centralDiff b x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x‖ ≤
        Ca * euclidNorm x ^ (-(d : ℝ)))
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ) (y : Site d) (R' : ℝ), 1 ≤ R' → euclidNorm y ≤ 2 * R' →
      (∀ x ∈ departureRange X n, euclidNorm (x - y) ≤ R' ∧ cell x ⊆ Metric.ball 0 R') →
        |ε * ∑ x ∈ departureRange X n, inner ℝ (ξ x) (centralDiff b (x - y)) -
            normPotential d ε Ψ (cellSet X n) (toSpace y)| ≤ C * ε * Real.log (R' + 2) := by
  have hd1 : 1 ≤ d := by omega
  have hΛ : 0 < normMax Ψ := normMax_pos hΨ hd1
  obtain ⟨Ca', hCa'0, hCa'⟩ :=
    exists_sum_norm_centralDiff_sub_newtonField_le (d := d) hd hR hgradA hgrad
  obtain ⟨Cb', hCb'0, hCb'⟩ := exists_sum_abs_inner_sub_setIntegral_le hd hΛ
  obtain ⟨CB, hCB0, hCB⟩ := hB
  have hcoef : 0 ≤ 2 / unitBallVolume d := (div_pos (by norm_num) (unitBallVolume_pos d)).le
  refine ⟨normMax Ψ * Ca' + (2 / unitBallVolume d) * (Cb' + CB), ?_, ?_⟩
  · exact add_nonneg (mul_nonneg hΛ.le hCa'0)
      (mul_nonneg hcoef (add_nonneg hCb'0 hCB0))
  · intro ε hε ξ hξ hξ0 X n y R' hR' hy hcell
    have hξΛ : ∀ x, ‖ξ x‖ ≤ normMax Ψ := norm_selection_le hΨ hd1 hξ hξ0
    set c : ℝ := 2 / unitBallVolume d with hc
    set S0 : ℝ := ∑ x ∈ departureRange X n, inner ℝ (ξ x) (centralDiff b (x - y)) with hS0
    set S1 : ℝ := ∑ x ∈ departureRange X n,
      inner ℝ (ξ x) (newtonField (toSpace x - toSpace y)) with hS1
    set S2 : ℝ := ∑ x ∈ departureRange X n,
      ∫ v in cell x, inner ℝ (ξ x) (newtonField (v - toSpace y)) with hS2
    set S3 : ℝ := ∑ x ∈ departureRange X n,
      ∫ v in cell x, inner ℝ (gradient Ψ v) (newtonField (v - toSpace y)) with hS3
    have h1 : |S0 - c * S1| ≤ normMax Ψ * Ca' * Real.log (R' + 2) := by
      have hsum := hCa' (departureRange X n) y R' hR' (fun x hx => (hcell x hx).1)
      have h := abs_sum_inner_centralDiff_sub_le (c := c) (departureRange X n) ξ hξΛ
        (fun x => centralDiff b (x - y)) (fun x => newtonField (toSpace x - toSpace y))
      simp only [toSpace_sub] at hsum
      calc |S0 - c * S1| ≤ normMax Ψ * ∑ x ∈ departureRange X n,
            ‖centralDiff b (x - y) - c • newtonField (toSpace x - toSpace y)‖ := h
        _ ≤ normMax Ψ * (Ca' * Real.log (R' + 2)) := mul_le_mul_of_nonneg_left hsum hΛ.le
        _ = normMax Ψ * Ca' * Real.log (R' + 2) := by ring
    have h2 : |c * S1 - c * S2| ≤ c * (Cb' * Real.log (R' + 2)) := by
      have hsum := hCb' (departureRange X n) ξ y R' hR' hξΛ (fun x hx => (hcell x hx).1)
      rw [abs_mul_sub_mul_eq hcoef]
      exact mul_le_mul_of_nonneg_left ((abs_sum_sub_sum_le _ _ _).trans hsum) hcoef
    have h3 : |c * S2 - c * S3| ≤ c * (CB * Real.log (R' + 2)) := by
      have hsum := hCB ξ hξ hξ0 (departureRange X n) (toSpace y) R' hR'
        (fun x hx => (hcell x hx).2) (by rwa [norm_toSpace])
      rw [abs_mul_sub_mul_eq hcoef]
      exact mul_le_mul_of_nonneg_left
        (abs_sum_setIntegral_sub_gradient_le hd hΨ hξΛ (departureRange X n) (toSpace y) hsum)
        hcoef
    have hmain : |S0 - c * S3| ≤
        normMax Ψ * Ca' * Real.log (R' + 2) +
          (c * (Cb' * Real.log (R' + 2)) + c * (CB * Real.log (R' + 2))) :=
      abs_sub_le_add_add h1 h2 h3
    have hpot : normPotential d ε Ψ (cellSet X n) (toSpace y) = ε * (c * S3) := by
      rw [normPotential_cellSet_eq hd hΨ, hc]
      ring
    calc |ε * S0 - normPotential d ε Ψ (cellSet X n) (toSpace y)|
        = |ε * S0 - ε * (c * S3)| := by rw [hpot]
      _ = ε * |S0 - c * S3| := abs_mul_sub_mul_eq hε _ _
      _ ≤ ε * (normMax Ψ * Ca' * Real.log (R' + 2) +
          (c * (Cb' * Real.log (R' + 2)) + c * (CB * Real.log (R' + 2)))) :=
          mul_le_mul_of_nonneg_left hmain hε
      _ = (normMax Ψ * Ca' + c * (Cb' + CB)) * ε * Real.log (R' + 2) := by ring

/-- A cell lies in the open ball of radius `R` when its site satisfies `|x| + √d/2 < R`. -/
private lemma cell_subset_ball_of_lt (x : Site d) {R : ℝ}
    (h : euclidNorm x + Real.sqrt d / 2 < R) : cell x ⊆ Metric.ball 0 R := by
  intro v hv
  rw [mem_ball_zero_iff]
  calc ‖v‖ ≤ ‖toSpace x‖ + ‖v - toSpace x‖ := norm_le_norm_add_norm_sub' v (toSpace x)
    _ = euclidNorm x + ‖v - toSpace x‖ := by rw [norm_toSpace]
    _ ≤ euclidNorm x + Real.sqrt d / 2 :=
        add_le_add le_rfl (norm_sub_toSpace_le_of_mem_cell hv)
    _ < R := h

/-- The logarithmic comparison constant `1 + log(4 + √d)/log 3` is nonnegative. -/
private lemma one_add_log_div_log_three_nonneg (d : ℕ) :
    0 ≤ 1 + Real.log (4 + Real.sqrt d) / Real.log 3 := by
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogd : 0 ≤ Real.log (4 + Real.sqrt d) :=
    Real.log_nonneg (by linarith [Real.sqrt_nonneg d] : (1 : ℝ) ≤ 4 + Real.sqrt d)
  have := div_nonneg hlogd (le_of_lt hlog3pos)
  linarith

/-- For `n ≥ 1`, the logarithm of `4n + √d + 2` is at most the logarithmic comparison
constant times `log(n + 2)`. -/
private lemma log_four_mul_add_sqrt_add_two_le (d n : ℕ) (hn : 1 ≤ n) :
    Real.log (4 * (n : ℝ) + Real.sqrt d + 2) ≤
      (1 + Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hsn : Real.sqrt d ≤ Real.sqrt d * n := by
    simpa using mul_le_mul_of_nonneg_left hn1 hs
  have hle1 : 4 * (n : ℝ) + Real.sqrt d + 2 ≤ (4 + Real.sqrt d) * ((n : ℝ) + 2) := by
    nlinarith [hs, hsn, hn1]
  have hpos1 : 0 < 4 * (n : ℝ) + Real.sqrt d + 2 := by linarith [hs, hn1]
  have hn2 : 0 < (n : ℝ) + 2 := by linarith [hn1]
  have h4 : 0 < 4 + Real.sqrt d := by linarith [hs]
  have hpos2 : 0 < (4 + Real.sqrt d) * ((n : ℝ) + 2) := mul_pos h4 hn2
  have hlog1 : Real.log (4 * (n : ℝ) + Real.sqrt d + 2) ≤
      Real.log ((4 + Real.sqrt d) * ((n : ℝ) + 2)) :=
    Real.log_le_log hpos1 hle1
  have hmul : Real.log ((4 + Real.sqrt d) * ((n : ℝ) + 2)) =
      Real.log (4 + Real.sqrt d) + Real.log ((n : ℝ) + 2) := by
    rw [Real.log_mul]
    · exact ne_of_gt h4
    · exact ne_of_gt hn2
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3 : Real.log 3 ≤ Real.log ((n : ℝ) + 2) := by
    apply Real.log_le_log (by norm_num)
    have h3n : 3 ≤ n + 2 := by omega
    exact_mod_cast h3n
  have hlogd : 0 ≤ Real.log (4 + Real.sqrt d) :=
    Real.log_nonneg (by linarith [hs] : (1 : ℝ) ≤ 4 + Real.sqrt d)
  have hratio : 1 ≤ Real.log ((n : ℝ) + 2) / Real.log 3 := by
    rw [le_div_iff₀ hlog3pos]
    linarith
  have hstep : Real.log (4 + Real.sqrt d) ≤
      (Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2) := by
    calc Real.log (4 + Real.sqrt d) = Real.log (4 + Real.sqrt d) * 1 := by ring
      _ ≤ Real.log (4 + Real.sqrt d) * (Real.log ((n : ℝ) + 2) / Real.log 3) :=
          mul_le_mul_of_nonneg_left hratio hlogd
      _ = (Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2) := by ring
  calc Real.log (4 * (n : ℝ) + Real.sqrt d + 2)
      ≤ Real.log ((4 + Real.sqrt d) * ((n : ℝ) + 2)) := hlog1
    _ = Real.log (4 + Real.sqrt d) + Real.log ((n : ℝ) + 2) := hmul
    _ ≤ Real.log ((n : ℝ) + 2) +
        (Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2) := by
        linarith [hstep]
    _ = (1 + Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2) := by ring

/-- On a path with `|Y_j| ≤ j` and a target `|y| ≤ 3n`, every departure site `x` satisfies
`|x - y| ≤ R'` and its cell lies in the ball of radius `R'`, where `R' = 4n + √d`. -/
private lemma departureRange_bounds (Y : ℕ → Site d) (hpath : ∀ j, euclidNorm (Y j) ≤ j)
    (n : ℕ) (hn : 1 ≤ n) (y : Site d) (hy : euclidNorm y ≤ 3 * n) :
    ∀ x ∈ departureRange Y n, euclidNorm (x - y) ≤ 4 * (n : ℝ) + Real.sqrt d ∧
      cell x ⊆ Metric.ball 0 (4 * (n : ℝ) + Real.sqrt d) := by
  intro x hx
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  rw [departureRange] at hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  have hjn : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
  have hxnorm : euclidNorm (Y j) ≤ (n : ℝ) := (hpath j).trans hjn
  refine ⟨?_, cell_subset_ball_of_lt _ ?_⟩
  · calc euclidNorm (Y j - y)
        ≤ euclidNorm (Y j) + euclidNorm y := euclidNorm_sub_le _ _
      _ ≤ (n : ℝ) + 3 * (n : ℝ) := add_le_add hxnorm hy
      _ = 4 * (n : ℝ) := by ring
      _ ≤ 4 * (n : ℝ) + Real.sqrt d := by linarith
  · linarith

/-- Logarithmic growth of `b` transfers to a bound by `log (R' + 2)` at points of norm at most
`R'`, with a nonnegative constant. -/
private lemma abs_le_max_mul_log {b : Site d → ℝ} {Cb : ℝ}
    (hCb : ∀ x, |b x| ≤ Cb * Real.log (euclidNorm x + 2)) {z : Site d} {R' : ℝ}
    (hz : euclidNorm z ≤ R') :
    |b z| ≤ max Cb 0 * Real.log (R' + 2) := by
  have hlog0 : 0 ≤ Real.log (euclidNorm z + 2) :=
    Real.log_nonneg (by linarith [LatticeProb.euclidNorm_nonneg z])
  calc |b z| ≤ Cb * Real.log (euclidNorm z + 2) := hCb z
    _ ≤ max Cb 0 * Real.log (euclidNorm z + 2) :=
        mul_le_mul_of_nonneg_right (le_max_left Cb 0) hlog0
    _ ≤ max Cb 0 * Real.log (R' + 2) :=
        mul_le_mul_of_nonneg_left
          (Real.log_le_log (by linarith [LatticeProb.euclidNorm_nonneg z]) (by linarith))
          (le_max_right Cb 0)


/-- The two endpoint terms and the source-sum error combine into `(2 C_b + C_S)(1 + ε) L`. -/
private lemma abs_endpoint_add_source_le {a₁ a₂ s Cb CS ε L : ℝ} (hb₁ : |a₁| ≤ Cb * L)
    (hb₂ : |a₂| ≤ Cb * L) (hs : |s| ≤ CS * ε * L) (hCb : 0 ≤ Cb) (hCS : 0 ≤ CS) (hε : 0 ≤ ε)
    (hL : 0 ≤ L) : |a₁ - a₂ + s| ≤ (2 * Cb + CS) * (1 + ε) * L := by
  have h1 : 0 ≤ (2 * Cb * ε) * L := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCb) hε) hL
  have h2 : 0 ≤ CS * L := mul_nonneg hCS hL
  calc |a₁ - a₂ + s| ≤ |a₁ - a₂| + |s| := abs_add_le _ _
    _ ≤ (|a₁| + |a₂|) + |s| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ Cb * L + Cb * L + CS * ε * L := add_le_add (add_le_add hb₁ hb₂) hs
    _ ≤ (2 * Cb + CS) * (1 + ε) * L := by linarith

open CERW.Support.Law CERW.Support.LocalTime CERW.Support.Drift in
/-- The pointwise decomposition of the local time: for a subgradient selection `ξ` and a path from
the origin with `|X_j| ≤ j`, `ℓ_n(y) - U_{D_n}(y) + 𝓜^y_n` is `O((1 + ε) log(n + 2))` for lattice
targets `|y| ≤ 3n`, uniformly in `ε`, `ξ` and the path. -/
theorem exists_abs_localTime_sub_normPotential_add_driftDynkin_le {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (hB : CERW.Support.Norm.ContactShared.BregmanSumBound d Ψ)
    {b : Site d → ℝ} {h : ℝ → ℝ} (hK : KernelFacts d b h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω), X 0 ω = 0 →
      (∀ j, euclidNorm (X j ω) ≤ j) → ∀ n : ℕ, 1 ≤ n → ∀ y : Site d,
      euclidNorm y ≤ 3 * n →
        |(localTime (fun j => X j ω) n y : ℝ) -
            normPotential d ε Ψ (cellSet (fun j => X j ω) n) (toSpace y) +
            driftDynkin ε ξ (fun z => b (z - y)) X n ω| ≤ C * (1 + ε) * Real.log (n + 2) := by
  obtain ⟨R, Ca, hR, hgradA⟩ := hK.gradAsymp
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  obtain ⟨Cb, hb⟩ := hK.growth
  obtain ⟨C_S, hCS, hsource⟩ :=
    exists_abs_source_sum_sub_normPotential_le hd hΨ hB hR hgradA hgrad
  set Cb' : ℝ := max Cb 0 with hCb'
  set K : ℝ := 1 + Real.log (4 + Real.sqrt d) / Real.log 3 with hK'
  have hCb'0 : 0 ≤ Cb' := le_max_right Cb 0
  have hKnn : 0 ≤ K := one_add_log_div_log_three_nonneg d
  refine ⟨(2 * Cb' + C_S) * K, mul_nonneg (by linarith) hKnn, ?_⟩
  intro ε hε ξ hξ hξ0 Ω X ω h0 hpath n hn y hy
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  set R' : ℝ := 4 * (n : ℝ) + Real.sqrt d with hR'
  set U : ℝ := normPotential d ε Ψ (cellSet (fun j => X j ω) n) (toSpace y) with hU
  rw [CERW.Support.Norm.ContactDynkin.localTime_eq_driftDynkin hK.poisson ε ξ hξ0 X ω h0 n y]
  set S : ℝ := ∑ x ∈ departureRange (fun j => X j ω) n, inner ℝ (ξ x) (centralDiff b (x - y))
    with hS
  have hgoal_eq : (b (X n ω - y) - b (-y) + ε * S - driftDynkin ε ξ (fun z => b (z - y)) X n ω) -
        U + driftDynkin ε ξ (fun z => b (z - y)) X n ω =
      b (X n ω - y) - b (-y) + (ε * S - U) := by ring
  rw [hgoal_eq]
  have hR'1 : 1 ≤ R' := by
    rw [hR']
    linarith
  have hsub : euclidNorm (X n ω - y) ≤ R' := by
    calc euclidNorm (X n ω - y) ≤ euclidNorm (X n ω) + euclidNorm y := euclidNorm_sub_le _ _
      _ ≤ (n : ℝ) + 3 * (n : ℝ) := add_le_add (hpath n) hy
      _ = 4 * (n : ℝ) := by ring
      _ ≤ R' := by rw [hR']; linarith
  have hneg : euclidNorm (-y) ≤ R' := by
    rw [CERW.Generic.Lattice.euclidNorm_neg]
    rw [hR']
    linarith
  have hb1 := abs_le_max_mul_log hb hsub
  have hb2 := abs_le_max_mul_log hb hneg
  have hsrc := hsource ε hε ξ hξ hξ0 (fun j => X j ω) n y R' hR'1 (by rw [hR']; linarith)
    (departureRange_bounds (fun j => X j ω) (fun j => hpath j) n hn y hy)
  have hlogR' : 0 ≤ Real.log (R' + 2) := Real.log_nonneg (by linarith)
  have hcomb : |b (X n ω - y) - b (-y) + (ε * S - U)| ≤
      (2 * Cb' + C_S) * (1 + ε) * Real.log (R' + 2) :=
    abs_endpoint_add_source_le hb1 hb2 hsrc hCb'0 hCS hε hlogR'
  have hlogK : Real.log (R' + 2) ≤ K * Real.log ((n : ℝ) + 2) := by
    rw [hR', hK']
    exact log_four_mul_add_sqrt_add_two_le d n hn
  have hcoef : 0 ≤ (2 * Cb' + C_S) * (1 + ε) := by
    exact mul_nonneg (by linarith) (by linarith)
  calc |b (X n ω - y) - b (-y) + (ε * S - U)|
      ≤ (2 * Cb' + C_S) * (1 + ε) * Real.log (R' + 2) := hcomb
    _ ≤ (2 * Cb' + C_S) * (1 + ε) * (K * Real.log ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hlogK hcoef
    _ = (2 * Cb' + C_S) * K * (1 + ε) * Real.log ((n : ℝ) + 2) := by ring

end CERW.Support.Norm.ContactPointwise

namespace CERW.Support.Norm.ContactPlanar

open CERW CERW.Support.Norm.ContactShared CERW.Support.Occupation

variable {d : ℕ}

/-- The truncated radial weight `s ↦ (1 + |s|)^{-d}` for `s < R`, and `0` for `s ≥ R`. -/
private noncomputable def radialWeight (d : ℕ) (R s : ℝ) : ℝ :=
  Set.indicator (Set.Iio R) (fun t : ℝ => (1 + |t|) ^ (-(d : ℝ))) s

/-- The truncated radial weight is measurable. -/
private theorem radialWeight_measurable (d : ℕ) (R : ℝ) : Measurable (radialWeight d R) := by
  unfold radialWeight
  exact (by fun_prop : Measurable fun t : ℝ => (1 + |t|) ^ (-(d : ℝ))).indicator
    measurableSet_Iio

/-- The truncated radial weight is nonnegative. -/
private theorem radialWeight_nonneg (d : ℕ) (R s : ℝ) : 0 ≤ radialWeight d R s := by
  unfold radialWeight
  exact Set.indicator_nonneg (fun t _ => Real.rpow_nonneg (by positivity) _) s

/-- The truncated radial weight is at most `1`. -/
private theorem radialWeight_le_one (d : ℕ) (R s : ℝ) : radialWeight d R s ≤ 1 := by
  unfold radialWeight
  by_cases h : s < R
  · rw [Set.indicator_of_mem (show s ∈ Set.Iio R from h)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg s])
      (by simp)
  · rw [Set.indicator_of_notMem (show s ∉ Set.Iio R from h)]
    exact zero_le_one

/-- Below the truncation radius the weight is `(1 + |s|)^{-d}`. -/
private theorem radialWeight_of_lt (d : ℕ) {R s : ℝ} (h : s < R) :
    radialWeight d R s = (1 + |s|) ^ (-(d : ℝ)) :=
  Set.indicator_of_mem (show s ∈ Set.Iio R from h) _

/-- Beyond the truncation radius the weight vanishes. -/
private theorem radialWeight_of_le (d : ℕ) {R s : ℝ} (h : R ≤ s) : radialWeight d R s = 0 :=
  Set.indicator_of_notMem (show s ∉ Set.Iio R from not_lt.mpr h) _

/-- The weight of the norm is the indicator of the ball of `(1 + ‖ζ‖)^{-d}`. -/
private theorem radialWeight_norm_eq_indicator (d : ℕ) (R : ℝ) :
    (fun ζ : EuclideanSpace ℝ (Fin d) => radialWeight d R ‖ζ‖) =
      Set.indicator (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R)
        (fun ζ => (1 + ‖ζ‖) ^ (-(d : ℝ))) := by
  ext ζ
  by_cases h : ‖ζ‖ < R
  · rw [radialWeight_of_lt d h, abs_of_nonneg (norm_nonneg ζ),
      Set.indicator_of_mem (show ζ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R from
        mem_ball_zero_iff.mpr h)]
  · rw [radialWeight_of_le d (not_lt.mp h),
      Set.indicator_of_notMem (show ζ ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R from
        fun hζ => h (mem_ball_zero_iff.mp hζ))]

/-- The truncated weight of the norm is integrable, with integral at most `σ_d log (1 + R)`. -/
private theorem integrable_radialWeight_norm (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => radialWeight d R ‖ζ‖) ∧
      ∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ ≤
        d * unitBallVolume d * Real.log (1 + R) := by
  obtain ⟨hint, hval⟩ := CERW.Generic.Kernel.integrableOn_ball_one_add_norm_rpow_and_integral_le
    hd hR
  rw [radialWeight_norm_eq_indicator]
  exact ⟨(integrable_indicator_iff measurableSet_ball).mpr hint,
    by rw [integral_indicator measurableSet_ball]; exact hval⟩

/-- The largest value of a norm on the unit sphere is nonnegative when `d ≥ 1`. -/
private theorem normMax_nonneg {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d) :
    0 ≤ normMax Ψ := by
  have hd0 : 0 < d := by omega
  have h1 := CERW.Generic.Norm.le_normMax_mul hΨ (coordVec (⟨0, hd0⟩ : Fin d))
  have h2 := (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 (coordVec (⟨0, hd0⟩ : Fin d))
  have h3 : ‖coordVec (⟨0, hd0⟩ : Fin d)‖ = 1 := by simp [coordVec, PiLp.norm_single]
  rw [h3] at h1
  linarith

/-- For `t ≥ 0`: `t (1 + t)^{-2} ≤ t^{-1}`. -/
private theorem rpow_mul_le_rpow_neg_one (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ (-(2 : ℝ)) * t ≤ t ^ (-(1 : ℝ)) := by
  rcases ht.eq_or_lt with rfl | hpos
  · simp
  · rw [Real.rpow_neg (by positivity), Real.rpow_neg hpos.le, Real.rpow_one, Real.rpow_two]
    rw [inv_mul_eq_div, div_le_iff₀ (by positivity), ← div_eq_inv_mul, le_div_iff₀ hpos]
    nlinarith

/-- The ball integral in the convolution estimate: for `d = 2`, the weighted `min (b, Ψ)` is
dominated by `Λ_Ψ |ζ|^{-1}` on the ball, which integrates to `Λ_Ψ σ_2 R`. -/
private theorem integral_weight_mul_min_le (hd : d = 2) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {R b : ℝ} (hR : 0 < R) (hb : 0 ≤ b) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ * min b (Ψ ζ) ≤
      normMax Ψ * (d * unitBallVolume d * R) := by
  have hd2 : (d : ℝ) = 2 := by rw [hd]; norm_num
  have hd1 : 1 ≤ d := by omega
  have hΛ := normMax_nonneg hΨ hd1
  obtain ⟨hint, hval⟩ := CERW.Generic.Kernel.integrableOn_ball_rpow_neg_and_integral_eq
    (d := d) (s := 1) (ρ := R) hd1 (by rw [hd2]; norm_num) hR
  have hgint : Integrable (Set.indicator (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R)
      (fun ζ => normMax Ψ * ‖ζ‖ ^ (-(1 : ℝ)))) :=
    (integrable_indicator_iff measurableSet_ball).mpr (hint.const_mul _)
  have hnn : ∀ y, 0 ≤ Ψ y := (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1
  calc ∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ * min b (Ψ ζ)
      ≤ ∫ ζ : EuclideanSpace ℝ (Fin d), Set.indicator (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R)
          (fun ζ => normMax Ψ * ‖ζ‖ ^ (-(1 : ℝ))) ζ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ζ => ?_) hgint
          (Filter.Eventually.of_forall fun ζ => ?_)
        · exact mul_nonneg (radialWeight_nonneg d R _) (le_min hb (hnn ζ))
        · beta_reduce
          by_cases h : ‖ζ‖ < R
          · rw [radialWeight_of_lt d h, abs_of_nonneg (norm_nonneg ζ),
              Set.indicator_of_mem (show ζ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R from
                mem_ball_zero_iff.mpr h), hd2]
            calc (1 + ‖ζ‖) ^ (-(2 : ℝ)) * min b (Ψ ζ)
                ≤ (1 + ‖ζ‖) ^ (-(2 : ℝ)) * (normMax Ψ * ‖ζ‖) :=
                  mul_le_mul_of_nonneg_left
                    ((min_le_right _ _).trans (CERW.Generic.Norm.le_normMax_mul hΨ ζ))
                    (Real.rpow_nonneg (by positivity) _)
              _ = normMax Ψ * ((1 + ‖ζ‖) ^ (-(2 : ℝ)) * ‖ζ‖) := by ring
              _ ≤ normMax Ψ * ‖ζ‖ ^ (-(1 : ℝ)) :=
                  mul_le_mul_of_nonneg_left (rpow_mul_le_rpow_neg_one _ (norm_nonneg ζ)) hΛ
          · rw [radialWeight_of_le d (not_lt.mp h), zero_mul,
              Set.indicator_of_notMem (show ζ ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R from
                fun hζ => h (mem_ball_zero_iff.mp hζ))]
      _ = normMax Ψ * ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R, ‖ζ‖ ^ (-(1 : ℝ)) := by
        rw [integral_indicator measurableSet_ball, integral_const_mul]
      _ = normMax Ψ * (d * unitBallVolume d * R) := by
        rw [hval, hd2]
        norm_num

/-- The sites of the departure range of a path with `|X_j| ≤ j` lie within `n` of the origin. -/
private theorem euclidNorm_le_of_mem_departureRange {X : ℕ → Site d} {n : ℕ}
    (hXn : ∀ j, euclidNorm (X j) ≤ j) {x : Site d} (hx : x ∈ departureRange X n) :
    euclidNorm x ≤ n := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  exact (hXn j).trans (by exact_mod_cast (Finset.mem_range.mp hj).le)

/-- The kernel `(1 + |x - z|)^{-d}` summed over the departure range, at a site `z` with
`|z| ≤ 3n`, is at most `C' log (n + 2)`. -/
private theorem kernel_sum_le (hd : d = 2) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (X : ℕ → Site d) (n : ℕ) (z : Site d), 1 ≤ n →
      (∀ j, euclidNorm (X j) ≤ j) → euclidNorm z ≤ 3 * n →
      ∑ x ∈ departureRange X n, (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) ≤
        C' * Real.log ((n : ℝ) + 2) := by
  obtain ⟨C, hC, hCs⟩ := CERW.Generic.Lattice.sum_finset_rpow_neg_le_log (d := d) (by omega)
  refine ⟨3 * C, by positivity, fun X n z hn hXn hz => ?_⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h4 : ∑ x ∈ departureRange X n, (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) ≤
      C * Real.log (4 * (n : ℝ) + 2) := by
    refine hCs (departureRange X n) z (4 * n) (by linarith) fun x hx => ?_
    calc euclidNorm (x - z) ≤ euclidNorm x + euclidNorm z := euclidNorm_sub_le x z
      _ ≤ n + 3 * n := add_le_add (euclidNorm_le_of_mem_departureRange hXn hx) hz
      _ = 4 * n := by ring
  have hlog : Real.log (4 * (n : ℝ) + 2) ≤ 3 * Real.log ((n : ℝ) + 2) := by
    have h3 : 3 * Real.log ((n : ℝ) + 2) = Real.log (((n : ℝ) + 2) ^ 3) := by
      rw [Real.log_pow]; norm_num
    rw [h3]
    refine Real.log_le_log (by linarith) ?_
    have : (0 : ℝ) ≤ n := by linarith
    nlinarith [sq_nonneg (n : ℝ), mul_nonneg this (sq_nonneg (n : ℝ))]
  calc _ ≤ C * Real.log (4 * (n : ℝ) + 2) := h4
    _ ≤ C * (3 * Real.log ((n : ℝ) + 2)) := mul_le_mul_of_nonneg_left hlog hC.le
    _ = 3 * C * Real.log ((n : ℝ) + 2) := by ring

/-- The recentred truncated weight `ζ ↦ w(‖y₀ - ζ‖)` is integrable. -/
private theorem integrable_radialWeight_sub (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R)
    (y₀ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => radialWeight d R ‖y₀ - ζ‖) :=
  (integrable_radialWeight_norm hd hR).1.comp_sub_left y₀

/-- The elementary comparison `1 + t + s ≤ (1 + s)(1 + t)`, in the form used for the weights. -/
private theorem rpow_mul_le_rpow_add {s t u : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : u ≤ t + s)
    (p : ℝ) (hp : p ≤ 0) (hu0 : 0 ≤ u) :
    (1 + s) ^ p * (1 + t) ^ p ≤ (1 + u) ^ p := by
  rw [← Real.mul_rpow (by linarith) (by linarith)]
  refine Real.rpow_le_rpow_of_nonpos (by linarith) ?_ hp
  nlinarith [mul_nonneg hs ht]

/-- If the cell of a site `y` lies in the ball `B(y₀, R)` and `z` is a site near `y₀`, the weight
of the cell is bounded below by the kernel at `z - y`. -/
private theorem weight_lower (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) (y₀ : EuclideanSpace ℝ (Fin d))
    (z y : Site d) (hzy : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2)
    (hcell : cell y ⊆ Metric.ball y₀ R) :
    (1 + Real.sqrt d) ^ (-(d : ℝ)) * (1 + euclidNorm (z - y)) ^ (-(d : ℝ)) ≤
      ∫ ζ in cell y, radialWeight d R ‖y₀ - ζ‖ := by
  have hint := (integrable_radialWeight_sub hd hR y₀).integrableOn (s := cell y)
  have hmeas := measurableSet_cell y
  have hvol : volume.real (cell y) = 1 := by rw [measureReal_def, volume_cell]; simp
  have hbound := setIntegral_ge_of_const_le_real (μ := volume) (s := cell y)
    (f := fun ζ : EuclideanSpace ℝ (Fin d) => radialWeight d R ‖y₀ - ζ‖)
    (c := (1 + Real.sqrt d) ^ (-(d : ℝ)) * (1 + euclidNorm (z - y)) ^ (-(d : ℝ))) hmeas
    (by rw [volume_cell]; exact ENNReal.one_ne_top) (fun ζ hζ => ?_) hint
  · rwa [hvol, mul_one] at hbound
  · have hζR : ‖y₀ - ζ‖ < R := by
      have := hcell hζ
      rwa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at this
    rw [radialWeight_of_lt d hζR, abs_of_nonneg (norm_nonneg _)]
    have h1 : ‖y₀ - ζ‖ ≤ euclidNorm (z - y) + Real.sqrt d := by
      have h2 : ‖ζ - toSpace y‖ ≤ Real.sqrt d / 2 := norm_sub_toSpace_le_of_mem_cell hζ
      have e1 : ‖y₀ - toSpace z‖ ≤ Real.sqrt d / 2 := by rw [norm_sub_rev]; exact hzy
      have e2 : ‖toSpace z - toSpace y‖ = euclidNorm (z - y) := by
        rw [← toSpace_sub, norm_toSpace]
      have e3 : ‖toSpace y - ζ‖ ≤ Real.sqrt d / 2 := by rw [norm_sub_rev]; exact h2
      calc ‖y₀ - ζ‖ = ‖(y₀ - toSpace z) + (toSpace z - toSpace y) + (toSpace y - ζ)‖ := by
            congr 1; abel
        _ ≤ ‖y₀ - toSpace z‖ + ‖toSpace z - toSpace y‖ + ‖toSpace y - ζ‖ := norm_add₃_le
        _ ≤ euclidNorm (z - y) + Real.sqrt d := by rw [e2] at *; linarith
    exact rpow_mul_le_rpow_add (Real.sqrt_nonneg _) (LatticeProb.euclidNorm_nonneg _)
      (by linarith) _ (by simp) (norm_nonneg _)

/-- On a cell of the departure range, the local time times the weight of the cell is at most the
integral over the cell of the weight times the dominating function. -/
private theorem cell_term_le (hd : 1 ≤ d) {R δ : ℝ} (hR : 0 < R) (X : ℕ → Site d) (n : ℕ)
    {y₀ : EuclideanSpace ℝ (Fin d)} (U : EuclideanSpace ℝ (Fin d) → ℝ)
    (hDball : cellSet X n ⊆ Metric.ball y₀ R)
    (hcr : ∀ ζ : EuclideanSpace ℝ (Fin d), ‖y₀ - ζ‖ < R → |cellLocalTime X n ζ - U ζ| ≤ δ)
    (hg : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      radialWeight d R ‖y₀ - ζ‖ * U ζ + radialWeight d R ‖y₀ - ζ‖ * δ))
    {x : Site d} (hx : x ∈ departureRange X n) :
    (localTime X n x : ℝ) * ∫ ζ in cell x, radialWeight d R ‖y₀ - ζ‖ ≤
      ∫ ζ in cell x, (radialWeight d R ‖y₀ - ζ‖ * U ζ + radialWeight d R ‖y₀ - ζ‖ * δ) := by
  rw [← integral_const_mul]
  refine setIntegral_mono_on ((integrable_radialWeight_sub hd hR y₀).const_mul _).integrableOn
    hg.integrableOn (measurableSet_cell x) fun ζ hζ => ?_
  have hζR : ‖y₀ - ζ‖ < R := by
    have := hDball (Set.mem_iUnion₂.mpr ⟨x, hx, hζ⟩)
    rwa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at this
  have hcl := hcr ζ hζR
  rw [cellLocalTime_of_mem_cell X n hζ] at hcl
  have hle' : (localTime X n x : ℝ) ≤ U ζ + δ := by linarith [(abs_le.mp hcl).2]
  calc (localTime X n x : ℝ) * radialWeight d R ‖y₀ - ζ‖
      = radialWeight d R ‖y₀ - ζ‖ * (localTime X n x : ℝ) := mul_comm _ _
    _ ≤ radialWeight d R ‖y₀ - ζ‖ * (U ζ + δ) :=
        mul_le_mul_of_nonneg_left hle' (radialWeight_nonneg d R _)
    _ = _ := by ring

/-- Outside the cell set the dominating function times the weight is nonnegative, because the
local time vanishes there. -/
private theorem dominating_nonneg_off {R δ : ℝ} (X : ℕ → Site d) (n : ℕ)
    {y₀ : EuclideanSpace ℝ (Fin d)} (U : EuclideanSpace ℝ (Fin d) → ℝ)
    (hcr : ∀ ζ : EuclideanSpace ℝ (Fin d), ‖y₀ - ζ‖ < R → |cellLocalTime X n ζ - U ζ| ≤ δ)
    {ζ : EuclideanSpace ℝ (Fin d)} (hζ : ζ ∈ (cellSet X n)ᶜ) :
    0 ≤ radialWeight d R ‖y₀ - ζ‖ * U ζ + radialWeight d R ‖y₀ - ζ‖ * δ := by
  by_cases hζR : ‖y₀ - ζ‖ < R
  · have hcl := hcr ζ hζR
    rw [cellLocalTime_eq_zero_of_not_mem X n hζ] at hcl
    have hU : 0 ≤ U ζ + δ := by linarith [(abs_le.mp hcl).2]
    calc (0 : ℝ) ≤ radialWeight d R ‖y₀ - ζ‖ * (U ζ + δ) :=
          mul_nonneg (radialWeight_nonneg d R _) hU
      _ = _ := by ring
  · rw [radialWeight_of_le d (not_lt.mp hζR)]
    simp

/-- The weighted sum of local times is at most the integral over the whole space of the weight
times the dominating function. -/
private theorem cell_sum_le_integral (hd : 1 ≤ d) {R δ : ℝ} (hR : 0 < R) (X : ℕ → Site d)
    (n : ℕ) {y₀ : EuclideanSpace ℝ (Fin d)} (U : EuclideanSpace ℝ (Fin d) → ℝ)
    (hDball : cellSet X n ⊆ Metric.ball y₀ R)
    (hcr : ∀ ζ : EuclideanSpace ℝ (Fin d), ‖y₀ - ζ‖ < R → |cellLocalTime X n ζ - U ζ| ≤ δ)
    (hint : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => radialWeight d R ‖y₀ - ζ‖ * U ζ)) :
    ∑ x ∈ departureRange X n, (localTime X n x : ℝ) * ∫ ζ in cell x, radialWeight d R ‖y₀ - ζ‖ ≤
      ∫ ζ : EuclideanSpace ℝ (Fin d),
        (radialWeight d R ‖y₀ - ζ‖ * U ζ + radialWeight d R ‖y₀ - ζ‖ * δ) := by
  have hg : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      radialWeight d R ‖y₀ - ζ‖ * U ζ + radialWeight d R ‖y₀ - ζ‖ * δ) :=
    hint.add ((integrable_radialWeight_sub hd hR y₀).mul_const δ)
  calc _ ≤ ∑ x ∈ departureRange X n, ∫ ζ in cell x,
        (radialWeight d R ‖y₀ - ζ‖ * U ζ + radialWeight d R ‖y₀ - ζ‖ * δ) :=
        Finset.sum_le_sum fun x hx => cell_term_le hd hR X n U hDball hcr hg hx
    _ = ∫ ζ in cellSet X n,
        (radialWeight d R ‖y₀ - ζ‖ * U ζ + radialWeight d R ‖y₀ - ζ‖ * δ) :=
        (integral_biUnion_finset (departureRange X n) (fun x _ => measurableSet_cell x)
          (fun x _ y _ hxy => cell_disjoint hxy) (fun x _ => hg.integrableOn)).symm
    _ ≤ _ := by
        rw [← integral_add_compl (measurableSet_cellSet X n) hg]
        exact le_add_of_nonneg_right (setIntegral_nonneg (measurableSet_cellSet X n).compl
          fun ζ hζ => dominating_nonneg_off X n U hcr hζ)

/-- The weighted sum of local times `∑_x ℓ(x) a(x)`, where `a(x)` is the weight of the cell of `x`,
is bounded by the convolution estimate: the local time is dominated by the potential plus the
error `δ` on the support of the weight, and `hconv` bounds the convolution of the potential. -/
private theorem weighted_sum_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ε : ℝ}
    (hconv : ConvBound d Ψ ε) (hd : 1 ≤ d) (X : ℕ → Site d) (n : ℕ) {b R δ : ℝ}
    {y₀ : EuclideanSpace ℝ (Fin d)} (hb : 0 < b) (hsub : {v | Ψ v < b} ⊆ cellSet X n)
    (hy₀ : Ψ y₀ = b) (hR : 0 < R) (hDball : cellSet X n ⊆ Metric.ball y₀ R)
    (hcr : ∀ ζ : EuclideanSpace ℝ (Fin d), ‖y₀ - ζ‖ < R →
      |cellLocalTime X n ζ - normPotential d ε Ψ (cellSet X n) ζ| ≤ δ) :
    ∑ x ∈ departureRange X n, (localTime X n x : ℝ) * ∫ ζ in cell x, radialWeight d R ‖y₀ - ζ‖ ≤
      2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ * min b (Ψ ζ)) +
        (∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖) *
          (normPotential d ε Ψ (cellSet X n) y₀ + δ) := by
  obtain ⟨hint, hle⟩ := hconv (radialWeight d R) (radialWeight_measurable d R)
    (radialWeight_nonneg d R) ⟨1, radialWeight_le_one d R⟩
    (integrable_radialWeight_norm hd hR).1 (cellSet X n) (measurableSet_cellSet X n)
    (Metric.isBounded_ball.subset hDball) b hb hsub y₀ hy₀
  have hint2 : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      radialWeight d R ‖y₀ - ζ‖ * normPotential d ε Ψ (cellSet X n) ζ) := by
    simpa only [sub_sub_cancel] using hint.comp_sub_left y₀
  have h1 := cell_sum_le_integral hd hR X n (normPotential d ε Ψ (cellSet X n)) hDball hcr hint2
  have hD : ∫ ζ : EuclideanSpace ℝ (Fin d), (radialWeight d R ‖y₀ - ζ‖ *
        normPotential d ε Ψ (cellSet X n) ζ + radialWeight d R ‖y₀ - ζ‖ * δ) =
      (∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ *
        normPotential d ε Ψ (cellSet X n) (y₀ - ζ)) +
      (∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖) * δ := by
    rw [integral_add hint2 ((integrable_radialWeight_sub hd hR y₀).mul_const δ),
      integral_mul_const]
    have e1 := integral_sub_left_eq_self (fun ζ : EuclideanSpace ℝ (Fin d) =>
      radialWeight d R ‖ζ‖ * normPotential d ε Ψ (cellSet X n) (y₀ - ζ)) volume y₀
    have e2 := integral_sub_left_eq_self (fun ζ : EuclideanSpace ℝ (Fin d) =>
      radialWeight d R ‖ζ‖) volume y₀
    simp only [sub_sub_cancel] at e1
    rw [e1, e2]
  rw [hD] at h1
  linarith

/-- Consequences of `L ≥ 1`, `r ≥ 1` and `L⁴ ≤ r`: `L ≤ L² ≤ √r ≤ r`. -/
private theorem log_power_bounds {L r : ℝ} (hL : 1 ≤ L) (hr : 1 ≤ r) (h : L ^ 4 ≤ r) :
    L ≤ L ^ 2 ∧ L ^ 2 ≤ Real.sqrt r ∧ Real.sqrt r ≤ r ∧ 1 ≤ Real.sqrt r ∧ L ≤ r := by
  have h1 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
  have hu2 : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt (by linarith)
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hL2s : L ^ 2 ≤ Real.sqrt r := by
    refine Real.le_sqrt_of_sq_le ?_
    calc (L ^ 2) ^ 2 = L ^ 4 := by ring
      _ ≤ r := h
  have hur : Real.sqrt r ≤ r := by nlinarith
  exact ⟨hL2, hL2s, hur, h1, by linarith⟩

/-- The square root of a product with a bounded factor: `√(a) ≤ √c · t` when `a ≤ c t²`. -/
private theorem sqrt_le_sqrt_mul {a c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) (h : a ≤ c * t ^ 2) :
    Real.sqrt a ≤ Real.sqrt c * t := by
  rw [Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) ht, ?_⟩
  calc a ≤ c * t ^ 2 := h
    _ = (Real.sqrt c * t) ^ 2 := by rw [mul_pow, Real.sq_sqrt hc]

/-- The crude bound on the potential at the contact point, in terms of `√r` and `L`: the local
times are at most `M ≤ C_M r`, so the weighted sum `W` is at most `C' M L`. -/
private theorem potential_crude_bound {C₁ C₂ C₃ CM C' L L' r M W H : ℝ} (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hCM : 0 ≤ CM) (hC' : 0 ≤ C') (hL : 1 ≤ L) (hL'0 : 0 ≤ L') (hL'L : L' ≤ L)
    (hr : 1 ≤ r) (hM : M ≤ CM * r) (hW : W ≤ C' * M * L)
    (hstar : H ≤ C₁ * Real.sqrt (W * L) + (C₁ + C₃) * L) :
    H + (C₂ * L' + C₂ * (Real.sqrt M * L')) ≤
      (C₁ * Real.sqrt (C' * CM) + C₂ * Real.sqrt CM) * Real.sqrt r * L + (C₁ + C₃ + C₂) * L := by
  have hu2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt (by linarith)
  have hL0 : 0 ≤ L := by linarith
  have hu0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hMu : Real.sqrt M ≤ Real.sqrt CM * Real.sqrt r :=
    sqrt_le_sqrt_mul hCM hu0 (by rw [hu2]; exact hM)
  have hWL : Real.sqrt (W * L) ≤ Real.sqrt (C' * CM) * (Real.sqrt r * L) := by
    refine sqrt_le_sqrt_mul (mul_nonneg hC' hCM) (mul_nonneg hu0 hL0) ?_
    calc W * L ≤ C' * M * L * L := mul_le_mul_of_nonneg_right hW hL0
      _ ≤ C' * (CM * r) * L * L :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hM hC') hL0) hL0
      _ = C' * CM * (Real.sqrt r * L) ^ 2 := by rw [mul_pow, hu2]; ring
  have hH1 : H ≤ C₁ * (Real.sqrt (C' * CM) * (Real.sqrt r * L)) + (C₁ + C₃) * L :=
    hstar.trans (add_le_add_left (mul_le_mul_of_nonneg_left hWL hC₁) _)
  have h1 : Real.sqrt M * L' ≤ Real.sqrt CM * Real.sqrt r * L :=
    mul_le_mul hMu hL'L hL'0 (mul_nonneg (Real.sqrt_nonneg _) hu0)
  have h2 := mul_le_mul_of_nonneg_left hL'L hC₂
  have h3 := mul_le_mul_of_nonneg_left h1 hC₂
  linarith

/-- The real-variable arithmetic of the contact argument. -/
private theorem final_bound (C₁ C₂ C₃ CM CR C' c₀ κ σ s : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hC₃ : 0 ≤ C₃) (hCM : 0 ≤ CM) (hCR : 0 ≤ CR) (hC' : 0 ≤ C') (hc₀ : 0 < c₀) (hκ : 0 ≤ κ)
    (hσ : 0 ≤ σ) (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ L L' r M R H W Λa m tB : ℝ, 1 ≤ L → 0 ≤ L' → L' ≤ L → 1 ≤ r →
      L ^ 4 ≤ r → M ≤ CM * r → R = 2 * CR * r + 2 * s → 0 ≤ W →
      H ≤ C₁ * Real.sqrt (W * L) + (C₁ + C₃) * L → W ≤ C' * M * L → c₀ * W ≤ Λa →
      Λa ≤ tB + m * (H + (C₂ * L' + C₂ * (Real.sqrt M * L'))) → tB ≤ κ * R → 0 ≤ m →
      m ≤ σ * L → H ≤ C * Real.sqrt (r * L) := by
  set P : ℝ := C₁ * Real.sqrt (C' * CM) + C₂ * Real.sqrt CM with hP
  set Q : ℝ := C₁ + C₃ + C₂ with hQ
  set K : ℝ := κ * (2 * CR + 2 * s) + σ * P + σ * Q with hK
  have hP0 : 0 ≤ P := add_nonneg (mul_nonneg hC₁ (Real.sqrt_nonneg _))
    (mul_nonneg hC₂ (Real.sqrt_nonneg _))
  have hQ0 : 0 ≤ Q := add_nonneg (add_nonneg hC₁ hC₃) hC₂
  have hK0 : 0 ≤ K := add_nonneg (add_nonneg (mul_nonneg hκ (by linarith)) (mul_nonneg hσ hP0))
    (mul_nonneg hσ hQ0)
  refine ⟨C₁ * Real.sqrt (K / c₀) + C₁ + C₃ + 1, ?_, ?_⟩
  · have := mul_nonneg hC₁ (Real.sqrt_nonneg (K / c₀))
    linarith
  intro L L' r M R H W Λa m tB hL hL'0 hL'L hr hLr hM hR hW0 hstar hW hc hΛ htB hm0 hmσ
  obtain ⟨hLL, hL2u, hur, hu1, hLr'⟩ := log_power_bounds hL hr hLr
  have hu2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt (by linarith)
  have hL0 : 0 ≤ L := by linarith
  have hu0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hT := potential_crude_bound hC₁ hC₂ hCM hC' hL hL'0 hL'L hr hM hW hstar
  have hT0 : 0 ≤ P * Real.sqrt r * L + Q * L :=
    add_nonneg (mul_nonneg (mul_nonneg hP0 hu0) hL0) (mul_nonneg hQ0 hL0)
  have hmT : m * (H + (C₂ * L' + C₂ * (Real.sqrt M * L'))) ≤
      σ * L * (P * Real.sqrt r * L + Q * L) :=
    (mul_le_mul_of_nonneg_left hT hm0).trans (mul_le_mul_of_nonneg_right hmσ hT0)
  have hσT : σ * L * (P * Real.sqrt r * L + Q * L) ≤ σ * P * r + σ * Q * r := by
    have h1 : Real.sqrt r * L ^ 2 ≤ r := by
      calc Real.sqrt r * L ^ 2 ≤ Real.sqrt r * Real.sqrt r :=
            mul_le_mul_of_nonneg_left hL2u hu0
        _ = r := by rw [← sq, hu2]
    have h2 : L ^ 2 ≤ r := hL2u.trans hur
    calc σ * L * (P * Real.sqrt r * L + Q * L)
        = σ * P * (Real.sqrt r * L ^ 2) + σ * Q * L ^ 2 := by ring
      _ ≤ σ * P * r + σ * Q * r :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (mul_nonneg hσ hP0))
            (mul_le_mul_of_nonneg_left h2 (mul_nonneg hσ hQ0))
  have hκR : κ * R ≤ κ * (2 * CR + 2 * s) * r := by
    have h1 : 2 * CR * r + 2 * s ≤ (2 * CR + 2 * s) * r := by
      have := mul_nonneg hs (sub_nonneg.mpr hr)
      linarith
    rw [hR]
    exact (mul_le_mul_of_nonneg_left h1 hκ).trans_eq (by ring)
  have hΛK : Λa ≤ K * r := by
    calc Λa ≤ tB + m * (H + (C₂ * L' + C₂ * (Real.sqrt M * L'))) := hΛ
      _ ≤ κ * (2 * CR + 2 * s) * r + (σ * P * r + σ * Q * r) := add_le_add (htB.trans hκR)
          (hmT.trans hσT)
      _ = K * r := by rw [hK]; ring
  have hWK : W ≤ K / c₀ * r := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
    linarith
  have hsq : Real.sqrt (W * L) ≤ Real.sqrt (K / c₀) * Real.sqrt (r * L) := by
    rw [← Real.sqrt_mul (div_nonneg hK0 hc₀.le)]
    refine Real.sqrt_le_sqrt ?_
    calc W * L ≤ K / c₀ * r * L := mul_le_mul_of_nonneg_right hWK hL0
      _ = K / c₀ * (r * L) := by ring
  have hLsq : L ≤ Real.sqrt (r * L) := by
    refine Real.le_sqrt_of_sq_le ?_
    calc L ^ 2 = L * L := sq L
      _ ≤ r * L := mul_le_mul_of_nonneg_right hLr' hL0
  have hs0 : 0 ≤ Real.sqrt (r * L) := Real.sqrt_nonneg _
  calc H ≤ C₁ * Real.sqrt (W * L) + (C₁ + C₃) * L := hstar
    _ ≤ C₁ * (Real.sqrt (K / c₀) * Real.sqrt (r * L)) + (C₁ + C₃) * Real.sqrt (r * L) :=
        add_le_add (mul_le_mul_of_nonneg_left hsq hC₁)
          (mul_le_mul_of_nonneg_left hLsq (add_nonneg hC₁ hC₃))
    _ ≤ _ := by linarith

/-- The cell set of a path lies in the ball of radius `2 C_R r + 2 √d` about a contact point `y₀`
with `|y₀| ≤ H_n + √d`, when `H_n ≤ C_R r`. -/
private theorem cellSet_subset_ball_contact (hd : 1 ≤ d) (X : ℕ → Site d) (n : ℕ)
    {y₀ : EuclideanSpace ℝ (Fin d)} {CR r : ℝ} (hHm : maxRadius X n ≤ CR * r)
    (hy₀ : ‖y₀‖ ≤ maxRadius X n + Real.sqrt d) :
    cellSet X n ⊆ Metric.ball y₀ (2 * CR * r + 2 * Real.sqrt d) := by
  intro v hv
  have hv' := cellSet_subset_ball hd X n hv
  rw [mem_ball_zero_iff] at hv'
  rw [Metric.mem_ball, dist_eq_norm]
  calc ‖v - y₀‖ ≤ ‖v‖ + ‖y₀‖ := norm_sub_le _ _
    _ < (maxRadius X n + Real.sqrt d) + (maxRadius X n + Real.sqrt d) :=
        add_lt_add_of_lt_of_le hv' hy₀
    _ ≤ 2 * CR * r + 2 * Real.sqrt d := by linarith

/-- The kernel `(1 + |x - z|)^{-d}` is nonnegative. -/
private theorem kernel_nonneg (x z : Site d) : 0 ≤ (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) :=
  Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg (x - z)]) _

/-- The local-time-weighted kernel sum over the departure range is at most `C' M L`, where `M` is
the maximal local time, once the unweighted kernel sum is at most `C' L`. -/
private theorem kernel_weight_le {C' : ℝ} (X : ℕ → Site d) (n : ℕ) (z : Site d)
    (hsum : ∑ x ∈ departureRange X n, (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) ≤
      C' * Real.log ((n : ℝ) + 2)) :
    ∑ x ∈ departureRange X n, (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) ≤
      C' * (maxLocalTime X n : ℝ) * Real.log ((n : ℝ) + 2) := by
  calc ∑ x ∈ departureRange X n, (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (-(d : ℝ))
      ≤ ∑ x ∈ departureRange X n, (maxLocalTime X n : ℝ) * (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right
          (by exact_mod_cast localTime_le_maxLocalTime X n x) (kernel_nonneg x z)
    _ = (maxLocalTime X n : ℝ) * ∑ x ∈ departureRange X n, (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (maxLocalTime X n : ℝ) * (C' * Real.log ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = C' * (maxLocalTime X n : ℝ) * Real.log ((n : ℝ) + 2) := by ring

/-- The local-time-weighted kernel sum at an unvisited site `z` near `y₀` is at most a constant
multiple of the weighted sum of local times `∑_x ℓ(x) a(x)`. -/
private theorem kernel_weight_ge (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) (X : ℕ → Site d) (n : ℕ)
    {y₀ : EuclideanSpace ℝ (Fin d)} {z : Site d} (hzy : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2)
    (hDball : cellSet X n ⊆ Metric.ball y₀ R) :
    (1 + Real.sqrt d) ^ (-(d : ℝ)) * ∑ x ∈ departureRange X n,
        (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) ≤
      ∑ x ∈ departureRange X n,
        (localTime X n x : ℝ) * ∫ ζ in cell x, radialWeight d R ‖y₀ - ζ‖ := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  have hcell : cell x ⊆ Metric.ball y₀ R :=
    (Set.subset_iUnion₂ (s := fun x (_ : x ∈ departureRange X n) => cell x) x hx).trans hDball
  have hlow := weight_lower hd hR y₀ z x hzy hcell
  have hsym : euclidNorm (z - x) = euclidNorm (x - z) := by
    rw [← neg_sub x z, CERW.Generic.Lattice.euclidNorm_neg]
  rw [hsym] at hlow
  calc (1 + Real.sqrt d) ^ (-(d : ℝ)) * ((localTime X n x : ℝ) *
        (1 + euclidNorm (x - z)) ^ (-(d : ℝ)))
      = (localTime X n x : ℝ) * ((1 + Real.sqrt d) ^ (-(d : ℝ)) *
        (1 + euclidNorm (x - z)) ^ (-(d : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg _)

/-- The ball term of the convolution estimate, for `d = 2`: `2 d ε ∫ w min(b, Ψ)` is at most
`2 d ε Λ_Ψ σ_2 R`. -/
private theorem ball_term_le (hd : d = 2) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε R b : ℝ} (hε : 0 < ε) (hR : 0 < R) (hb : 0 ≤ b) :
    2 * (d : ℝ) * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ * min b (Ψ ζ)) ≤
      2 * (d : ℝ) * ε * (normMax Ψ * ((d : ℝ) * unitBallVolume d)) * R := by
  have hd2 : (d : ℝ) = 2 := by rw [hd]; norm_num
  calc _ ≤ 2 * (d : ℝ) * ε * (normMax Ψ * ((d : ℝ) * unitBallVolume d * R)) :=
        mul_le_mul_of_nonneg_left (integral_weight_mul_min_le hd hΨ hR hb)
          (by rw [hd2]; linarith)
    _ = _ := by ring

/-- The mass `∫ w(|ζ|)` of the truncated weight is nonnegative and at most `σ_d log (n + 2)` when
the truncation radius is at most `n`. -/
private theorem weight_mass_le (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) {n : ℕ} (hRn : R ≤ n) :
    0 ≤ ∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ ∧
      ∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ ≤
        (d : ℝ) * unitBallVolume d * Real.log ((n : ℝ) + 2) := by
  refine ⟨integral_nonneg fun ζ => radialWeight_nonneg d _ _, ?_⟩
  have hlog : Real.log (1 + R) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hσ : 0 ≤ (d : ℝ) * unitBallVolume d :=
    mul_nonneg (Nat.cast_nonneg _) (unitBallVolume_pos d).le
  exact (integrable_radialWeight_norm hd hR).2.trans (mul_le_mul_of_nonneg_left hlog hσ)

/-- The deterministic contact argument in the plane: for `d = 2`, the potential at a contact point
of the inradius is at most `C √(r log (n + 2))`. -/
theorem contact_bound_two {d : ℕ} (hd : d = 2) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε) (hconv : CERW.Support.Norm.ContactShared.ConvBound d Ψ ε)
    (C₁ C₂ C₃ CM CR : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hCM : 0 ≤ CM)
    (hCR : 0 ≤ CR) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ → Site d) (n : ℕ) (r : ℝ), 2 ≤ n → X 0 = 0 →
      (∀ j, euclidNorm (X j) ≤ j) → 1 ≤ r → Real.log ((n : ℝ) + 2) ^ 4 ≤ r →
      3 * CR * r + 6 * Real.sqrt d ≤ n → (maxLocalTime X n : ℝ) ≤ CM * r →
      maxRadius X n ≤ CR * r →
      (∀ y : Site d, euclidNorm y ≤ 3 * n →
        |(localTime X n y : ℝ) - normPotential d ε Ψ (cellSet X n) (toSpace y)| ≤
          C₁ * (Real.sqrt ((∑ j ∈ Finset.range n,
            (1 + euclidNorm (X j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2))) →
      (∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ ≤ 2 * n →
        |cellLocalTime X n v - normPotential d ε Ψ (cellSet X n) v| ≤
          C₂ * Real.log n + C₂ * (Real.sqrt (maxLocalTime X n) * Real.log n)) →
      (∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * ((n : ℝ) + Real.sqrt d) →
        ‖y - z‖ ≤ Real.sqrt d →
        |normPotential d ε Ψ (cellSet X n) y - normPotential d ε Ψ (cellSet X n) z| ≤
          C₃ * Real.log ((n : ℝ) + 2)) →
      ∀ y₀ : EuclideanSpace ℝ (Fin d), Ψ y₀ = normInnerRadius Ψ X n →
        y₀ ∈ closure (cellSet X n)ᶜ →
        normPotential d ε Ψ (cellSet X n) y₀ ≤ C * Real.sqrt (r * Real.log ((n : ℝ) + 2)) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (d : ℝ) = 2 := by rw [hd]; norm_num
  have hexp : (2 - 2 * (d : ℝ)) = -(d : ℝ) := by rw [hd2]; norm_num
  have hs0 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by rw [hd2]; norm_num)
  have hΛ : 0 ≤ normMax Ψ := normMax_nonneg hΨ hd1
  obtain ⟨C', hC'pos, hC'⟩ := kernel_sum_le hd
  have hc₀ : 0 < (1 + Real.sqrt d) ^ (-(d : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  have hσ : 0 ≤ (d : ℝ) * unitBallVolume d :=
    mul_nonneg (Nat.cast_nonneg _) (unitBallVolume_pos d).le
  have hκ : 0 ≤ 2 * (d : ℝ) * ε * (normMax Ψ * ((d : ℝ) * unitBallVolume d)) :=
    mul_nonneg (by rw [hd2]; linarith) (mul_nonneg hΛ hσ)
  obtain ⟨C, hCpos, hCfin⟩ := final_bound C₁ C₂ C₃ CM CR C' ((1 + Real.sqrt d) ^ (-(d : ℝ)))
    (2 * (d : ℝ) * ε * (normMax Ψ * ((d : ℝ) * unitBallVolume d))) ((d : ℝ) * unitBallVolume d)
    (Real.sqrt d) hC₁ hC₂ hC₃ hCM hCR hC'pos.le hc₀ hκ hσ hs0.le
  refine ⟨C, hCpos, ?_⟩
  intro X n r hn2 hX0 hXn hr hLr hnr hM hHm hfine hcrude hmod y₀ hy₀ hcl
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hL1 : 1 ≤ Real.log ((n : ℝ) + 2) := CERW.Support.Law.one_le_log_add_two hn2
  have hL'0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hL'L : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  obtain ⟨hbpos, hsub, -, hy₀norm, z, hz0, hzy, hzn⟩ :=
    contact_setup (by omega) hΨ X n hn1 hX0 hy₀ hcl
  have hHm0 : 0 ≤ maxRadius X n :=
    (LatticeProb.euclidNorm_nonneg (X 0)).trans (euclidNorm_le_maxRadius X (Nat.zero_le n))
  have hCRr : 0 ≤ CR * r := mul_nonneg hCR (by linarith)
  have hRpos : 0 < 2 * CR * r + 2 * Real.sqrt d := by linarith
  have hRn : 2 * CR * r + 2 * Real.sqrt d ≤ n := by linarith
  have hDball := cellSet_subset_ball_contact hd1 X n hHm hy₀norm
  have hcr : ∀ ζ : EuclideanSpace ℝ (Fin d), ‖y₀ - ζ‖ < 2 * CR * r + 2 * Real.sqrt d →
      |cellLocalTime X n ζ - normPotential d ε Ψ (cellSet X n) ζ| ≤
        C₂ * Real.log (n : ℝ) + C₂ * (Real.sqrt (maxLocalTime X n) * Real.log (n : ℝ)) := by
    intro ζ hζ
    refine hcrude ζ ?_
    have h1 : ‖ζ‖ ≤ ‖y₀‖ + ‖y₀ - ζ‖ := by
      calc ‖ζ‖ = ‖y₀ - (y₀ - ζ)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖y₀‖ + ‖y₀ - ζ‖ := norm_sub_le _ _
    linarith
  have hws := weighted_sum_le hconv hd1 X n hbpos hsub hy₀ hRpos hDball hcr
  have hzn3 : euclidNorm z ≤ 3 * n := by linarith
  have hfz := hfine z hzn3
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = ∑ j ∈ Finset.range n,
      (1 + euclidNorm (X j - z)) ^ (-(d : ℝ)) := ⟨_, rfl⟩
  rw [hexp, ← hWdef, hz0, Nat.cast_zero, zero_sub, abs_neg] at hfz
  have hmz := hmod y₀ (toSpace z) (by linarith) (by rw [norm_sub_rev]; linarith)
  have hstar : normPotential d ε Ψ (cellSet X n) y₀ ≤
      C₁ * Real.sqrt (W * Real.log ((n : ℝ) + 2)) + (C₁ + C₃) * Real.log ((n : ℝ) + 2) := by
    linarith [(abs_le.mp hfz).2, (abs_le.mp hmz).2]
  have hW_eq : W = ∑ x ∈ departureRange X n,
      (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) := by
    rw [hWdef]
    exact CERW.Support.LocalTime.sum_range_eq_sum_localTime X n
      (fun x => (1 + euclidNorm (x - z)) ^ (-(d : ℝ)))
  have hW0 : 0 ≤ W := by
    rw [hW_eq]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (Nat.cast_nonneg _) (kernel_nonneg x z)
  obtain ⟨hm0, hmσ⟩ := weight_mass_le hd1 hRpos hRn
  exact hCfin (Real.log ((n : ℝ) + 2)) (Real.log (n : ℝ)) r (maxLocalTime X n : ℝ)
    (2 * CR * r + 2 * Real.sqrt d) _ W _ _ _ hL1 hL'0 hL'L hr hLr hM rfl hW0 hstar
    (hW_eq ▸ kernel_weight_le X n z (hC' X n z hn1 hXn hzn3))
    (hW_eq ▸ kernel_weight_ge hd1 hRpos X n hzy hDball) hws
    (ball_term_le hd hΨ hε hRpos hbpos.le) hm0 hmσ

end CERW.Support.Norm.ContactPlanar

namespace CERW.Support.Norm.ContactHigh

open CERW CERW.Generic.Lattice

variable {d : ℕ}

/-- Young's inequality for a square root: `A √(B L) ≤ λ B + A² L / (4 λ)`. -/
private lemma mul_sqrt_le_add (B L A lam : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hlam : 0 < lam) :
    A * Real.sqrt (B * L) ≤ lam * B + A ^ 2 * L / (4 * lam) := by
  set u : ℝ := lam * B with hu
  set v : ℝ := A ^ 2 * L / (4 * lam) with hv
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hsq : (A * Real.sqrt (B * L) / 2) ^ 2 = u * v := by
    rw [hu, hv]
    rw [div_pow, mul_pow, Real.sq_sqrt (mul_nonneg hB hL)]
    field_simp
    ring
  have hroot : Real.sqrt (u * v) = A * Real.sqrt (B * L) / 2 := by
    rw [← hsq, Real.sqrt_sq]
    positivity
  have hamgm : 2 * Real.sqrt (u * v) ≤ u + v := by
    have h := two_mul_le_add_sq (Real.sqrt u) (Real.sqrt v)
    rw [Real.sq_sqrt hu0, Real.sq_sqrt hv0] at h
    rw [mul_assoc, ← Real.sqrt_mul hu0 v] at h
    linarith
  rw [hroot] at hamgm
  have : 2 * (A * Real.sqrt (B * L) / 2) = A * Real.sqrt (B * L) := by ring
  rw [this] at hamgm
  rw [hu, hv] at hamgm
  exact hamgm

/-- The lattice weight `k(w) = (1 + |w|)^{2-2d}`. -/
private noncomputable def kern (d : ℕ) (w : Site d) : ℝ :=
  (1 + euclidNorm w) ^ (2 - 2 * (d : ℝ))

/-- The lattice weight is nonnegative. -/
private lemma kern_nonneg (w : Site d) : 0 ≤ kern d w :=
  Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg w]) _

/-- The lattice weight is symmetric: `k(x - y) = k(y - x)`. -/
private lemma kern_sub_comm (x y : Site d) : kern d (x - y) = kern d (y - x) := by
  unfold kern
  rw [← neg_sub y x, euclidNorm_neg]

/-- Comparison of powers with a nonpositive exponent: if `1 + f ≤ c (1 + e)` then
`(1 + e)^q ≤ c^{-q} (1 + f)^q`. -/
private lemma rpow_le_mul_rpow_of_le {e f c q : ℝ} (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < c)
    (hq : q ≤ 0) (h : 1 + f ≤ c * (1 + e)) :
    (1 + e) ^ q ≤ c ^ (-q) * (1 + f) ^ q := by
  have h1 : (c * (1 + e)) ^ q ≤ (1 + f) ^ q :=
    Real.rpow_le_rpow_of_nonpos (by linarith) h hq
  rw [Real.mul_rpow hc.le (by linarith)] at h1
  have h2 : c ^ (-q) * c ^ q = 1 := by
    rw [← Real.rpow_add hc, neg_add_cancel, Real.rpow_zero]
  calc (1 + e) ^ q = c ^ (-q) * (c ^ q * (1 + e) ^ q) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ c ^ (-q) * (1 + f) ^ q :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hc.le _)

/-- The triangle inequality for the lattice kernel: `|z - x| ≤ |z - y| + |y - x|`. -/
private lemma euclidNorm_sub_le_add (z y x : Site d) :
    euclidNorm (z - x) ≤ euclidNorm (z - y) + euclidNorm (y - x) := by
  have h := CERW.Support.Occupation.euclidNorm_add_le (z - y) (y - x)
  rwa [sub_add_sub_cancel] at h

/-- If `e ≥ ρ / 2` then the weight at `e` is at most `2^{2d-2}` times the weight at `ρ`. -/
private lemma rpow_le_two_rpow_mul {e ρ q : ℝ} (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hq : q ≤ 0)
    (h : ρ / 2 ≤ e) : (1 + e) ^ q ≤ (2 : ℝ) ^ (-q) * (1 + ρ) ^ q :=
  rpow_le_mul_rpow_of_le he hρ (by norm_num) hq (by linarith)

/-- Each term of the lattice convolution of two weights is at most `2^{2d-2} k(z - x)` times
the sum of the two weights. -/
private lemma kern_mul_le (hd : 1 ≤ d) (z y x : Site d) :
    kern d (z - y) * kern d (y - x) ≤
      (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) * (kern d (z - y) + kern d (y - x)) := by
  have hq : 2 - 2 * (d : ℝ) ≤ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hk1 := kern_nonneg (z - y)
  have hk2 := kern_nonneg (y - x)
  have hk3 := kern_nonneg (z - x)
  have hc : 0 ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have htri := euclidNorm_sub_le_add z y x
  have hn1 := LatticeProb.euclidNorm_nonneg (z - y)
  have hn2 := LatticeProb.euclidNorm_nonneg (y - x)
  have hn3 := LatticeProb.euclidNorm_nonneg (z - x)
  by_cases hcase : euclidNorm (z - x) / 2 ≤ euclidNorm (y - x)
  · have hb : kern d (y - x) ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) :=
      rpow_le_two_rpow_mul hn2 hn3 hq hcase
    calc kern d (z - y) * kern d (y - x)
        ≤ kern d (z - y) * ((2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x)) :=
          mul_le_mul_of_nonneg_left hb hk1
      _ = (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) * kern d (z - y) := by ring
      _ ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) * (kern d (z - y) + kern d (y - x)) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc hk3)
  · have hcase' : euclidNorm (z - x) / 2 ≤ euclidNorm (z - y) := by
      rw [not_le] at hcase
      linarith
    have ha : kern d (z - y) ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) :=
      rpow_le_two_rpow_mul hn1 hn3 hq hcase'
    calc kern d (z - y) * kern d (y - x)
        ≤ ((2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x)) * kern d (y - x) :=
          mul_le_mul_of_nonneg_right ha hk2
      _ ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) * (kern d (z - y) + kern d (y - x)) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc hk3)

/-- The lattice convolution of the weight with itself, over any finite set, is bounded by a
constant multiple of the weight. -/
private lemma sum_kern_mul_kern_le (hd : 1 ≤ d) {K₀ : ℝ}
    (hK₀ : ∀ (F : Finset (Site d)) (u : Site d), ∑ y ∈ F, kern d (y - u) ≤ K₀)
    (F : Finset (Site d)) (z x : Site d) :
    ∑ y ∈ F, kern d (z - y) * kern d (y - x) ≤
      (2 * (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * K₀) * kern d (z - x) := by
  have hk3 := kern_nonneg (z - x)
  have hc : 0 ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hsum1 : ∑ y ∈ F, kern d (z - y) ≤ K₀ := by
    have := hK₀ F z
    simpa only [kern_sub_comm z] using this
  have hsum2 := hK₀ F x
  calc ∑ y ∈ F, kern d (z - y) * kern d (y - x)
      ≤ ∑ y ∈ F, (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) *
          (kern d (z - y) + kern d (y - x)) :=
        Finset.sum_le_sum fun y _ => kern_mul_le hd z y x
    _ = (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) *
          (∑ y ∈ F, kern d (z - y) + ∑ y ∈ F, kern d (y - x)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) * (K₀ + K₀) :=
        mul_le_mul_of_nonneg_left (add_le_add hsum1 hsum2) (mul_nonneg hc hk3)
    _ = (2 * (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * K₀) * kern d (z - x) := by ring

/-- The lattice absorption estimate: if the local time satisfies the pointwise bound on `S`
with a square root of the kernel sum, and `a` is comparable to the kernel at `z`, then the
`a`-weighted local time sum is bounded by twice the `a`-weighted potential sum, up to a
multiple of `L`. -/
private lemma absorb_sum {ℓ U a : Site d → ℝ} {S : Finset (Site d)} {z : Site d}
    {c₀ c₁ K₀ A₀ C₁ L γ : ℝ}
    (hK₀ : ∀ (F : Finset (Site d)) (u : Site d), ∑ y ∈ F, kern d (y - u) ≤ K₀)
    (hconv : ∀ (F : Finset (Site d)) (x : Site d),
      ∑ y ∈ F, kern d (z - y) * kern d (y - x) ≤ A₀ * kern d (z - x))
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hA₀ : 0 ≤ A₀)
    (ha : ∀ y, c₀ * kern d (z - y) ≤ a y ∧ a y ≤ c₁ * kern d (z - y))
    (hℓ0 : ∀ y, 0 ≤ ℓ y) (hC₁ : 0 ≤ C₁) (hL : 0 ≤ L) (hγ : 0 < γ)
    (hγ' : γ * (c₁ * A₀) ≤ c₀ / 2)
    (hfine : ∀ y ∈ S,
      ℓ y ≤ U y + C₁ * (Real.sqrt ((∑ x ∈ S, ℓ x * kern d (x - y)) * L) + L)) :
    ∑ y ∈ S, a y * ℓ y ≤
      2 * ∑ y ∈ S, a y * U y + 2 * ((C₁ + C₁ ^ 2 / (4 * γ)) * L) * (c₁ * K₀) := by
  have ha0 : ∀ y, 0 ≤ a y := fun y => (mul_nonneg hc₀.le (kern_nonneg _)).trans (ha y).1
  set W : Site d → ℝ := fun y => ∑ x ∈ S, ℓ x * kern d (x - y) with hW
  have hW0 : ∀ y, 0 ≤ W y := fun y =>
    Finset.sum_nonneg fun x _ => mul_nonneg (hℓ0 x) (kern_nonneg _)
  set Cg : ℝ := C₁ + C₁ ^ 2 / (4 * γ) with hCg
  have hCg0 : 0 ≤ Cg := by rw [hCg]; positivity
  have h1 : ∀ y ∈ S, ℓ y ≤ U y + Cg * L + γ * W y := by
    intro y hy
    have h := hfine y hy
    have hyoung := mul_sqrt_le_add (W y) L C₁ γ (hW0 y) hL hC₁ hγ
    calc ℓ y ≤ U y + C₁ * (Real.sqrt (W y * L) + L) := h
      _ = U y + (C₁ * Real.sqrt (W y * L) + C₁ * L) := by ring
      _ ≤ U y + (γ * W y + C₁ ^ 2 * L / (4 * γ) + C₁ * L) := by linarith
      _ = U y + Cg * L + γ * W y := by rw [hCg]; ring
  have h2 : ∑ y ∈ S, a y * ℓ y ≤
      ∑ y ∈ S, (a y * U y + (Cg * L) * a y + γ * (a y * W y)) := by
    refine Finset.sum_le_sum fun y hy => ?_
    calc a y * ℓ y ≤ a y * (U y + Cg * L + γ * W y) :=
          mul_le_mul_of_nonneg_left (h1 y hy) (ha0 y)
      _ = a y * U y + (Cg * L) * a y + γ * (a y * W y) := by ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h2
  have hsumA : ∑ y ∈ S, a y ≤ c₁ * K₀ := by
    calc ∑ y ∈ S, a y ≤ ∑ y ∈ S, c₁ * kern d (y - z) :=
          Finset.sum_le_sum fun y _ => by rw [← kern_sub_comm z y]; exact (ha y).2
      _ = c₁ * ∑ y ∈ S, kern d (y - z) := by rw [Finset.mul_sum]
      _ ≤ c₁ * K₀ := mul_le_mul_of_nonneg_left (hK₀ S z) hc₁.le
  have hswap : ∑ y ∈ S, a y * W y = ∑ x ∈ S, ℓ x * ∑ y ∈ S, a y * kern d (x - y) := by
    simp only [hW, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have hinner : ∀ x, ∑ y ∈ S, a y * kern d (x - y) ≤ c₁ * A₀ * kern d (z - x) := by
    intro x
    calc ∑ y ∈ S, a y * kern d (x - y)
        ≤ ∑ y ∈ S, c₁ * (kern d (z - y) * kern d (y - x)) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [kern_sub_comm x y]
          calc a y * kern d (y - x) ≤ (c₁ * kern d (z - y)) * kern d (y - x) :=
                mul_le_mul_of_nonneg_right (ha y).2 (kern_nonneg _)
            _ = c₁ * (kern d (z - y) * kern d (y - x)) := by ring
      _ = c₁ * ∑ y ∈ S, kern d (z - y) * kern d (y - x) := by rw [Finset.mul_sum]
      _ ≤ c₁ * (A₀ * kern d (z - x)) := mul_le_mul_of_nonneg_left (hconv S x) hc₁.le
      _ = c₁ * A₀ * kern d (z - x) := by ring
  have hAW : c₀ * ∑ y ∈ S, a y * W y ≤ c₁ * A₀ * ∑ x ∈ S, a x * ℓ x := by
    rw [hswap, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have hnn : 0 ≤ c₁ * A₀ * ℓ x := mul_nonneg (mul_nonneg hc₁.le hA₀) (hℓ0 x)
    calc c₀ * (ℓ x * ∑ y ∈ S, a y * kern d (x - y))
        ≤ c₀ * (ℓ x * (c₁ * A₀ * kern d (z - x))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hinner x) (hℓ0 x)) hc₀.le
      _ = c₁ * A₀ * ℓ x * (c₀ * kern d (z - x)) := by ring
      _ ≤ c₁ * A₀ * ℓ x * a x := mul_le_mul_of_nonneg_left (ha x).1 hnn
      _ = c₁ * A₀ * (a x * ℓ x) := by ring
  have hΛ0 : 0 ≤ ∑ x ∈ S, a x * ℓ x :=
    Finset.sum_nonneg fun x _ => mul_nonneg (ha0 x) (hℓ0 x)
  have hγAW : γ * ∑ y ∈ S, a y * W y ≤ (∑ x ∈ S, a x * ℓ x) / 2 := by
    have h3 : γ * (c₁ * A₀) * ∑ x ∈ S, a x * ℓ x ≤ c₀ / 2 * ∑ x ∈ S, a x * ℓ x :=
      mul_le_mul_of_nonneg_right hγ' hΛ0
    have h4 : c₀ * (γ * ∑ y ∈ S, a y * W y) ≤ c₀ * ((∑ x ∈ S, a x * ℓ x) / 2) := by
      calc c₀ * (γ * ∑ y ∈ S, a y * W y) = γ * (c₀ * ∑ y ∈ S, a y * W y) := by ring
        _ ≤ γ * (c₁ * A₀ * ∑ x ∈ S, a x * ℓ x) := mul_le_mul_of_nonneg_left hAW hγ.le
        _ = γ * (c₁ * A₀) * ∑ x ∈ S, a x * ℓ x := by ring
        _ ≤ c₀ / 2 * ∑ x ∈ S, a x * ℓ x := h3
        _ = c₀ * ((∑ x ∈ S, a x * ℓ x) / 2) := by ring
    exact le_of_mul_le_mul_left h4 hc₀
  have hCL : Cg * L * ∑ y ∈ S, a y ≤ Cg * L * (c₁ * K₀) :=
    mul_le_mul_of_nonneg_left hsumA (mul_nonneg hCg0 hL)
  linarith

/-- The radial weight `χ(s) = (1 + |s|)^{2-2d}`. -/
private noncomputable def chi (d : ℕ) (s : ℝ) : ℝ := (1 + |s|) ^ (2 - 2 * (d : ℝ))

/-- The radial weight is nonnegative. -/
private lemma chi_nonneg (s : ℝ) : 0 ≤ chi d s :=
  Real.rpow_nonneg (by linarith [abs_nonneg s]) _

/-- The radial weight is at most one. -/
private lemma chi_le_one (hd : 1 ≤ d) (s : ℝ) : chi d s ≤ 1 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg s]) (by linarith)

/-- The radial weight is measurable. -/
private lemma measurable_chi : Measurable (chi d) := by
  unfold chi
  fun_prop

/-- The weight of a norm is `(1 + ‖ζ‖)^{2-2d}`. -/
private lemma chi_norm (ζ : EuclideanSpace ℝ (Fin d)) :
    chi d ‖ζ‖ = (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) := by
  rw [chi, abs_norm]

/-- For `d ≥ 3` the radial weight is integrable on `ℝ^d`. -/
private lemma integrable_chi_norm (hd : 3 ≤ d) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => chi d ‖ζ‖) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h := integrable_one_add_norm (E := EuclideanSpace ℝ (Fin d)) (μ := volume)
    (r := 2 * (d : ℝ) - 2) (by rw [finrank_euclideanSpace_fin]; linarith)
  refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
  show (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) = chi d ‖ζ‖
  rw [chi_norm, show -(2 * (d : ℝ) - 2) = 2 - 2 * (d : ℝ) by ring]

/-- The cell weight `a(y) = ∫_{C_y} χ(|y₀ - ζ|) dζ`. -/
private noncomputable def cellWeight (d : ℕ) (y₀ : EuclideanSpace ℝ (Fin d)) (y : Site d) : ℝ :=
  ∫ ζ in cell y, chi d ‖y₀ - ζ‖

/-- Two-sided bounds for the integral over a unit cell of a function bounded on the cell. -/
private lemma setIntegral_cell_mem_Icc {G : EuclideanSpace ℝ (Fin d) → ℝ} (y : Site d)
    (hG : IntegrableOn G (cell y)) {lo hi : ℝ}
    (h : ∀ ζ ∈ cell y, lo ≤ G ζ ∧ G ζ ≤ hi) :
    lo ≤ ∫ ζ in cell y, G ζ ∧ ∫ ζ in cell y, G ζ ≤ hi := by
  have hvol : volume (cell y) ≠ ⊤ := by
    rw [CERW.Support.Occupation.volume_cell]
    exact ENNReal.one_ne_top
  have hmeas := CERW.Support.Occupation.measurableSet_cell (d := d) y
  have hreal : volume.real (cell y) = 1 := by
    rw [Measure.real, CERW.Support.Occupation.volume_cell]
    simp
  have hc : ∀ c : ℝ, IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) => c) (cell y) :=
    fun c => integrableOn_const hvol
  constructor
  · have := setIntegral_mono_on (hc lo) hG hmeas fun ζ hζ => (h ζ hζ).1
    rwa [setIntegral_const, hreal, one_smul] at this
  · have := setIntegral_mono_on hG (hc hi) hmeas fun ζ hζ => (h ζ hζ).2
    rwa [setIntegral_const, hreal, one_smul] at this

/-- For a point `ζ` of the cell of `y`, and a site `z` whose cell is near `y₀`, the distance
`|y₀ - ζ|` differs from `|z - y|` by at most `√d`. -/
private lemma abs_norm_sub_sub_euclidNorm_le {y₀ ζ : EuclideanSpace ℝ (Fin d)} {y z : Site d}
    (hζ : ζ ∈ cell y) (hz : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2) :
    |‖y₀ - ζ‖ - euclidNorm (z - y)| ≤ Real.sqrt d := by
  have h1 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hζ
  have hw : euclidNorm (z - y) = ‖toSpace z - toSpace y‖ := by
    rw [← norm_toSpace, CERW.Support.Occupation.toSpace_sub]
  set w : EuclideanSpace ℝ (Fin d) := toSpace z - toSpace y with hwdef
  set r : EuclideanSpace ℝ (Fin d) := (y₀ - toSpace z) + (toSpace y - ζ) with hr
  have hsplit : y₀ - ζ = w + r := by rw [hwdef, hr]; abel
  have hrn : ‖r‖ ≤ Real.sqrt d := by
    calc ‖r‖ ≤ ‖y₀ - toSpace z‖ + ‖toSpace y - ζ‖ := norm_add_le _ _
      _ ≤ Real.sqrt d / 2 + Real.sqrt d / 2 := by
          rw [norm_sub_rev y₀, norm_sub_rev (toSpace y)]
          exact add_le_add hz h1
      _ = Real.sqrt d := by ring
  have h3 := abs_norm_sub_norm_le (w + r) w
  rw [add_sub_cancel_left] at h3
  rw [hw, hsplit]
  exact h3.trans hrn

/-- The comparison of the cell weight with the lattice kernel, pointwise on the cell. -/
private lemma chi_cell_bounds (hd : 1 ≤ d) {y₀ ζ : EuclideanSpace ℝ (Fin d)} {y z : Site d}
    (hζ : ζ ∈ cell y) (hz : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2) :
    ((1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))))⁻¹ * kern d (z - y) ≤ chi d ‖y₀ - ζ‖ ∧
      chi d ‖y₀ - ζ‖ ≤ (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - y) := by
  have hq : 2 - 2 * (d : ℝ) ≤ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have habs := abs_norm_sub_sub_euclidNorm_le (y₀ := y₀) hζ hz
  have hr0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hs0 : 0 ≤ ‖y₀ - ζ‖ := norm_nonneg _
  have ht0 := LatticeProb.euclidNorm_nonneg (z - y)
  have hc : 0 < 1 + Real.sqrt d := by linarith
  have hcpos : 0 < (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) := Real.rpow_pos_of_pos hc _
  obtain ⟨habs1, habs2⟩ := abs_le.mp habs
  have hup := rpow_le_mul_rpow_of_le hs0 ht0 hc hq
    (show 1 + euclidNorm (z - y) ≤ (1 + Real.sqrt d) * (1 + ‖y₀ - ζ‖) by
      linarith [mul_nonneg hr0 hs0])
  have hlow := rpow_le_mul_rpow_of_le ht0 hs0 hc hq
    (show 1 + ‖y₀ - ζ‖ ≤ (1 + Real.sqrt d) * (1 + euclidNorm (z - y)) by
      linarith [mul_nonneg hr0 ht0])
  rw [chi_norm]
  constructor
  · rw [inv_mul_le_iff₀ hcpos]
    exact hlow
  · exact hup

/-- Two-sided bounds for the cell weight by the lattice kernel. -/
private lemma cellWeight_bounds (hd : 3 ≤ d) {y₀ : EuclideanSpace ℝ (Fin d)} {z : Site d}
    (hz : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2) (y : Site d) :
    ((1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))))⁻¹ * kern d (z - y) ≤ cellWeight d y₀ y ∧
      cellWeight d y₀ y ≤ (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - y) := by
  have hint : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => chi d ‖y₀ - ζ‖) :=
    (integrable_chi_norm hd).comp_sub_left y₀
  exact setIntegral_cell_mem_Icc y hint.integrableOn fun ζ hζ =>
    chi_cell_bounds (by omega) hζ hz

/-- Summing over the cells of a finite set of sites: if `Uf` varies by at most `M` across each
cell and is at least `-Cf` off the union of the cells, then the cell-weighted sum of the values
of `Uf` at the sites is at most the integral of `G Uf` plus `(M + Cf) ∫ G`. -/
private lemma sum_setIntegral_mul_le {G Uf : EuclideanSpace ℝ (Fin d) → ℝ} {S : Finset (Site d)}
    {M Cf : ℝ} (hG0 : ∀ ζ, 0 ≤ G ζ) (hG : Integrable G)
    (hGU : Integrable (fun ζ => G ζ * Uf ζ)) (hM : 0 ≤ M) (hCf : 0 ≤ Cf)
    (hmod : ∀ y ∈ S, ∀ ζ ∈ cell y, Uf (toSpace y) ≤ Uf ζ + M)
    (hfar : ∀ ζ ∉ ⋃ y ∈ S, cell y, -Cf ≤ Uf ζ) :
    ∑ y ∈ S, (∫ ζ in cell y, G ζ) * Uf (toSpace y) ≤
      (∫ ζ, G ζ * Uf ζ) + (M + Cf) * ∫ ζ, G ζ := by
  set F : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => G ζ * (Uf ζ + M + Cf) with hF
  have hFeq : F = fun ζ => G ζ * Uf ζ + (M + Cf) * G ζ := by
    funext ζ
    rw [hF]
    ring
  have hFint : Integrable F := by
    rw [hFeq]
    exact hGU.add (hG.const_mul _)
  have hVmeas : MeasurableSet (⋃ y ∈ S, cell y) :=
    Finset.measurableSet_biUnion S fun y _ => CERW.Support.Occupation.measurableSet_cell y
  have hterm : ∀ y ∈ S, (∫ ζ in cell y, G ζ) * Uf (toSpace y) ≤ ∫ ζ in cell y, F ζ := by
    intro y hy
    rw [← integral_mul_const]
    refine setIntegral_mono_on (hG.integrableOn.mul_const _) hFint.integrableOn
      (CERW.Support.Occupation.measurableSet_cell y) fun ζ hζ => ?_
    have h1 := mul_le_mul_of_nonneg_left (hmod y hy ζ hζ) (hG0 ζ)
    have h2 : G ζ * (Uf ζ + M) ≤ G ζ * (Uf ζ + M + Cf) :=
      mul_le_mul_of_nonneg_left (by linarith) (hG0 ζ)
    exact h1.trans h2
  have hsum : ∑ y ∈ S, ∫ ζ in cell y, F ζ = ∫ ζ in ⋃ y ∈ S, cell y, F ζ := by
    rw [integral_biUnion_finset S (fun y _ => CERW.Support.Occupation.measurableSet_cell y)
      (fun x _ y _ hxy => cell_disjoint hxy) (fun y _ => hFint.integrableOn)]
  have hcompl : 0 ≤ ∫ ζ in (⋃ y ∈ S, cell y)ᶜ, F ζ := by
    refine setIntegral_nonneg hVmeas.compl fun ζ hζ => ?_
    have := hfar ζ hζ
    exact mul_nonneg (hG0 ζ) (by linarith)
  have htot := integral_add_compl hVmeas hFint
  have hFval : ∫ ζ, F ζ = (∫ ζ, G ζ * Uf ζ) + (M + Cf) * ∫ ζ, G ζ := by
    rw [hFeq, integral_add hGU (hG.const_mul _), integral_const_mul]
  calc ∑ y ∈ S, (∫ ζ in cell y, G ζ) * Uf (toSpace y)
      ≤ ∑ y ∈ S, ∫ ζ in cell y, F ζ := Finset.sum_le_sum hterm
    _ = ∫ ζ in ⋃ y ∈ S, cell y, F ζ := hsum
    _ ≤ ∫ ζ, F ζ := by linarith
    _ = (∫ ζ, G ζ * Uf ζ) + (M + Cf) * ∫ ζ, G ζ := hFval

/-- For `d ≥ 1`, `Λ_Ψ ≥ 0`. -/
private lemma normMax_nonneg {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d) :
    0 ≤ normMax Ψ := by
  have h1 := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd
  have hn : ‖coordVec (⟨0, by omega⟩ : Fin d)‖ = 1 := by
    simp [coordVec, PiLp.norm_single]
  have h2 := CERW.Generic.Norm.le_normMax_mul hΨ (coordVec (⟨0, by omega⟩ : Fin d))
  have h3 := h1.2 (coordVec (⟨0, by omega⟩ : Fin d))
  rw [hn] at h2 h3
  linarith [h1.1]

/-- The gradient of a norm has Euclidean norm at most `Λ_Ψ` everywhere: where `Ψ` is
differentiable it is a subgradient, and elsewhere it is `0`. -/
private lemma norm_gradient_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d)
    (v : EuclideanSpace ℝ (Fin d)) : ‖gradient Ψ v‖ ≤ normMax Ψ := by
  by_cases hv : DifferentiableAt ℝ Ψ v
  · have h := (CERW.Generic.Norm.subgradient_euler hΨ
      (CERW.Generic.Norm.gradient_isSubgradient hΨ hv)).2 (gradient Ψ v)
    have h2 := CERW.Generic.Norm.le_normMax_mul hΨ (gradient Ψ v)
    rw [real_inner_self_eq_norm_mul_norm] at h
    have h3 : ‖gradient Ψ v‖ * ‖gradient Ψ v‖ ≤ normMax Ψ * ‖gradient Ψ v‖ := h.trans h2
    rcases eq_or_lt_of_le (norm_nonneg (gradient Ψ v)) with h0 | h0
    · rw [← h0]
      exact normMax_nonneg hΨ hd
    · exact le_of_mul_le_mul_right h3 h0
  · have h0 : gradient Ψ v = 0 := by
      rw [gradient, fderiv_zero_of_not_differentiableAt hv]
      simp
    rw [h0, norm_zero]
    exact normMax_nonneg hΨ hd

/-- The potential of a finite-volume set `D` at a point at distance at least `R ≥ 1` from every
point of `D` is at most `(2ε/ω_d) Λ |D| / R` in absolute value. -/
private lemma abs_normPotential_le_of_far {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDfin : volume D ≠ ⊤) {R : ℝ} (hR : 1 ≤ R) {ζ : EuclideanSpace ℝ (Fin d)}
    (hfar : ∀ v ∈ D, R ≤ ‖v - ζ‖) :
    |normPotential d ε Ψ D ζ| ≤
      2 * ε / unitBallVolume d * (normMax Ψ * (volume D).toReal / R) := by
  have hω := unitBallVolume_pos d
  have hΛ := normMax_nonneg hΨ (by omega)
  have hbd : ∀ v ∈ D, ‖inner ℝ (gradient Ψ v) (v - ζ) / ‖v - ζ‖ ^ d‖ ≤ normMax Ψ / R := by
    intro v hv
    have hw := hfar v hv
    have hw1 : 1 ≤ ‖v - ζ‖ := hR.trans hw
    have hwpos : 0 < ‖v - ζ‖ := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hwpos d)]
    have h1 : |inner ℝ (gradient Ψ v) (v - ζ)| ≤ normMax Ψ * ‖v - ζ‖ :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_gradient_le hΨ (by omega) v) (norm_nonneg _))
    have h2 : ‖v - ζ‖ ^ 2 ≤ ‖v - ζ‖ ^ d := pow_le_pow_right₀ hw1 hd
    rw [div_le_div_iff₀ (pow_pos hwpos d) (by linarith)]
    calc |inner ℝ (gradient Ψ v) (v - ζ)| * R ≤ (normMax Ψ * ‖v - ζ‖) * ‖v - ζ‖ :=
          mul_le_mul h1 hw (by linarith) (mul_nonneg hΛ hwpos.le)
      _ = normMax Ψ * ‖v - ζ‖ ^ 2 := by ring
      _ ≤ normMax Ψ * ‖v - ζ‖ ^ d := mul_le_mul_of_nonneg_left h2 hΛ
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume) hDfin.lt_top hbd
  have hreal : volume.real D = (volume D).toReal := rfl
  rw [hreal] at hint
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  unfold normPotential
  rw [abs_mul, abs_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [← Real.norm_eq_abs]
  calc ‖∫ v in D, inner ℝ (gradient Ψ v) (v - ζ) / ‖v - ζ‖ ^ d‖
      ≤ normMax Ψ / R * (volume D).toReal := hint
    _ = normMax Ψ * (volume D).toReal / R := by ring

/-- Near the origin the integrand of the radial estimate is at most `Λ (1 + |ζ|)^{-d}`. -/
private lemma chi_mul_min_le_near (hd : 3 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) (b : ℝ) (ζ : EuclideanSpace ℝ (Fin d)) :
    chi d ‖ζ‖ * min b (Ψ ζ) ≤ normMax Ψ * (1 + ‖ζ‖) ^ (-(d : ℝ)) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hx : 1 ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
  have hx0 : 0 < 1 + ‖ζ‖ := by linarith
  have hΨ0 : 0 ≤ Ψ ζ := (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 ζ
  have hΛ : Ψ ζ ≤ normMax Ψ * ‖ζ‖ := CERW.Generic.Norm.le_normMax_mul hΨ ζ
  have hΛ0 : 0 ≤ normMax Ψ := normMax_nonneg hΨ (by omega)
  have h1 : chi d ‖ζ‖ * min b (Ψ ζ) ≤ chi d ‖ζ‖ * (normMax Ψ * ‖ζ‖) :=
    mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hΛ) (chi_nonneg _)
  have h2 : (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) * ‖ζ‖ ≤ (1 + ‖ζ‖) ^ (-(d : ℝ)) := by
    calc (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) * ‖ζ‖
        ≤ (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) * (1 + ‖ζ‖) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hx0.le _)
      _ = (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ) + 1) := (Real.rpow_add_one hx0.ne' _).symm
      _ ≤ (1 + ‖ζ‖) ^ (-(d : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  calc chi d ‖ζ‖ * min b (Ψ ζ) ≤ chi d ‖ζ‖ * (normMax Ψ * ‖ζ‖) := h1
    _ = normMax Ψ * ((1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) * ‖ζ‖) := by rw [chi_norm]; ring
    _ ≤ normMax Ψ * (1 + ‖ζ‖) ^ (-(d : ℝ)) := mul_le_mul_of_nonneg_left h2 hΛ0

/-- Far from the origin the integrand of the radial estimate is at most `b |ζ|^{2-2d}`. -/
private lemma chi_mul_min_le_far (hd : 1 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {b : ℝ} (hb : 0 < b) {ζ : EuclideanSpace ℝ (Fin d)} (hζ : 0 < ‖ζ‖) :
    chi d ‖ζ‖ * min b (Ψ ζ) ≤ b * ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) ≤ ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) :=
    Real.rpow_le_rpow_of_nonpos hζ (by linarith) (by linarith)
  rw [chi_norm, show 2 - 2 * (d : ℝ) = -(2 * (d : ℝ) - 2) by ring]
  calc (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) * min b (Ψ ζ)
      ≤ (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) * b :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.rpow_nonneg (by linarith [hζ]) _)
    _ ≤ ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) * b := mul_le_mul_of_nonneg_right h1 hb.le
    _ = b * ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) := by ring

/-- The radial estimate `∫ χ(|ζ|) min(b, Ψ ζ) dζ ≤ σ_d (Λ log(1 + T) + 1)` with `T = max 1 b` and
`σ_d = d ω_d`. -/
private lemma integral_chi_mul_min_le (hd : 3 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {b : ℝ} (hb : 0 < b) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ * min b (Ψ ζ) ≤
      d * unitBallVolume d * (normMax Ψ * Real.log (1 + max 1 b) + 1) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set T : ℝ := max 1 b with hT
  have hT1 : 1 ≤ T := le_max_left _ _
  have hTb : b ≤ T := le_max_right _ _
  have hTpos : 0 < T := by linarith
  have hΛ0 : 0 ≤ normMax Ψ := normMax_nonneg hΨ (by omega)
  have hω := unitBallVolume_pos d
  set f : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => chi d ‖ζ‖ * min b (Ψ ζ) with hf
  have hfm : Measurable f :=
    (measurable_chi.comp measurable_norm).mul
      (measurable_const.min (CERW.Generic.Norm.norm_continuous hΨ).measurable)
  have hf0 : ∀ ζ, 0 ≤ f ζ := fun ζ =>
    mul_nonneg (chi_nonneg _) (le_min hb.le ((CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 ζ))
  obtain ⟨hI1, hJ1⟩ :=
    CERW.Generic.Kernel.integrableOn_ball_one_add_norm_rpow_and_integral_le (d := d)
      (by omega) hTpos
  obtain ⟨hI2, hJ2⟩ :=
    CERW.Generic.Kernel.integrableOn_compl_ball_rpow_neg_and_integral_eq (d := d)
      (s := 2 * (d : ℝ) - 2) (ρ := T) (by omega) (by linarith) hTpos
  have hfb : IntegrableOn f (Metric.ball 0 T) :=
    (hI1.const_mul (normMax Ψ)).mono' hfm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_ball fun ζ _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ζ)]
        exact chi_mul_min_le_near hd hΨ b ζ)
  have hfc : IntegrableOn f (Metric.ball 0 T)ᶜ :=
    (hI2.const_mul b).mono' hfm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_ball.compl fun ζ hζ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ζ)]
        have hζT : T ≤ ‖ζ‖ := by
          rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hζ
          exact hζ
        exact chi_mul_min_le_far (by omega) hb (by linarith))
  have hfint : Integrable f := by
    have := hfb.union hfc
    rwa [Set.union_compl_self, integrableOn_univ] at this
  have hA : ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T, f ζ ≤
      normMax Ψ * (d * unitBallVolume d * Real.log (1 + T)) := by
    calc ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T, f ζ
        ≤ ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T,
            normMax Ψ * (1 + ‖ζ‖) ^ (-(d : ℝ)) :=
          setIntegral_mono_on hfb (hI1.const_mul _) measurableSet_ball fun ζ _ =>
            chi_mul_min_le_near hd hΨ b ζ
      _ = normMax Ψ * ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T,
            (1 + ‖ζ‖) ^ (-(d : ℝ)) := integral_const_mul _ _
      _ ≤ normMax Ψ * (d * unitBallVolume d * Real.log (1 + T)) :=
          mul_le_mul_of_nonneg_left hJ1 hΛ0
  have hexp : (d : ℝ) - (2 * (d : ℝ) - 2) ≤ -1 := by linarith
  have hbT : b * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) ≤ 1 := by
    have h1 : T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) ≤ T ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hT1 hexp
    rw [Real.rpow_neg_one] at h1
    calc b * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) ≤ T * T⁻¹ :=
          mul_le_mul hTb h1 (Real.rpow_nonneg hTpos.le _) hTpos.le
      _ = 1 := mul_inv_cancel₀ hTpos.ne'
  have hB : ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ, f ζ ≤ d * unitBallVolume d := by
    have hdiv : (1 : ℝ) ≤ 2 * (d : ℝ) - 2 - d := by linarith
    calc ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ, f ζ
        ≤ ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ,
            b * ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) :=
          setIntegral_mono_on hfc (hI2.const_mul b) measurableSet_ball.compl fun ζ hζ => by
            have hζT : T ≤ ‖ζ‖ := by
              rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hζ
              exact hζ
            exact chi_mul_min_le_far (by omega) hb (by linarith)
      _ = b * (d * unitBallVolume d * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) /
            (2 * (d : ℝ) - 2 - d)) := by rw [integral_const_mul, hJ2]
      _ = d * unitBallVolume d * (b * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2))) /
            (2 * (d : ℝ) - 2 - d) := by ring
      _ ≤ d * unitBallVolume d * 1 / (2 * (d : ℝ) - 2 - d) := by
          gcongr
      _ ≤ d * unitBallVolume d := by
          rw [mul_one, div_le_iff₀ (by linarith)]
          have : 0 ≤ (d : ℝ) * unitBallVolume d := by positivity
          calc (d : ℝ) * unitBallVolume d = d * unitBallVolume d * 1 := (mul_one _).symm
            _ ≤ d * unitBallVolume d * (2 * (d : ℝ) - 2 - d) :=
                mul_le_mul_of_nonneg_left hdiv this
  rw [← integral_add_compl measurableSet_ball hfint]
  calc (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T, f ζ) +
        ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ, f ζ
      ≤ normMax Ψ * (d * unitBallVolume d * Real.log (1 + T)) + d * unitBallVolume d :=
        add_le_add hA hB
    _ = d * unitBallVolume d * (normMax Ψ * Real.log (1 + T) + 1) := by ring

/-- The kernel sum over times equals the local-time weighted kernel sum over any finite set of
sites containing the departure range. -/
private lemma sum_range_kern_eq (X : ℕ → Site d) (n : ℕ) {S : Finset (Site d)}
    (hS : departureRange X n ⊆ S) (y : Site d) :
    ∑ j ∈ Finset.range n, kern d (X j - y) =
      ∑ x ∈ S, (localTime X n x : ℝ) * kern d (x - y) := by
  rw [CERW.Support.LocalTime.sum_range_eq_sum_localTime X n (fun w => kern d (w - y))]
  refine Finset.sum_subset hS fun x _ hx => ?_
  rw [mem_departureRange_iff, not_lt, Nat.le_zero] at hx
  rw [hx, Nat.cast_zero, zero_mul]

/-- The lattice departure range lies in the lattice ball of radius `2n`. -/
private lemma departureRange_subset_ballFinset_two_mul {X : ℕ → Site d} {n : ℕ}
    (hXn : ∀ j, euclidNorm (X j) ≤ j) :
    departureRange X n ⊆ LatticeProb.ballFinset d (2 * n) := by
  intro x hx
  have h1 := CERW.Support.Occupation.departureRange_subset_ballFinset X n hx
  rw [LatticeProb.mem_ballFinset_iff] at h1 ⊢
  have h2 := CERW.Support.Norm.ContactShared.maxRadius_le_nat X n hXn
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The lattice step: there are constants `c₀, α₁` depending only on `d` and `C₁` such that the
kernel sum at a site `z` whose cell is near `y₀` satisfies
`c₀ Σ_j k(X_j - z) ≤ 2 Σ_{y} a(y) U(y) + α₁ L`. -/
private lemma kernel_sum_le (hd : 3 ≤ d) {C₁ : ℝ} (hC₁ : 0 ≤ C₁) :
    ∃ c₀ α₁ : ℝ, 0 < c₀ ∧ 0 ≤ α₁ ∧ ∀ (X : ℕ → Site d) (n : ℕ) (U : Site d → ℝ),
      (∀ j, euclidNorm (X j) ≤ j) →
      (∀ y : Site d, euclidNorm y ≤ 3 * n →
        |(localTime X n y : ℝ) - U y| ≤
          C₁ * (Real.sqrt ((∑ j ∈ Finset.range n, kern d (X j - y)) *
            Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2))) →
      ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (z : Site d), ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2 →
        c₀ * ∑ j ∈ Finset.range n, kern d (X j - z) ≤
          2 * ∑ y ∈ LatticeProb.ballFinset d (2 * n), cellWeight d y₀ y * U y +
            α₁ * Real.log ((n : ℝ) + 2) := by
  obtain ⟨K₀, hK₀pos, hK⟩ := CERW.Generic.Lattice.sum_finset_rpow_two_sub_two_mul_le hd
  have hK₀ : ∀ (F : Finset (Site d)) (u : Site d), ∑ y ∈ F, kern d (y - u) ≤ K₀ :=
    fun F u => hK F u
  have hd1 : 1 ≤ d := by omega
  set A₀ : ℝ := 2 * (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * K₀ with hA₀
  have hA₀pos : 0 < A₀ := by
    rw [hA₀]
    exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)) hK₀pos
  have hsq : 0 < 1 + Real.sqrt d := by linarith [Real.sqrt_nonneg (d : ℝ)]
  set c₁ : ℝ := (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) with hc₁
  have hc₁pos : 0 < c₁ := Real.rpow_pos_of_pos hsq _
  set c₀ : ℝ := c₁⁻¹ with hc₀
  have hc₀pos : 0 < c₀ := inv_pos.mpr hc₁pos
  set γ : ℝ := c₀ / (2 * (c₁ * A₀)) with hγ
  have hγpos : 0 < γ := by rw [hγ]; positivity
  have hγ' : γ * (c₁ * A₀) ≤ c₀ / 2 := by
    rw [hγ]
    have : 0 < c₁ * A₀ := mul_pos hc₁pos hA₀pos
    field_simp
    exact le_refl _
  refine ⟨c₀, 2 * (C₁ + C₁ ^ 2 / (4 * γ)) * (c₁ * K₀), hc₀pos, by positivity, ?_⟩
  intro X n U hXn hfine y₀ z hz
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  set S : Finset (Site d) := LatticeProb.ballFinset d (2 * n) with hS
  have hAS : departureRange X n ⊆ S := departureRange_subset_ballFinset_two_mul hXn
  have hℓ0 : ∀ y : Site d, 0 ≤ (localTime X n y : ℝ) := fun y => Nat.cast_nonneg _
  have hw := fun y => cellWeight_bounds hd hz y
  have hfine' : ∀ y ∈ S, (localTime X n y : ℝ) ≤ U y +
      C₁ * (Real.sqrt ((∑ x ∈ S, (localTime X n x : ℝ) * kern d (x - y)) * L) + L) := by
    intro y hy
    rw [hS, LatticeProb.mem_ballFinset_iff] at hy
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h := hfine y (by linarith)
    rw [← sum_range_kern_eq X n hAS y] at *
    have := (abs_le.mp h).2
    linarith
  have habs := absorb_sum (S := S) (z := z) (c₀ := c₀) (c₁ := c₁) (K₀ := K₀) (A₀ := A₀)
    (C₁ := C₁) (L := L) (γ := γ) (ℓ := fun y => (localTime X n y : ℝ)) (U := U)
    (a := cellWeight d y₀) hK₀ (fun F x => sum_kern_mul_kern_le hd1 hK₀ F z x) hc₀pos hc₁pos
    hA₀pos.le (fun y => by
      have := hw y
      rw [hc₀]
      exact this) hℓ0 hC₁ hL0 hγpos hγ' hfine'
  have hlow : c₀ * ∑ j ∈ Finset.range n, kern d (X j - z) ≤
      ∑ y ∈ S, cellWeight d y₀ y * (localTime X n y : ℝ) := by
    rw [sum_range_kern_eq X n hAS z, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    calc c₀ * ((localTime X n x : ℝ) * kern d (x - z))
        = (localTime X n x : ℝ) * (c₀ * kern d (z - x)) := by
          rw [kern_sub_comm x z]; ring
      _ ≤ (localTime X n x : ℝ) * cellWeight d y₀ x :=
          mul_le_mul_of_nonneg_left (hw x).1 (hℓ0 x)
      _ = cellWeight d y₀ x * (localTime X n x : ℝ) := by ring
  calc c₀ * ∑ j ∈ Finset.range n, kern d (X j - z)
      ≤ ∑ y ∈ S, cellWeight d y₀ y * (localTime X n y : ℝ) := hlow
    _ ≤ 2 * ∑ y ∈ S, cellWeight d y₀ y * U y +
          2 * ((C₁ + C₁ ^ 2 / (4 * γ)) * L) * (c₁ * K₀) := habs
    _ = 2 * ∑ y ∈ S, cellWeight d y₀ y * U y +
          2 * (C₁ + C₁ ^ 2 / (4 * γ)) * (c₁ * K₀) * L := by ring

/-- The logarithm of `1 + max 1 b` is at most a constant multiple of `log (n + 2)` when
`b ≤ 2 Λ n`. -/
private lemma log_one_add_max_le {Λ b : ℝ} {n : ℕ} (hn : 2 ≤ n) (hb : b ≤ Λ * (2 * n)) :
    Real.log (1 + max 1 b) ≤
      (1 + Real.log (1 + max 1 (2 * Λ))) * Real.log ((n : ℝ) + 2) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set Λ' : ℝ := max 1 (2 * Λ) with hΛ'
  have hΛ'1 : 1 ≤ Λ' := le_max_left _ _
  have hΛ'2 : 2 * Λ ≤ Λ' := le_max_right _ _
  have hn2 : 1 ≤ (n : ℝ) + 2 := by linarith
  have hT : max 1 b ≤ Λ' * ((n : ℝ) + 2) := by
    refine max_le ?_ ?_
    · exact one_le_mul_of_one_le_of_one_le hΛ'1 hn2
    · calc b ≤ Λ * (2 * n) := hb
        _ = (2 * Λ) * n := by ring
        _ ≤ Λ' * n := mul_le_mul_of_nonneg_right hΛ'2 hn0
        _ ≤ Λ' * ((n : ℝ) + 2) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h1 : 1 + max 1 b ≤ (1 + Λ') * ((n : ℝ) + 2) := by
    calc 1 + max 1 b ≤ 1 + Λ' * ((n : ℝ) + 2) := by linarith
      _ ≤ (1 + Λ') * ((n : ℝ) + 2) := by linarith
  have hpos1 : 0 < 1 + max 1 b := by linarith [le_max_left (1 : ℝ) b]
  have hpos2 : 0 < 1 + Λ' := by linarith
  have hpos3 : 0 < (n : ℝ) + 2 := by linarith
  have hL : 1 ≤ Real.log ((n : ℝ) + 2) := CERW.Support.Law.one_le_log_add_two hn
  have hlog0 : 0 ≤ Real.log (1 + Λ') := Real.log_nonneg (by linarith)
  calc Real.log (1 + max 1 b) ≤ Real.log ((1 + Λ') * ((n : ℝ) + 2)) :=
        Real.log_le_log hpos1 h1
    _ = Real.log (1 + Λ') + Real.log ((n : ℝ) + 2) := Real.log_mul hpos2.ne' hpos3.ne'
    _ ≤ (1 + Real.log (1 + Λ')) * Real.log ((n : ℝ) + 2) := by
        linarith [mul_nonneg hlog0 (sub_nonneg.mpr hL)]

/-- The far-field bound: at a point of the complement of the cells of the ball of radius `2n`,
the potential of `D_n` is at least `-C` for a constant `C`. -/
private lemma neg_le_normPotential_of_not_mem {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) {X : ℕ → Site d} {n : ℕ} (hn : 2 ≤ n)
    (hn4 : 4 * Real.sqrt d ≤ n) (hXn : ∀ j, euclidNorm (X j) ≤ j)
    {ζ : EuclideanSpace ℝ (Fin d)}
    (hζ : ζ ∉ ⋃ y ∈ LatticeProb.ballFinset d (2 * n), cell y) :
    -(2 * ε / unitBallVolume d * (2 * normMax Ψ)) ≤ normPotential d ε Ψ (cellSet X n) ζ := by
  have hω := unitBallVolume_pos d
  have hΛ0 := normMax_nonneg hΨ (by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmax : maxRadius X n ≤ n := CERW.Support.Norm.ContactShared.maxRadius_le_nat X n hXn
  have hc : cellCenter ζ ∉ LatticeProb.ballFinset d (2 * n) := fun hcS =>
    hζ (Set.mem_iUnion₂.mpr ⟨cellCenter ζ, hcS, mem_cell_cellCenter ζ⟩)
  rw [LatticeProb.mem_ballFinset_iff, not_le] at hc
  have h1 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter ζ)
  have hζn : 2 * (n : ℝ) - Real.sqrt d / 2 < ‖ζ‖ := by
    have h2 : ‖toSpace (cellCenter ζ)‖ ≤ ‖ζ‖ + ‖ζ - toSpace (cellCenter ζ)‖ := by
      calc ‖toSpace (cellCenter ζ)‖ = ‖ζ - (ζ - toSpace (cellCenter ζ))‖ := by
            rw [sub_sub_cancel]
        _ ≤ ‖ζ‖ + ‖ζ - toSpace (cellCenter ζ)‖ := norm_sub_le _ _
    rw [norm_toSpace] at h2
    linarith
  have hfar : ∀ v ∈ cellSet X n, (n : ℝ) / 2 ≤ ‖v - ζ‖ := by
    intro v hv
    have hvn := CERW.Support.Occupation.norm_le_of_mem_cellSet X n hv
    have h3 : ‖ζ‖ - ‖v‖ ≤ ‖ζ - v‖ := norm_sub_norm_le ζ v
    rw [norm_sub_rev] at h3
    linarith [Real.sqrt_nonneg (d : ℝ)]
  have hDfin : volume (cellSet X n) ≠ ⊤ := by
    rw [CERW.Support.Occupation.volume_cellSet]
    exact ENNReal.natCast_ne_top _
  have hvol : (volume (cellSet X n)).toReal ≤ n := by
    rw [CERW.Support.Occupation.volume_cellSet, ENNReal.toReal_natCast]
    exact_mod_cast CERW.Support.Occupation.card_departureRange_le X n
  have hpot := abs_normPotential_le_of_far hΨ hd hε hDfin (R := (n : ℝ) / 2)
    (by linarith) hfar
  have hratio : normMax Ψ * (volume (cellSet X n)).toReal / ((n : ℝ) / 2) ≤ 2 * normMax Ψ := by
    rw [div_le_iff₀ (by linarith)]
    calc normMax Ψ * (volume (cellSet X n)).toReal ≤ normMax Ψ * n :=
          mul_le_mul_of_nonneg_left hvol hΛ0
      _ = 2 * normMax Ψ * ((n : ℝ) / 2) := by ring
  have hc0 : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hbound := hpot.trans (mul_le_mul_of_nonneg_left hratio hc0)
  exact (neg_le_neg_iff.mpr hbound).trans (neg_abs_le _)

/-- The potential step: the `a`-weighted sum of the potential over the lattice ball of radius
`2n` is at most `β L + m U(y₀)`, where `m = ∫ χ(|ζ|) dζ` and `β` depends only on `d, Ψ, ε, C₃`. -/
private lemma sum_cellWeight_mul_potential_le (hd : 3 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hconv : CERW.Support.Norm.ContactShared.ConvBound d Ψ ε) {C₃ : ℝ} (hC₃ : 0 ≤ C₃) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ (X : ℕ → Site d) (n : ℕ), 2 ≤ n → 4 * Real.sqrt d ≤ n →
      (∀ j, euclidNorm (X j) ≤ j) →
      (∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * ((n : ℝ) + Real.sqrt d) →
        ‖y - z‖ ≤ Real.sqrt d →
        |normPotential d ε Ψ (cellSet X n) y - normPotential d ε Ψ (cellSet X n) z| ≤
          C₃ * Real.log ((n : ℝ) + 2)) →
      ∀ (b : ℝ) (y₀ : EuclideanSpace ℝ (Fin d)), 0 < b → {v | Ψ v < b} ⊆ cellSet X n →
        b ≤ normMax Ψ * (maxRadius X n + Real.sqrt d) → Ψ y₀ = b →
        ∑ y ∈ LatticeProb.ballFinset d (2 * n),
            cellWeight d y₀ y * normPotential d ε Ψ (cellSet X n) (toSpace y) ≤
          β * Real.log ((n : ℝ) + 2) +
            (∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖) * normPotential d ε Ψ (cellSet X n) y₀ := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hω := unitBallVolume_pos d
  have hΛ0 := normMax_nonneg hΨ hd1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set m : ℝ := ∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun ζ => chi_nonneg _
  set Cf : ℝ := 2 * ε / unitBallVolume d * (2 * normMax Ψ) with hCf
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  set CT : ℝ := 1 + Real.log (1 + max 1 (2 * normMax Ψ)) with hCT
  have hCT0 : 0 ≤ CT := by
    rw [hCT]
    have : 0 ≤ Real.log (1 + max 1 (2 * normMax Ψ)) :=
      Real.log_nonneg (by linarith [le_max_left (1 : ℝ) (2 * normMax Ψ)])
    linarith
  refine ⟨2 * d * ε * (d * unitBallVolume d * (normMax Ψ * CT + 1)) + (C₃ + Cf) * m,
    by positivity, ?_⟩
  intro X n hn hn4 hXn hmod b y₀ hb hsub hble hy₀
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hL1 : 1 ≤ L := CERW.Support.Law.one_le_log_add_two hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmax : maxRadius X n ≤ n := CERW.Support.Norm.ContactShared.maxRadius_le_nat X n hXn
  have hsd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  set D : Set (EuclideanSpace ℝ (Fin d)) := cellSet X n with hD
  have hDmeas : MeasurableSet D := CERW.Support.Occupation.measurableSet_cellSet X n
  have hDbdd : Bornology.IsBounded D :=
    (Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin d)))
      (r := maxRadius X n + Real.sqrt d)).subset
      (CERW.Support.Occupation.cellSet_subset_ball hd1 X n)
  obtain ⟨hint, hle⟩ := hconv (chi d) measurable_chi chi_nonneg ⟨1, chi_le_one hd1⟩
    (integrable_chi_norm hd) D hDmeas hDbdd b hb hsub y₀ hy₀
  set G : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => chi d ‖y₀ - ζ‖ with hG
  set Uf : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => normPotential d ε Ψ D ζ with hUf
  have hG0 : ∀ ζ, 0 ≤ G ζ := fun ζ => chi_nonneg _
  have hGint : Integrable G := (integrable_chi_norm hd).comp_sub_left y₀
  have hGU : Integrable (fun ζ => G ζ * Uf ζ) := by
    have := hint.comp_sub_left y₀
    simpa only [sub_sub_cancel] using this
  have hGUint : ∫ ζ, G ζ * Uf ζ =
      ∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ * normPotential d ε Ψ D (y₀ - ζ) := by
    have := integral_sub_left_eq_self
      (fun ζ : EuclideanSpace ℝ (Fin d) => chi d ‖ζ‖ * normPotential d ε Ψ D (y₀ - ζ))
      volume y₀
    simpa only [sub_sub_cancel] using this
  have hGm : ∫ ζ, G ζ = m :=
    integral_sub_left_eq_self (fun ζ : EuclideanSpace ℝ (Fin d) => chi d ‖ζ‖) volume y₀
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
    neg_le_normPotential_of_not_mem hΨ hd2 hε.le hn hn4 hXn hζ
  have hsum := sum_setIntegral_mul_le (S := LatticeProb.ballFinset d (2 * n)) (M := C₃ * L)
    (Cf := Cf) hG0 hGint hGU (mul_nonneg hC₃ (by linarith)) hCf0 hmod' hfar
  have hb2 : b ≤ normMax Ψ * (2 * n) := by
    calc b ≤ normMax Ψ * (maxRadius X n + Real.sqrt d) := hble
      _ ≤ normMax Ψ * (2 * n) := mul_le_mul_of_nonneg_left (by linarith) hΛ0
  have hlog := log_one_add_max_le hn hb2
  have hIB := integral_chi_mul_min_le hd hΨ hb
  have hIB' : ∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ * min b (Ψ ζ) ≤
      d * unitBallVolume d * ((normMax Ψ * CT + 1) * L) := by
    refine hIB.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    calc normMax Ψ * Real.log (1 + max 1 b) + 1
        ≤ normMax Ψ * (CT * L) + 1 := by
          have := mul_le_mul_of_nonneg_left hlog hΛ0
          linarith
      _ ≤ (normMax Ψ * CT + 1) * L := by
          linarith
  have hP : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  have hstep : 2 * (d : ℝ) * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ * min b (Ψ ζ)) ≤
      2 * d * ε * (d * unitBallVolume d * (normMax Ψ * CT + 1)) * L := by
    calc 2 * (d : ℝ) * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ * min b (Ψ ζ))
        ≤ 2 * d * ε * (d * unitBallVolume d * ((normMax Ψ * CT + 1) * L)) :=
          mul_le_mul_of_nonneg_left hIB' hP
      _ = 2 * d * ε * (d * unitBallVolume d * (normMax Ψ * CT + 1)) * L := by ring
  have hCfm : Cf * m ≤ Cf * m * L := by
    have := mul_nonneg (mul_nonneg hCf0 hm0) (sub_nonneg.mpr hL1)
    linarith
  calc ∑ y ∈ LatticeProb.ballFinset d (2 * n),
          cellWeight d y₀ y * normPotential d ε Ψ D (toSpace y)
      ≤ (∫ ζ, G ζ * Uf ζ) + (C₃ * L + Cf) * ∫ ζ, G ζ := hsum
    _ ≤ (2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ * min b (Ψ ζ)) +
          m * normPotential d ε Ψ D y₀) + (C₃ * L + Cf) * m := by
        rw [hGm, hGUint]
        linarith
    _ ≤ (2 * d * ε * (d * unitBallVolume d * (normMax Ψ * CT + 1)) * L +
          m * normPotential d ε Ψ D y₀) + (C₃ * L + Cf) * m := by linarith
    _ ≤ (2 * d * ε * (d * unitBallVolume d * (normMax Ψ * CT + 1)) + (C₃ + Cf) * m) * L +
          m * normPotential d ε Ψ D y₀ := by linarith

/-- The final absorption: if `H ≤ C₁ √(W L) + (C₁ + C₃) L` and `W ≤ M (H + L)`, with `H ≥ 0`,
then `H ≤ (1 + C₁² M + 2 C₁ + 2 C₃) L`. -/
private lemma le_of_le_sqrt_add {H W L M C₁ C₃ : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hC₁ : 0 ≤ C₁)
    (hH0 : 0 ≤ H) (hW : W ≤ M * (H + L))
    (hH : H ≤ C₁ * Real.sqrt (W * L) + (C₁ + C₃) * L) :
    H ≤ (1 + C₁ ^ 2 * M + 2 * C₁ + 2 * C₃) * L := by
  have h1 : Real.sqrt (W * L) ≤ Real.sqrt ((H + L) * (M * L)) := by
    refine Real.sqrt_le_sqrt ?_
    calc W * L ≤ M * (H + L) * L := mul_le_mul_of_nonneg_right hW hL
      _ = (H + L) * (M * L) := by ring
  have h2 := mul_sqrt_le_add (H + L) (M * L) C₁ (1 / 2) (by linarith) (mul_nonneg hM hL) hC₁
    (by norm_num)
  have h3 : C₁ * Real.sqrt (W * L) ≤ C₁ * Real.sqrt ((H + L) * (M * L)) :=
    mul_le_mul_of_nonneg_left h1 hC₁
  have h4 : C₁ ^ 2 * (M * L) / (4 * (1 / 2)) = C₁ ^ 2 * M * L / 2 := by ring
  rw [h4] at h2
  linarith

/-- **The contact bound in dimension `d ≥ 3`.** The potential of the cell set at a contact point
is at most a constant times `log (n + 2)`, given the pointwise local-time bound and the modulus of
the potential on cells. -/
theorem contact_bound_three_le {d : ℕ} (hd : 3 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε) (hconv : CERW.Support.Norm.ContactShared.ConvBound d Ψ ε)
    (C₁ C₃ : ℝ) (hC₁ : 0 ≤ C₁) (hC₃ : 0 ≤ C₃) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ → Site d) (n : ℕ), 2 ≤ n → 4 * Real.sqrt d ≤ n → X 0 = 0 →
      (∀ j, euclidNorm (X j) ≤ j) →
      (∀ y : Site d, euclidNorm y ≤ 3 * n →
        |(localTime X n y : ℝ) - normPotential d ε Ψ (cellSet X n) (toSpace y)| ≤
          C₁ * (Real.sqrt ((∑ j ∈ Finset.range n,
            (1 + euclidNorm (X j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2))) →
      (∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * ((n : ℝ) + Real.sqrt d) →
        ‖y - z‖ ≤ Real.sqrt d →
        |normPotential d ε Ψ (cellSet X n) y - normPotential d ε Ψ (cellSet X n) z| ≤
          C₃ * Real.log ((n : ℝ) + 2)) →
      ∀ y₀ : EuclideanSpace ℝ (Fin d), Ψ y₀ = normInnerRadius Ψ X n →
        y₀ ∈ closure (cellSet X n)ᶜ →
        normPotential d ε Ψ (cellSet X n) y₀ ≤ C * Real.log ((n : ℝ) + 2) := by
  obtain ⟨c₀, α₁, hc₀, hα₁, hlat⟩ := kernel_sum_le hd hC₁
  obtain ⟨β, hβ, hpot⟩ := sum_cellWeight_mul_potential_le hd hΨ hε hconv hC₃
  set m : ℝ := ∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun ζ => chi_nonneg _
  set M : ℝ := (2 * β + α₁ + 2 * m) / c₀ with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine ⟨1 + C₁ ^ 2 * M + 2 * C₁ + 2 * C₃, by positivity, ?_⟩
  intro X n hn hn4 hX0 hXn hfine hmod y₀ hy₀ hcl
  obtain ⟨hbpos, hsub, hble, hy₀n, z, hz0, hzy, hzn⟩ :=
    CERW.Support.Norm.ContactShared.contact_setup (by omega) hΨ X n (by omega) hX0 hy₀ hcl
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hL1 : 1 ≤ L := CERW.Support.Law.one_le_log_add_two hn
  set H : ℝ := normPotential d ε Ψ (cellSet X n) y₀ with hH
  by_cases hH0 : H ≤ 0
  · have : 0 ≤ (1 + C₁ ^ 2 * M + 2 * C₁ + 2 * C₃) * L := by positivity
    linarith
  rw [not_le] at hH0
  have hmax : maxRadius X n ≤ n := CERW.Support.Norm.ContactShared.maxRadius_le_nat X n hXn
  have hsd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hfz := hfine z (by linarith)
  rw [hz0, Nat.cast_zero, zero_sub, abs_neg] at hfz
  have hmodz := hmod y₀ (toSpace z) (by linarith) (by rw [norm_sub_rev]; linarith)
  have hUz := (abs_le.mp hfz).2
  have hstar : H ≤ C₁ * Real.sqrt ((∑ j ∈ Finset.range n, kern d (X j - z)) * L) +
      (C₁ + C₃) * L := by
    have := (abs_le.mp hmodz).1
    have h2 : H - normPotential d ε Ψ (cellSet X n) (toSpace z) ≤ C₃ * L := by
      have := (abs_le.mp hmodz).2
      linarith
    change normPotential d ε Ψ (cellSet X n) (toSpace z) ≤
      C₁ * (Real.sqrt ((∑ j ∈ Finset.range n, kern d (X j - z)) * L) + L) at hUz
    linarith
  have hb1 := hlat X n (fun y => normPotential d ε Ψ (cellSet X n) (toSpace y)) hXn hfine y₀ z hzy
  have hb2 := hpot X n hn hn4 hXn hmod (normInnerRadius Ψ X n) y₀ hbpos hsub hble hy₀
  have hW : (∑ j ∈ Finset.range n, kern d (X j - z)) ≤ M * (H + L) := by
    refine le_of_mul_le_mul_left ?_ hc₀
    have h1 : c₀ * (∑ j ∈ Finset.range n, kern d (X j - z)) ≤
        (2 * β + α₁) * L + 2 * m * H := by
      linarith
    have h2 : c₀ * (M * (H + L)) = (2 * β + α₁ + 2 * m) * (H + L) := by
      rw [hM]
      field_simp
    rw [h2]
    have h3 : 0 ≤ (2 * β + α₁) * H := mul_nonneg (by linarith) hH0.le
    have h4 : 0 ≤ 2 * m * L := mul_nonneg (by linarith) (by linarith)
    linarith
  exact le_of_le_sqrt_add (by linarith) hM0 hC₁ hH0.le hW hstar

end CERW.Support.Norm.ContactHigh

namespace CERW.Support.Norm.ContactAssembly

open MeasureTheory Filter Topology
open CERW

variable {d : ℕ}

/-- A subgradient selection of a norm with ellipticity gives the coordinate bound
`ε |ξ_i(x)| ≤ 1/d` needed for the transition probabilities to be nonnegative. -/
theorem drift_coord_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    {ξ : LatticeProb.Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : LatticeProb.Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0) :
    ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ) := by
  intro z i
  by_cases hz : z = 0
  · rw [hz, hξ0]
    simp only [PiLp.zero_apply, abs_zero, mul_zero]
    positivity
  · exact (mul_le_mul_of_nonneg_left
      (CERW.Generic.Norm.subgradient_abs_coord_le hΨ (hξ z hz) i) hε.le).trans (hell i).le

/-- A set covered by three events of small probability and a null event has small probability. -/
theorem measure_le_of_subset_union_three {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S E₁ E₂ E₃ N : Set Ω} {a₁ a₂ a₃ C : ℝ} (hS : S ⊆ E₁ ∪ E₂ ∪ E₃ ∪ N)
    (h₁ : μ E₁ ≤ ENNReal.ofReal a₁) (h₂ : μ E₂ ≤ ENNReal.ofReal a₂)
    (h₃ : μ E₃ ≤ ENNReal.ofReal a₃) (hN : μ N = 0) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (ha₃ : 0 ≤ a₃) (hC : a₁ + a₂ + a₃ ≤ C) : μ S ≤ ENNReal.ofReal C := by
  calc μ S ≤ μ (E₁ ∪ E₂ ∪ E₃ ∪ N) := measure_mono hS
    _ ≤ μ (E₁ ∪ E₂ ∪ E₃) + μ N := measure_union_le _ _
    _ = μ (E₁ ∪ E₂ ∪ E₃) := by rw [hN, add_zero]
    _ ≤ μ (E₁ ∪ E₂) + μ E₃ := measure_union_le _ _
    _ ≤ (μ E₁ + μ E₂) + μ E₃ := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ (ENNReal.ofReal a₁ + ENNReal.ofReal a₂) + ENNReal.ofReal a₃ := by gcongr
    _ = ENNReal.ofReal (a₁ + a₂ + a₃) := by
        rw [ENNReal.ofReal_add (add_nonneg ha₁ ha₂) ha₃, ENNReal.ofReal_add ha₁ ha₂]
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC

/-- `r √(a/r) = √(r a)` for `r > 0`. -/
theorem mul_sqrt_div_eq {r a : ℝ} (hr : 0 < r) :
    r * Real.sqrt (a / r) = Real.sqrt (r * a) := by
  have h : r * a = r ^ 2 * (a / r) := by
    field_simp
  rw [h, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]

/-- For `n ≥ 2`, `log(n + 2) ≤ 2 log n`. -/
theorem log_add_two_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  calc Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log (by linarith) h1
    _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num

/-- For `n ≥ 2` the logarithm `log n` is positive. -/
theorem log_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log (n : ℝ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact Real.log_pos (by linarith)

/-- The extreme values of a norm on the Euclidean unit sphere satisfy `c_Ψ ≤ Λ_Ψ`. -/
theorem normMin_le_normMax {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hd : 1 ≤ d) (hΨ : IsNorm Ψ) :
    normMin Ψ ≤ normMax Ψ := by
  have hn : ‖coordVec (⟨0, by omega⟩ : Fin d)‖ = 1 := by
    simp [coordVec, PiLp.norm_single]
  have h1 := (CERW.Generic.Norm.normMin_pos_mul_le hΨ hd).2 (coordVec (⟨0, by omega⟩ : Fin d))
  have h2 := CERW.Generic.Norm.le_normMax_mul hΨ (coordVec (⟨0, by omega⟩ : Fin d))
  rw [hn] at h1 h2
  linarith

/-- The unit ball of a norm has positive volume. -/
theorem normBallVolume_pos' {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hd : 1 ≤ d) (hΨ : IsNorm Ψ) :
    0 < normBallVolume Ψ := by
  obtain ⟨hc, hle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc (normMin_le_normMax hd hΨ)
  have hlow : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / normMax Ψ) ⊆
      {y | Ψ y < 1} := by
    intro y hy
    rw [mem_ball_zero_iff, lt_div_iff₀ hΛ] at hy
    have := CERW.Generic.Norm.le_normMax_mul hΨ y
    simp only [Set.mem_setOf_eq]
    nlinarith
  have hup : {y | Ψ y < 1} ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / normMin Ψ) := by
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    rw [mem_ball_zero_iff, lt_div_iff₀ hc]
    have := hle y
    nlinarith
  unfold normBallVolume
  refine ENNReal.toReal_pos ?_ ?_
  · exact (lt_of_lt_of_le (Metric.measure_ball_pos volume _ (one_div_pos.mpr hΛ))
      (measure_mono hlow)).ne'
  · exact ((measure_mono hup).trans_lt measure_ball_lt_top).ne

end CERW.Support.Norm.ContactAssembly

namespace CERW.Support.Norm.ContactAssembly

open Filter Topology

/-- The cube root scale `r_n = (a n)^{1/3}` eventually dominates `1` and `log(n + 2)^4`, and is
eventually so small that `c₁ r_n + c₂ ≤ n`. -/
theorem eventually_cube_root_scale {a : ℝ} (ha : 0 < a) (c₁ c₂ : ℝ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ (a * (n : ℝ)) ^ ((1 : ℝ) / 3) ∧
      Real.log ((n : ℝ) + 2) ^ 4 ≤ (a * (n : ℝ)) ^ ((1 : ℝ) / 3) ∧
      c₁ * (a * (n : ℝ)) ^ ((1 : ℝ) / 3) + c₂ ≤ n := by
  set K : ℝ := a ^ ((1 : ℝ) / 3) with hK
  have hKpos : 0 < K := Real.rpow_pos_of_pos ha _
  have hmul : ∀ n : ℕ, (a * (n : ℝ)) ^ ((1 : ℝ) / 3) = K * (n : ℝ) ^ ((1 : ℝ) / 3) := fun n =>
    Real.mul_rpow ha.le (Nat.cast_nonneg n)
  have hT : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 3)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hlog := CERW.Support.Main.tendsto_log_rpow_div_rpow 4 (c := (1 : ℝ) / 3) (by norm_num)
  have hlog' : ∀ᶠ n : ℕ in atTop, Real.log ((n : ℝ) + 2) ^ (4 : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 3) < K :=
    hlog.eventually (gt_mem_nhds hKpos)
  set t₀ : ℝ := max 1 (max (1 / K) (|c₁| * K + |c₂| + 1)) with ht₀
  have hbig : ∀ᶠ n : ℕ in atTop, t₀ ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := hT.eventually_ge_atTop t₀
  have hpos : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  filter_upwards [hlog', hbig, hpos] with n h1 h2 h3
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h3
  have hnt : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hn0 _
  rw [hmul n]
  have ht1 : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := (le_max_left _ _).trans h2
  have ht2 : 1 / K ≤ (n : ℝ) ^ ((1 : ℝ) / 3) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans h2
  have ht3 : |c₁| * K + |c₂| + 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 3) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans h2
  refine ⟨?_, ?_, ?_⟩
  · have : 1 ≤ K * (n : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [div_le_iff₀ hKpos] at ht2
      linarith
    exact this
  · have h4 : Real.log ((n : ℝ) + 2) ^ (4 : ℝ) < K * (n : ℝ) ^ ((1 : ℝ) / 3) := by
      have := (div_lt_iff₀ hnt).mp h1
      linarith
    have h5 : Real.log ((n : ℝ) + 2) ^ (4 : ℝ) = Real.log ((n : ℝ) + 2) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [h5] at h4
    exact h4.le
  · set t : ℝ := (n : ℝ) ^ ((1 : ℝ) / 3) with htdef
    have hcube : (n : ℝ) = t ^ 3 := by
      rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      norm_num
    have ht2' : t ≤ t ^ 2 := by nlinarith
    have h5 : |c₁| * K + |c₂| ≤ t ^ 2 := by linarith
    have h6 : (|c₁| * K + |c₂|) * t ≤ t ^ 2 * t :=
      mul_le_mul_of_nonneg_right h5 hnt.le
    have h7 : c₁ * (K * t) + c₂ ≤ (|c₁| * K + |c₂|) * t := by
      have e1 : c₁ * (K * t) ≤ |c₁| * (K * t) := mul_le_mul_of_nonneg_right (le_abs_self c₁)
        (by positivity)
      have e2 : c₂ ≤ |c₂| * t := by
        calc c₂ ≤ |c₂| := le_abs_self c₂
          _ = |c₂| * 1 := (mul_one _).symm
          _ ≤ |c₂| * t := mul_le_mul_of_nonneg_left ht1 (abs_nonneg _)
      nlinarith
    calc c₁ * (K * t) + c₂ ≤ (|c₁| * K + |c₂|) * t := h7
      _ ≤ t ^ 2 * t := h6
      _ = n := by rw [hcube]; ring

end CERW.Support.Norm.ContactAssembly

namespace CERW.Support.Norm

open CERW.Support.Statements CERW.Support.Norm.ContactShared CERW.Support.Norm.ContactAssembly

/-- The fine pointwise bound from the Dynkin decomposition and the local martingale bound: if
`|a + m| ≤ c₁ L` and `|m| ≤ c₂ (s + L)` then `|a| ≤ (c₁ + c₂)(s + L)`. -/
private lemma abs_le_add_of_abs_add_le {a m L s c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁)
    (hs : 0 ≤ s) (h1 : |a + m| ≤ c₁ * L) (h2 : |m| ≤ c₂ * (s + L)) :
    |a| ≤ (c₁ + c₂) * (s + L) := by
  have h3 : |a| ≤ |a + m| + |m| := by
    calc |a| = |(a + m) - m| := by ring_nf
      _ ≤ |a + m| + |m| := abs_sub _ _
  have h4 : c₁ * L ≤ c₁ * (s + L) := mul_le_mul_of_nonneg_left (by linarith) hc₁
  calc |a| ≤ c₁ * L + c₂ * (s + L) := h3.trans (add_le_add h1 h2)
    _ ≤ c₁ * (s + L) + c₂ * (s + L) := by linarith
    _ = (c₁ + c₂) * (s + L) := by ring

/-- The cell modulus along a path: the cell set lies in the ball of radius `n + √d`, so the
modulus at radius `R = n + √d` gives `C₃ log(n+2)` with `C₃ = C ε (1 + log(1 + √d))`. -/
private lemma cell_modulus_of_path {d : ℕ} (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {ε C_mod : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C_mod)
    (hmod : ∀ ε : ℝ, 0 ≤ ε → ∀ R : ℝ, 1 ≤ R →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → D ⊆ Metric.ball 0 R →
      ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R → ‖y - z‖ ≤ Real.sqrt d →
        |normPotential d ε Ψ D y - normPotential d ε Ψ D z| ≤ C_mod * ε * Real.log (R + 2))
    (X : ℕ → Site d) (n : ℕ) (hn : 2 ≤ n) (hXn : ∀ j, euclidNorm (X j) ≤ j) :
    ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * ((n : ℝ) + Real.sqrt d) →
      ‖y - z‖ ≤ Real.sqrt d →
      |normPotential d ε Ψ (cellSet X n) y - normPotential d ε Ψ (cellSet X n) z| ≤
        (C_mod * ε * (1 + Real.log (1 + Real.sqrt d))) * Real.log ((n : ℝ) + 2) := by
  intro y z hy hyz
  have hd1 : 1 ≤ d := by omega
  have hsq : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd1)
  have hball : cellSet X n ⊆ Metric.ball 0 ((n : ℝ) + Real.sqrt d) :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 X n).trans
      (Metric.ball_subset_ball (by
        linarith [CERW.Support.Norm.ContactShared.maxRadius_le_nat X n hXn]))
  have hR : (1 : ℝ) ≤ (n : ℝ) + Real.sqrt d := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1 := hmod ε hε _ hR (cellSet X n) (CERW.Support.Occupation.measurableSet_cellSet X n)
    hball y z hy hyz
  have hL1 : 1 ≤ Real.log ((n : ℝ) + 2) := CERW.Support.Law.one_le_log_add_two hn
  have hlog : Real.log ((n : ℝ) + Real.sqrt d + 2) ≤
      (1 + Real.log (1 + Real.sqrt d)) * Real.log ((n : ℝ) + 2) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2 : (n : ℝ) + Real.sqrt d + 2 ≤ (1 + Real.sqrt d) * ((n : ℝ) + 2) := by
      nlinarith
    calc Real.log ((n : ℝ) + Real.sqrt d + 2)
        ≤ Real.log ((1 + Real.sqrt d) * ((n : ℝ) + 2)) :=
          Real.log_le_log (by positivity) h2
      _ = Real.log (1 + Real.sqrt d) + Real.log ((n : ℝ) + 2) :=
          Real.log_mul (by positivity) (by positivity)
      _ ≤ (1 + Real.log (1 + Real.sqrt d)) * Real.log ((n : ℝ) + 2) := by
          have hl0 : 0 ≤ Real.log (1 + Real.sqrt d) :=
            Real.log_nonneg (by linarith)
          nlinarith
  have hCe : 0 ≤ C_mod * ε := mul_nonneg hC hε
  calc _ ≤ C_mod * ε * Real.log ((n : ℝ) + Real.sqrt d + 2) := h1
    _ ≤ C_mod * ε * ((1 + Real.log (1 + Real.sqrt d)) * Real.log ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hlog hCe
    _ = _ := by ring

/-- `lem:contact` of the paper in its probabilistic closure: for every `p` there are `C` and `n₀`
such that, for `n ≥ n₀` and with probability at least `1 - C n^{-p}`, every contact point `y₀` of
the cell set has `U_{D_n}(y₀) ≤ C r_n q_n`. The proof intersects the events of `lem:local`,
`prop:coarse` and the local martingale bound at the targets `|y| ≤ 3n`; on their intersection the
bound is deterministic (`ContactPlanar.contact_bound_two` for `d = 2`,
`ContactHigh.contact_bound_three_le` for `d ≥ 3`). -/
theorem contact_potential_of (hlocal : norm_local_time_potential.{u})
    (hcoarse : norm_coarse_bounds.{u}) (hgeom : norm_potential_geometry)
    (hball : norm_ball_potential) : contact_potential.{u} := by
  intro d hd Ψ hΨ ε hε hell r q p hp
  have hd1 : 1 ≤ d := by omega
  obtain ⟨b, h, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts hd
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  have hB : BregmanSumBound d Ψ := ContactBregman.bregmanSumBound_of hd hΨ
    (fun φ h1 h2 h3 => ContactWeakLap.inner_gradient_integral_nonpos hΨ h1 h2 h3)
    (ContactCellTest.cellTestBound hd hΨ)
  have hconv : ConvBound d Ψ ε := ContactConv.convBound hd hΨ hε hgeom hball
  obtain ⟨C_pt, hCpt, hpt⟩ :=
    ContactPointwise.exists_abs_localTime_sub_normPotential_add_driftDynkin_le.{u} hd hΨ hB hK
  obtain ⟨C_mod, hCmod, hmod⟩ := ContactModulus.exists_normPotential_cell_modulus hd hΨ
  obtain ⟨C_B, hCB, hMB⟩ := ContactDynkin.exists_drift_local_mart.{u} hd hε.le hgrad hp
  obtain ⟨c_co, C_co, hcc, hCc, hco⟩ := hcoarse hd Ψ hΨ ε hε hell p hp
  obtain ⟨C_loc, hCl, hloc⟩ := hlocal hd Ψ hΨ ε hε hell p hp
  have hC₁ : 0 ≤ C_pt * (1 + ε) + C_B := by positivity
  have hC₃ : 0 ≤ C_mod * ε * (1 + Real.log (1 + Real.sqrt d)) := by
    have : 0 ≤ Real.log (1 + Real.sqrt d) :=
      Real.log_nonneg (by linarith [Real.sqrt_nonneg (d : ℝ)])
    positivity
  have hV : 0 < normBallVolume Ψ := normBallVolume_pos' hd1 hΨ
  have hrpos : ∀ n : ℕ, 0 < n → 0 < r n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    exact Real.rpow_pos_of_pos (by positivity) _
  rcases Nat.lt_or_ge d 3 with hd3 | hd3
  · have hd2 : d = 2 := by omega
    obtain ⟨C_G, hCG, hG⟩ := ContactPlanar.contact_bound_two hd2 hΨ hε hconv
      (C_pt * (1 + ε) + C_B) C_loc (C_mod * ε * (1 + Real.log (1 + Real.sqrt d))) C_co C_co
      hC₁ hCl.le hC₃ hCc.le hCc.le
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 3 / (2 * (d : ℝ) * ε * normBallVolume Ψ) := ⟨_, rfl⟩
    have hapos : 0 < a := by
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      rw [ha]
      positivity
    have hrn : ∀ n : ℕ, r n = (a * (n : ℝ)) ^ ((1 : ℝ) / 3) := by
      intro n
      have h3 : (d : ℝ) + 1 = 3 := by
        rw [hd2]
        norm_num
      show (((d : ℝ) + 1) * n / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / ((d : ℝ) + 1)) = _
      rw [h3, ha]
      congr 1
      ring
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
      ((eventually_cube_root_scale hapos (3 * C_co) (6 * Real.sqrt d)).and
        (eventually_ge_atTop 2))
    refine ⟨max (C_co + C_loc + C_B) (2 * C_G), lt_max_of_lt_left (by positivity), n₀, ?_⟩
    intro ξ hξ hξ0 Ω _ μ _ X hX n hn
    obtain ⟨⟨hr1, hrlog, hrlarge⟩, hn2⟩ := hn₀ n hn
    have hξ' := drift_coord_le hΨ hε hell hξ hξ0
    have hpath : ∀ᵐ ω ∂μ, X 0 ω = 0 ∧ ∀ j, euclidNorm (X j ω) ≤ j := by
      have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
        rw [ae_iff]
        exact hX.start
      filter_upwards [h0, CERW.Support.Drift.ae_euclidNorm_le_drift hd1 hε.le hξ' hX] with
        ω h0 h1
      exact ⟨h0, h1⟩
    have hN := ae_iff.mp hpath
    have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    refine measure_le_of_subset_union_three ?_ (hco ξ hξ hξ0 μ X hX n hn2)
      (hMB hξ' hX n hn2) (hloc ξ hξ hξ0 μ X hX n hn2) hN (by positivity) (by positivity)
      (by positivity) ?_
    · intro ω hω
      by_contra hnot
      simp only [Set.mem_union, not_or] at hnot
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hnot
      have hpathω : X 0 ω = 0 ∧ ∀ j, euclidNorm (X j ω) ≤ j := by
        by_contra hc
        exact h4 hc
      have hconj := not_not.mp h1
      obtain ⟨-, -, -, hM, -, hRad⟩ := hconj
      have hlocω := not_not.mp h3
      have hMBω : ∀ y : Site d, euclidNorm y ≤ 3 * n →
          |CERW.Support.Drift.driftDynkin ε ξ (fun z => b (z - y)) X n ω| ≤
            C_B * (Real.sqrt ((∑ j ∈ Finset.range n,
              (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log (n + 2)) +
                Real.log (n + 2)) := by
        intro y hy
        by_contra hc
        exact h2 ⟨y, hy, not_le.mp hc⟩
      have hfine : ∀ y : Site d, euclidNorm y ≤ 3 * n →
          |(localTime (fun j => X j ω) n y : ℝ) -
              normPotential d ε Ψ (cellSet (fun j => X j ω) n) (toSpace y)| ≤
            (C_pt * (1 + ε) + C_B) * (Real.sqrt ((∑ j ∈ Finset.range n,
              (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
                Real.log ((n : ℝ) + 2)) := fun y hy =>
        abs_le_add_of_abs_add_le (by positivity) (Real.sqrt_nonneg _)
          (hpt ε hε.le ξ hξ hξ0 X ω hpathω.1 hpathω.2 n (by omega) y hy) (hMBω y hy)
      have hcrude : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ ≤ 2 * n →
          |cellLocalTime (fun j => X j ω) n v -
              normPotential d ε Ψ (cellSet (fun j => X j ω) n) v| ≤
            C_loc * Real.log n + C_loc *
              (Real.sqrt (maxLocalTime (fun j => X j ω) n) * Real.log n) := by
        intro v hv
        have := hlocω.2.2 v hv
        rwa [if_pos hd2] at this
      have hmodω := cell_modulus_of_path hd hε.le hCmod hmod (fun j => X j ω) n hn2 hpathω.2
      have hr1' : 1 ≤ r n := by
        rw [hrn n]
        exact hr1
      have hrlog' : Real.log ((n : ℝ) + 2) ^ 4 ≤ r n := by
        rw [hrn n]
        exact hrlog
      have hlarge : 3 * C_co * r n + 6 * Real.sqrt d ≤ n := by
        rw [hrn n]
        exact hrlarge
      have hU := hG (fun j => X j ω) n (r n) hn2 hpathω.1 hpathω.2 hr1' hrlog' hlarge hM hRad
        hfine hcrude hmodω
      simp only [Set.mem_setOf_eq] at hω
      apply hω
      intro y₀ hy₀ hcl
      have hr := hrpos n (by omega)
      have hqn : q n = Real.sqrt (Real.log n / r n) := by
        show (if d = 2 then _ else _) = _
        rw [if_pos hd2]
      rw [hqn]
      have hlogn := log_pos_of_two_le hn2
      have hL := log_add_two_le hn2
      have hsq : Real.sqrt (r n * Real.log ((n : ℝ) + 2)) ≤ 2 * Real.sqrt (r n * Real.log n) := by
        have h4 : r n * Real.log ((n : ℝ) + 2) ≤ 2 ^ 2 * (r n * Real.log n) := by
          have : r n * Real.log ((n : ℝ) + 2) ≤ r n * (2 * Real.log n) :=
            mul_le_mul_of_nonneg_left hL hr.le
          nlinarith [mul_nonneg hr.le hlogn.le]
        calc Real.sqrt (r n * Real.log ((n : ℝ) + 2))
            ≤ Real.sqrt (2 ^ 2 * (r n * Real.log n)) := Real.sqrt_le_sqrt h4
          _ = 2 * Real.sqrt (r n * Real.log n) := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      have hsn : 0 ≤ Real.sqrt (r n * Real.log n) := Real.sqrt_nonneg _
      calc normPotential d ε Ψ (cellSet (fun j => X j ω) n) y₀
          ≤ C_G * Real.sqrt (r n * Real.log ((n : ℝ) + 2)) := hU y₀ hy₀ hcl
        _ ≤ C_G * (2 * Real.sqrt (r n * Real.log n)) := mul_le_mul_of_nonneg_left hsq hCG.le
        _ = 2 * C_G * Real.sqrt (r n * Real.log n) := by ring
        _ ≤ max (C_co + C_loc + C_B) (2 * C_G) * Real.sqrt (r n * Real.log n) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hsn
        _ = max (C_co + C_loc + C_B) (2 * C_G) * r n * Real.sqrt (Real.log n / r n) := by
            rw [mul_assoc, mul_sqrt_div_eq hr]
    · calc C_co * (n : ℝ) ^ (-p) + C_B * (n : ℝ) ^ (-p) + C_loc * (n : ℝ) ^ (-p)
          = (C_co + C_loc + C_B) * (n : ℝ) ^ (-p) := by ring
        _ ≤ max (C_co + C_loc + C_B) (2 * C_G) * (n : ℝ) ^ (-p) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hnp
  · obtain ⟨C_H, hCH, hH⟩ := ContactHigh.contact_bound_three_le hd3 hΨ hε hconv
      (C_pt * (1 + ε) + C_B) (C_mod * ε * (1 + Real.log (1 + Real.sqrt d))) hC₁ hC₃
    obtain ⟨n₁, hn₁⟩ := exists_nat_ge (4 * Real.sqrt d)
    refine ⟨max (C_co + C_loc + C_B) (2 * C_H), lt_max_of_lt_left (by positivity),
      max n₁ 2, ?_⟩
    intro ξ hξ hξ0 Ω _ μ _ X hX n hn
    have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
    have hn4 : 4 * Real.sqrt d ≤ n :=
      hn₁.trans (by exact_mod_cast (le_max_left _ _).trans hn)
    have hξ' := drift_coord_le hΨ hε hell hξ hξ0
    have hpath : ∀ᵐ ω ∂μ, X 0 ω = 0 ∧ ∀ j, euclidNorm (X j ω) ≤ j := by
      have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
        rw [ae_iff]
        exact hX.start
      filter_upwards [h0, CERW.Support.Drift.ae_euclidNorm_le_drift hd1 hε.le hξ' hX] with
        ω h0 h1
      exact ⟨h0, h1⟩
    have hN := ae_iff.mp hpath
    have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    refine measure_le_of_subset_union_three ?_ (hco ξ hξ hξ0 μ X hX n hn2)
      (hMB hξ' hX n hn2) (hloc ξ hξ hξ0 μ X hX n hn2) hN (by positivity) (by positivity)
      (by positivity) ?_
    · intro ω hω
      by_contra hnot
      simp only [Set.mem_union, not_or] at hnot
      obtain ⟨⟨⟨_, h2⟩, _⟩, h4⟩ := hnot
      have hpathω : X 0 ω = 0 ∧ ∀ j, euclidNorm (X j ω) ≤ j := by
        by_contra hc
        exact h4 hc
      have hMBω : ∀ y : Site d, euclidNorm y ≤ 3 * n →
          |CERW.Support.Drift.driftDynkin ε ξ (fun z => b (z - y)) X n ω| ≤
            C_B * (Real.sqrt ((∑ j ∈ Finset.range n,
              (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log (n + 2)) +
                Real.log (n + 2)) := by
        intro y hy
        by_contra hc
        exact h2 ⟨y, hy, not_le.mp hc⟩
      have hfine : ∀ y : Site d, euclidNorm y ≤ 3 * n →
          |(localTime (fun j => X j ω) n y : ℝ) -
              normPotential d ε Ψ (cellSet (fun j => X j ω) n) (toSpace y)| ≤
            (C_pt * (1 + ε) + C_B) * (Real.sqrt ((∑ j ∈ Finset.range n,
              (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
                Real.log ((n : ℝ) + 2)) := fun y hy =>
        abs_le_add_of_abs_add_le (by positivity) (Real.sqrt_nonneg _)
          (hpt ε hε.le ξ hξ hξ0 X ω hpathω.1 hpathω.2 n (by omega) y hy) (hMBω y hy)
      have hmodω := cell_modulus_of_path hd hε.le hCmod hmod (fun j => X j ω) n hn2 hpathω.2
      have hU := hH (fun j => X j ω) n hn2 hn4 hpathω.1 hpathω.2 hfine hmodω
      simp only [Set.mem_setOf_eq] at hω
      apply hω
      intro y₀ hy₀ hcl
      have hr := hrpos n (by omega)
      have hqn : q n = Real.log n / r n := by
        show (if d = 2 then _ else _) = _
        rw [if_neg (by omega)]
      rw [hqn]
      have hlogn := log_pos_of_two_le hn2
      have hL := log_add_two_le hn2
      calc normPotential d ε Ψ (cellSet (fun j => X j ω) n) y₀
          ≤ C_H * Real.log ((n : ℝ) + 2) := hU y₀ hy₀ hcl
        _ ≤ C_H * (2 * Real.log n) := mul_le_mul_of_nonneg_left hL hCH.le
        _ = 2 * C_H * Real.log n := by ring
        _ ≤ max (C_co + C_loc + C_B) (2 * C_H) * Real.log n :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hlogn.le
        _ = max (C_co + C_loc + C_B) (2 * C_H) * r n * (Real.log n / r n) := by
            field_simp
    · calc C_co * (n : ℝ) ^ (-p) + C_B * (n : ℝ) ^ (-p) + C_loc * (n : ℝ) ^ (-p)
          = (C_co + C_loc + C_B) * (n : ℝ) ^ (-p) := by ring
        _ ≤ max (C_co + C_loc + C_B) (2 * C_H) * (n : ℝ) ^ (-p) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hnp

end CERW.Support.Norm
