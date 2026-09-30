import CERW.Model
import CERW.Generic.Norm

/-!
# The Moreau envelope of a norm and the cap lemma

For a norm `Ψ` on `ℝ^d` and `τ > 0` the function `w ↦ Ψ w + |x - w|²/(2τ)` has a unique
minimizer `z_x` (`sec:moreau`). Its first-order condition says that `p_x = (x - z_x)/τ` is a
subgradient of `Ψ` at `z_x`. Evaluating the minimized function at `z_x` gives the upper Taylor
bound `F_τ(x + h) - F_τ(x) ≤ p_x · h + |h|²/(2τ)`, and a subgradient inequality for `p_x` shows
that `F_τ(v) ≥ F_τ(x) + p_x · (v - x)`. Together these make `F_τ` differentiable with
`∇F_τ(x) = p_x`, so `z_x = x - τ ∇F_τ(x)`; they also give the comparison
`Ψ - τ Λ_Ψ²/2 ≤ F_τ ≤ min {Ψ, ∇F_τ · x}`. Lemma `lem:cap` (`moreau_cap`) then compares the
gradients of `F_τ` at two points through the tangent-plane excess of `F_τ`.
-/

open Filter Topology

namespace CERW.Support.Norm

section MoreauEnvelope

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} {τ : ℝ}

/-- `z` minimizes `w ↦ Ψ w + |x - w|²/(2τ)`, the function whose minimum is `F_τ(x)`. -/
def IsMoreauMinimizer (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (τ : ℝ)
    (x z : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ w, Ψ z + ‖x - z‖ ^ 2 / (2 * τ) ≤ Ψ w + ‖x - w‖ ^ 2 / (2 * τ)

/-- The function minimized in `F_τ(x)` is bounded below (by zero). -/
private lemma bddBelow_moreau (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ) (x : EuclideanSpace ℝ (Fin d)) :
    BddBelow (Set.range fun z => Ψ z + ‖x - z‖ ^ 2 / (2 * τ)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact add_nonneg ((CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 z) (by positivity)

/-- The function `w ↦ Ψ w + |x - w|²/(2τ)` has a minimizer. -/
theorem exists_isMoreauMinimizer (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    (x : EuclideanSpace ℝ (Fin d)) : ∃ z, IsMoreauMinimizer Ψ τ x z := by
  have hcont : Continuous fun z : EuclideanSpace ℝ (Fin d) => Ψ z + ‖x - z‖ ^ 2 / (2 * τ) :=
    (CERW.Generic.Norm.norm_continuous hΨ).add (by fun_prop)
  have h1 : Tendsto (fun z : EuclideanSpace ℝ (Fin d) => ‖x - z‖) (cocompact _) atTop :=
    tendsto_norm_cocompact_atTop.comp (Homeomorph.subLeft x).isClosedEmbedding.tendsto_cocompact
  have h2 : Tendsto (fun z : EuclideanSpace ℝ (Fin d) => ‖x - z‖ ^ 2 / (2 * τ))
      (cocompact _) atTop :=
    Tendsto.atTop_div_const (by positivity) ((tendsto_pow_atTop two_ne_zero).comp h1)
  have hlim : Tendsto (fun z : EuclideanSpace ℝ (Fin d) => Ψ z + ‖x - z‖ ^ 2 / (2 * τ))
      (cocompact _) atTop :=
    tendsto_atTop_mono (fun z => le_add_of_nonneg_left
      ((CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 z)) h2
  obtain ⟨z, hz⟩ := hcont.exists_forall_le hlim
  exact ⟨z, hz⟩

/-- The function minimized in `F_τ(x)` dominates `F_τ(x)`. -/
theorem moreauEnvelope_le (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ) (x w : EuclideanSpace ℝ (Fin d)) :
    CERW.moreauEnvelope Ψ τ x ≤ Ψ w + ‖x - w‖ ^ 2 / (2 * τ) :=
  ciInf_le (bddBelow_moreau hΨ hτ x) w

/-- A lower bound on the function minimized in `F_τ(x)` is a lower bound for `F_τ(x)`. -/
theorem le_moreauEnvelope {x : EuclideanSpace ℝ (Fin d)} {c : ℝ}
    (h : ∀ w, c ≤ Ψ w + ‖x - w‖ ^ 2 / (2 * τ)) : c ≤ CERW.moreauEnvelope Ψ τ x :=
  le_ciInf h

/-- At a minimizer `z`, `F_τ(x) = Ψ(z) + |x - z|²/(2τ)`. -/
theorem moreauEnvelope_eq (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ) {x z : EuclideanSpace ℝ (Fin d)}
    (hz : IsMoreauMinimizer Ψ τ x z) :
    CERW.moreauEnvelope Ψ τ x = Ψ z + ‖x - z‖ ^ 2 / (2 * τ) :=
  le_antisymm (moreauEnvelope_le hΨ hτ x z) (le_moreauEnvelope hz)

/-- A real `A` with `A ≤ B + t K` for all `t ∈ (0, 1]` satisfies `A ≤ B` when `K ≥ 0`. -/
private lemma le_of_forall_le_add_mul {A B K : ℝ} (hK : 0 ≤ K)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → A ≤ B + t * K) : A ≤ B := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hK1 : 0 < K + 1 := by linarith
  have ht : 0 < min 1 (ε / (K + 1)) := lt_min one_pos (div_pos hε hK1)
  have hle : min 1 (ε / (K + 1)) * K ≤ ε :=
    calc min 1 (ε / (K + 1)) * K ≤ ε / (K + 1) * K :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hK
      _ = ε * K / (K + 1) := by rw [div_mul_eq_mul_div]
      _ ≤ ε := by
          rw [div_le_iff₀ hK1]
          exact mul_le_mul_of_nonneg_left (by linarith) hε.le
  have := h _ ht (min_le_left _ _)
  linarith

/-- First-order condition: at a minimizer `z` of `w ↦ Ψ w + |x - w|²/(2τ)`, the vector
`(x - z)/τ` is a subgradient of `Ψ` at `z`. -/
theorem isSubgradient_of_isMoreauMinimizer (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    {x z : EuclideanSpace ℝ (Fin d)} (hz : IsMoreauMinimizer Ψ τ x z) :
    CERW.IsSubgradient Ψ z (τ⁻¹ • (x - z)) := by
  intro y
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      Ψ z + inner ℝ (τ⁻¹ • (x - z)) (y - z) ≤ Ψ y + t * (‖y - z‖ ^ 2 / (2 * τ)) := by
    intro t ht0 ht1
    have h1 := hz (z + t • (y - z))
    have h2 : Ψ (z + t • (y - z)) ≤ (1 - t) * Ψ z + t * Ψ y := by
      have e : z + t • (y - z) = (1 - t) • z + t • y := by module
      rw [e]
      calc Ψ ((1 - t) • z + t • y) ≤ Ψ ((1 - t) • z) + Ψ (t • y) := hΨ.add_le _ _
        _ = (1 - t) * Ψ z + t * Ψ y := by
            rw [hΨ.smul, hΨ.smul, abs_of_nonneg (by linarith), abs_of_nonneg ht0.le]
    have h3 : ‖x - (z + t • (y - z))‖ ^ 2
        = ‖x - z‖ ^ 2 - 2 * (t * inner ℝ (x - z) (y - z)) + t ^ 2 * ‖y - z‖ ^ 2 := by
      have e : x - (z + t • (y - z)) = (x - z) - t • (y - z) := by abel
      rw [e, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht0.le, mul_pow]
    rw [h3] at h1
    rw [real_inner_smul_left]
    have h4 : (‖x - z‖ ^ 2 - 2 * (t * inner ℝ (x - z) (y - z)) + t ^ 2 * ‖y - z‖ ^ 2) /
        (2 * τ) = ‖x - z‖ ^ 2 / (2 * τ) - t * (τ⁻¹ * inner ℝ (x - z) (y - z))
          + t ^ 2 * (‖y - z‖ ^ 2 / (2 * τ)) := by
      field_simp
    rw [h4] at h1
    have h5 : t * (Ψ z + τ⁻¹ * inner ℝ (x - z) (y - z))
        ≤ t * (Ψ y + t * (‖y - z‖ ^ 2 / (2 * τ))) := by nlinarith
    exact le_of_mul_le_mul_left h5 ht0
  exact le_of_forall_le_add_mul (by positivity) key


/-- Quadratic growth at a point `z` whose vector `(x - z)/τ` is a subgradient of `Ψ`:
`Ψ z + |x - z|²/(2τ) + |w - z|²/(2τ) ≤ Ψ w + |x - w|²/(2τ)` for every `w`. -/
private lemma moreau_growth (hτ : 0 < τ) {x z : EuclideanSpace ℝ (Fin d)}
    (h : CERW.IsSubgradient Ψ z (τ⁻¹ • (x - z))) (w : EuclideanSpace ℝ (Fin d)) :
    Ψ z + ‖x - z‖ ^ 2 / (2 * τ) + ‖w - z‖ ^ 2 / (2 * τ) ≤ Ψ w + ‖x - w‖ ^ 2 / (2 * τ) := by
  have h1 := h w
  rw [real_inner_smul_left] at h1
  have e : x - w = (x - z) - (w - z) := by abel
  have h2 : ‖x - w‖ ^ 2 / (2 * τ) = ‖x - z‖ ^ 2 / (2 * τ) - τ⁻¹ * inner ℝ (x - z) (w - z)
      + ‖w - z‖ ^ 2 / (2 * τ) := by
    rw [e, norm_sub_sq_real]
    field_simp
  linarith

/-- Conversely, if `(x - z)/τ` is a subgradient of `Ψ` at `z`, then `z` minimizes
`w ↦ Ψ w + |x - w|²/(2τ)`. -/
theorem isMoreauMinimizer_of_isSubgradient (hτ : 0 < τ) {x z : EuclideanSpace ℝ (Fin d)}
    (h : CERW.IsSubgradient Ψ z (τ⁻¹ • (x - z))) : IsMoreauMinimizer Ψ τ x z := by
  intro w
  have := moreau_growth hτ h w
  have h0 : 0 ≤ ‖w - z‖ ^ 2 / (2 * τ) := by positivity
  linarith

/-- The minimizer of `w ↦ Ψ w + |x - w|²/(2τ)` is unique. -/
theorem IsMoreauMinimizer.eq (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    {x z z' : EuclideanSpace ℝ (Fin d)} (hz : IsMoreauMinimizer Ψ τ x z)
    (hz' : IsMoreauMinimizer Ψ τ x z') : z' = z := by
  have h1 := moreau_growth hτ (isSubgradient_of_isMoreauMinimizer hΨ hτ hz) z'
  have h2 := hz' z
  have h3 : ‖z' - z‖ ^ 2 / (2 * τ) ≤ 0 := by linarith
  have h4 : ‖z' - z‖ ^ 2 ≤ 0 := by
    have := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 2 * τ)
    rwa [div_mul_cancel₀ _ (by positivity), zero_mul] at this
  have h5 : ‖z' - z‖ = 0 := by nlinarith [norm_nonneg (z' - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h5)

/-- The function `w ↦ Ψ w + |x - w|²/(2τ)` has exactly one minimizer `z_x`. -/
theorem existsUnique_isMoreauMinimizer (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    (x : EuclideanSpace ℝ (Fin d)) : ∃! z, IsMoreauMinimizer Ψ τ x z := by
  obtain ⟨z, hz⟩ := exists_isMoreauMinimizer hΨ hτ x
  exact ⟨z, hz, fun z' hz' => hz.eq hΨ hτ hz'⟩


/-- Upper Taylor bound at a minimizer `z`:
`F_τ(x + h) - F_τ(x) ≤ ((x - z)/τ) · h + |h|²/(2τ)`. -/
private lemma taylor_upper_of_isMoreauMinimizer (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    {x z : EuclideanSpace ℝ (Fin d)} (hz : IsMoreauMinimizer Ψ τ x z)
    (h : EuclideanSpace ℝ (Fin d)) :
    CERW.moreauEnvelope Ψ τ (x + h) - CERW.moreauEnvelope Ψ τ x
      ≤ inner ℝ (τ⁻¹ • (x - z)) h + ‖h‖ ^ 2 / (2 * τ) := by
  have h1 := moreauEnvelope_le hΨ hτ (x + h) z
  have h2 := moreauEnvelope_eq hΨ hτ hz
  have e : x + h - z = (x - z) + h := by abel
  have h3 : ‖x + h - z‖ ^ 2 / (2 * τ) = ‖x - z‖ ^ 2 / (2 * τ) + τ⁻¹ * inner ℝ (x - z) h
      + ‖h‖ ^ 2 / (2 * τ) := by
    rw [e, norm_add_sq_real]
    field_simp
  rw [real_inner_smul_left]
  linarith

/-- Lower bound at a minimizer `z`: `F_τ(x) + ((x - z)/τ) · (v - x) ≤ F_τ(v)`. -/
private lemma taylor_lower_of_isMoreauMinimizer (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    {x z : EuclideanSpace ℝ (Fin d)} (hz : IsMoreauMinimizer Ψ τ x z)
    (v : EuclideanSpace ℝ (Fin d)) :
    CERW.moreauEnvelope Ψ τ x + inner ℝ (τ⁻¹ • (x - z)) (v - x) ≤ CERW.moreauEnvelope Ψ τ v := by
  refine le_moreauEnvelope fun w => ?_
  have hsub := isSubgradient_of_isMoreauMinimizer hΨ hτ hz
  have h1 := hsub w
  have h2 := moreauEnvelope_eq hΨ hτ hz
  have e : v - w = (x - z) + ((v - x) - (w - z)) := by abel
  have h3 : ‖v - w‖ ^ 2 / (2 * τ) = ‖x - z‖ ^ 2 / (2 * τ)
      + τ⁻¹ * (inner ℝ (x - z) (v - x) - inner ℝ (x - z) (w - z))
      + ‖(v - x) - (w - z)‖ ^ 2 / (2 * τ) := by
    rw [e, norm_add_sq_real, inner_sub_right]
    field_simp
  rw [real_inner_smul_left] at h1 ⊢
  have h4 : 0 ≤ ‖(v - x) - (w - z)‖ ^ 2 / (2 * τ) := by positivity
  have h5 : τ⁻¹ * (inner ℝ (x - z) (v - x) - inner ℝ (x - z) (w - z))
      = τ⁻¹ * inner ℝ (x - z) (v - x) - τ⁻¹ * inner ℝ (x - z) (w - z) := by ring
  linarith


/-- The Moreau envelope `F_τ` has gradient `(x - z)/τ` at `x`, where `z` is the minimizer
`z_x`: this is `∇F_τ(x) = p_x`. -/
theorem hasGradientAt_moreauEnvelope (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    {x z : EuclideanSpace ℝ (Fin d)} (hz : IsMoreauMinimizer Ψ τ x z) :
    HasGradientAt (CERW.moreauEnvelope Ψ τ) (τ⁻¹ • (x - z)) x := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero,
    Asymptotics.isLittleO_iff]
  intro c hc
  have hδ : 0 < 2 * τ * c := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin d)) hδ] with h hh
  rw [mem_ball_zero_iff] at hh
  have hup := taylor_upper_of_isMoreauMinimizer hΨ hτ hz h
  have hlow := taylor_lower_of_isMoreauMinimizer hΨ hτ hz (x + h)
  rw [add_sub_cancel_left] at hlow
  have hdual : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))) (τ⁻¹ • (x - z)) h
      = inner ℝ (τ⁻¹ • (x - z)) h := InnerProductSpace.toDual_apply_apply ..
  rw [hdual]
  have hr0 : 0 ≤ CERW.moreauEnvelope Ψ τ (x + h) - CERW.moreauEnvelope Ψ τ x
      - inner ℝ (τ⁻¹ • (x - z)) h := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hq : ‖h‖ ^ 2 / (2 * τ) ≤ c * ‖h‖ := by
    rw [div_le_iff₀ (by positivity)]
    calc ‖h‖ ^ 2 = ‖h‖ * ‖h‖ := sq ‖h‖
      _ ≤ ‖h‖ * (2 * τ * c) := mul_le_mul_of_nonneg_left hh.le (norm_nonneg h)
      _ = c * ‖h‖ * (2 * τ) := by ring
  linarith

/-- The gradient of the Moreau envelope at `x` is `(x - z)/τ`, for the minimizer `z = z_x`. -/
theorem gradient_moreauEnvelope_of_isMoreauMinimizer (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    {x z : EuclideanSpace ℝ (Fin d)} (hz : IsMoreauMinimizer Ψ τ x z) :
    gradient (CERW.moreauEnvelope Ψ τ) x = τ⁻¹ • (x - z) :=
  (hasGradientAt_moreauEnvelope hΨ hτ hz).gradient

/-- The Moreau envelope `F_τ` is differentiable. -/
theorem differentiableAt_moreauEnvelope (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    (x : EuclideanSpace ℝ (Fin d)) : DifferentiableAt ℝ (CERW.moreauEnvelope Ψ τ) x := by
  obtain ⟨z, hz⟩ := exists_isMoreauMinimizer hΨ hτ x
  exact (hasGradientAt_moreauEnvelope hΨ hτ hz).differentiableAt


/-- The minimizer `z_x` is `x - τ ∇F_τ(x)`, i.e. `p_x = (x - z_x)/τ` is the gradient. -/
theorem eq_sub_smul_gradient_moreauEnvelope (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    {x z : EuclideanSpace ℝ (Fin d)} (hz : IsMoreauMinimizer Ψ τ x z) :
    z = x - τ • gradient (CERW.moreauEnvelope Ψ τ) x := by
  rw [gradient_moreauEnvelope_of_isMoreauMinimizer hΨ hτ hz, smul_inv_smul₀ hτ.ne']
  abel

/-- `x - τ ∇F_τ(x)` is the minimizer `z_x` of `w ↦ Ψ w + |x - w|²/(2τ)`. -/
theorem isMoreauMinimizer_sub_smul_gradient (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    (x : EuclideanSpace ℝ (Fin d)) :
    IsMoreauMinimizer Ψ τ x (x - τ • gradient (CERW.moreauEnvelope Ψ τ) x) := by
  obtain ⟨z, hz⟩ := exists_isMoreauMinimizer hΨ hτ x
  rwa [← eq_sub_smul_gradient_moreauEnvelope hΨ hτ hz]

/-- The gradient `p_x = ∇F_τ(x)` of the Moreau envelope is a subgradient of `Ψ` at
`z_x = x - τ p_x`. -/
theorem isSubgradient_gradient_moreauEnvelope (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    (x : EuclideanSpace ℝ (Fin d)) :
    CERW.IsSubgradient Ψ (x - τ • gradient (CERW.moreauEnvelope Ψ τ) x)
      (gradient (CERW.moreauEnvelope Ψ τ) x) := by
  obtain ⟨z, hz⟩ := exists_isMoreauMinimizer hΨ hτ x
  have h := isSubgradient_of_isMoreauMinimizer hΨ hτ hz
  rw [← gradient_moreauEnvelope_of_isMoreauMinimizer hΨ hτ hz] at h
  rwa [← eq_sub_smul_gradient_moreauEnvelope hΨ hτ hz]

/-- Upper Taylor bound (`eq:moreau-taylor`, right inequality):
`F_τ(x + h) - F_τ(x) ≤ ∇F_τ(x) · h + |h|²/(2τ)`. -/
theorem moreauEnvelope_taylor_upper (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    (x h : EuclideanSpace ℝ (Fin d)) :
    CERW.moreauEnvelope Ψ τ (x + h) - CERW.moreauEnvelope Ψ τ x
      ≤ inner ℝ (gradient (CERW.moreauEnvelope Ψ τ) x) h + ‖h‖ ^ 2 / (2 * τ) := by
  obtain ⟨z, hz⟩ := exists_isMoreauMinimizer hΨ hτ x
  rw [gradient_moreauEnvelope_of_isMoreauMinimizer hΨ hτ hz]
  exact taylor_upper_of_isMoreauMinimizer hΨ hτ hz h

/-- Lower Taylor bound (`eq:moreau-taylor`, left inequality):
`∇F_τ(x + h) · h - |h|²/(2τ) ≤ F_τ(x + h) - F_τ(x)`. -/
theorem moreauEnvelope_taylor_lower (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    (x h : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (gradient (CERW.moreauEnvelope Ψ τ) (x + h)) h - ‖h‖ ^ 2 / (2 * τ)
      ≤ CERW.moreauEnvelope Ψ τ (x + h) - CERW.moreauEnvelope Ψ τ x := by
  have := moreauEnvelope_taylor_upper hΨ hτ (x + h) (-h)
  rw [add_neg_cancel_right, inner_neg_right, norm_neg] at this
  linarith

/-- `∇F_τ(x)` is a subgradient of the convex function `F_τ` at `x`:
`F_τ(x) + ∇F_τ(x) · (v - x) ≤ F_τ(v)`. -/
theorem moreauEnvelope_ge_linear (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    (x v : EuclideanSpace ℝ (Fin d)) :
    CERW.moreauEnvelope Ψ τ x + inner ℝ (gradient (CERW.moreauEnvelope Ψ τ) x) (v - x)
      ≤ CERW.moreauEnvelope Ψ τ v := by
  obtain ⟨z, hz⟩ := exists_isMoreauMinimizer hΨ hτ x
  rw [gradient_moreauEnvelope_of_isMoreauMinimizer hΨ hτ hz]
  exact taylor_lower_of_isMoreauMinimizer hΨ hτ hz v

/-- A subgradient `ξ` of a norm `Ψ` satisfies `|ξ| ≤ Λ_Ψ`. -/
theorem norm_le_normMax_of_isSubgradient (hΨ : CERW.IsNorm Ψ) {x ξ : EuclideanSpace ℝ (Fin d)}
    (h : CERW.IsSubgradient Ψ x ξ) : ‖ξ‖ ≤ CERW.normMax Ψ := by
  have h0 : 0 ≤ CERW.normMax Ψ := by
    refine Real.sSup_nonneg ?_
    rintro _ ⟨u, -, rfl⟩
    exact (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 u
  have h1 := (CERW.Generic.Norm.subgradient_euler hΨ h).2 ξ
  have h2 := CERW.Generic.Norm.le_normMax_mul hΨ ξ
  rw [real_inner_self_eq_norm_sq] at h1
  by_contra hnot
  have hlt := not_le.mp hnot
  have h3 := mul_lt_mul_of_pos_right hlt (lt_of_le_of_lt h0 hlt)
  have h4 : ‖ξ‖ * ‖ξ‖ = ‖ξ‖ ^ 2 := (sq ‖ξ‖).symm
  linarith


/-- The comparison `eq:moreau-comparison`:
`Ψ(x) - τ Λ_Ψ²/2 ≤ F_τ(x) ≤ min {Ψ(x), ∇F_τ(x) · x}`. -/
theorem moreauEnvelope_comparison (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Ψ x - τ * CERW.normMax Ψ ^ 2 / 2 ≤ CERW.moreauEnvelope Ψ τ x ∧
      CERW.moreauEnvelope Ψ τ x
        ≤ min (Ψ x) (inner ℝ (gradient (CERW.moreauEnvelope Ψ τ) x) x) := by
  refine ⟨?_, le_min ?_ ?_⟩
  · refine le_moreauEnvelope fun w => ?_
    have h1 : Ψ x - CERW.normMax Ψ * ‖x - w‖ ≤ Ψ w := by
      have h2 := CERW.Generic.Norm.abs_sub_le hΨ x w
      have h3 := CERW.Generic.Norm.le_normMax_mul hΨ (x - w)
      have h4 := (abs_le.mp h2).2
      linarith
    have h5 : (‖x - w‖ - τ * CERW.normMax Ψ) ^ 2 / (2 * τ)
        = ‖x - w‖ ^ 2 / (2 * τ) - CERW.normMax Ψ * ‖x - w‖ + τ * CERW.normMax Ψ ^ 2 / 2 := by
      field_simp
      ring
    have h6 : 0 ≤ (‖x - w‖ - τ * CERW.normMax Ψ) ^ 2 / (2 * τ) := by positivity
    linarith
  · have := moreauEnvelope_le hΨ hτ x x
    rwa [sub_self, norm_zero, zero_pow two_ne_zero, zero_div, add_zero] at this
  · set p := gradient (CERW.moreauEnvelope Ψ τ) x with hp
    set z := x - τ • p with hzdef
    have hz : IsMoreauMinimizer Ψ τ x z := isMoreauMinimizer_sub_smul_gradient hΨ hτ x
    have hsub : CERW.IsSubgradient Ψ z p := isSubgradient_gradient_moreauEnvelope hΨ hτ x
    have heuler := (CERW.Generic.Norm.subgradient_euler hΨ hsub).1
    have hxz : x - z = τ • p := by rw [hzdef]; abel
    have hx : x = z + τ • p := by rw [hzdef]; abel
    have h1 := moreauEnvelope_eq hΨ hτ hz
    have h2 : ‖x - z‖ ^ 2 / (2 * τ) = τ * ‖p‖ ^ 2 / 2 := by
      rw [hxz, norm_smul, Real.norm_eq_abs, abs_of_pos hτ, mul_pow]
      field_simp
    have h3 : inner ℝ p x = Ψ z + τ * ‖p‖ ^ 2 := by
      conv_lhs => rw [hx]
      rw [inner_add_right, heuler, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have h4 : 0 ≤ τ * ‖p‖ ^ 2 := by positivity
    linarith


/-- Between two points, the gradient of the Moreau envelope moves by at most the excess over
the tangent plane: `(τ/2) |∇F_τ(y) - ∇F_τ(x)|² ≤ F_τ(y) - F_τ(x) - ∇F_τ(x) · (y - x)`. -/
private lemma gradient_moreauEnvelope_dist_sq_le (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    τ / 2 * ‖gradient (CERW.moreauEnvelope Ψ τ) y - gradient (CERW.moreauEnvelope Ψ τ) x‖ ^ 2
      ≤ CERW.moreauEnvelope Ψ τ y - CERW.moreauEnvelope Ψ τ x
        - inner ℝ (gradient (CERW.moreauEnvelope Ψ τ) x) (y - x) := by
  set q := gradient (CERW.moreauEnvelope Ψ τ) x with hq
  set p := gradient (CERW.moreauEnvelope Ψ τ) y with hp
  set h : EuclideanSpace ℝ (Fin d) := -(τ • (p - q)) with hh
  have h1 := moreauEnvelope_ge_linear hΨ hτ x (y + h)
  have h2 := moreauEnvelope_taylor_upper hΨ hτ y h
  have h3 : inner ℝ q (y + h - x) = inner ℝ q (y - x) + inner ℝ q h := by
    rw [← inner_add_right]
    congr 1
    abel
  have h4 : inner ℝ p h - inner ℝ q h = -(τ * ‖p - q‖ ^ 2) := by
    rw [← inner_sub_left, hh, inner_neg_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
  have h5 : ‖h‖ ^ 2 / (2 * τ) = τ / 2 * ‖p - q‖ ^ 2 := by
    rw [hh, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hτ, mul_pow]
    field_simp
  linarith

/-- Monotonicity of the subdifferential: if `ξ` is a subgradient of `Ψ` at `y`, `p` one at
`z`, and `y - z = τ p`, then `|p|² ≤ ξ · p`. -/
private lemma norm_sq_le_inner_of_isSubgradient (hΨ : CERW.IsNorm Ψ) (hτ : 0 < τ)
    {y z ξ p : EuclideanSpace ℝ (Fin d)} (hξ : CERW.IsSubgradient Ψ y ξ)
    (hp : CERW.IsSubgradient Ψ z p) (hyz : y - z = τ • p) : ‖p‖ ^ 2 ≤ inner ℝ ξ p := by
  obtain ⟨hξy, hξw⟩ := CERW.Generic.Norm.subgradient_euler hΨ hξ
  obtain ⟨hpz, hpw⟩ := CERW.Generic.Norm.subgradient_euler hΨ hp
  have h1 := hpw y
  have h2 := hξw z
  have h3 : inner ℝ ξ (y - z) = inner ℝ ξ y - inner ℝ ξ z := inner_sub_right _ _ _
  have h4 : inner ℝ p (y - z) = inner ℝ p y - inner ℝ p z := inner_sub_right _ _ _
  rw [hyz, real_inner_smul_right, real_inner_self_eq_norm_sq] at h4
  rw [hyz, real_inner_smul_right] at h3
  have h5 : τ * ‖p‖ ^ 2 ≤ τ * inner ℝ ξ p := by linarith
  exact le_of_mul_le_mul_left h5 hτ

/-- A subgradient `p` of a norm at `z ≠ 0` has length at least `c_Ψ`. -/
private lemma normMin_le_norm_of_isSubgradient (hΨ : CERW.IsNorm Ψ) (hd : 1 ≤ d)
    {z p : EuclideanSpace ℝ (Fin d)} (hp : CERW.IsSubgradient Ψ z p) (hz : z ≠ 0) :
    CERW.normMin Ψ ≤ ‖p‖ := by
  have h1 := (CERW.Generic.Norm.subgradient_euler hΨ hp).1
  have h2 := (CERW.Generic.Norm.normMin_pos_mul_le hΨ hd).2 z
  have h3 : inner ℝ p z ≤ ‖p‖ * ‖z‖ := real_inner_le_norm p z
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h4 : CERW.normMin Ψ * ‖z‖ ≤ ‖p‖ * ‖z‖ := by linarith
  exact le_of_mul_le_mul_right h4 hz0


end MoreauEnvelope

/-- Lemma `lem:cap`. With `η = c_Ψ⁴/(8 Λ_Ψ²)` and `q = ∇F_τ(x)`, if `F_τ(y) ≤ F_τ(x)`,
`q · y > q · x - η τ` and `|y| > τ Λ_Ψ`, then every subgradient `ξ` of `Ψ` at `y` satisfies
`q · ξ ≥ c_Ψ²/2`. -/
theorem moreau_cap {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ) {τ : ℝ} (hτ : 0 < τ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    let η : ℝ := CERW.normMin Ψ ^ 4 / (8 * CERW.normMax Ψ ^ 2)
    let q : EuclideanSpace ℝ (Fin d) := gradient (CERW.moreauEnvelope Ψ τ) x
    CERW.moreauEnvelope Ψ τ y ≤ CERW.moreauEnvelope Ψ τ x →
    inner ℝ q x - η * τ < inner ℝ q y →
    τ * CERW.normMax Ψ < ‖y‖ →
    ∀ ξ : EuclideanSpace ℝ (Fin d), CERW.IsSubgradient Ψ y ξ →
      CERW.normMin Ψ ^ 2 / 2 ≤ inner ℝ q ξ := by
  intro η q hFy hqy hy ξ hξ
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hcpos, -⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  set p := gradient (CERW.moreauEnvelope Ψ τ) y with hp
  have hpsub : CERW.IsSubgradient Ψ (y - τ • p) p := isSubgradient_gradient_moreauEnvelope hΨ hτ y
  have hyz : y - (y - τ • p) = τ • p := by abel
  have hpΛ : ‖p‖ ≤ CERW.normMax Ψ := norm_le_normMax_of_isSubgradient hΨ hpsub
  have hξΛ : ‖ξ‖ ≤ CERW.normMax Ψ := norm_le_normMax_of_isSubgradient hΨ hξ
  have hz0 : y - τ • p ≠ 0 := by
    intro hz0
    have hyp : y = τ • p := sub_eq_zero.mp hz0
    have : ‖y‖ ≤ τ * CERW.normMax Ψ := by
      rw [hyp, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
      exact mul_le_mul_of_nonneg_left hpΛ hτ.le
    linarith
  have hcp : CERW.normMin Ψ ≤ ‖p‖ := normMin_le_norm_of_isSubgradient hΨ hd1 hpsub hz0
  have hmono : ‖p‖ ^ 2 ≤ inner ℝ ξ p := norm_sq_le_inner_of_isSubgradient hΨ hτ hξ hpsub hyz
  have hc2 : CERW.normMin Ψ ^ 2 ≤ ‖p‖ ^ 2 := pow_le_pow_left₀ hcpos.le hcp 2
  have hΛpos : 0 < CERW.normMax Ψ := lt_of_lt_of_le hcpos (hcp.trans hpΛ)
  have hdist : τ / 2 * ‖p - q‖ ^ 2
      ≤ CERW.moreauEnvelope Ψ τ y - CERW.moreauEnvelope Ψ τ x - inner ℝ q (y - x) :=
    gradient_moreauEnvelope_dist_sq_le hΨ hτ x y
  have hlt : τ / 2 * ‖p - q‖ ^ 2 < τ / 2 * (2 * η) := by
    have h1 : inner ℝ q (y - x) = inner ℝ q y - inner ℝ q x := inner_sub_right _ _ _
    linarith
  have hsq : ‖p - q‖ ^ 2 < 2 * η := lt_of_mul_lt_mul_left hlt (by positivity)
  have hη : CERW.normMax Ψ ^ 2 * (2 * η) = (CERW.normMin Ψ ^ 2 / 2) ^ 2 := by
    have : η = CERW.normMin Ψ ^ 4 / (8 * CERW.normMax Ψ ^ 2) := rfl
    rw [this]
    field_simp
    ring
  have hprod : (CERW.normMax Ψ * ‖p - q‖) ^ 2 < (CERW.normMin Ψ ^ 2 / 2) ^ 2 := by
    rw [mul_pow, ← hη]
    exact mul_lt_mul_of_pos_left hsq (by positivity)
  have hbound : CERW.normMax Ψ * ‖p - q‖ ≤ CERW.normMin Ψ ^ 2 / 2 :=
    (le_abs_self _).trans (abs_lt_of_sq_lt_sq hprod (by positivity)).le
  have h7 : inner ℝ ξ q = inner ℝ ξ p - inner ℝ ξ (p - q) := by
    rw [← inner_sub_right]
    congr 1
    abel
  have h8 : inner ℝ ξ (p - q) ≤ ‖ξ‖ * ‖p - q‖ := real_inner_le_norm _ _
  have h9 : ‖ξ‖ * ‖p - q‖ ≤ CERW.normMax Ψ * ‖p - q‖ :=
    mul_le_mul_of_nonneg_right hξΛ (norm_nonneg _)
  have h10 : inner ℝ q ξ = inner ℝ ξ q := real_inner_comm _ _
  linarith

end CERW.Support.Norm
