import CERW.Support.Norm.CoarseVolume
import CERW.Support.Drift.Bridge

/-!
# The Euclidean coarse bounds from the coarse bounds of the walk with a norm

`prop:coarse` for centrally excited random walk is the case `Ψ = |·|` of the coarse bounds of the
walk whose drift is a subgradient of a norm. The Euclidean walk is the walk with drift field
`ξ(x) = u_x = x/|x|` (`Support.Drift.isCERW_iff_isDriftCERW`), `u_x` is a subgradient of the
Euclidean norm at `x ≠ 0` and `u_0 = 0`, the Euclidean unit ball has volume `ω_d`, and the scale
`r_n = ((d+1) n/(2 d ε ω_d))^{1/(d+1)}` of the norm statement is the constant
`κ = ((d+1)/(2 d ε ω_d))^{1/(d+1)}` times `N = n^{1/(d+1)}`. The six bounds at the scale `r_n` give
the six bounds at the scale `N` with the constants `min (c κ^d, c κ)` and `max (C, C κ^d, C κ)`.

* `isNorm_euclidean`, `isSubgradient_unitDir`, `unitDir_toSpace_zero`, `normBallVolume_euclidean`:
  the bridges, with real proofs.
* `coarseScale_euclidean`: `r_n = κ N`.
* `six_bounds_scaled`: the conversion of the six bounds from the scale `κ N` to the scale `N`.
* `coarse_bounds_euclid`: the statement of `CERW.Frozen.coarse_bounds`, in every universe, from
  `norm_coarse_bounds_closed`.

No coarse, radial or Moreau estimate of the earlier route is used.
-/

universe u

open MeasureTheory
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.EuclideanCoarse

open CERW CERW.Support.Norm.CoarseVolume

variable {d : ℕ}

/-- The Euclidean norm is a norm on `ℝ^d`. -/
theorem isNorm_euclidean : IsNorm (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) :=
  ⟨norm_add_le, fun t x => by simp only [norm_smul, Real.norm_eq_abs], fun _ hx =>
    norm_eq_zero.mp hx⟩

/-- A site that embeds at the origin of `ℝ^d` is the origin. -/
theorem eq_zero_of_toSpace_eq_zero {x : Site d} (h : toSpace x = 0) : x = 0 := by
  funext i
  have hi := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v i) h
  simpa using hi

/-- The direction `u_v = v/|v|` is a subgradient of the Euclidean norm at `v ≠ 0`. -/
theorem isSubgradient_unitDir {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    IsSubgradient (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖) v (unitDir v) := by
  intro y
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hinner : inner ℝ (unitDir v) (y - v) = ‖v‖⁻¹ * (inner ℝ v y - ‖v‖ ^ 2) := by
    rw [unitDir, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq]
  have hcs : inner ℝ v y ≤ ‖v‖ * ‖y‖ := real_inner_le_norm v y
  have hle : ‖v‖⁻¹ * inner ℝ v y ≤ ‖y‖ := by
    calc ‖v‖⁻¹ * inner ℝ v y ≤ ‖v‖⁻¹ * (‖v‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr hpos.le)
      _ = ‖y‖ := by rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  have hexp : ‖v‖ + ‖v‖⁻¹ * (inner ℝ v y - ‖v‖ ^ 2) = ‖v‖⁻¹ * inner ℝ v y := by
    field_simp
    ring
  show ‖v‖ + inner ℝ (unitDir v) (y - v) ≤ ‖y‖
  rw [hinner, hexp]
  exact hle

/-- The field `x ↦ u_x` vanishes at the origin. -/
theorem unitDir_toSpace_zero : unitDir (toSpace (0 : Site d)) = 0 := by
  have h0 : toSpace (0 : Site d) = 0 := by
    ext i
    simp
  rw [h0]
  exact unitDir_zero

/-- The volume `|B_Ψ|` of the unit ball of the Euclidean norm is `ω_d`. -/
theorem normBallVolume_euclidean :
    normBallVolume (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) = unitBallVolume d := by
  unfold normBallVolume unitBallVolume
  congr 2
  ext v
  simp

/-- The scale `r_n` of the norm statement for the Euclidean norm is `κ n^{1/(d+1)}`, with
`κ = ((d+1)/(2 d ε ω_d))^{1/(d+1)}`. -/
theorem coarseScale_euclidean {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    coarseScale (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n =
      (((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1)) *
        (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
  have hω := unitBallVolume_pos d
  by_cases hd0 : d = 0
  · subst hd0
    simp [coarseScale]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  unfold coarseScale
  rw [normBallVolume_euclidean, ← Real.mul_rpow (by positivity) (Nat.cast_nonneg n)]
  congr 1
  ring

/-- The six bounds at the scale `r = κ N` give the six bounds at the scale `N`. -/
theorem six_bounds_scaled {κ N c C S M R : ℝ} {d : ℕ} (hN : 0 ≤ N)
    (h : c * (κ * N) ^ d ≤ S ∧ S ≤ C * (κ * N) ^ d ∧ c * (κ * N) ≤ M ∧ M ≤ C * (κ * N) ∧
      c * (κ * N) ≤ R ∧ R ≤ C * (κ * N)) :
    min (c * κ ^ d) (c * κ) * N ^ d ≤ S ∧ S ≤ max C (max (C * κ ^ d) (C * κ)) * N ^ d ∧
      min (c * κ ^ d) (c * κ) * N ≤ M ∧ M ≤ max C (max (C * κ ^ d) (C * κ)) * N ∧
      min (c * κ ^ d) (c * κ) * N ≤ R ∧ R ≤ max C (max (C * κ ^ d) (C * κ)) * N := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hNd : 0 ≤ N ^ d := pow_nonneg hN d
  have hmul : (κ * N) ^ d = κ ^ d * N ^ d := mul_pow κ N d
  have hlow1 : min (c * κ ^ d) (c * κ) ≤ c * κ ^ d := min_le_left _ _
  have hlow2 : min (c * κ ^ d) (c * κ) ≤ c * κ := min_le_right _ _
  have hup1 : C * κ ^ d ≤ max C (max (C * κ ^ d) (C * κ)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hup2 : C * κ ≤ max C (max (C * κ ^ d) (C * κ)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc min (c * κ ^ d) (c * κ) * N ^ d ≤ (c * κ ^ d) * N ^ d :=
          mul_le_mul_of_nonneg_right hlow1 hNd
      _ = c * (κ * N) ^ d := by rw [hmul]; ring
      _ ≤ S := h1
  · calc S ≤ C * (κ * N) ^ d := h2
      _ = (C * κ ^ d) * N ^ d := by rw [hmul]; ring
      _ ≤ max C (max (C * κ ^ d) (C * κ)) * N ^ d := mul_le_mul_of_nonneg_right hup1 hNd
  · calc min (c * κ ^ d) (c * κ) * N ≤ (c * κ) * N := mul_le_mul_of_nonneg_right hlow2 hN
      _ = c * (κ * N) := by ring
      _ ≤ M := h3
  · calc M ≤ C * (κ * N) := h4
      _ = (C * κ) * N := by ring
      _ ≤ max C (max (C * κ ^ d) (C * κ)) * N := mul_le_mul_of_nonneg_right hup2 hN
  · calc min (c * κ ^ d) (c * κ) * N ≤ (c * κ) * N := mul_le_mul_of_nonneg_right hlow2 hN
      _ = c * (κ * N) := by ring
      _ ≤ R := h5
  · calc R ≤ C * (κ * N) := h6
      _ = (C * κ) * N := by ring
      _ ≤ max C (max (C * κ ^ d) (C * κ)) * N := mul_le_mul_of_nonneg_right hup2 hN

/-- **The coarse bounds of centrally excited random walk** (the statement of
`CERW.Frozen.coarse_bounds`, in every universe): for `d ≥ 2`, `0 < ε < 1/d` and `p > 0` there are
`c, C > 0`, depending only on `d, ε, p`, such that for every walk `X` with law `IsCERW μ ε X` and
every `n ≥ 2`, with probability at least `1 − C n^{-p}`, `c N^d ≤ |A_n| ≤ C N^d`,
`c N ≤ max ℓ_n ≤ C N` and `c N ≤ max_{j ≤ n} |X_j| ≤ C N`, where `N = n^{1/(d+1)}`. It is the case
`Ψ = |·|` of `norm_coarse_bounds_closed`, through `isCERW_iff_isDriftCERW`, the subgradient
`u_x = x/|x|` of the Euclidean norm and `r_n = κ N`. -/
theorem coarse_bounds_euclid {d : ℕ} (hd : 2 ≤ d) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) → ∀ p : ℝ, 0 < p → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
        μ {ω | ¬ (c * N ^ d ≤ ((CERW.departureRange (X · ω) n).card : ℝ) ∧
                  ((CERW.departureRange (X · ω) n).card : ℝ) ≤ C * N ^ d ∧
                  c * N ≤ (CERW.maxLocalTime (X · ω) n : ℝ) ∧
                  (CERW.maxLocalTime (X · ω) n : ℝ) ≤ C * N ∧
                  c * N ≤ CERW.maxRadius (X · ω) n ∧ CERW.maxRadius (X · ω) n ≤ C * N)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  intro ε hε hεd p hp
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hell : ∀ i : Fin d, ε * ‖coordVec (d := d) i‖ < 1 / (d : ℝ) := by
    intro i
    have h1 : ‖coordVec (d := d) i‖ = 1 := by simp [coordVec]
    rw [h1, mul_one]
    exact hεd
  obtain ⟨c, C, hc, hC, hall⟩ := norm_coarse_bounds_closed.{u} hd
    (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) isNorm_euclidean ε hε hell p hp
  have hω := unitBallVolume_pos d
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = (((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d)) ^
      ((1 : ℝ) / (d + 1)) := ⟨_, rfl⟩
  have hκ : 0 < κ := by
    rw [hκdef]
    exact Real.rpow_pos_of_pos (by positivity) _
  refine ⟨min (c * κ ^ d) (c * κ), max C (max (C * κ ^ d) (C * κ)),
    lt_min (by positivity) (by positivity),
    lt_max_of_lt_left hC, ?_⟩
  intro Ω _ μ _ X hX n hn N
  have hNdef : N = (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := rfl
  have hX' : IsDriftCERW μ ε (fun z => unitDir (toSpace z)) X :=
    (CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).mp hX
  have hsel : ∀ x : Site d, x ≠ 0 →
      IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (unitDir (toSpace x)) :=
    fun x hx => isSubgradient_unitDir fun h => hx (eq_zero_of_toSpace_eq_zero h)
  have hbound := hall (fun z => unitDir (toSpace z)) hsel unitDir_toSpace_zero μ X hX' n hn
  have hN : 0 ≤ N := by rw [hNdef]; exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hscale : coarseScale (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n = κ * N := by
    rw [hNdef, hκdef]
    exact coarseScale_euclidean hε n
  have hCle : C ≤ max C (max (C * κ ^ d) (C * κ)) := le_max_left _ _
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine le_trans (measure_mono ?_)
    (hbound.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCle hnp)))
  intro ω hω hsix
  apply hω
  exact six_bounds_scaled hN (by rw [← hscale]; exact hsix)

end CERW.Support.Norm.EuclideanCoarse
