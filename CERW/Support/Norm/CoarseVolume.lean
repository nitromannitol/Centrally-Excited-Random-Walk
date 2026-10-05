import CERW.Support.Norm.CoarseCapEvents
import CERW.Support.Occupation.Cells
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellSetVolume

/-!
# The coarse bounds of the walk with a norm, from the cap event

The scale `r_n = ((d+1) n / (2 d ε |B_Ψ|))^{1/(d+1)}`, the volume and counting facts, and the
coarse bounds of the walk with a norm, derived from the cap event of `CoarseCapEvents`.

* `coarseScale` is `r_n`; every power of `log n` is negligible against it
  (`eventually_mul_log_pow_le_coarseScale`), and `n = κ r_n^{d+1}` (`nat_eq_coarseScale_pow`).
* The counting bound `|A_n|^{1/d} ≤ 2 max_j |X_j| + 1` (`rpow_card_le`), the volume comparison
  `|B_Ψ| ρ^d ≤ |A_n|` for a norm ball of radius `ρ` in the cell set
  (`normBallVolume_mul_pow_le_card`) and the contact bound (`contact_potential_le`): the potential
  of the cell set at a limit point of its complement is at most the error of the local time
  approximation, because the cell local time vanishes off the cell set and the potential is
  continuous.
* The real-number arguments: the scale `s = |A_n|^{1/d}` is at least of order `r_n`
  (`scale_le_rpow_card`), the error of the local time approximation is `O(s^{1/2} log n)`
  (`delta_le`), the excess and the local time beyond the inner radius are controlled
  (`excess_le`, `localTime_beyond_le`), the inner radius is at least of order `s`
  (`inner_radius_lower`), the volume of the excess is small (`volume_excess_le`), and the mass
  identity gives `s ≤ C r_n` (`scale_card_le`, `scale_upper`).
* `coarse_path` combines these with the public `inner_geometry` for one path, and
  `coarse_deterministic` collects the constants, which depend only on `Ψ`, `ε`, `C_L`, `C_out`
  and the geometry statements, before the path and the time: for every path of `LocalTimeEvent` and
  `RoughOuter`, and every large `n`, the six two-sided bounds hold.
* `norm_coarse_bounds_of_cap` is the statement `norm_coarse_bounds` with the cap event, the local
  time potential lemma and `coarse_deterministic`; `norm_coarse_bounds_closed` is its closed form
  with the proved producers. No radial test, old coarse bound, Moreau envelope or contact
  estimate of the earlier route is used.
-/

universe u

open MeasureTheory Filter Topology
open scoped Pointwise
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.CoarseVolume

open CERW CERW.Support.Norm.CoarseCrossing CERW.Support.Norm.CoarseCapEvents

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ## The scale -/

/-- The radius `r_n = ((d+1) n / (2 d ε |B_Ψ|))^{1/(d+1)}` of `eq:radius-norm`. -/
noncomputable def coarseScale (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  (((d : ℝ) + 1) * n / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))

/-- The scale is nonnegative. -/
theorem coarseScale_nonneg {ε : ℝ} (hε : 0 < ε) (hV : 0 < normBallVolume Ψ) (n : ℕ) :
    0 ≤ coarseScale Ψ ε n := by
  unfold coarseScale
  exact Real.rpow_nonneg (by positivity) _

/-- The `(d+1)`-st power of the scale: `n = (2 d ε |B_Ψ| / (d+1)) r_n^{d+1}`. -/
theorem nat_eq_coarseScale_pow (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hV : 0 < normBallVolume Ψ)
    (n : ℕ) :
    (n : ℝ) = 2 * d * ε * normBallVolume Ψ / (d + 1) * coarseScale Ψ ε n ^ (d + 1) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hX : 0 < 2 * (d : ℝ) * ε * normBallVolume Ψ := by positivity
  have hx : (0 : ℝ) ≤ ((d : ℝ) + 1) * n / (2 * d * ε * normBallVolume Ψ) := by positivity
  have h : coarseScale Ψ ε n ^ (d + 1) =
      ((d : ℝ) + 1) * n / (2 * d * ε * normBallVolume Ψ) := by
    unfold coarseScale
    rw [show (1 : ℝ) / (d + 1) = (((d + 1 : ℕ) : ℝ))⁻¹ by
      rw [one_div, Nat.cast_add, Nat.cast_one]]
    exact Real.rpow_inv_natCast_pow hx (by omega)
  rw [h]
  field_simp

/-- The scale of a positive time is positive. -/
theorem coarseScale_pos (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hV : 0 < normBallVolume Ψ) {n : ℕ}
    (hn : 1 ≤ n) : 0 < coarseScale Ψ ε n := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  unfold coarseScale
  refine Real.rpow_pos_of_pos ?_ _
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

/-- Every power of the logarithm is negligible against the scale: for every `K > 0` and every
`k`, eventually `K (log n)^k ≤ r_n`. -/
theorem eventually_mul_log_pow_le_coarseScale (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hV : 0 < normBallVolume Ψ) {K : ℝ} (hK : 0 < K) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, K * Real.log n ^ k ≤ coarseScale Ψ ε n := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hX : 0 < 2 * (d : ℝ) * ε * normBallVolume Ψ := by positivity
  set A : ℝ := (((d : ℝ) + 1) / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1)) with hA
  have hApos : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  have hlo := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (s := (1 : ℝ) / (d + 1))
    (by positivity)).def (c := A / K) (by positivity)
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlo
  filter_upwards [hnat, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hcs : coarseScale Ψ ε n = A * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    unfold coarseScale
    rw [hA, ← Real.mul_rpow (by positivity) hn0.le]
    congr 1
    field_simp
  rw [hcs]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog _),
    Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _), Real.rpow_natCast] at hn
  have h2 : K * (A / K * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) = A * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    field_simp
  calc K * Real.log n ^ k ≤ K * (A / K * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) :=
        mul_le_mul_of_nonneg_left hn hK.le
    _ = _ := h2

/-! ## Lattice and volume facts -/

/-- A path that runs for a positive time has visited at least one site. -/
theorem one_le_card_departureRange (x : ℕ → Site d) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ (departureRange x n).card :=
  Finset.card_pos.mpr ⟨x 0, Finset.mem_image_of_mem x (Finset.mem_range.mpr (by omega))⟩

/-- The number of departed sites is at most `(2 H_n + 1)^d`. -/
theorem card_le_pow_maxRadius (x : ℕ → Site d) (n : ℕ) :
    ((departureRange x n).card : ℝ) ≤ (2 * maxRadius x n + 1) ^ d := by
  have hR : 0 ≤ maxRadius x n :=
    (by rw [← norm_toSpace]; exact norm_nonneg _ : 0 ≤ euclidNorm (x 0)).trans
      (euclidNorm_le_maxRadius x (Nat.zero_le n))
  exact (Nat.cast_le.mpr (Finset.card_le_card
    (CERW.Support.Occupation.departureRange_subset_ballFinset x n))).trans
    (LatticeProb.card_ballFinset_le d hR)

/-- `|A_n|^{1/d} ≤ 2 H_n + 1`. -/
theorem rpow_card_le (hd : 1 ≤ d) (x : ℕ → Site d) (n : ℕ) :
    ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d) ≤ 2 * maxRadius x n + 1 := by
  have hR : 0 ≤ maxRadius x n :=
    (by rw [← norm_toSpace]; exact norm_nonneg _ : 0 ≤ euclidNorm (x 0)).trans
      (euclidNorm_le_maxRadius x (Nat.zero_le n))
  calc ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d)
      ≤ ((2 * maxRadius x n + 1) ^ d) ^ ((1 : ℝ) / d) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (card_le_pow_maxRadius x n) (by positivity)
    _ = 2 * maxRadius x n + 1 := by
        rw [one_div]
        exact Real.pow_rpow_inv_natCast (by positivity) (by omega)

/-- The norm ball `{Ψ < ρ}` has volume `|B_Ψ| ρ^d`. -/
theorem volume_sublevel (hΨ : IsNorm Ψ) {ρ : ℝ} (hρ : 0 < ρ) :
    volume {y : EuclideanSpace ℝ (Fin d) | Ψ y < ρ} =
      ENNReal.ofReal (ρ ^ d) * volume {y : EuclideanSpace ℝ (Fin d) | Ψ y < 1} := by
  have hset : {y : EuclideanSpace ℝ (Fin d) | Ψ y < ρ} =
      ρ • {y : EuclideanSpace ℝ (Fin d) | Ψ y < 1} := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hρ.ne']
    simp only [Set.mem_setOf_eq]
    rw [hΨ.smul, abs_of_pos (inv_pos.mpr hρ), inv_mul_lt_iff₀ hρ, mul_one]
  rw [hset, Measure.addHaar_smul, finrank_euclideanSpace_fin, abs_of_pos (pow_pos hρ d)]

/-- The volume of a norm ball inside the cell set is at most the number of departed sites:
`|B_Ψ| ρ^d ≤ |A_n|`. -/
theorem normBallVolume_mul_pow_le_card (hΨ : IsNorm Ψ) {ρ : ℝ} (hρ : 0 < ρ)
    {x : ℕ → Site d} {n : ℕ} (hsub : {y : EuclideanSpace ℝ (Fin d) | Ψ y < ρ} ⊆ cellSet x n) :
    normBallVolume Ψ * ρ ^ d ≤ ((departureRange x n).card : ℝ) := by
  have h1 : ((volume {y : EuclideanSpace ℝ (Fin d) | Ψ y < ρ}).toReal) ≤
      (volume (cellSet x n)).toReal := by
    refine ENNReal.toReal_mono ?_ (measure_mono hsub)
    rw [CERW.Support.Occupation.volume_cellSet]
    exact ENNReal.natCast_ne_top _
  rw [CERW.Support.Occupation.volume_cellSet, ENNReal.toReal_natCast] at h1
  rw [volume_sublevel hΨ hρ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h1
  unfold normBallVolume
  linarith

/-- A point of norm below the inner radius lies in the cell set. -/
theorem sublevel_subset_cellSet (hΨ : IsNorm Ψ) (x : ℕ → Site d) (n : ℕ) :
    {y : EuclideanSpace ℝ (Fin d) | Ψ y < normInnerRadius Ψ x n} ⊆ cellSet x n := by
  intro y hy
  by_contra hnot
  have hbdd : BddBelow (Ψ '' (cellSet x n)ᶜ) :=
    ⟨0, by
      rintro _ ⟨z, -, rfl⟩
      exact (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 z⟩
  exact absurd hy (not_lt.mpr (csInf_le hbdd ⟨y, hnot, rfl⟩))


/-! ## The contact bound -/

/-- The potential of a bounded measurable set is continuous: the Hölder bound of `lem:geometry` has
a finite constant. -/
theorem continuous_normPotential (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hgeom : CERW.Support.Statements.norm_potential_geometry)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D) :
    Continuous (normPotential d ε Ψ D) := by
  obtain ⟨Cg, hCg, hgeo⟩ := hgeom hd Ψ hΨ
  have hH := (hgeo ε hε D hD hDb).2.1
  set K : ℝ := Cg * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) with hK
  have hK0 : 0 ≤ K := by positivity
  rw [Metric.continuous_iff]
  intro y η hη
  have hK1 : 0 < K + 1 := by linarith
  refine ⟨(η / (K + 1)) ^ 2, by positivity, fun z hz => ?_⟩
  rw [Real.dist_eq]
  have h1 := hH z y
  have h2 : ‖z - y‖ ^ ((1 : ℝ) / 2) ≤ ((η / (K + 1)) ^ 2) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (norm_nonneg _) (by rw [dist_eq_norm] at hz; exact hz.le) (by norm_num)
  have h3 : ((η / (K + 1)) ^ 2) ^ ((1 : ℝ) / 2) = η / (K + 1) := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  rw [h3] at h2
  calc |normPotential d ε Ψ D z - normPotential d ε Ψ D y| ≤ K * ‖z - y‖ ^ ((1 : ℝ) / 2) := h1
    _ ≤ K * (η / (K + 1)) := mul_le_mul_of_nonneg_left h2 hK0
    _ < η := by
        rw [mul_div_assoc', div_lt_iff₀ hK1]
        linarith

/-- **The contact bound.** If the cell local time approximates the potential of the cell set within
`δ` on `{|y| ≤ 2n}`, then the potential is at most `δ` at every limit point of the complement of the
cell set of norm below `2n`: the cell local time vanishes off the cell set, and the potential is
continuous. -/
theorem normPotential_le_of_mem_closure (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hgeom : CERW.Support.Statements.norm_potential_geometry) {x : ℕ → Site d} {n : ℕ}
    {R δ : ℝ} (hDR : cellSet x n ⊆ Metric.ball 0 R)
    (happrox : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
      |cellLocalTime x n y - normPotential d ε Ψ (cellSet x n) y| ≤ δ)
    {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : y₀ ∈ closure (cellSet x n)ᶜ) (hn : ‖y₀‖ < 2 * n) :
    normPotential d ε Ψ (cellSet x n) y₀ ≤ δ := by
  have hcont := continuous_normPotential hd hΨ hε hgeom
    (CERW.Support.Occupation.measurableSet_cellSet x n) (Metric.isBounded_ball.subset hDR)
  have hA : ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (2 * n) ∩ (cellSet x n)ᶜ,
      normPotential d ε Ψ (cellSet x n) y ≤ δ := by
    rintro y ⟨hyb, hyD⟩
    have h := happrox y (le_of_lt (mem_ball_zero_iff.mp hyb))
    rw [CERW.Support.Occupation.cellLocalTime_eq_zero_of_not_mem x n hyD, zero_sub,
      abs_neg] at h
    exact (le_abs_self _).trans h
  have hy₀' : y₀ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (2 * n) ∩ closure (cellSet x n)ᶜ :=
    ⟨mem_ball_zero_iff.mpr hn, hy₀⟩
  have hcl := Metric.isOpen_ball.inter_closure hy₀'
  exact closure_minimal hA (isClosed_le hcont continuous_const) hcl

/-- The hypothesis of the inner geometry at the contact points: every point `y₀` with `Ψ y₀` equal
to the inner radius `b` and in the closure of the complement of the cell set has potential at most
`δ`, provided that `b < 2 n c_Ψ`, which makes `|y₀| < 2n`. -/
theorem contact_potential_le (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hgeom : CERW.Support.Statements.norm_potential_geometry) {x : ℕ → Site d} {n : ℕ}
    {R δ : ℝ} (hDR : cellSet x n ⊆ Metric.ball 0 R)
    (happrox : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
      |cellLocalTime x n y - normPotential d ε Ψ (cellSet x n) y| ≤ δ)
    (hb : normInnerRadius Ψ x n < 2 * n * normMin Ψ) :
    ∀ y₀ : EuclideanSpace ℝ (Fin d), Ψ y₀ = normInnerRadius Ψ x n →
      y₀ ∈ closure (cellSet x n)ᶜ → normPotential d ε Ψ (cellSet x n) y₀ ≤ δ := by
  intro y₀ hΨy₀ hcl
  obtain ⟨hc0, hcle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ (by omega : 1 ≤ d)
  refine normPotential_le_of_mem_closure hd hΨ hε hgeom hDR happrox hcl ?_
  have h1 : normMin Ψ * ‖y₀‖ ≤ normInnerRadius Ψ x n := hΨy₀ ▸ hcle y₀
  by_contra hnot
  have h2 : 2 * (n : ℝ) ≤ ‖y₀‖ := not_lt.mp hnot
  have h3 : normMin Ψ * (2 * (n : ℝ)) ≤ normMin Ψ * ‖y₀‖ := mul_le_mul_of_nonneg_left h2 hc0.le
  linarith


/-! ## Real arithmetic of the coarse bounds

These lemmas only manipulate real numbers. Throughout, `u` is the scale `r_n`, `κ = 2dε|B_Ψ|/(d+1)`
(so that `n = κ u^{d+1}`), `L = log n`, `s = |A_n|^{1/d}`, and `q = s^{1/(4(d+1))}`, so that every
power of `s` that occurs is a natural power of `q`: `√s = q^{2(d+1)}`, `s^{3/4} = q^{3(d+1)}`,
`s^{(2d+1)/(2d+2)} = q^{4d+2}`. -/

/-- The square root of `q^{4(d+1)}` is `q^{2(d+1)}`. -/
theorem sqrt_pow_four {q : ℝ} (hq : 0 ≤ q) (d : ℕ) :
    Real.sqrt (q ^ (4 * (d + 1))) = q ^ (2 * (d + 1)) := by
  rw [show 4 * (d + 1) = 2 * (d + 1) * 2 by ring, pow_mul]
  exact Real.sqrt_sq (by positivity)

/-- **First bound on the number of sites.** If `n ≤ M |A_n|` and `M ≤ C_L s + C_L L²` and
`C_L L² c₁^d ≤ (κ/4) u`, then `s ≥ c₁ u`, where `c₁^{d+1} = κ/(2 C_L)`. -/
theorem scale_le_rpow_card (hd : 1 ≤ d) {κ C_L u s M L : ℝ} (hκ : 0 < κ) (hC : 0 < C_L)
    (hu : 0 < u) (hs : 0 < s) (h1 : κ * u ^ (d + 1) ≤ M * s ^ d)
    (h2 : M ≤ C_L * s + C_L * L ^ 2)
    (hsmall : C_L * L ^ 2 * ((κ / (2 * C_L)) ^ ((1 : ℝ) / (d + 1))) ^ d ≤ κ / 4 * u) :
    (κ / (2 * C_L)) ^ ((1 : ℝ) / (d + 1)) * u ≤ s := by
  set c₁ : ℝ := (κ / (2 * C_L)) ^ ((1 : ℝ) / (d + 1)) with hc₁
  have hc₁0 : 0 < c₁ := Real.rpow_pos_of_pos (by positivity) _
  have hc₁pow : c₁ ^ (d + 1) = κ / (2 * C_L) := by
    rw [hc₁, show (1 : ℝ) / (d + 1) = (((d + 1 : ℕ) : ℝ))⁻¹ by
      rw [one_div, Nat.cast_add, Nat.cast_one]]
    exact Real.rpow_inv_natCast_pow (by positivity) (by omega)
  by_contra hlt
  rw [not_le] at hlt
  have hsd : s ^ d ≤ (c₁ * u) ^ d := pow_le_pow_left₀ hs.le hlt.le d
  have hsd1 : s ^ (d + 1) ≤ (c₁ * u) ^ (d + 1) := pow_le_pow_left₀ hs.le hlt.le (d + 1)
  have hcu : (c₁ * u) ^ (d + 1) = κ / (2 * C_L) * u ^ (d + 1) := by rw [mul_pow, hc₁pow]
  have hcud : (c₁ * u) ^ d = c₁ ^ d * u ^ d := mul_pow _ _ _
  have e1 : M * s ^ d ≤ C_L * s ^ (d + 1) + C_L * L ^ 2 * s ^ d := by
    calc M * s ^ d ≤ (C_L * s + C_L * L ^ 2) * s ^ d :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = C_L * s ^ (d + 1) + C_L * L ^ 2 * s ^ d := by ring
  have e2 : C_L * s ^ (d + 1) ≤ κ / 2 * u ^ (d + 1) := by
    calc C_L * s ^ (d + 1) ≤ C_L * ((c₁ * u) ^ (d + 1)) := mul_le_mul_of_nonneg_left hsd1 hC.le
      _ = κ / 2 * u ^ (d + 1) := by rw [hcu]; field_simp
  have e3 : C_L * L ^ 2 * s ^ d ≤ κ / 4 * u ^ (d + 1) := by
    calc C_L * L ^ 2 * s ^ d ≤ C_L * L ^ 2 * ((c₁ * u) ^ d) :=
          mul_le_mul_of_nonneg_left hsd (by positivity)
      _ = (C_L * L ^ 2 * c₁ ^ d) * u ^ d := by rw [hcud]; ring
      _ ≤ (κ / 4 * u) * u ^ d := mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = κ / 4 * u ^ (d + 1) := by ring
  have hpos : 0 < κ * u ^ (d + 1) := by positivity
  linarith


/-- **The error of the local time approximation.** If `M ≤ C₂ q^{4(d+1)}` and `δ` is at most the
error `C_L log n + C_L (√M log n or √(M log n))` of the local time lemma, then
`δ ≤ C_L (1 + √C₂) q^{2(d+1)} log n`. -/
theorem delta_le {q L C_L C₂ M δ : ℝ} (d : ℕ) (hq : 1 ≤ q) (hL : 1 ≤ L) (hC_L : 0 ≤ C_L)
    (hC₂ : 0 ≤ C₂) (hM : M ≤ C₂ * q ^ (4 * (d + 1)))
    (hδ : δ ≤ C_L * L + C_L * (if d = 2 then Real.sqrt M * L else Real.sqrt (M * L))) :
    δ ≤ C_L * (1 + Real.sqrt C₂) * (q ^ (2 * (d + 1)) * L) := by
  have hq0 : 0 ≤ q := by linarith
  have hQ : 1 ≤ q ^ (2 * (d + 1)) := one_le_pow₀ hq
  have hsq : Real.sqrt (C₂ * q ^ (4 * (d + 1))) = Real.sqrt C₂ * q ^ (2 * (d + 1)) := by
    rw [Real.sqrt_mul hC₂, sqrt_pow_four hq0]
  have hsM : Real.sqrt M ≤ Real.sqrt C₂ * q ^ (2 * (d + 1)) := by
    rw [← hsq]
    exact Real.sqrt_le_sqrt hM
  have hsL : Real.sqrt L ≤ L := by
    calc Real.sqrt L ≤ Real.sqrt (L ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = L := Real.sqrt_sq (by linarith)
  have hsC : 0 ≤ Real.sqrt C₂ := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := by linarith
  have h0 : L ≤ q ^ (2 * (d + 1)) * L := by nlinarith
  split_ifs at hδ with h2
  · calc δ ≤ C_L * L + C_L * (Real.sqrt M * L) := hδ
      _ ≤ C_L * (q ^ (2 * (d + 1)) * L) + C_L * (Real.sqrt C₂ * q ^ (2 * (d + 1)) * L) := by
          gcongr
      _ = C_L * (1 + Real.sqrt C₂) * (q ^ (2 * (d + 1)) * L) := by ring
  · have hML : Real.sqrt (M * L) ≤ Real.sqrt C₂ * q ^ (2 * (d + 1)) * L := by
      have hM0 : M ≤ C₂ * q ^ (4 * (d + 1)) := hM
      calc Real.sqrt (M * L) ≤ Real.sqrt (C₂ * q ^ (4 * (d + 1)) * L) :=
            Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hM0 hL0)
        _ = Real.sqrt (C₂ * q ^ (4 * (d + 1))) * Real.sqrt L := Real.sqrt_mul (by positivity) L
        _ = Real.sqrt C₂ * q ^ (2 * (d + 1)) * Real.sqrt L := by rw [hsq]
        _ ≤ Real.sqrt C₂ * q ^ (2 * (d + 1)) * L := by gcongr
    calc δ ≤ C_L * L + C_L * Real.sqrt (M * L) := hδ
      _ ≤ C_L * (q ^ (2 * (d + 1)) * L) + C_L * (Real.sqrt C₂ * q ^ (2 * (d + 1)) * L) := by
          gcongr
      _ = C_L * (1 + Real.sqrt C₂) * (q ^ (2 * (d + 1)) * L) := by ring

/-- The excess integral `I ≤ (ω/(2ε)) ((1 + Λ/c) R)^d H` with `R ≤ C₇ q^{4(d+1)} L` and
`H ≤ C₄ q^{2(d+1)} L` is at most `K_I (q^{4d+2} L)^{d+1}`. -/
theorem excess_le {q L A B R H C₇ C₄ I : ℝ} (d : ℕ) (hq : 1 ≤ q) (hL : 1 ≤ L) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hR0 : 0 ≤ R) (hH0 : 0 ≤ H) (hC₇ : 0 ≤ C₇)
    (hR : R ≤ C₇ * (q ^ (4 * (d + 1)) * L)) (hH : H ≤ C₄ * (q ^ (2 * (d + 1)) * L))
    (hI : I ≤ A * (B * R) ^ d * H) :
    I ≤ A * (B * C₇) ^ d * C₄ * (q ^ (4 * d + 2) * L) ^ (d + 1) := by
  have hq0 : 0 ≤ q := by linarith
  have hL0 : 0 ≤ L := by linarith
  have h1 : (B * R) ^ d ≤ (B * (C₇ * (q ^ (4 * (d + 1)) * L))) ^ d :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hR hB) d
  have e : (q ^ (4 * (d + 1))) ^ d * q ^ (2 * (d + 1)) = (q ^ (4 * d + 2)) ^ (d + 1) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  calc I ≤ A * (B * R) ^ d * H := hI
    _ ≤ A * (B * (C₇ * (q ^ (4 * (d + 1)) * L))) ^ d * (C₄ * (q ^ (2 * (d + 1)) * L)) := by
        gcongr
    _ = A * (B * C₇) ^ d * C₄ * (((q ^ (4 * (d + 1))) ^ d * q ^ (2 * (d + 1))) * L ^ (d + 1)) := by
        rw [show (B * (C₇ * (q ^ (4 * (d + 1)) * L))) = (B * C₇) * (q ^ (4 * (d + 1)) * L) by ring,
          mul_pow, mul_pow]
        ring
    _ = A * (B * C₇) ^ d * C₄ * (q ^ (4 * d + 2) * L) ^ (d + 1) := by
        rw [e, mul_pow (q ^ (4 * d + 2)) L (d + 1)]

/-- The largest local time beyond the inner radius: if `Lb ≤ δ + C_G I^{1/(d+1)}` with
`δ ≤ C₄ q^{2(d+1)} L` and `I ≤ K_I (q^{4d+2} L)^{d+1}`, then `Lb ≤ C₅ q^{4d+2} L`. -/
theorem localTime_beyond_le {q L δ I Lb C₄ K_I C_G : ℝ} (d : ℕ) (hq : 1 ≤ q) (hL : 1 ≤ L)
    (hI0 : 0 ≤ I) (hK : 0 ≤ K_I) (hC_G : 0 ≤ C_G) (hC₄ : 0 ≤ C₄)
    (hLb : Lb ≤ δ + C_G * I ^ ((1 : ℝ) / (d + 1)))
    (hδ : δ ≤ C₄ * (q ^ (2 * (d + 1)) * L)) (hI : I ≤ K_I * (q ^ (4 * d + 2) * L) ^ (d + 1)) :
    Lb ≤ (C₄ + C_G * (K_I + 1)) * (q ^ (4 * d + 2) * L) := by
  have hq0 : 0 ≤ q := by linarith
  have hL0 : 0 ≤ L := by linarith
  set e : ℝ := q ^ (4 * d + 2) * L with he
  have he0 : 0 ≤ e := by positivity
  have hQ : q ^ (2 * (d + 1)) ≤ q ^ (4 * d + 2) := pow_le_pow_right₀ hq (by omega)
  have hδe : δ ≤ C₄ * e := by
    calc δ ≤ C₄ * (q ^ (2 * (d + 1)) * L) := hδ
      _ ≤ C₄ * e := by rw [he]; gcongr
  have hZ : I ≤ ((K_I + 1) * e) ^ (d + 1) := by
    calc I ≤ K_I * e ^ (d + 1) := hI
      _ ≤ (K_I + 1) * e ^ (d + 1) := by
          nlinarith [pow_nonneg he0 (d + 1)]
      _ ≤ (K_I + 1) ^ (d + 1) * e ^ (d + 1) := by
          gcongr
          exact le_self_pow₀ (by linarith) (by omega)
      _ = ((K_I + 1) * e) ^ (d + 1) := (mul_pow (K_I + 1) e (d + 1)).symm
  have hroot : I ^ ((1 : ℝ) / (d + 1)) ≤ (K_I + 1) * e := by
    calc I ^ ((1 : ℝ) / (d + 1)) ≤ (((K_I + 1) * e) ^ (d + 1)) ^ ((1 : ℝ) / (d + 1)) :=
          Real.rpow_le_rpow hI0 hZ (by positivity)
      _ = (K_I + 1) * e := by
          rw [show (1 : ℝ) / (d + 1) = (((d + 1 : ℕ) : ℝ))⁻¹ by
            rw [one_div, Nat.cast_add, Nat.cast_one]]
          exact Real.pow_rpow_inv_natCast (by positivity) (by omega)
  calc Lb ≤ δ + C_G * I ^ ((1 : ℝ) / (d + 1)) := hLb
    _ ≤ C₄ * e + C_G * ((K_I + 1) * e) := add_le_add hδe (mul_le_mul_of_nonneg_left hroot hC_G)
    _ = (C₄ + C_G * (K_I + 1)) * e := by ring

/-- **A lower bound for the inner radius.** From `s ≤ 2 R₀ + 1`, the rough outer bound at the inner
radius `R₀ ≤ b/c + C_out (1 + Lb) L`, `Lb ≤ C₅ q^{4d+2} L` and `8 C_out (1 + C₅) L² ≤ q²`, with
`s = q^{4(d+1)}` and `q ≥ 2`, the inner radius satisfies `c s/4 ≤ b`, and `R₀ ≤ b/c + s/8`. -/
theorem inner_radius_lower {q L c b R₀ s Lb C_out C₅ : ℝ} (d : ℕ) (hq : 2 ≤ q) (hL : 1 ≤ L)
    (hc : 0 < c) (hC_out : 0 ≤ C_out) (hs : s = q ^ (4 * (d + 1)))
    (hcount : s ≤ 2 * R₀ + 1) (hrough : R₀ ≤ b / c + C_out * (1 + Lb) * L)
    (hLb : Lb ≤ C₅ * (q ^ (4 * d + 2) * L))
    (hsmall : 8 * (C_out * (1 + C₅)) * L ^ 2 ≤ q ^ 2) :
    c * s / 4 ≤ b ∧ R₀ ≤ b / c + s / 8 := by
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hL0 : 0 ≤ L := by linarith
  have he1 : 1 ≤ q ^ (4 * d + 2) * L := by
    have := one_le_pow₀ (n := 4 * d + 2) hq1
    nlinarith
  set e : ℝ := q ^ (4 * d + 2) * L with he
  have h1 : C_out * (1 + Lb) * L ≤ C_out * (1 + C₅) * (e * L) := by
    have : 1 + Lb ≤ (1 + C₅) * e := by nlinarith
    calc C_out * (1 + Lb) * L ≤ C_out * ((1 + C₅) * e) * L := by gcongr
      _ = C_out * (1 + C₅) * (e * L) := by ring
  have h2 : 8 * (C_out * (1 + C₅) * (e * L)) ≤ s := by
    have e2 : e * L = q ^ (4 * d + 2) * L ^ 2 := by rw [he]; ring
    have e3 : s = q ^ (4 * d + 2) * q ^ 2 := by rw [hs, ← pow_add]; congr 1
    rw [e2, e3]
    calc 8 * (C_out * (1 + C₅) * (q ^ (4 * d + 2) * L ^ 2))
        = q ^ (4 * d + 2) * (8 * (C_out * (1 + C₅)) * L ^ 2) := by ring
      _ ≤ q ^ (4 * d + 2) * q ^ 2 := mul_le_mul_of_nonneg_left hsmall (by positivity)
  have h4 : 4 ≤ s := by
    have : q ^ 4 ≤ q ^ (4 * (d + 1)) := pow_le_pow_right₀ hq1 (by omega)
    have h16 : (2 : ℝ) ^ 4 ≤ q ^ 4 := pow_le_pow_left₀ (by norm_num) hq 4
    rw [hs]
    linarith
  have hR₀ : R₀ ≤ b / c + s / 8 := by
    linarith
  have hbc : b / c = b * c⁻¹ := div_eq_mul_inv _ _
  have h5 : s ≤ 2 * (b / c) + s / 4 + 1 := by linarith
  have h6 : s ≤ 4 * (b / c) := by linarith
  rw [div_eq_mul_inv] at h6
  have h7 : c * s ≤ 4 * b := by
    have := mul_le_mul_of_nonneg_left h6 hc.le
    calc c * s ≤ c * (4 * (b * c⁻¹)) := this
      _ = 4 * b := by field_simp
  exact ⟨by linarith, hR₀⟩


/-- `(x + y)^{m+1} - x^{m+1} ≤ (m + 1) y (x + y)^m` for `x, y ≥ 0`. -/
theorem pow_succ_sub_pow_succ_le (m : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ (m + 1) - x ^ (m + 1) ≤ (m + 1) * y * (x + y) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hxy : 0 ≤ x + y := add_nonneg hx hy
    have hpow : x ^ (m + 1) ≤ (x + y) ^ (m + 1) := pow_le_pow_left₀ hx (by linarith) _
    have e : (x + y) ^ (m + 1 + 1) - x ^ (m + 1 + 1) =
        (x + y) * ((x + y) ^ (m + 1) - x ^ (m + 1)) + x ^ (m + 1) * y := by ring
    rw [e]
    calc (x + y) * ((x + y) ^ (m + 1) - x ^ (m + 1)) + x ^ (m + 1) * y
        ≤ (x + y) * ((m + 1) * y * (x + y) ^ m) + (x + y) ^ (m + 1) * y := by
          gcongr
      _ = ((m + 1 : ℕ) + 1) * y * (x + y) ^ (m + 1) := by
          push_cast
          ring

/-- **The volume of the excess.** With `d = m + 1`, `W b ≤ s` for `s = q^{4(d+1)}`, the layer bound
`Ev ≤ V((b+t)^d - b^d) + I/t` for every `t > 0` and `I ≤ K_I (q^{4d+2} L)^{d+1}`, the excess has
`q^{3(d+1)} Ev ≤ K_E (q^{4d+2})^{d+1} L^{d+1}`, with `K_E = V d (W⁻¹ + 1)^m + K_I`. -/
theorem volume_excess_le {q L V W b I Ev K_I : ℝ} {m : ℕ} (hq : 1 ≤ q) (hL : 1 ≤ L)
    (hV : 0 ≤ V) (hW : 0 < W) (hb0 : 0 ≤ b) (hbW : W * b ≤ q ^ (4 * (m + 1 + 1)))
    (hI : I ≤ K_I * (q ^ (4 * (m + 1) + 2) * L) ^ (m + 1 + 1))
    (hEv : ∀ t : ℝ, 0 < t → Ev ≤ V * ((b + t) ^ (m + 1) - b ^ (m + 1)) + I / t) :
    q ^ (3 * (m + 1 + 1)) * Ev ≤
      (V * (m + 1) * (W⁻¹ + 1) ^ m + K_I) * (q ^ ((4 * (m + 1) + 2) * (m + 1 + 1)) *
        L ^ (m + 1 + 1)) := by
  have hq0 : 0 < q := by linarith
  have hL0 : 0 ≤ L := by linarith
  set t : ℝ := q ^ (3 * (m + 1 + 1)) with ht
  set s : ℝ := q ^ (4 * (m + 1 + 1)) with hs
  have ht0 : 0 < t := by positivity
  have hts : t ≤ s := pow_le_pow_right₀ hq (by omega)
  have hbs : b ≤ W⁻¹ * s := by
    rw [← div_eq_inv_mul, le_div_iff₀ hW]
    linarith
  have hbt : b + t ≤ (W⁻¹ + 1) * s := by
    have : (W⁻¹ + 1) * s = W⁻¹ * s + s := by ring
    linarith
  have hLpow : 1 ≤ L ^ (m + 1 + 1) := one_le_pow₀ hL
  have h1 := hEv t ht0
  have h2 : (b + t) ^ (m + 1) - b ^ (m + 1) ≤ (m + 1) * t * (b + t) ^ m := by
    have := pow_succ_sub_pow_succ_le m hb0 ht0.le
    simpa using this
  have h3 : (b + t) ^ m ≤ ((W⁻¹ + 1) * s) ^ m := pow_le_pow_left₀ (by positivity) hbt m
  have h4 : t * Ev ≤ V * t * ((m + 1) * t * ((W⁻¹ + 1) * s) ^ m) + I := by
    calc t * Ev ≤ t * (V * ((b + t) ^ (m + 1) - b ^ (m + 1)) + I / t) :=
          mul_le_mul_of_nonneg_left h1 ht0.le
      _ = V * t * ((b + t) ^ (m + 1) - b ^ (m + 1)) + I := by field_simp
      _ ≤ V * t * ((m + 1) * t * ((W⁻¹ + 1) * s) ^ m) + I := by
          gcongr
          exact h2.trans (by gcongr)
  have e1 : V * t * ((m + 1) * t * ((W⁻¹ + 1) * s) ^ m) =
      V * (m + 1) * (W⁻¹ + 1) ^ m * q ^ ((4 * (m + 1) + 2) * (m + 1 + 1)) := by
    rw [ht, hs, mul_pow, ← pow_mul]
    have : q ^ (3 * (m + 1 + 1)) * (q ^ (3 * (m + 1 + 1)) * (q ^ (4 * (m + 1 + 1) * m))) =
        q ^ ((4 * (m + 1) + 2) * (m + 1 + 1)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring
    calc V * q ^ (3 * (m + 1 + 1)) * ((m + 1) * q ^ (3 * (m + 1 + 1)) *
          ((W⁻¹ + 1) ^ m * q ^ (4 * (m + 1 + 1) * m)))
        = V * (m + 1) * (W⁻¹ + 1) ^ m * (q ^ (3 * (m + 1 + 1)) *
          (q ^ (3 * (m + 1 + 1)) * q ^ (4 * (m + 1 + 1) * m))) := by ring
      _ = _ := by rw [this]
  have e2 : q ^ ((4 * (m + 1) + 2) * (m + 1 + 1)) * L ^ (m + 1 + 1) =
      (q ^ (4 * (m + 1) + 2) * L) ^ (m + 1 + 1) := by
    rw [mul_pow, ← pow_mul]
  have hQ0 : 0 ≤ q ^ ((4 * (m + 1) + 2) * (m + 1 + 1)) := by positivity
  rw [e1] at h4
  rw [mul_pow] at hI
  calc q ^ (3 * (m + 1 + 1)) * Ev = t * Ev := rfl
    _ ≤ V * (m + 1) * (W⁻¹ + 1) ^ m * q ^ ((4 * (m + 1) + 2) * (m + 1 + 1)) + I := h4
    _ ≤ V * (m + 1) * (W⁻¹ + 1) ^ m * (q ^ ((4 * (m + 1) + 2) * (m + 1 + 1)) *
          L ^ (m + 1 + 1)) + K_I * (q ^ ((4 * (m + 1) + 2) * (m + 1 + 1)) *
          L ^ (m + 1 + 1)) := by
        have h5 : V * (m + 1) * (W⁻¹ + 1) ^ m * q ^ ((4 * (m + 1) + 2) * (m + 1 + 1)) ≤
            V * (m + 1) * (W⁻¹ + 1) ^ m * (q ^ ((4 * (m + 1) + 2) * (m + 1 + 1)) *
              L ^ (m + 1 + 1)) := by
          have : q ^ ((4 * (m + 1) + 2) * (m + 1 + 1)) ≤
              q ^ ((4 * (m + 1) + 2) * (m + 1 + 1)) * L ^ (m + 1 + 1) :=
            le_mul_of_one_le_right hQ0 hLpow
          have hc : 0 ≤ V * (m + 1) * (W⁻¹ + 1) ^ m := by positivity
          exact mul_le_mul_of_nonneg_left this hc
        have h6 : I ≤ K_I * (q ^ ((4 * (m + 1) + 2) * (m + 1 + 1)) * L ^ (m + 1 + 1)) := by
          rw [← pow_mul] at hI
          exact hI
        linarith
    _ = _ := by ring


/-- **Closing the mass identity.** With `d = m + 1`, `s = q^{4(d+1)}`, `n = κ u^{d+1}`, `c₂ s ≤ b`,
the mass identity `|n - κ b^{d+1}| ≤ ω R^d δ + 2εΛ R Ev`, `R ≤ C₇ s L`, `δ ≤ C₄ q^{2(d+1)} L`, the
volume bound `q^{3(d+1)} Ev ≤ K_E (q^{4d+2})^{d+1} L^{d+1}` and the smallness
`(ω C₇^d C₄ + 2εΛ C₇ K_E) L^{d+2} ≤ (κ c₂^{d+1}/2) q^{d+1}`, we get `s ≤ 2u/c₂`. -/
theorem scale_card_le {q L u s b n κ c₂ ω ε Λ R δ Ev C₇ C₄ K_E : ℝ} {m : ℕ} (hq : 1 ≤ q)
    (hL : 1 ≤ L) (hs : s = q ^ (4 * (m + 1 + 1))) (hκ : 0 < κ) (hc₂ : 0 < c₂) (hu : 0 ≤ u)
    (hb : c₂ * s ≤ b) (hnκ : n = κ * u ^ (m + 1 + 1)) (hω : 0 ≤ ω) (hε : 0 ≤ ε) (hΛ : 0 ≤ Λ)
    (hR0 : 0 ≤ R) (hR : R ≤ C₇ * (q ^ (4 * (m + 1 + 1)) * L)) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ C₄ * (q ^ (2 * (m + 1 + 1)) * L)) (hC₇ : 0 ≤ C₇) (hEv0 : 0 ≤ Ev)
    (hEv : q ^ (3 * (m + 1 + 1)) * Ev ≤ K_E * (q ^ ((4 * (m + 1) + 2) * (m + 1 + 1)) *
      L ^ (m + 1 + 1)))
    (hmass : |n - κ * b ^ (m + 1 + 1)| ≤ ω * R ^ (m + 1) * δ + 2 * ε * Λ * R * Ev)
    (hsmall : (ω * C₇ ^ (m + 1) * C₄ + 2 * ε * Λ * C₇ * K_E) * L ^ (m + 1 + 2) ≤
      κ * c₂ ^ (m + 1 + 1) / 2 * q ^ (m + 1 + 1)) :
    s ≤ 2 * u / c₂ := by
  have hq0 : 0 < q := by linarith
  have hL0 : 0 ≤ L := by linarith
  set t : ℝ := q ^ (3 * (m + 1 + 1)) with ht
  have ht0 : 0 < t := by positivity
  set P : ℕ := (4 * (m + 1) + 2) * (m + 1 + 1) with hP
  -- the first term of the error
  have hT1 : ω * R ^ (m + 1) * δ ≤ ω * C₇ ^ (m + 1) * C₄ * (q ^ P * L ^ (m + 1 + 1)) := by
    have h := excess_le (q := q) (L := L) (A := ω) (B := 1) (R := R) (H := δ) (C₇ := C₇)
      (C₄ := C₄) (I := ω * R ^ (m + 1) * δ) (m + 1) hq hL hω zero_le_one hR0 hδ0 hC₇ hR hδ
      (by rw [one_mul])
    rw [one_mul, mul_pow, ← pow_mul] at h
    rw [hP]
    exact h
  -- the second term of the error, multiplied by `t`
  have hT2 : t * (2 * ε * Λ * R * Ev) ≤
      2 * ε * Λ * C₇ * K_E * (q ^ (4 * (m + 1 + 1) + P) * L ^ (m + 1 + 2)) := by
    have e : t * (2 * ε * Λ * R * Ev) = 2 * ε * Λ * R * (t * Ev) := by ring
    have h1 : R * (t * Ev) ≤ (C₇ * (q ^ (4 * (m + 1 + 1)) * L)) *
        (K_E * (q ^ P * L ^ (m + 1 + 1))) :=
      mul_le_mul hR hEv (by positivity) (by positivity)
    have h2 : (C₇ * (q ^ (4 * (m + 1 + 1)) * L)) * (K_E * (q ^ P * L ^ (m + 1 + 1))) =
        C₇ * K_E * (q ^ (4 * (m + 1 + 1) + P) * L ^ (m + 1 + 2)) := by
      rw [pow_add, pow_succ L (m + 1 + 1)]
      ring
    have hc : 0 ≤ 2 * ε * Λ := by positivity
    calc t * (2 * ε * Λ * R * Ev) = 2 * ε * Λ * (R * (t * Ev)) := by rw [e]; ring
      _ ≤ 2 * ε * Λ * ((C₇ * (q ^ (4 * (m + 1 + 1)) * L)) *
          (K_E * (q ^ P * L ^ (m + 1 + 1)))) := mul_le_mul_of_nonneg_left h1 hc
      _ = 2 * ε * Λ * C₇ * K_E * (q ^ (4 * (m + 1 + 1) + P) * L ^ (m + 1 + 2)) := by
          rw [h2]; ring
  -- `t * Err ≤ θ q^{(4d+7)(d+1)}`
  set θ : ℝ := κ * c₂ ^ (m + 1 + 1) / 2 with hθ
  have hLpow : L ^ (m + 1 + 1) ≤ L ^ (m + 1 + 2) := pow_le_pow_right₀ hL (by omega)
  have hqpow : q ^ (3 * (m + 1 + 1) + P) ≤ q ^ (4 * (m + 1 + 1) + P) :=
    pow_le_pow_right₀ hq (by omega)
  have hQP : 0 ≤ q ^ (3 * (m + 1 + 1) + P) := by positivity
  have hterr : t * (ω * R ^ (m + 1) * δ + 2 * ε * Λ * R * Ev) ≤
      (ω * C₇ ^ (m + 1) * C₄ + 2 * ε * Λ * C₇ * K_E) *
        (q ^ (4 * (m + 1 + 1) + P) * L ^ (m + 1 + 2)) := by
    have h1 : t * (ω * R ^ (m + 1) * δ) ≤
        ω * C₇ ^ (m + 1) * C₄ * (q ^ (4 * (m + 1 + 1) + P) * L ^ (m + 1 + 2)) := by
      calc t * (ω * R ^ (m + 1) * δ)
          ≤ t * (ω * C₇ ^ (m + 1) * C₄ * (q ^ P * L ^ (m + 1 + 1))) :=
            mul_le_mul_of_nonneg_left hT1 ht0.le
        _ = ω * C₇ ^ (m + 1) * C₄ * (q ^ (3 * (m + 1 + 1) + P) * L ^ (m + 1 + 1)) := by
            rw [ht, pow_add]; ring
        _ ≤ ω * C₇ ^ (m + 1) * C₄ * (q ^ (4 * (m + 1 + 1) + P) * L ^ (m + 1 + 2)) := by
            have hc : 0 ≤ ω * C₇ ^ (m + 1) * C₄ := by
              have : 0 ≤ C₄ := by
                by_contra hneg
                have hlt : C₄ < 0 := not_le.mp hneg
                have : C₄ * (q ^ (2 * (m + 1 + 1)) * L) < 0 :=
                  mul_neg_of_neg_of_pos hlt (by positivity)
                linarith
              positivity
            exact mul_le_mul_of_nonneg_left (mul_le_mul hqpow hLpow (by positivity)
              (by positivity)) hc
    calc t * (ω * R ^ (m + 1) * δ + 2 * ε * Λ * R * Ev)
        = t * (ω * R ^ (m + 1) * δ) + t * (2 * ε * Λ * R * Ev) := by ring
      _ ≤ _ := by linarith
  have hsq : q ^ (4 * (m + 1 + 1) + P) * L ^ (m + 1 + 2) *
      (ω * C₇ ^ (m + 1) * C₄ + 2 * ε * Λ * C₇ * K_E) ≤
      q ^ (4 * (m + 1 + 1) + P) * (θ * q ^ (m + 1 + 1)) := by
    have := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ q ^ (4 * (m + 1 + 1) + P))
    linarith
  have e1 : q ^ (4 * (m + 1 + 1) + P) * (θ * q ^ (m + 1 + 1)) =
      t * (θ * s ^ (m + 1 + 1)) := by
    rw [ht, hs, ← pow_mul]
    have : q ^ (4 * (m + 1 + 1) + P) * q ^ (m + 1 + 1) =
        q ^ (3 * (m + 1 + 1)) * q ^ (4 * (m + 1 + 1) * (m + 1 + 1)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      rw [hP]
      ring
    calc q ^ (4 * (m + 1 + 1) + P) * (θ * q ^ (m + 1 + 1))
        = θ * (q ^ (4 * (m + 1 + 1) + P) * q ^ (m + 1 + 1)) := by ring
      _ = θ * (q ^ (3 * (m + 1 + 1)) * q ^ (4 * (m + 1 + 1) * (m + 1 + 1))) := by rw [this]
      _ = q ^ (3 * (m + 1 + 1)) * (θ * q ^ (4 * (m + 1 + 1) * (m + 1 + 1))) := by ring
  have herr : ω * R ^ (m + 1) * δ + 2 * ε * Λ * R * Ev ≤ θ * s ^ (m + 1 + 1) := by
    have h := hterr.trans (by
      calc (ω * C₇ ^ (m + 1) * C₄ + 2 * ε * Λ * C₇ * K_E) *
            (q ^ (4 * (m + 1 + 1) + P) * L ^ (m + 1 + 2))
          = q ^ (4 * (m + 1 + 1) + P) * L ^ (m + 1 + 2) *
            (ω * C₇ ^ (m + 1) * C₄ + 2 * ε * Λ * C₇ * K_E) := by ring
        _ ≤ t * (θ * s ^ (m + 1 + 1)) := by rw [← e1]; exact hsq)
    exact le_of_mul_le_mul_left h ht0
  -- conclude
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hbpow : c₂ ^ (m + 1 + 1) * s ^ (m + 1 + 1) ≤ b ^ (m + 1 + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hc₂.le hs0) hb _
  have hmass' : κ * b ^ (m + 1 + 1) ≤ n + (ω * R ^ (m + 1) * δ + 2 * ε * Λ * R * Ev) := by
    have := (abs_le.mp hmass).1
    linarith
  have h3 : θ * s ^ (m + 1 + 1) ≤ n := by
    have h4 : κ * (c₂ ^ (m + 1 + 1) * s ^ (m + 1 + 1)) ≤ κ * b ^ (m + 1 + 1) :=
      mul_le_mul_of_nonneg_left hbpow hκ.le
    have h5 : κ * (c₂ ^ (m + 1 + 1) * s ^ (m + 1 + 1)) = 2 * (θ * s ^ (m + 1 + 1)) := by
      rw [hθ]; ring
    linarith
  have h6 : (c₂ * s) ^ (m + 1 + 1) ≤ (2 * u) ^ (m + 1 + 1) := by
    have h7 : θ * s ^ (m + 1 + 1) ≤ κ * u ^ (m + 1 + 1) := hnκ ▸ h3
    have h8 : κ * c₂ ^ (m + 1 + 1) * s ^ (m + 1 + 1) ≤ 2 * (κ * u ^ (m + 1 + 1)) := by
      rw [hθ] at h7; linarith
    have h9 : κ * (c₂ * s) ^ (m + 1 + 1) ≤ κ * (2 * u ^ (m + 1 + 1)) := by
      rw [mul_pow]; linarith
    have h10 : (c₂ * s) ^ (m + 1 + 1) ≤ 2 * u ^ (m + 1 + 1) := le_of_mul_le_mul_left h9 hκ
    calc (c₂ * s) ^ (m + 1 + 1) ≤ 2 * u ^ (m + 1 + 1) := h10
      _ ≤ 2 ^ (m + 1 + 1) * u ^ (m + 1 + 1) := by
          gcongr
          exact le_self_pow₀ (by norm_num) (by omega)
      _ = (2 * u) ^ (m + 1 + 1) := (mul_pow 2 u (m + 1 + 1)).symm
  have h11 : c₂ * s ≤ 2 * u :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).mp h6
  rw [le_div_iff₀ hc₂]
  linarith


/-! ## The path-level stages of the coarse bounds -/

/-- **The upper bound for the scale from the inner geometry.** With `s = q^{4(d+1)}`, `q ≥ 2`, the
rough outer bound at the inner radius, the bound `Lb ≤ C₅ q^{4d+2} L` for the local time beyond the
inner radius, the bound for the excess `I`, the layer bound for the volume of the excess, the mass
identity and the smallness of the error terms, one has `c s/4 ≤ b`, `R₀ ≤ b/c + s/8` and
`s ≤ 2 u/c₂` for `c₂ = c/4`. -/
theorem scale_upper {m : ℕ} {q L u s b R₀ δ I Ev Lb n R : ℝ}
    {c κ ω ε Λ W V C_out C₇ C₄ K_I C₅ c₂ K_E K_Err θ : ℝ}
    (hs : s = q ^ (4 * (m + 1 + 1))) (hq : 2 ≤ q) (hL : 1 ≤ L) (hc : 0 < c)
    (hC_out : 0 ≤ C_out) (hcount : s ≤ 2 * R₀ + 1)
    (hrough : R₀ ≤ b / c + C_out * (1 + Lb) * L)
    (hLb : Lb ≤ C₅ * (q ^ (4 * (m + 1) + 2) * L))
    (hsmall₁ : 8 * (C_out * (1 + C₅)) * L ^ 2 ≤ q ^ 2)
    (hV : 0 ≤ V) (hW : 0 < W) (hb0 : 0 ≤ b) (hbW : W * b ≤ q ^ (4 * (m + 1 + 1)))
    (hI : I ≤ K_I * (q ^ (4 * (m + 1) + 2) * L) ^ (m + 1 + 1))
    (hEv : ∀ t : ℝ, 0 < t → Ev ≤ V * ((b + t) ^ (m + 1) - b ^ (m + 1)) + I / t)
    (hK_E : K_E = V * (m + 1) * (W⁻¹ + 1) ^ m + K_I) (hκ : 0 < κ) (hc₂ : c₂ = c / 4)
    (hu : 0 ≤ u) (hnκ : n = κ * u ^ (m + 1 + 1)) (hω : 0 ≤ ω) (hε : 0 ≤ ε) (hΛ : 0 ≤ Λ)
    (hR0 : 0 ≤ R) (hR : R ≤ C₇ * (q ^ (4 * (m + 1 + 1)) * L)) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ C₄ * (q ^ (2 * (m + 1 + 1)) * L)) (hC₇ : 0 ≤ C₇) (hEv0 : 0 ≤ Ev)
    (hmass : |n - κ * b ^ (m + 1 + 1)| ≤ ω * R ^ (m + 1) * δ + 2 * ε * Λ * R * Ev)
    (hK_Err : K_Err = ω * C₇ ^ (m + 1) * C₄ + 2 * ε * Λ * C₇ * K_E)
    (hθ : θ = κ * c₂ ^ (m + 1 + 1) / 2) (hsmall₂ : K_Err * L ^ (m + 1 + 2) ≤ θ * q ^ (m + 1 + 1)) :
    c * s / 4 ≤ b ∧ R₀ ≤ b / c + s / 8 ∧ s ≤ 2 * u / c₂ := by
  have hc₂0 : 0 < c₂ := by rw [hc₂]; positivity
  obtain ⟨hb, hR₀⟩ := inner_radius_lower (m + 1) hq hL hc hC_out hs hcount hrough hLb hsmall₁
  have hq1 : 1 ≤ q := by linarith
  have hEv' := volume_excess_le hq1 hL hV hW hb0 hbW hI hEv
  rw [← hK_E] at hEv'
  have hb' : c₂ * s ≤ b := by rw [hc₂]; linarith
  have hsmall : (ω * C₇ ^ (m + 1) * C₄ + 2 * ε * Λ * C₇ * K_E) * L ^ (m + 1 + 2) ≤
      κ * c₂ ^ (m + 1 + 1) / 2 * q ^ (m + 1 + 1) := by
    rw [← hK_Err, ← hθ]
    exact hsmall₂
  exact ⟨hb, hR₀, scale_card_le hq1 hL hs hκ hc₂0 hu hb' hnκ hω hε hΛ hR0 hR hδ0 hδ hC₇ hEv0 hEv'
    hmass hsmall⟩

/-- A natural number at most `n` has square root at most `n`. -/
theorem sqrt_cast_le_of_le {a n : ℕ} (h : a ≤ n) : Real.sqrt (a : ℝ) ≤ n :=
  Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg _, by
    exact_mod_cast h.trans (Nat.le_self_pow two_ne_zero n)⟩

/-- For `n ≥ 3`, `log n ≥ 1`. -/
theorem one_le_log_of_three_le {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith [Real.exp_one_lt_three]

/-- The inner radius `b` of the cell set satisfies `W b ≤ s` for `W^d = |B_Ψ|` and `s^d = |A_n|`:
the norm ball of radius `b` lies in the cell set. -/
theorem inner_radius_le_scale (hΨ : IsNorm Ψ) (hd : 1 ≤ d) {W s : ℝ} (hW : 0 < W)
    (hWpow : W ^ d = normBallVolume Ψ) (hs0 : 0 ≤ s)
    (x : ℕ → Site d) (n : ℕ) (hspow : s ^ d = ((departureRange x n).card : ℝ)) :
    W * normInnerRadius Ψ x n ≤ s := by
  have hb0 := normInnerRadius_nonneg hΨ x n
  rcases hb0.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact hs0
  · have h := normBallVolume_mul_pow_le_card hΨ hpos (sublevel_subset_cellSet hΨ x n)
    rw [← hspow, ← hWpow, ← mul_pow] at h
    exact (pow_le_pow_iff_left₀ (by positivity) hs0 (by omega)).1 h

/-- The inner radius is below `2 n c_Ψ`, so the contact points lie in `{|y| < 2n}`, as soon as
`s² ≤ n` and `((W c)⁻¹)² ≤ n`. -/
theorem contact_level_lt {W c s n b : ℝ} (hW : 0 < W) (hc : 0 < c) (hn : 0 < n) (hs0 : 0 ≤ s)
    (hs2 : s ^ 2 ≤ n) (hE : ((W * c)⁻¹) ^ 2 ≤ n) (hb : W * b ≤ s) : b < 2 * n * c := by
  have hWc : 0 < W * c := mul_pos hW hc
  have ht0 : 0 ≤ (W * c)⁻¹ := inv_nonneg.mpr hWc.le
  have h1 : (s * (W * c)⁻¹) ^ 2 ≤ n ^ 2 := by
    calc (s * (W * c)⁻¹) ^ 2 = s ^ 2 * ((W * c)⁻¹) ^ 2 := mul_pow _ _ _
      _ ≤ n * n := mul_le_mul hs2 hE (by positivity) hn.le
      _ = n ^ 2 := (sq n).symm
  have h2 : s * (W * c)⁻¹ ≤ n :=
    (pow_le_pow_iff_left₀ (by positivity) hn.le (by norm_num)).1 h1
  have h3 : s ≤ n * (W * c) := by
    have := mul_le_mul_of_nonneg_right h2 hWc.le
    calc s = s * (W * c)⁻¹ * (W * c) := by field_simp
      _ ≤ n * (W * c) := this
  have h4 : W * b ≤ W * (n * c) := by
    calc W * b ≤ s := hb
      _ ≤ n * (W * c) := h3
      _ = W * (n * c) := by ring
  have h5 : b ≤ n * c := le_of_mul_le_mul_left h4 hW
  have : 0 < n * c := mul_pos hn hc
  linarith

/-- The local time beyond the level `b` is at most `B` as soon as the profile of the cell local time
is within `B` of the cone `2 d ε (b - Ψ)_+` everywhere. -/
theorem localTime_filter_le_of_profile (x : ℕ → Site d) (n : ℕ) {b ε B : ℝ}
    (hprof : ∀ y : EuclideanSpace ℝ (Fin d),
      |cellLocalTime x n y - 2 * d * ε * max (b - Ψ y) 0| ≤ B) (hB : 0 ≤ B) :
    ((((departureRange x n).filter (fun z => b ≤ Ψ (toSpace z))).sup (localTime x n) : ℕ) : ℝ) ≤
      B := by
  refine sup_localTime_filter_le hB x n fun z hz => ?_
  have h := hprof (toSpace z)
  rw [CERW.cellLocalTime_of_mem_cell x n (toSpace_mem_cell z), max_eq_right (by linarith),
    mul_zero, sub_zero] at h
  exact (le_abs_self _).trans h

/-- Absorbing the constant of an eventual condition: `(K / c₁) P ≤ u` and `c₁ u ≤ s` give
`K P ≤ s`. -/
theorem scaled_le_scale {K P c₁ u s : ℝ} (hc₁ : 0 < c₁) (h : K / c₁ * P ≤ u)
    (hA : c₁ * u ≤ s) : K * P ≤ s := by
  have := mul_le_mul_of_nonneg_left h hc₁.le
  calc K * P = c₁ * (K / c₁ * P) := by field_simp
    _ ≤ c₁ * u := this
    _ ≤ s := hA

/-- **First stage.** The number of departed sites is at least of order `r_n^d`, the largest local
time is `O(s)` and the farthest radius is `O(s log n)`, where `s = |A_n|^{1/d}`. -/
theorem stage_one (hd1 : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hV : 0 < normBallVolume Ψ)
    {C_L C_out κ c₁ s : ℝ} (hC_L : 0 < C_L) (hC_out : 0 < C_out) (hκ : 0 < κ)
    (hc₁ : c₁ = (κ / (2 * C_L)) ^ ((1 : ℝ) / ((d : ℝ) + 1)))
    (hκdef : κ = 2 * (d : ℝ) * ε * normBallVolume Ψ / ((d : ℝ) + 1))
    {n : ℕ} (hn3 : 3 ≤ n) (x : ℕ → Site d)
    (hs : s = ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / (d : ℝ)))
    (hloc1 : (maxLocalTime x n : ℝ) ≤ C_L * s + C_L * Real.log n ^ 2)
    (hrough : RoughOuter Ψ C_out n x)
    (hE2 : (4 * C_L * c₁ ^ d / κ) * Real.log n ^ 2 ≤ coarseScale Ψ ε n)
    (hE3 : (1 / c₁) * Real.log n ^ 2 ≤ coarseScale Ψ ε n) :
    1 ≤ s ∧ c₁ * coarseScale Ψ ε n ≤ s ∧ (maxLocalTime x n : ℝ) ≤ 2 * C_L * s ∧
      maxRadius x n ≤ C_out * (1 + 2 * C_L) * (s * Real.log n) := by
  have hn1 : 1 ≤ n := by omega
  have hu0 : 0 < coarseScale Ψ ε n := coarseScale_pos hd1 hε hV hn1
  have hS1 : (1 : ℝ) ≤ ((departureRange x n).card : ℝ) := by
    exact_mod_cast one_le_card_departureRange x hn1
  have hs1 : 1 ≤ s := by
    rw [hs]
    exact Real.one_le_rpow hS1 (by positivity)
  have hspow : s ^ d = ((departureRange x n).card : ℝ) := by
    rw [hs, one_div]
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)
  have hnκ : (n : ℝ) = κ * coarseScale Ψ ε n ^ (d + 1) := by
    rw [hκdef]
    exact nat_eq_coarseScale_pow hd1 hε hV n
  have hMn : (n : ℝ) ≤ (maxLocalTime x n : ℝ) * ((departureRange x n).card : ℝ) := by
    exact_mod_cast CERW.Support.Occupation.le_maxLocalTime_mul_card x n
  have hM0 : (0 : ℝ) ≤ (maxLocalTime x n : ℝ) := Nat.cast_nonneg _
  have hc₁0 : 0 < c₁ := by rw [hc₁]; exact Real.rpow_pos_of_pos (by positivity) _
  have hsmall : C_L * Real.log n ^ 2 * c₁ ^ d ≤ κ / 4 * coarseScale Ψ ε n := by
    have h := mul_le_mul_of_nonneg_left hE2 (by positivity : 0 ≤ κ / 4)
    calc C_L * Real.log n ^ 2 * c₁ ^ d
        = κ / 4 * (4 * C_L * c₁ ^ d / κ * Real.log n ^ 2) := by field_simp
      _ ≤ κ / 4 * coarseScale Ψ ε n := h
  have hA : c₁ * coarseScale Ψ ε n ≤ s := by
    rw [hc₁] at hsmall ⊢
    refine scale_le_rpow_card hd1 hκ hC_L hu0 (by linarith) ?_ hloc1 hsmall
    rw [← hnκ, hspow]
    exact hMn
  have hL2 : Real.log n ^ 2 ≤ s := by
    have h := mul_le_mul_of_nonneg_left hE3 hc₁0.le
    have : Real.log n ^ 2 ≤ c₁ * coarseScale Ψ ε n := by
      calc Real.log n ^ 2 = c₁ * (1 / c₁ * Real.log n ^ 2) := by field_simp
        _ ≤ c₁ * coarseScale Ψ ε n := h
    linarith
  have hM : (maxLocalTime x n : ℝ) ≤ 2 * C_L * s := by
    have : C_L * Real.log n ^ 2 ≤ C_L * s := mul_le_mul_of_nonneg_left hL2 hC_L.le
    linarith
  have hsup : ((((departureRange x n).filter (fun z => 0 ≤ Ψ (toSpace z))).sup
      (localTime x n) : ℕ) : ℝ) ≤ (maxLocalTime x n : ℝ) :=
    sup_localTime_filter_le hM0 x n fun z _ => by
      exact_mod_cast CERW.localTime_le_maxLocalTime x n z
  have hR := hrough 0 le_rfl
  rw [zero_div, zero_add] at hR
  refine ⟨hs1, hA, hM, ?_⟩
  have hLog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have h1 : 1 + ((((departureRange x n).filter (fun z => 0 ≤ Ψ (toSpace z))).sup
      (localTime x n) : ℕ) : ℝ) ≤ (1 + 2 * C_L) * s := by nlinarith
  calc maxRadius x n ≤ C_out * (1 + ((((departureRange x n).filter
        (fun z => 0 ≤ Ψ (toSpace z))).sup (localTime x n) : ℕ) : ℝ)) * Real.log n := hR
    _ ≤ C_out * ((1 + 2 * C_L) * s) * Real.log n := by gcongr
    _ = C_out * (1 + 2 * C_L) * (s * Real.log n) := by ring

/-- **The scale of a path.** Fix the constants, as real numbers related by the displayed
equations, and let `x` be a nearest-neighbour path from the origin with the local time event with
constant `C_L` and the rough outer bound for every real level with constant `C_out`, at a time `n`
that satisfies the finitely many conditions `hE₂, …, hE₇` (each says that a constant times a power
of `log n`, or a fixed constant, is at most the scale `r_n` or at most `n`). Let `hIG` be the
inner-geometry statement with constant `C_G`. Then, with `s = |A_n|^{1/d}`: `c₁ r_n ≤ s`,
`s ≤ 2 r_n / c₂`, the largest local time is at most `2 C_L s`, `s ≥ 2` and the farthest radius is at
most `(1/(W c_Ψ) + 1/8) s`. -/
theorem coarse_path {m : ℕ} {Ψ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hd : 2 ≤ m + 1) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hgeom : CERW.Support.Statements.norm_potential_geometry)
    {C_L C_out C_G κ W c₁ C₂ C₃ C₇ C₄ K_I C₅ C₆ c₂ K_E K_Err θ : ℝ}
    (hC_L : 0 < C_L) (hC_out : 0 < C_out) (hC_G : 0 < C_G) (hκ : 0 < κ)
    (hκdef : κ = 2 * ((m + 1 : ℕ) : ℝ) * ε * normBallVolume Ψ / (((m + 1 : ℕ) : ℝ) + 1))
    (hW0 : 0 < W) (hWpow : W ^ (m + 1) = normBallVolume Ψ)
    (hc₁def : c₁ = (κ / (2 * C_L)) ^ ((1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1)))
    (hC₂ : C₂ = 2 * C_L) (hC₃ : C₃ = C_out * (1 + C₂))
    (hC₇ : C₇ = C₃ + Real.sqrt ((m + 1 : ℕ) : ℝ)) (hC₄ : C₄ = C_L * (1 + Real.sqrt C₂))
    (hK_I : K_I = unitBallVolume (m + 1) / (2 * ε) *
      ((1 + normMax Ψ / normMin Ψ) * C₇) ^ (m + 1) * C₄)
    (hC₅ : C₅ = C₄ + C_G * (K_I + 1)) (hC₆ : C₆ = C_out * (1 + C₅)) (hc₂ : c₂ = normMin Ψ / 4)
    (hK_E : K_E = normBallVolume Ψ * ((m : ℝ) + 1) * (W⁻¹ + 1) ^ m + K_I)
    (hK_Err : K_Err = unitBallVolume (m + 1) * C₇ ^ (m + 1) * C₄ +
      2 * ε * normMax Ψ * C₇ * K_E)
    (hθ : θ = κ * c₂ ^ (m + 1 + 1) / 2)
    (hIG : ∀ (X : ℕ → Site (m + 1)) (n : ℕ), X 0 = 0 → 1 ≤ n →
      ∀ {R δ H : ℝ}, cellSet X n ⊆ Metric.ball 0 R →
      (∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) R,
        |cellLocalTime X n y - normPotential (m + 1) ε Ψ (cellSet X n) y| ≤ δ) →
      (∀ y₀ : EuclideanSpace ℝ (Fin (m + 1)), Ψ y₀ = normInnerRadius Ψ X n →
        y₀ ∈ closure (cellSet X n)ᶜ → normPotential (m + 1) ε Ψ (cellSet X n) y₀ ≤ H) →
      0 < normInnerRadius Ψ X n ∧ normInnerRadius Ψ X n ≤ normMax Ψ * R ∧
      0 ≤ (∫ v in cellSet X n \ {v | Ψ v < normInnerRadius Ψ X n},
          (Ψ v - normInnerRadius Ψ X n)) ∧
      ∫ v in cellSet X n \ {v | Ψ v < normInnerRadius Ψ X n},
          (Ψ v - normInnerRadius Ψ X n) ≤
        unitBallVolume (m + 1) / (2 * ε) * ((1 + normMax Ψ / normMin Ψ) * R) ^ (m + 1) * H ∧
      (∀ s : ℝ, 0 < s →
        (volume (cellSet X n \ {v | Ψ v < normInnerRadius Ψ X n})).toReal ≤
          normBallVolume Ψ * ((normInnerRadius Ψ X n + s) ^ (m + 1) -
            normInnerRadius Ψ X n ^ (m + 1)) +
            (∫ v in cellSet X n \ {v | Ψ v < normInnerRadius Ψ X n},
              (Ψ v - normInnerRadius Ψ X n)) / s) ∧
      |(n : ℝ) - 2 * ε * (((m + 1 : ℕ) : ℝ) * normBallVolume Ψ *
          normInnerRadius Ψ X n ^ (m + 1 + 1) / (((m + 1 : ℕ) : ℝ) + 1))| ≤
        unitBallVolume (m + 1) * R ^ (m + 1) * δ + 2 * ε * normMax Ψ * R *
          (volume (cellSet X n \ {v | Ψ v < normInnerRadius Ψ X n})).toReal ∧
      ∀ y : EuclideanSpace ℝ (Fin (m + 1)),
        |cellLocalTime X n y - 2 * ((m + 1 : ℕ) : ℝ) * ε * max (normInnerRadius Ψ X n - Ψ y) 0| ≤
          δ + C_G * (∫ v in cellSet X n \ {v | Ψ v < normInnerRadius Ψ X n},
            (Ψ v - normInnerRadius Ψ X n)) ^ ((1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1)))
    {n : ℕ} (hn4 : m + 4 ≤ n)
    (hE₂ : (4 * C_L * c₁ ^ (m + 1) / κ) * Real.log n ^ 2 ≤ coarseScale Ψ ε n)
    (hE₃ : (1 / c₁) * Real.log n ^ 2 ≤ coarseScale Ψ ε n)
    (hE₄ : (2 ^ (4 * (m + 1 + 1)) / c₁) * Real.log n ^ 0 ≤ coarseScale Ψ ε n)
    (hE₅ : ((8 * C₆) ^ (2 * (m + 1 + 1)) / c₁) * Real.log n ^ (4 * (m + 1 + 1)) ≤
      coarseScale Ψ ε n)
    (hE₆ : ((K_Err / θ) ^ 4 / c₁ + 1) * Real.log n ^ (4 * (m + 1 + 2)) ≤ coarseScale Ψ ε n)
    (hE₇ : ((W * normMin Ψ)⁻¹) ^ 2 ≤ (n : ℝ))
    {x : ℕ → Site (m + 1)} (hx0 : x 0 = 0) (hstep : ∀ j, x (j + 1) - x j ∈ unitSteps (m + 1))
    (hloc : LocalTimeEvent Ψ ε C_L n x) (hrough : RoughOuter Ψ C_out n x) :
    c₁ * coarseScale Ψ ε n ≤ ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) ∧
    ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) ≤
      2 * coarseScale Ψ ε n / c₂ ∧
    (maxLocalTime x n : ℝ) ≤
      2 * C_L * ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) ∧
    2 ≤ ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) ∧
    maxRadius x n ≤ (1 / (W * normMin Ψ) + 1 / 8) *
      ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
  have hd1 : 1 ≤ m + 1 := by omega
  obtain ⟨hc0, -⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hcΛ : normMin Ψ ≤ normMax Ψ :=
    CERW.Support.Norm.ContactAssembly.normMin_le_normMax hd1 hΨ
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc0 hcΛ
  have hV : 0 < normBallVolume Ψ :=
    CERW.Support.Norm.ContactAssembly.normBallVolume_pos' hd1 hΨ
  have hω : 0 < unitBallVolume (m + 1) := unitBallVolume_pos _
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hL1 : 1 ≤ Real.log n := one_le_log_of_three_le hn3
  have hC₂0 : 0 < C₂ := by rw [hC₂]; positivity
  have hC₃0 : 0 < C₃ := by rw [hC₃]; positivity
  have hC₇0 : 0 < C₇ := by rw [hC₇]; positivity
  have hC₄0 : 0 < C₄ := by rw [hC₄]; positivity
  have hK_I0 : 0 ≤ K_I := by rw [hK_I]; positivity
  have hC₅0 : 0 < C₅ := by rw [hC₅]; positivity
  have hC₆0 : 0 < C₆ := by rw [hC₆]; positivity
  have hc₂0 : 0 < c₂ := by rw [hc₂]; positivity
  have hK_E0 : 0 ≤ K_E := by rw [hK_E]; positivity
  have hK_Err0 : 0 ≤ K_Err := by rw [hK_Err]; positivity
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hc₁0 : 0 < c₁ := by rw [hc₁def]; exact Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨hloc1, -, hloc3⟩ := hloc
  obtain ⟨s, hs⟩ : ∃ s : ℝ,
      s = ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) := ⟨_, rfl⟩
  rw [← hs]
  have hloc1' : (maxLocalTime x n : ℝ) ≤ C_L * s + C_L * Real.log n ^ 2 := by
    rw [hs]
    exact hloc1
  obtain ⟨hs1, hA, hM, hRad⟩ :=
    stage_one hd1 hε hV hC_L hC_out hκ hc₁def hκdef hn3 x hs hloc1' hrough hE₂ hE₃
  have hRad' : maxRadius x n ≤ C₃ * (s * Real.log n) := by
    rw [hC₃, hC₂]
    exact hRad
  have hspow : s ^ (m + 1) = ((departureRange x n).card : ℝ) := by
    rw [hs, one_div]
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)
  have hnκ : (n : ℝ) = κ * coarseScale Ψ ε n ^ (m + 1 + 1) := by
    rw [hκdef]
    exact nat_eq_coarseScale_pow hd1 hε hV n
  -- the fourth root of the number of departed sites
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = s ^ (((4 * (m + 1 + 1) : ℕ) : ℝ)⁻¹) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact Real.rpow_nonneg (by linarith) _
  have hqs : q ^ (4 * (m + 1 + 1)) = s := by
    rw [hq]
    exact Real.rpow_inv_natCast_pow (by linarith) (by omega)
  have hq2 : 2 ≤ q := by
    have h := scaled_le_scale hc₁0 hE₄ hA
    rw [pow_zero, mul_one, ← hqs] at h
    exact (pow_le_pow_iff_left₀ (by norm_num) hq0 (by omega)).1 h
  have hq1 : 1 ≤ q := by linarith
  have hs2' : 2 ≤ s := by
    rw [← hqs]
    calc (2 : ℝ) ≤ q ^ 1 := by rw [pow_one]; exact hq2
      _ ≤ q ^ (4 * (m + 1 + 1)) := pow_le_pow_right₀ hq1 (by omega)
  have hsmall₁ : 8 * (C_out * (1 + C₅)) * Real.log n ^ 2 ≤ q ^ 2 := by
    have h := scaled_le_scale hc₁0 hE₅ hA
    rw [← hqs] at h
    have h2 : (8 * C₆ * Real.log n ^ 2) ^ (2 * (m + 1 + 1)) ≤ (q ^ 2) ^ (2 * (m + 1 + 1)) := by
      calc (8 * C₆ * Real.log n ^ 2) ^ (2 * (m + 1 + 1))
          = (8 * C₆) ^ (2 * (m + 1 + 1)) * Real.log n ^ (4 * (m + 1 + 1)) := by
            rw [mul_pow, ← pow_mul]
            ring
        _ ≤ q ^ (4 * (m + 1 + 1)) := h
        _ = (q ^ 2) ^ (2 * (m + 1 + 1)) := by
            rw [← pow_mul]
            ring
    have h3 := (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).1 h2
    rw [hC₆] at h3
    exact h3
  have hsmall₂ : K_Err * Real.log n ^ (m + 1 + 2) ≤ θ * q ^ (m + 1 + 1) := by
    have hLk : 0 ≤ Real.log n ^ (4 * (m + 1 + 2)) := by positivity
    have h' : (K_Err / θ) ^ 4 / c₁ * Real.log n ^ (4 * (m + 1 + 2)) ≤ coarseScale Ψ ε n := by
      refine le_trans ?_ hE₆
      exact mul_le_mul_of_nonneg_right (by linarith) hLk
    have h := scaled_le_scale hc₁0 h' hA
    rw [← hqs] at h
    have h2 : (K_Err / θ * Real.log n ^ (m + 1 + 2)) ^ 4 ≤ (q ^ (m + 1 + 1)) ^ 4 := by
      calc (K_Err / θ * Real.log n ^ (m + 1 + 2)) ^ 4
          = (K_Err / θ) ^ 4 * Real.log n ^ (4 * (m + 1 + 2)) := by
            rw [mul_pow, ← pow_mul]
            ring
        _ ≤ q ^ (4 * (m + 1 + 1)) := h
        _ = (q ^ (m + 1 + 1)) ^ 4 := by
            rw [← pow_mul]
            ring
    have h3 := (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h2
    rw [div_mul_eq_mul_div, div_le_iff₀ hθ0] at h3
    linarith
  -- the contact bound
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = maxRadius x n + Real.sqrt ((m + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hDR : cellSet x n ⊆ Metric.ball 0 R := by
    rw [hRdef]
    exact CERW.Support.Occupation.cellSet_subset_ball hd1 x n
  have hR2n : R ≤ 2 * n := by
    have h1 : maxRadius x n ≤ n := CERW.Support.Occupation.maxRadius_le_of_steps x hx0 hstep n
    have h2 := sqrt_cast_le_of_le (a := m + 1) (n := n) (by omega)
    rw [hRdef]
    linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = C_L * Real.log n + C_L *
      (if m + 1 = 2 then Real.sqrt (maxLocalTime x n) * Real.log n
        else Real.sqrt (maxLocalTime x n * Real.log n)) := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by
    rw [hδdef]
    split_ifs <;> positivity
  have happrox : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ ≤ 2 * n →
      |cellLocalTime x n y - normPotential (m + 1) ε Ψ (cellSet x n) y| ≤ δ := by
    intro y hy
    rw [hδdef]
    exact hloc3 y hy
  have hWb : W * normInnerRadius Ψ x n ≤ s :=
    inner_radius_le_scale hΨ hd1 hW0 hWpow (by linarith) x n hspow
  have hs2n : s ^ 2 ≤ (n : ℝ) := by
    calc s ^ 2 ≤ s ^ (m + 1) := pow_le_pow_right₀ hs1 hd
      _ = ((departureRange x n).card : ℝ) := hspow
      _ ≤ n := by exact_mod_cast CERW.Support.Occupation.card_departureRange_le x n
  have hb : normInnerRadius Ψ x n < 2 * n * normMin Ψ :=
    contact_level_lt hW0 hc0 (by exact_mod_cast hn1) (by linarith) hs2n hE₇ hWb
  have hcon := contact_potential_le hd hΨ hε hgeom hDR happrox hb
  obtain ⟨hb0, -, hI0, hIle, hvol, hmass, hprof⟩ :=
    hIG x n hx0 hn1 hDR (fun y hy => happrox y (by
      have := mem_ball_zero_iff.mp hy
      linarith)) hcon
  -- the numerical bounds
  have hsL : 1 ≤ s * Real.log n := one_le_mul_of_one_le_of_one_le hs1 hL1
  have hR : R ≤ C₇ * (q ^ (4 * (m + 1 + 1)) * Real.log n) := by
    rw [hqs, hC₇, hRdef]
    have h1 : Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) * (s * Real.log n) :=
      le_mul_of_one_le_right (Real.sqrt_nonneg _) hsL
    calc maxRadius x n + Real.sqrt ((m + 1 : ℕ) : ℝ)
        ≤ C₃ * (s * Real.log n) + Real.sqrt ((m + 1 : ℕ) : ℝ) * (s * Real.log n) :=
          add_le_add hRad' h1
      _ = (C₃ + Real.sqrt ((m + 1 : ℕ) : ℝ)) * (s * Real.log n) := by ring
  have hcount : s ≤ 2 * maxRadius x n + 1 := by
    rw [hs]
    exact rpow_card_le hd1 x n
  have hmr0 : 0 ≤ maxRadius x n := by linarith
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hMq : (maxLocalTime x n : ℝ) ≤ C₂ * q ^ (4 * (m + 1 + 1)) := by
    rw [hqs, hC₂]
    exact hM
  have hδ : δ ≤ C₄ * (q ^ (2 * (m + 1 + 1)) * Real.log n) := by
    have := delta_le (m + 1) hq1 hL1 hC_L.le hC₂0.le hMq hδdef.le
    rw [hC₄]
    exact this
  have hIex := excess_le (m + 1) hq1 hL1 (by positivity) (by positivity) hR0 hδ0 hC₇0.le hR hδ hIle
  have hI' : (∫ v in cellSet x n \ {v | Ψ v < normInnerRadius Ψ x n},
      (Ψ v - normInnerRadius Ψ x n)) ≤
      K_I * (q ^ (4 * (m + 1) + 2) * Real.log n) ^ (m + 1 + 1) := by
    rw [hK_I]
    exact hIex
  have hB0 : 0 ≤ δ + C_G * (∫ v in cellSet x n \ {v | Ψ v < normInnerRadius Ψ x n},
      (Ψ v - normInnerRadius Ψ x n)) ^ ((1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1)) :=
    add_nonneg hδ0 (mul_nonneg hC_G.le (Real.rpow_nonneg hI0 _))
  have hLbprof := localTime_filter_le_of_profile x n hprof hB0
  have hLb := localTime_beyond_le (m + 1) hq1 hL1 hI0 hK_I0 hC_G.le hC₄0.le hLbprof hδ hI'
  rw [← hC₅] at hLb
  have hrb := hrough (normInnerRadius Ψ x n) hb0.le
  have hmass' : |(n : ℝ) - κ * normInnerRadius Ψ x n ^ (m + 1 + 1)| ≤
      unitBallVolume (m + 1) * R ^ (m + 1) * δ + 2 * ε * normMax Ψ * R *
        (volume (cellSet x n \ {v | Ψ v < normInnerRadius Ψ x n})).toReal := by
    have e : 2 * ε * (((m + 1 : ℕ) : ℝ) * normBallVolume Ψ *
        normInnerRadius Ψ x n ^ (m + 1 + 1) / (((m + 1 : ℕ) : ℝ) + 1)) =
        κ * normInnerRadius Ψ x n ^ (m + 1 + 1) := by
      rw [hκdef]
      ring
    rw [e] at hmass
    exact hmass
  obtain ⟨-, hR₀, hscale⟩ := scale_upper hqs.symm hq2 hL1 hc0 hC_out.le hcount hrb hLb hsmall₁
    hV.le hW0 hb0.le (by rw [hqs]; exact hWb) hI' hvol hK_E hκ hc₂ (coarseScale_nonneg hε hV n)
    hnκ hω.le hε.le hΛ.le hR0 hR hδ0 hδ hC₇0.le ENNReal.toReal_nonneg hmass' hK_Err hθ hsmall₂
  refine ⟨hA, hscale, hM, hs2', ?_⟩
  have hbs : normInnerRadius Ψ x n ≤ s / W := by
    rw [le_div_iff₀ hW0]
    linarith
  have hbc : normInnerRadius Ψ x n / normMin Ψ ≤ 1 / (W * normMin Ψ) * s := by
    calc normInnerRadius Ψ x n / normMin Ψ ≤ s / W / normMin Ψ :=
          div_le_div_of_nonneg_right hbs hc0.le
      _ = 1 / (W * normMin Ψ) * s := by field_simp
  calc maxRadius x n ≤ normInnerRadius Ψ x n / normMin Ψ + s / 8 := hR₀
    _ ≤ 1 / (W * normMin Ψ) * s + s / 8 := by linarith
    _ = (1 / (W * normMin Ψ) + 1 / 8) * s := by ring

/-- **The six bounds from the scale facts.** The bounds `c₁ u ≤ s ≤ 2 u/c₂`, `M ≤ 2 C_L s`,
`s ≥ 2`, `R₀ ≤ (1/(W c) + 1/8) s`, `s ≤ 2 R₀ + 1`, the identities `s^d = |A_n|` and
`n = κ u^{d+1}` and `n ≤ M |A_n|` give the six bounds with the constants `c_f`, `C_f`. -/
theorem final_bounds {d : ℕ} {u s S M R₀ n κ C_L c₂ W c c₁ c_f C_f : ℝ} (hu : 0 < u)
    (hC_L : 0 < C_L) (hc₂ : 0 < c₂) (hc₁ : 0 < c₁) (hM0 : 0 ≤ M) (hspow : s ^ d = S)
    (hnκ : n = κ * u ^ (d + 1)) (hMn : n ≤ M * S) (hA : c₁ * u ≤ s) (hB : s ≤ 2 * u / c₂)
    (hM : M ≤ 2 * C_L * s) (hs2 : 2 ≤ s) (hR : R₀ ≤ (1 / (W * c) + 1 / 8) * s)
    (hcount : s ≤ 2 * R₀ + 1)
    (hc_f : c_f = min (min (c₁ ^ d) (κ * (c₂ / 2) ^ d)) (c₁ / 4))
    (hC_f : C_f = max (max ((2 / c₂) ^ d + 1) (2 * C_L * (2 / c₂) + 1))
      ((1 / (W * c) + 1 / 8) * (2 / c₂) + 1))
    (hWc : 0 ≤ 1 / (W * c)) :
    c_f * u ^ d ≤ S ∧ S ≤ C_f * u ^ d ∧ c_f * u ≤ M ∧ M ≤ C_f * u ∧ c_f * u ≤ R₀ ∧
      R₀ ≤ C_f * u := by
  have hcf1 : c_f ≤ c₁ ^ d := by rw [hc_f]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hcf2 : c_f ≤ κ * (c₂ / 2) ^ d := by
    rw [hc_f]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hcf3 : c_f ≤ c₁ / 4 := by rw [hc_f]; exact min_le_right _ _
  have hCf1 : (2 / c₂) ^ d + 1 ≤ C_f := by
    rw [hC_f]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hCf2 : 2 * C_L * (2 / c₂) + 1 ≤ C_f := by
    rw [hC_f]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hCf3 : (1 / (W * c) + 1 / 8) * (2 / c₂) + 1 ≤ C_f := by rw [hC_f]; exact le_max_right _ _
  have hud : 0 < u ^ d := pow_pos hu d
  have hs0 : 0 ≤ s := by linarith
  have e2 : 2 * u / c₂ = 2 / c₂ * u := by ring
  have hSle : s ^ d ≤ (2 / c₂) ^ d * u ^ d := by
    calc s ^ d ≤ (2 * u / c₂) ^ d := pow_le_pow_left₀ hs0 hB d
      _ = (2 / c₂) ^ d * u ^ d := by rw [e2, mul_pow]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc c_f * u ^ d ≤ c₁ ^ d * u ^ d := mul_le_mul_of_nonneg_right hcf1 hud.le
      _ = (c₁ * u) ^ d := (mul_pow _ _ _).symm
      _ ≤ s ^ d := pow_le_pow_left₀ (by positivity) hA d
      _ = S := hspow
  · calc S = s ^ d := hspow.symm
      _ ≤ (2 / c₂) ^ d * u ^ d := hSle
      _ ≤ C_f * u ^ d := mul_le_mul_of_nonneg_right (by linarith) hud.le
  · have h1 : κ * u ^ (d + 1) ≤ M * ((2 / c₂) ^ d * u ^ d) := by
      calc κ * u ^ (d + 1) = n := hnκ.symm
        _ ≤ M * S := hMn
        _ = M * s ^ d := by rw [hspow]
        _ ≤ M * ((2 / c₂) ^ d * u ^ d) := mul_le_mul_of_nonneg_left hSle hM0
    have h2 : κ * u ≤ M * (2 / c₂) ^ d := by
      have : (κ * u) * u ^ d ≤ (M * (2 / c₂) ^ d) * u ^ d := by
        calc (κ * u) * u ^ d = κ * u ^ (d + 1) := by ring
          _ ≤ M * ((2 / c₂) ^ d * u ^ d) := h1
          _ = (M * (2 / c₂) ^ d) * u ^ d := by ring
      exact le_of_mul_le_mul_right this hud
    have hp : (c₂ / 2) ^ d * (2 / c₂) ^ d = 1 := by
      have : c₂ / 2 * (2 / c₂) = 1 := by field_simp
      rw [← mul_pow, this, one_pow]
    have h3 : κ * (c₂ / 2) ^ d * u ≤ M := by
      calc κ * (c₂ / 2) ^ d * u = (c₂ / 2) ^ d * (κ * u) := by ring
        _ ≤ (c₂ / 2) ^ d * (M * (2 / c₂) ^ d) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = M * ((c₂ / 2) ^ d * (2 / c₂) ^ d) := by ring
        _ = M := by rw [hp, mul_one]
    exact (mul_le_mul_of_nonneg_right hcf2 hu.le).trans h3
  · calc M ≤ 2 * C_L * s := hM
      _ ≤ 2 * C_L * (2 / c₂ * u) := by
          rw [← e2]
          exact mul_le_mul_of_nonneg_left hB (by positivity)
      _ = (2 * C_L * (2 / c₂)) * u := by ring
      _ ≤ C_f * u := mul_le_mul_of_nonneg_right (by linarith) hu.le
  · have h1 : c_f * u ≤ c₁ / 4 * u := mul_le_mul_of_nonneg_right hcf3 hu.le
    have h2 : c₁ / 4 * u = c₁ * u / 4 := by ring
    linarith
  · have hK : 0 ≤ 1 / (W * c) + 1 / 8 := by positivity
    calc R₀ ≤ (1 / (W * c) + 1 / 8) * s := hR
      _ ≤ (1 / (W * c) + 1 / 8) * (2 / c₂ * u) := by
          rw [← e2]
          exact mul_le_mul_of_nonneg_left hB hK
      _ = ((1 / (W * c) + 1 / 8) * (2 / c₂)) * u := by ring
      _ ≤ C_f * u := mul_le_mul_of_nonneg_right (by linarith) hu.le

/-! ## The deterministic coarse bounds -/

/-- **The coarse bounds of a path.** Let `Ψ` be a norm on `ℝ^{m+1}` with `m + 1 ≥ 2`, `ε > 0`, and
let `C_L`, `C_out` be positive constants. There are `c, C > 0` and `n₀` such that, for every
`n ≥ n₀` and every nearest-neighbour path from the origin that satisfies the local time event
`LocalTimeEvent` with constant `C_L` and the rough outer bound `RoughOuter` for every real level
with constant `C_out`, the number of departed sites, the largest local time and the largest radius
are all of order `r_n^d`, `r_n`, `r_n`, with constants `c` and `C`. The geometry enters only
through the norm ball, layer and potential statements `hball`, `hlayer`, `hgeom`, used through
`inner_geometry`; no coarse, radial or Moreau estimate is used. -/
theorem coarse_deterministic {m : ℕ} {Ψ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hd : 2 ≤ m + 1) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hball : CERW.Support.Statements.norm_ball_potential)
    (hlayer : CERW.Support.Statements.layer_potential)
    (hgeom : CERW.Support.Statements.norm_potential_geometry) {C_L C_out : ℝ}
    (hC_L : 0 < C_L) (hC_out : 0 < C_out) :
    ∃ c C : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, n₀ ≤ n → ∀ x : ℕ → Site (m + 1), x 0 = 0 →
      (∀ j, x (j + 1) - x j ∈ unitSteps (m + 1)) → LocalTimeEvent Ψ ε C_L n x →
      RoughOuter Ψ C_out n x →
      c * coarseScale Ψ ε n ^ (m + 1) ≤ ((departureRange x n).card : ℝ) ∧
      ((departureRange x n).card : ℝ) ≤ C * coarseScale Ψ ε n ^ (m + 1) ∧
      c * coarseScale Ψ ε n ≤ (maxLocalTime x n : ℝ) ∧
      (maxLocalTime x n : ℝ) ≤ C * coarseScale Ψ ε n ∧
      c * coarseScale Ψ ε n ≤ maxRadius x n ∧ maxRadius x n ≤ C * coarseScale Ψ ε n := by
  have hd1 : 1 ≤ m + 1 := by omega
  obtain ⟨hc0, hcle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hcΛ : normMin Ψ ≤ normMax Ψ :=
    CERW.Support.Norm.ContactAssembly.normMin_le_normMax hd1 hΨ
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc0 hcΛ
  have hV : 0 < normBallVolume Ψ :=
    CERW.Support.Norm.ContactAssembly.normBallVolume_pos' hd1 hΨ
  have hω : 0 < unitBallVolume (m + 1) := unitBallVolume_pos _
  obtain ⟨C_G, hC_G, hIG⟩ := inner_geometry hd hΨ hε hball hlayer hgeom
  have hdR0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 2 * ((m + 1 : ℕ) : ℝ) * ε * normBallVolume Ψ /
      (((m + 1 : ℕ) : ℝ) + 1) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; positivity
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = normBallVolume Ψ ^ (((m + 1 : ℕ) : ℝ)⁻¹) := ⟨_, rfl⟩
  have hW0 : 0 < W := by rw [hWdef]; exact Real.rpow_pos_of_pos hV _
  have hWpow : W ^ (m + 1) = normBallVolume Ψ := by
    rw [hWdef]; exact Real.rpow_inv_natCast_pow hV.le (by omega)
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : ℝ, c₁ = (κ / (2 * C_L)) ^ ((1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1)) :=
    ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁def]; exact Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = 2 * C_L := ⟨_, rfl⟩
  obtain ⟨C₃, hC₃⟩ : ∃ C₃ : ℝ, C₃ = C_out * (1 + C₂) := ⟨_, rfl⟩
  obtain ⟨C₇, hC₇⟩ : ∃ C₇ : ℝ, C₇ = C₃ + Real.sqrt ((m + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨C₄, hC₄⟩ : ∃ C₄ : ℝ, C₄ = C_L * (1 + Real.sqrt C₂) := ⟨_, rfl⟩
  have hC₂0 : 0 < C₂ := by rw [hC₂]; positivity
  have hC₃0 : 0 < C₃ := by rw [hC₃]; positivity
  have hC₇0 : 0 < C₇ := by rw [hC₇]; positivity
  have hC₄0 : 0 < C₄ := by rw [hC₄]; positivity
  obtain ⟨K_I, hK_I⟩ : ∃ K_I : ℝ, K_I = unitBallVolume (m + 1) / (2 * ε) *
      ((1 + normMax Ψ / normMin Ψ) * C₇) ^ (m + 1) * C₄ := ⟨_, rfl⟩
  have hK_I0 : 0 ≤ K_I := by rw [hK_I]; positivity
  obtain ⟨C₅, hC₅⟩ : ∃ C₅ : ℝ, C₅ = C₄ + C_G * (K_I + 1) := ⟨_, rfl⟩
  have hC₅0 : 0 < C₅ := by rw [hC₅]; positivity
  obtain ⟨C₆, hC₆⟩ : ∃ C₆ : ℝ, C₆ = C_out * (1 + C₅) := ⟨_, rfl⟩
  have hC₆0 : 0 < C₆ := by rw [hC₆]; positivity
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℝ, c₂ = normMin Ψ / 4 := ⟨_, rfl⟩
  have hc₂0 : 0 < c₂ := by rw [hc₂]; positivity
  obtain ⟨K_E, hK_E⟩ : ∃ K_E : ℝ, K_E = normBallVolume Ψ * ((m : ℝ) + 1) * (W⁻¹ + 1) ^ m + K_I :=
    ⟨_, rfl⟩
  have hK_E0 : 0 ≤ K_E := by rw [hK_E]; positivity
  obtain ⟨K_Err, hK_Err⟩ : ∃ K_Err : ℝ, K_Err = unitBallVolume (m + 1) * C₇ ^ (m + 1) * C₄ +
      2 * ε * normMax Ψ * C₇ * K_E := ⟨_, rfl⟩
  have hK_Err0 : 0 ≤ K_Err := by rw [hK_Err]; positivity
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = κ * c₂ ^ (m + 1 + 1) / 2 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  -- the final constants
  obtain ⟨c_f, hc_f⟩ : ∃ c_f : ℝ, c_f = min (min (c₁ ^ (m + 1)) (κ * (c₂ / 2) ^ (m + 1)))
      (c₁ / 4) := ⟨_, rfl⟩
  obtain ⟨C_f, hC_f⟩ : ∃ C_f : ℝ, C_f = max (max ((2 / c₂) ^ (m + 1) + 1)
      (2 * C_L * (2 / c₂) + 1)) ((1 / (W * normMin Ψ) + 1 / 8) * (2 / c₂) + 1) := ⟨_, rfl⟩
  have hc_f0 : 0 < c_f := by rw [hc_f]; positivity
  have hC_f0 : 0 < C_f := by
    rw [hC_f]
    exact lt_max_of_lt_left (lt_max_of_lt_left (by positivity))
  -- the conditions on `n`
  have hev : ∀ᶠ n : ℕ in atTop, m + 4 ≤ n ∧
      (4 * C_L * c₁ ^ (m + 1) / κ) * Real.log n ^ 2 ≤ coarseScale Ψ ε n ∧
      (1 / c₁) * Real.log n ^ 2 ≤ coarseScale Ψ ε n ∧
      (2 ^ (4 * (m + 1 + 1)) / c₁) * Real.log n ^ 0 ≤ coarseScale Ψ ε n ∧
      ((8 * C₆) ^ (2 * (m + 1 + 1)) / c₁) * Real.log n ^ (4 * (m + 1 + 1)) ≤
        coarseScale Ψ ε n ∧
      ((K_Err / θ) ^ 4 / c₁ + 1) * Real.log n ^ (4 * (m + 1 + 2)) ≤ coarseScale Ψ ε n ∧
      ((W * normMin Ψ)⁻¹) ^ 2 ≤ (n : ℝ) := by
    have e1 := eventually_mul_log_pow_le_coarseScale (Ψ := Ψ) hd1 hε hV
      (K := 4 * C_L * c₁ ^ (m + 1) / κ) (by positivity) 2
    have e2 := eventually_mul_log_pow_le_coarseScale (Ψ := Ψ) hd1 hε hV
      (K := 1 / c₁) (by positivity) 2
    have e3 := eventually_mul_log_pow_le_coarseScale (Ψ := Ψ) hd1 hε hV
      (K := 2 ^ (4 * (m + 1 + 1)) / c₁) (by positivity) 0
    have e4 := eventually_mul_log_pow_le_coarseScale (Ψ := Ψ) hd1 hε hV
      (K := (8 * C₆) ^ (2 * (m + 1 + 1)) / c₁) (by positivity) (4 * (m + 1 + 1))
    have hKθ : 0 < (K_Err / θ) ^ 4 / c₁ + 1 := by positivity
    have e5 := eventually_mul_log_pow_le_coarseScale (Ψ := Ψ) hd1 hε hV
      (K := (K_Err / θ) ^ 4 / c₁ + 1) hKθ (4 * (m + 1 + 2))
    have e6 : ∀ᶠ n : ℕ in atTop, ((W * normMin Ψ)⁻¹) ^ 2 ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
        (eventually_ge_atTop (((W * normMin Ψ)⁻¹) ^ 2))
    filter_upwards [eventually_ge_atTop (m + 4), e1, e2, e3, e4, e5, e6] with n h0 h1 h2 h3 h4 h5 h6
    exact ⟨h0, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  refine ⟨c_f, C_f, n₀, hc_f0, hC_f0, ?_⟩
  intro n hn x hx0 hstep hloc hrough
  obtain ⟨hn4, hE₂, hE₃, hE₄, hE₅, hE₆, hE₇⟩ := hn₀ n hn
  have hn1 : 1 ≤ n := by omega
  have hu0 : 0 < coarseScale Ψ ε n := coarseScale_pos hd1 hε hV hn1
  obtain ⟨hA, hB, hM, hs2, hR⟩ := coarse_path hd hΨ hε hgeom hC_L hC_out hC_G hκ hκdef hW0 hWpow
    hc₁def hC₂ hC₃ hC₇ hC₄ hK_I hC₅ hC₆ hc₂ hK_E hK_Err hθ hIG hn4 hE₂ hE₃ hE₄ hE₅ hE₆ hE₇ hx0 hstep
    hloc hrough
  obtain ⟨s, hs⟩ : ∃ s : ℝ,
      s = ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) := ⟨_, rfl⟩
  rw [← hs] at hA hB hM hs2 hR
  have hspow : s ^ (m + 1) = ((departureRange x n).card : ℝ) := by
    rw [hs, one_div]
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)
  have hnκ : (n : ℝ) = κ * coarseScale Ψ ε n ^ (m + 1 + 1) := by
    rw [hκdef]
    exact nat_eq_coarseScale_pow hd1 hε hV n
  have hMn : (n : ℝ) ≤ (maxLocalTime x n : ℝ) * ((departureRange x n).card : ℝ) := by
    exact_mod_cast CERW.Support.Occupation.le_maxLocalTime_mul_card x n
  have hcount : s ≤ 2 * maxRadius x n + 1 := by
    rw [hs]
    exact rpow_card_le hd1 x n
  have hWc : 0 ≤ 1 / (W * normMin Ψ) := by positivity
  exact final_bounds hu0 hC_L hc₂0 hc₁0 (Nat.cast_nonneg _) hspow hnκ hMn hA hB hM hs2 hR hcount
    hc_f hC_f hWc

/-! ## The probability bound -/

/-- **The coarse bounds, from the cap event.** The statement `norm_coarse_bounds` (the six bounds
for the number of departed sites, the largest local time and the largest radius, with
probability at least `1 - C n^{-p}`) follows from the local time potential lemma `hlocal`, the
norm ball, layer and potential geometry statements `hball`, `hlayer`, `hgeom`, the cap event of
`CoarseCapEvents` and the deterministic bounds `coarse_deterministic`. The constants `c`, `C` are
chosen before the field of subgradients, the probability space, the walk and `n`. No radial test,
old coarse bound or Moreau envelope is used. -/
theorem norm_coarse_bounds_of_cap (hlocal : CERW.Support.Statements.norm_local_time_potential.{u})
    (hball : CERW.Support.Statements.norm_ball_potential)
    (hlayer : CERW.Support.Statements.layer_potential)
    (hgeom : CERW.Support.Statements.norm_potential_geometry) :
    CERW.Support.Statements.norm_coarse_bounds.{u} := by
  intro d hd Ψ hΨ ε hε hell r p hp
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  obtain ⟨C_V, C_M, C_L, C₁, hC_V, hC_L, hC₁, hev⟩ :=
    exists_cap_local_failure_bound hlocal hd hΨ hε hell hp
  obtain ⟨C_out, hC_out, hrough⟩ := exists_rough_outer_of_capEvent hd hΨ hε hell (C_M := C_M) hC_V
  obtain ⟨c, C, n₀, hc, hC, hdet⟩ := coarse_deterministic hd hΨ hε hball hlayer hgeom hC_L hC_out
  have hV : 0 < normBallVolume Ψ :=
    CERW.Support.Norm.ContactAssembly.normBallVolume_pos' (by omega) hΨ
  have hn₀p : 0 ≤ (n₀ : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨c, max C (C₁ + (n₀ : ℝ) ^ p), hc, lt_max_of_lt_left hC, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  by_cases hn₀le : n₀ ≤ n
  · refine le_trans (measure_mono fun ω hω => ?_)
      ((hev ξ hξ hξ0 μ X hX n hn).trans (ENNReal.ofReal_le_ofReal ?_))
    · intro hcap
      apply hω
      obtain ⟨hcapE, hloc⟩ := hcap
      obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hdet n hn₀le (fun j => X j ω) hcapE.1 hcapE.2.1 hloc
        (hrough ξ hξ hξ0 n hn (fun j => X j ω) hcapE)
      have hr0 : 0 ≤ coarseScale Ψ ε n := coarseScale_nonneg hε hV n
      have hCm : C ≤ max C (C₁ + (n₀ : ℝ) ^ p) := le_max_left _ _
      exact ⟨h₁, h₂.trans (mul_le_mul_of_nonneg_right hCm (pow_nonneg hr0 _)), h₃,
        h₄.trans (mul_le_mul_of_nonneg_right hCm hr0), h₅,
        h₆.trans (mul_le_mul_of_nonneg_right hCm hr0)⟩
    · refine mul_le_mul_of_nonneg_right ?_ hnp
      exact le_max_of_le_right (by linarith)
  · rw [not_le] at hn₀le
    refine le_trans prob_le_one ?_
    rw [ENNReal.one_le_ofReal]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h1 : (n : ℝ) ^ p ≤ (n₀ : ℝ) ^ p :=
      Real.rpow_le_rpow hnpos.le (by exact_mod_cast hn₀le.le) hp.le
    have h2 : 1 ≤ (n₀ : ℝ) ^ p * (n : ℝ) ^ (-p) := by
      rw [Real.rpow_neg hnpos.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hnpos p)]
      exact h1
    calc (1 : ℝ) ≤ (n₀ : ℝ) ^ p * (n : ℝ) ^ (-p) := h2
      _ ≤ max C (C₁ + (n₀ : ℝ) ^ p) * (n : ℝ) ^ (-p) :=
        mul_le_mul_of_nonneg_right (le_max_of_le_right (by linarith)) hnp

/-- The closed form of the coarse bounds: the statement `norm_coarse_bounds`, from the proved
local time potential lemma and the proved norm ball, layer and potential geometry statements, by
the cap event argument. -/
theorem norm_coarse_bounds_closed : CERW.Support.Statements.norm_coarse_bounds.{u} :=
  norm_coarse_bounds_of_cap.{u}
    (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds)
    @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.layer_potential
    @CERW.Support.Norm.norm_potential_geometry

end CERW.Support.Norm.CoarseVolume
