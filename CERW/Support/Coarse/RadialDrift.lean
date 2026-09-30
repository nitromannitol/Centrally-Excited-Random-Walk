import CERW.Support.Law.StepMean
import CERW.Model.Potential
import CERW.Support.Occupation.Facts
import LatticeProb.Walk.ExteriorDirichlet

/-!
# The drift of the radial test

For a level `h` and the radial test `φ = (b - h)_+`, suppose `b ≤ h` on `|x| ≤ r - 1` and
`b ≥ h` on `|x| ≥ r + 1` (`eq:levelsets`). Every increment of `φ` then vanishes from
`|x| ≤ r - 2`. For `|x| > r + 3`, `φ = b - h` at `x` and its neighbours, so
`(P - I)φ(x) = (P - I)b(x) = 0`. There, `eq:gradient` gives
`u_x · Dφ(x) ≥ (2/ω_d)|x|^{1-d} - C|x|^{-d} ≥ ω_d⁻¹ |x|^{1-d}` for large `|x|`
(`eq:radial-drift`).
Everywhere, the positive part is `1`-Lipschitz, so the increments of `φ` are at most those of `b`.
-/

namespace CERW.Support.Coarse

open LatticeProb CERW CERW.Support.Law

variable {d : ℕ}

/-- When `b y ≤ h`, the positive part `(b y - h)_+` vanishes. -/
private lemma max_sub_eq_zero_of_nonpos {b : Site d → ℝ} {h : ℝ} {y : Site d}
    (hy : b y ≤ h) : max (b y - h) 0 = 0 :=
  max_eq_right (sub_nonpos.mpr hy)

/-- When `h ≤ b y`, the positive part `(b y - h)_+` equals `b y - h`. -/
private lemma max_sub_eq_self_of_le {b : Site d → ℝ} {h : ℝ} {y : Site d}
    (hy : h ≤ b y) : max (b y - h) 0 = b y - h :=
  max_eq_left (sub_nonneg.mpr hy)

/-- A forward unit step moves a site by at most one in Euclidean norm. -/
private lemma le_euclidNorm_add_unit (x : Site d) (i : Fin d) :
    euclidNorm x - 1 ≤ euclidNorm (x + unit i) := by
  have h := CERW.Support.Occupation.euclidNorm_add_le (x + unit i) (-unit i)
  have he : euclidNorm (-unit i) = 1 :=
    euclidNorm_of_mem_unitSteps (mem_unitSteps.mpr ⟨i, Or.inr rfl⟩)
  have hx : x + unit i + -unit i = x := by abel
  rw [hx, he] at h
  linarith

/-- A backward unit step moves a site by at most one in Euclidean norm. -/
private lemma le_euclidNorm_sub_unit (x : Site d) (i : Fin d) :
    euclidNorm x - 1 ≤ euclidNorm (x - unit i) := by
  have h := CERW.Support.Occupation.euclidNorm_add_le (x - unit i) (unit i)
  have he : euclidNorm (unit i) = 1 :=
    euclidNorm_of_mem_unitSteps (mem_unitSteps.mpr ⟨i, Or.inl rfl⟩)
  have hx : x - unit i + unit i = x := by abel
  rw [hx, he] at h
  linarith

/-- For positive `ρ`, `ρ ^ (1 - d) = ρ * ρ ^ (-d)`. -/
private lemma rpow_one_sub_eq_mul {ρ : ℝ} (hρ : 0 < ρ) (d : ℕ) :
    ρ ^ (1 - (d : ℝ)) = ρ * ρ ^ (-(d : ℝ)) := by
  have h : ρ ^ (1 + -(d : ℝ)) = ρ * ρ ^ (-(d : ℝ)) := by
    rw [Real.rpow_add hρ, Real.rpow_one]
  exact h

/-- For positive `ρ`, `(c / ω / ρ ^ d) * ρ = (c / ω) * ρ ^ (1 - d)`. -/
private lemma mul_div_pow_eq_mul_rpow (c ρ ω : ℝ) (hρ : 0 < ρ) (d : ℕ) :
    (c / ω / ρ ^ d) * ρ = (c / ω) * ρ ^ (1 - (d : ℝ)) := by
  rw [Real.rpow_sub hρ, Real.rpow_one, Real.rpow_natCast]
  ring

/-- If `Ca * ω ≤ ρ` with `ρ, ω > 0`, then `Ca * ρ ^ (-d) ≤ ω⁻¹ * ρ ^ (1 - d)`. -/
private lemma mul_rpow_neg_le_of_mul_le {ρ ω Ca : ℝ} (hρ : 0 < ρ) (hω : 0 < ω)
    (hC : Ca * ω ≤ ρ) (d : ℕ) :
    Ca * ρ ^ (-(d : ℝ)) ≤ ω⁻¹ * ρ ^ (1 - (d : ℝ)) := by
  have hCa : Ca ≤ ρ * ω⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hC (le_of_lt (inv_pos.mpr hω))
    rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hω), mul_one] at h
  have hA : 0 ≤ ρ ^ (-(d : ℝ)) := Real.rpow_nonneg (le_of_lt hρ) _
  calc Ca * ρ ^ (-(d : ℝ))
      ≤ (ρ * ω⁻¹) * ρ ^ (-(d : ℝ)) := mul_le_mul_of_nonneg_right hCa hA
    _ = ω⁻¹ * (ρ * ρ ^ (-(d : ℝ))) := by ring
    _ = ω⁻¹ * ρ ^ (1 - (d : ℝ)) := by rw [rpow_one_sub_eq_mul hρ d]

/-- The numerical inequality `ω⁻¹ ρ ^ (1 - d) ≤ (2/ω) ρ ^ (1 - d) - Ca ρ ^ (-d)`. -/
private lemma drift_numeric_bound {ρ ω Ca : ℝ} (hρ : 0 < ρ) (hω : 0 < ω)
    (hC : Ca * ω ≤ ρ) (d : ℕ) :
    ω⁻¹ * ρ ^ (1 - (d : ℝ)) ≤
      (2 / ω) * ρ ^ (1 - (d : ℝ)) - Ca * ρ ^ (-(d : ℝ)) := by
  have hkey := mul_rpow_neg_le_of_mul_le hρ hω hC d
  calc ω⁻¹ * ρ ^ (1 - (d : ℝ))
      = (2 / ω) * ρ ^ (1 - (d : ℝ)) - ω⁻¹ * ρ ^ (1 - (d : ℝ)) := by ring
    _ ≤ (2 / ω) * ρ ^ (1 - (d : ℝ)) - Ca * ρ ^ (-(d : ℝ)) := by linarith

/-- The radial-drift lower bound: if `v = (2/ω/ρ^d) • t + w` with
`‖w‖ ≤ Ca ρ ^ (-d)`, then
`inner u_t v ≥ (2/ω) ρ ^ (1 - d) - Ca ρ ^ (-d)`, where `u_t` is the direction of `t`. -/
private lemma inner_sub_const_lower_bound {t v w : EuclideanSpace ℝ (Fin d)} {ρ Ca : ℝ}
    (hρ : 0 < ρ) (ht : ‖t‖ = ρ)
    (hv : v = (2 / unitBallVolume d / ρ ^ d) • t + w)
    (hw : ‖w‖ ≤ Ca * ρ ^ (-(d : ℝ))) :
    (2 / unitBallVolume d) * ρ ^ (1 - (d : ℝ)) - Ca * ρ ^ (-(d : ℝ)) ≤
      inner ℝ (unitDir t) v := by
  have habs : |inner ℝ (unitDir t) w| ≤ Ca * ρ ^ (-(d : ℝ)) :=
    (abs_real_inner_le_norm (unitDir t) w).trans <| by
      calc ‖unitDir t‖ * ‖w‖ ≤ 1 * ‖w‖ :=
            mul_le_mul_of_nonneg_right (norm_unitDir_le t) (norm_nonneg w)
        _ = ‖w‖ := one_mul _
        _ ≤ Ca * ρ ^ (-(d : ℝ)) := hw
  have hwle : -Ca * ρ ^ (-(d : ℝ)) ≤ inner ℝ (unitDir t) w := by
    have := neg_abs_le (inner ℝ (unitDir t) w)
    linarith
  have hinner_t : inner ℝ (unitDir t) t = ρ := by
    rw [unitDir, real_inner_smul_left, real_inner_self_eq_norm_sq, ht, sq, ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt hρ), one_mul]
  have hfirst : inner ℝ (unitDir t) ((2 / unitBallVolume d / ρ ^ d) • t) =
      (2 / unitBallVolume d) * ρ ^ (1 - (d : ℝ)) := by
    rw [real_inner_smul_right, hinner_t,
      mul_div_pow_eq_mul_rpow 2 ρ (unitBallVolume d) hρ d]
  rw [hv, inner_add_right, hfirst]
  linarith

/-- The increments of `(b - h)_+` are at most those of `b`. -/
theorem abs_max_sub_add_sub_le (b : Site d → ℝ) (h : ℝ) (x e : Site d) :
    |max (b (x + e) - h) 0 - max (b x - h) 0| ≤ |b (x + e) - b x| := by
  have hsub : (b (x + e) - h) - (b x - h) = b (x + e) - b x := by ring
  have := abs_max_sub_max_le_abs (b (x + e) - h) (b x - h) (0 : ℝ)
  rwa [hsub] at this

/-- Inside: if `b ≤ h` on `|x| ≤ r - 1`, then `(b - h)_+` vanishes at every site with
`|x| ≤ r - 2` and at its neighbours. -/
theorem max_sub_eq_zero_of_le {b : Site d → ℝ} {h r : ℝ}
    (hin : ∀ x, euclidNorm x ≤ r - 1 → b x ≤ h) {x : Site d} (hx : euclidNorm x ≤ r - 2)
    {e : Site d} (he : e ∈ unitSteps d) :
    max (b (x + e) - h) 0 = 0 ∧ max (b x - h) 0 = 0 := by
  have he1 : euclidNorm e = 1 := euclidNorm_of_mem_unitSteps he
  have hxe : euclidNorm (x + e) ≤ r - 1 := by
    calc euclidNorm (x + e) ≤ euclidNorm x + euclidNorm e :=
          CERW.Support.Occupation.euclidNorm_add_le x e
      _ = euclidNorm x + 1 := by rw [he1]
      _ ≤ r - 2 + 1 := by linarith
      _ = r - 1 := by ring
  have hx1 : euclidNorm x ≤ r - 1 := by linarith
  exact ⟨max_sub_eq_zero_of_nonpos (hin (x + e) hxe),
    max_sub_eq_zero_of_nonpos (hin x hx1)⟩

/-- Outside, `eq:radial-drift`: if `b ≥ h` on `|x| ≥ r + 1` with `r ≥ 0`,
`(P - I) b = 1_{0}`, and
`|Db(x) - (2/ω_d) x/|x|^d| ≤ C_a |x|^{-d}` for `|x| ≥ R`, then at every `x` with `|x| > r + 3`,
`|x| ≥ R` and `|x| ≥ C_a ω_d`: `(P - I)(b - h)_+(x) = 0` and
`u_x · D(b - h)_+(x) ≥ ω_d⁻¹ |x|^{1-d}`. -/
theorem radial_drift {b : Site d → ℝ} {h r R Ca : ℝ} (hd : 1 ≤ d) (hr : 0 ≤ r)
    (hout : ∀ x, r + 1 ≤ euclidNorm x → h ≤ b x)
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0)
    (hgrad : ∀ x, R ≤ euclidNorm x →
      ‖centralDiff b x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x‖ ≤
        Ca * euclidNorm x ^ (-(d : ℝ)))
    {x : Site d} (hx : r + 3 < euclidNorm x) (hxR : R ≤ euclidNorm x)
    (hxC : Ca * unitBallVolume d ≤ euclidNorm x) :
    walkOp (fun z => max (b z - h) 0) x - max (b x - h) 0 = 0 ∧
      (unitBallVolume d)⁻¹ * euclidNorm x ^ (1 - (d : ℝ)) ≤
        inner ℝ (unitDir (toSpace x)) (centralDiff (fun z => max (b z - h) 0) x) := by
  have hρ : 0 < euclidNorm x := by linarith [hx, hr]
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at hx
    simp [euclidNorm] at hx
    linarith
  have hφx : max (b x - h) 0 = b x - h := max_sub_eq_self_of_le (hout x (by linarith))
  have hφnbr : ∀ i : Fin d,
      max (b (x + unit i) - h) 0 = b (x + unit i) - h ∧
      max (b (x - unit i) - h) 0 = b (x - unit i) - h := by
    intro i
    have h1 : r + 1 ≤ euclidNorm (x + unit i) := by
      have := le_euclidNorm_add_unit x i
      linarith
    have h2 : r + 1 ≤ euclidNorm (x - unit i) := by
      have := le_euclidNorm_sub_unit x i
      linarith
    exact ⟨max_sub_eq_self_of_le (hout _ h1), max_sub_eq_self_of_le (hout _ h2)⟩
  have hwalk : walkOp (fun z => max (b z - h) 0) x = walkOp b x - h := by
    have h1 : walkOp (fun z => max (b z - h) 0) x = walkOp (fun z => b z - h) x := by
      simp only [walkOp, nbrSum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [(hφnbr i).1, (hφnbr i).2]
    have h2 : walkOp (fun z => b z - h) x = walkOp b x - h := by
      rw [walkOp_sub, walkOp_const hd h x]
    exact h1.trans h2
  have hzero : walkOp (fun z => max (b z - h) 0) x - max (b x - h) 0 = 0 := by
    rw [hwalk, hφx]
    have hb0 : walkOp b x - b x = 0 := by
      have := hb x
      rwa [if_neg hx0] at this
    linarith
  have hcd : centralDiff (fun z => max (b z - h) 0) x = centralDiff b x := by
    have h1 : centralDiff (fun z => max (b z - h) 0) x =
        centralDiff (fun z => b z - h) x := by
      apply PiLp.ext
      intro i
      simp only [centralDiff, PiLp.toLp_apply]
      rw [(hφnbr i).1, (hφnbr i).2]
    have h2 : centralDiff (fun z => b z - h) x = centralDiff b x := by
      apply PiLp.ext
      intro i
      simp only [centralDiff, PiLp.toLp_apply]
      ring
    exact h1.trans h2
  refine ⟨hzero, ?_⟩
  rw [hcd]
  have hmain : (2 / unitBallVolume d) * euclidNorm x ^ (1 - (d : ℝ)) -
      Ca * euclidNorm x ^ (-(d : ℝ)) ≤
      inner ℝ (unitDir (toSpace x)) (centralDiff b x) :=
    inner_sub_const_lower_bound (t := toSpace x) (ρ := euclidNorm x)
      (v := centralDiff b x)
      (w := centralDiff b x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x)
      hρ (norm_toSpace x) (by abel) (hgrad x hxR)
  have hnum := drift_numeric_bound (ρ := euclidNorm x) (ω := unitBallVolume d) (Ca := Ca)
    hρ (unitBallVolume_pos d) hxC d
  exact hnum.trans hmain

end CERW.Support.Coarse
