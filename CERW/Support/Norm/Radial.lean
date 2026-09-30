import CERW.Support.Statements
import CERW.Support.LocalTime.KernelAsymptotics
import CERW.Support.LocalTime.Bracket
import CERW.Support.Coarse.RadialDrift
import CERW.Support.Coarse.TailLower
import CERW.Support.Coarse.ShellCount
import CERW.Support.Drift.Dynkin
import CERW.Support.Drift.Bridge
import CERW.Support.Norm.Freedman
import CERW.Generic.Norm.Sphere
import CERW.Generic.Norm.Subgradient
import CERW.Support.Law.ScaleArith
import CERW.Support.Occupation.FreshSum
import CERW.Support.Occupation.CellWeight
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Geometry.TailBasic

/-!
# The radial test for the walk with a drift field

`lem:radial` for the walk with drift field `ξ`, the subgradients of a norm `Ψ`. The test function
is `φ_ρ = (b - h(ρ))_+` for the potential kernel `b` of the simple random walk. Its drift at a
first departure from `x` with `|x| > ρ + 3` is `ξ(x) · Dφ_ρ(x) ≥ c |x|^{1-d}`, because
`ξ(x) · x = Ψ(x) ≥ c_Ψ |x|` and `|ξ(x)| ≤ Λ_Ψ`. The Dynkin formula bounds the tail `F(ρ + 4d)`
by the local times on the shell and the Dynkin martingale of `φ_ρ`. The bracket of this
martingale only sees the sites beyond `ρ - 2`, so the largest local time in the bound is taken
over the departure sites with `|x| ≥ ρ - 4d`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm

open CERW.Support.Statements
open LatticeProb Finset CERW CERW.Support.Law CERW.Support.Drift CERW.Support.Occupation
  CERW.Support.Coarse CERW.Support.LocalTime

variable {d : ℕ}

/-! ### Facts about the subgradients -/

/-- The largest value of a norm on the unit sphere is nonnegative. -/
private lemma normMax_nonneg {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) :
    0 ≤ normMax Ψ :=
  Real.sSup_nonneg (by
    rintro _ ⟨u, -, rfl⟩
    exact (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 u)

/-- A subgradient of a norm `Ψ` has Euclidean norm at most `Λ_Ψ`. -/
private lemma norm_subgradient_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {x ξ : EuclideanSpace ℝ (Fin d)} (h : IsSubgradient Ψ x ξ) : ‖ξ‖ ≤ normMax Ψ := by
  have h1 := (CERW.Generic.Norm.subgradient_euler hΨ h).2 ξ
  have h2 := CERW.Generic.Norm.le_normMax_mul hΨ ξ
  rw [real_inner_self_eq_norm_sq] at h1
  have h3 : ‖ξ‖ * ‖ξ‖ ≤ normMax Ψ * ‖ξ‖ := by
    rw [← sq]
    exact h1.trans h2
  rcases (norm_nonneg ξ).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact normMax_nonneg hΨ
  · exact le_of_mul_le_mul_right h3 hpos

/-- The drift field of a norm satisfies the ellipticity bound `ε |ξ_i(z)| ≤ 1/d`. -/
private lemma drift_coord_bound {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {ε : ℝ}
    (hε : 0 < ε) (hεΨ : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0) :
    ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ) := by
  intro z i
  by_cases hz : z = 0
  · rw [hz, hξ0]
    simp
  · have h1 := CERW.Generic.Norm.subgradient_abs_coord_le hΨ (hξ z hz) i
    exact ((mul_le_mul_of_nonneg_left h1 hε.le).trans (hεΨ i).le)

/-- Euler's relation with `c_Ψ`: `ξ(x) · x ≥ c_Ψ |x|` at every site. -/
private lemma euler_lower {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    (x : Site d) : normMin Ψ * euclidNorm x ≤ inner ℝ (ξ x) (toSpace x) := by
  by_cases hx : x = 0
  · rw [hx, hξ0, inner_zero_left, euclidNorm_zero, mul_zero]
  · rw [(CERW.Generic.Norm.subgradient_euler hΨ (hξ x hx)).1, ← norm_toSpace]
    exact (CERW.Generic.Norm.normMin_pos_mul_le hΨ hd).2 _

/-- Every value of the drift field has norm at most `Λ_Ψ`. -/
private lemma norm_field_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    (x : Site d) : ‖ξ x‖ ≤ normMax Ψ := by
  by_cases hx : x = 0
  · rw [hx, hξ0, norm_zero]
    exact normMax_nonneg hΨ
  · exact norm_subgradient_le hΨ (hξ x hx)

/-! ### The drift of the radial test -/

/-- A unit step moves a site by at most one in Euclidean norm. -/
private lemma sub_one_le_euclidNorm_add {x e : Site d} (he : e ∈ unitSteps d) :
    euclidNorm x - 1 ≤ euclidNorm (x + e) := by
  have hne : -e ∈ unitSteps d := by
    obtain ⟨i, rfl | rfl⟩ := mem_unitSteps.mp he
    · exact mem_unitSteps.mpr ⟨i, Or.inr rfl⟩
    · exact mem_unitSteps.mpr ⟨i, Or.inl (neg_neg _)⟩
  have h := euclidNorm_add_le (x + e) (-e)
  have hx : x + e + -e = x := by abel
  rw [hx, euclidNorm_of_mem_unitSteps hne] at h
  linarith

/-- For positive `ρ`, `ρ ^ (1 - d) = ρ * ρ ^ (-d)`. -/
private lemma rpow_one_sub_eq_mul {ρ : ℝ} (hρ : 0 < ρ) :
    ρ ^ (1 - (d : ℝ)) = ρ * ρ ^ (-(d : ℝ)) := by
  rw [sub_eq_add_neg, Real.rpow_add hρ, Real.rpow_one]

/-- For positive `ρ`, `(ρ ^ d)⁻¹ = ρ ^ (-d)`. -/
private lemma inv_pow_eq_rpow_neg {ρ : ℝ} (hρ : 0 < ρ) :
    (ρ ^ d)⁻¹ = ρ ^ (-(d : ℝ)) := by
  rw [Real.rpow_neg hρ.le, Real.rpow_natCast]

/-- Beyond the shell, `(P - I) φ = 0` and the drift `ξ(x) · Dφ(x)` of the radial test
`φ = (b - h)_+` is at least `c_Ψ ω_d⁻¹ |x|^{1-d}`, where `ξ(x) · x ≥ c_Ψ |x|` and
`|ξ(x)| ≤ Λ`. -/
private lemma radial_drift_field {b : Site d → ℝ} {h r R Ca cΨ Λ : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hd : 1 ≤ d) (hr : 0 ≤ r)
    (hEuler : ∀ x, cΨ * euclidNorm x ≤ inner ℝ (ξ x) (toSpace x))
    (hnorm : ∀ x, ‖ξ x‖ ≤ Λ)
    (hout : ∀ x, r + 1 ≤ euclidNorm x → h ≤ b x)
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0)
    (hgrad : ∀ x, R ≤ euclidNorm x →
      ‖centralDiff b x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x‖ ≤
        Ca * euclidNorm x ^ (-(d : ℝ)))
    {x : Site d} (hx : r + 3 < euclidNorm x) (hxR : R ≤ euclidNorm x)
    (hxC : Λ * Ca * unitBallVolume d ≤ cΨ * euclidNorm x) :
    walkOp (fun z => max (b z - h) 0) x - max (b x - h) 0 = 0 ∧
      cΨ * (unitBallVolume d)⁻¹ * euclidNorm x ^ (1 - (d : ℝ)) ≤
        inner ℝ (ξ x) (centralDiff (fun z => max (b z - h) 0) x) := by
  have hρ : 0 < euclidNorm x := by linarith
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, euclidNorm_zero] at hx
    linarith
  have hφx : max (b x - h) 0 = b x - h :=
    max_eq_left (sub_nonneg.mpr (hout x (by linarith)))
  have hφnbr : ∀ i : Fin d,
      max (b (x + unit i) - h) 0 = b (x + unit i) - h ∧
      max (b (x - unit i) - h) 0 = b (x - unit i) - h := by
    intro i
    have h1 : r + 1 ≤ euclidNorm (x + unit i) := by
      have := sub_one_le_euclidNorm_add (x := x) (mem_unitSteps.mpr ⟨i, Or.inl rfl⟩)
      linarith
    have h2 : r + 1 ≤ euclidNorm (x - unit i) := by
      have := sub_one_le_euclidNorm_add (x := x) (mem_unitSteps.mpr ⟨i, Or.inr rfl⟩)
      rw [← sub_eq_add_neg] at this
      linarith
    exact ⟨max_eq_left (sub_nonneg.mpr (hout _ h1)), max_eq_left (sub_nonneg.mpr (hout _ h2))⟩
  have hwalk : walkOp (fun z => max (b z - h) 0) x = walkOp b x - h := by
    have h1 : walkOp (fun z => max (b z - h) 0) x = walkOp (fun z => b z - h) x := by
      simp only [walkOp, nbrSum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(hφnbr i).1, (hφnbr i).2]
    rw [h1, walkOp_sub, walkOp_const hd h x]
  have hzero : walkOp (fun z => max (b z - h) 0) x - max (b x - h) 0 = 0 := by
    rw [hwalk, hφx]
    have hb0 : walkOp b x - b x = 0 := by
      have := hb x
      rwa [if_neg hx0] at this
    linarith
  have hcd : centralDiff (fun z => max (b z - h) 0) x = centralDiff b x := by
    apply PiLp.ext
    intro i
    simp only [centralDiff, PiLp.toLp_apply]
    rw [(hφnbr i).1, (hφnbr i).2]
    ring
  refine ⟨hzero, ?_⟩
  rw [hcd]
  set ρ : ℝ := euclidNorm x with hρdef
  set ω : ℝ := unitBallVolume d with hωdef
  set u : ℝ := ρ ^ (-(d : ℝ)) with hu
  set w : EuclideanSpace ℝ (Fin d) :=
    centralDiff b x - (2 / ω / ρ ^ d) • toSpace x with hw
  have hu0 : 0 ≤ u := Real.rpow_nonneg hρ.le _
  have hdec : centralDiff b x = (2 / ω / ρ ^ d) • toSpace x + w := by
    rw [hw]
    abel
  have hcoef : 2 / ω / ρ ^ d = 2 / ω * u := by
    rw [hu, ← inv_pow_eq_rpow_neg hρ]
    field_simp
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hnorm x)
  have hwn : ‖w‖ ≤ Ca * u := hgrad x hxR
  have habs : |inner ℝ (ξ x) w| ≤ Λ * (Ca * u) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hnorm x) hwn (norm_nonneg _) hΛ0)
  have hwlow : -(Λ * (Ca * u)) ≤ inner ℝ (ξ x) w := by
    have := neg_abs_le (inner ℝ (ξ x) w)
    linarith
  have hfirst : 2 / ω * u * (cΨ * ρ) ≤ inner ℝ (ξ x) ((2 / ω / ρ ^ d) • toSpace x) := by
    rw [real_inner_smul_right, hcoef]
    exact mul_le_mul_of_nonneg_left (hEuler x) (by positivity)
  have hC : Λ * Ca ≤ cΨ * ρ / ω := (le_div_iff₀ hω).mpr hxC
  have hC' : Λ * (Ca * u) ≤ cΨ * ρ / ω * u := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hC hu0
  rw [hdec, inner_add_right, rpow_one_sub_eq_mul hρ]
  have hkey : cΨ * ω⁻¹ * (ρ * u) = cΨ * ρ / ω * u := by
    field_simp
  have h2 : 2 / ω * u * (cΨ * ρ) = 2 * (cΨ * ρ / ω * u) := by
    field_simp
  rw [hkey]
  linarith

/-! ### The source inequality -/

/-- The radial power is antitone past the exponent `1 - d ≤ 0`. -/
private lemma rpow_one_sub_le_of_le {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (hd : 1 ≤ d) :
    c ^ (1 - (d : ℝ)) ≤ a ^ (1 - (d : ℝ)) :=
  Real.rpow_le_rpow_of_nonpos ha hac (by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith)

/-- On the shell, a one-step increment of `(b - h)_+` is at most `Cg (r - 1)^(1 - d)`. -/
private lemma max_sub_increment_le {b : Site d → ℝ} {h Cg r : ℝ} (hd : 1 ≤ d) (hr : 2 ≤ r)
    (hCg : 0 ≤ Cg)
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {x : Site d} (hx : r - 2 < euclidNorm x) {e : Site d} (he : e ∈ unitSteps d) :
    |max (b (x + e) - h) 0 - max (b x - h) 0| ≤ Cg * (r - 1) ^ (1 - (d : ℝ)) := by
  have hr1 : 0 < r - 1 := by linarith
  have hx1 : r - 1 ≤ 1 + euclidNorm x := by linarith
  have hpow : (1 + euclidNorm x) ^ (1 - (d : ℝ)) ≤ (r - 1) ^ (1 - (d : ℝ)) :=
    rpow_one_sub_le_of_le hr1 hx1 hd
  calc |max (b (x + e) - h) 0 - max (b x - h) 0|
      ≤ |b (x + e) - b x| := abs_max_sub_add_sub_le b h x e
    _ ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)) := hgrad x e he
    _ ≤ Cg * (r - 1) ^ (1 - (d : ℝ)) := mul_le_mul_of_nonneg_left hpow hCg

/-- If every neighbour value of `f` at `x` agrees with `f x` within `c`, then the walk operator
applied at `x` is within `c` of `f x`. -/
private lemma abs_walkOp_sub_le {f : Site d → ℝ} {x : Site d} {c : ℝ} (hd : 1 ≤ d)
    (h : ∀ e ∈ unitSteps d, |f (x + e) - f x| ≤ c) : |walkOp f x - f x| ≤ c := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have h2d : (0 : ℝ) < 2 * d := by positivity
  have hrepr : walkOp f x - f x = walkOp (fun y => f y - f x) x := by
    rw [walkOp_sub, walkOp_const hd]
  rw [hrepr, walkOp, nbrSum, abs_div, abs_of_pos h2d, div_le_iff₀ h2d]
  calc |∑ i : Fin d, ((f (x + unit i) - f x) + (f (x - unit i) - f x))|
      ≤ ∑ i : Fin d, |(f (x + unit i) - f x) + (f (x - unit i) - f x)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (c + c) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (abs_add_le _ _).trans ?_
        exact add_le_add (h (unit i) (mem_unitSteps.mpr ⟨i, Or.inl rfl⟩))
          (h (-unit i) (mem_unitSteps.mpr ⟨i, Or.inr rfl⟩))
    _ = c * (2 * (d : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Each coordinate of the central difference is at most `c` when every one-step increment of
`f` is at most `c`. -/
private lemma abs_centralDiff_coord_le {f : Site d → ℝ} {x : Site d} {c : ℝ}
    (h : ∀ e ∈ unitSteps d, |f (x + e) - f x| ≤ c) (i : Fin d) :
    ‖(centralDiff f x) i‖ ≤ c := by
  have h1 : |f (x + unit i) - f x| ≤ c := h (unit i) (mem_unitSteps.mpr ⟨i, Or.inl rfl⟩)
  have h2 : |f (x - unit i) - f x| ≤ c := h (-unit i) (mem_unitSteps.mpr ⟨i, Or.inr rfl⟩)
  have htri : |(f (x + unit i) - f x) - (f (x - unit i) - f x)| ≤ 2 * c := by
    have h := abs_sub_le (f (x + unit i) - f x) 0 (f (x - unit i) - f x)
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith
  have hcoord : (centralDiff f x) i =
      ((f (x + unit i) - f x) - (f (x - unit i) - f x)) / 2 := by
    simp only [centralDiff, PiLp.toLp_apply]
    ring
  rw [hcoord, Real.norm_eq_abs, abs_div]
  have h2abs : |(2 : ℝ)| = 2 := by norm_num
  rw [h2abs]
  linarith

/-- The norm of the central difference is at most `√d c` when every coordinate is at most `c`. -/
private lemma norm_centralDiff_le {f : Site d → ℝ} {x : Site d} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i : Fin d, ‖(centralDiff f x) i‖ ≤ c) :
    ‖centralDiff f x‖ ≤ Real.sqrt d * c := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ i : Fin d, ‖(centralDiff f x) i‖ ^ 2)
      ≤ √(∑ _i : Fin d, c ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
    _ = √((d : ℝ) * c ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = Real.sqrt d * c := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hc]

/-- The first-departure drift term at a shell site is at most `ε Λ √d c`. -/
private lemma abs_smul_inner_field_le {f : Site d → ℝ} {x : Site d} {c ε Λ : ℝ}
    {v : EuclideanSpace ℝ (Fin d)} (hε : 0 ≤ ε) (hc : 0 ≤ c) (hv : ‖v‖ ≤ Λ)
    (h : ∀ i : Fin d, ‖(centralDiff f x) i‖ ≤ c) :
    |ε * inner ℝ v (centralDiff f x)| ≤ ε * Λ * Real.sqrt d * c := by
  have hnorm := norm_centralDiff_le hc h
  have hinner : |inner ℝ v (centralDiff f x)| ≤ Λ * (Real.sqrt d * c) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul hv hnorm (norm_nonneg _) ((norm_nonneg _).trans hv))
  calc |ε * inner ℝ v (centralDiff f x)|
      = ε * |inner ℝ v (centralDiff f x)| := by rw [abs_mul, abs_of_nonneg hε]
    _ ≤ ε * (Λ * (Real.sqrt d * c)) := mul_le_mul_of_nonneg_left hinner hε
    _ = ε * Λ * Real.sqrt d * c := by ring

/-- An `if`-then-zero is bounded by the bound on the branch value. -/
private lemma abs_ite_le_of_abs_le {P : Prop} [Decidable P] {A B : ℝ} (hA : |A| ≤ B)
    (hB : 0 ≤ B) : |(if P then A else 0)| ≤ B := by
  split_ifs with h
  · exact hA
  · simpa using hB

/-- If all neighbours of a function vanish at `x`, its walk operator vanishes there. -/
private lemma walkOp_eq_zero_of_nbr_eq_zero {f : Site d → ℝ} {x : Site d}
    (h : ∀ i : Fin d, f (x + unit i) = 0 ∧ f (x - unit i) = 0) : walkOp f x = 0 := by
  rw [walkOp, nbrSum]
  have hsum : (∑ i : Fin d, (f (x + unit i) + f (x - unit i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [(h i).1, (h i).2, add_zero]
  rw [hsum, zero_div]

/-- If a function has equal values on the forward and backward neighbours of `x`, its central
difference vanishes there. -/
private lemma centralDiff_eq_zero_of_nbr {f : Site d → ℝ} {x : Site d}
    (h : ∀ i : Fin d, f (x + unit i) = f (x - unit i)) : centralDiff f x = 0 := by
  apply PiLp.ext
  intro i
  simp only [centralDiff, PiLp.toLp_apply]
  rw [h i, sub_self, zero_div]
  rfl

/-- `eq:radial-source`, pathwise, for a path from the origin and a drift field `ξ` with
`ξ(x) · x ≥ c_Ψ |x|` and `|ξ(x)| ≤ Λ`. -/
private theorem radial_source_field {b : Site d → ℝ} {h r R Ca Cg ε cΨ Λ : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hd : 1 ≤ d) (hr : 2 ≤ r) (hε : 0 ≤ ε)
    (hcΨ : 0 ≤ cΨ) (hEuler : ∀ x, cΨ * euclidNorm x ≤ inner ℝ (ξ x) (toSpace x))
    (hnorm : ∀ x, ‖ξ x‖ ≤ Λ) (hin : ∀ x, euclidNorm x ≤ r - 1 → b x ≤ h)
    (hout : ∀ x, r + 1 ≤ euclidNorm x → h ≤ b x)
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0)
    (hgradA : ∀ x, R ≤ euclidNorm x →
      ‖centralDiff b x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x‖ ≤
        Ca * euclidNorm x ^ (-(d : ℝ)))
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (hR : R ≤ r + 3) (hCa : Λ * Ca * unitBallVolume d ≤ cΨ * (r + 3))
    {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (h0 : X 0 ω = 0) (n : ℕ) :
    ε * (cΨ * (unitBallVolume d)⁻¹) *
        ∑ z ∈ (departureRange (fun j => X j ω) n).filter (fun z => r + 3 < euclidNorm z),
          euclidNorm z ^ (1 - (d : ℝ)) ≤
      (1 + ε * Λ * Real.sqrt d) * Cg * (r - 1) ^ (1 - (d : ℝ)) *
          ∑ j ∈ range n,
            (if r - 2 < euclidNorm (X j ω) ∧ euclidNorm (X j ω) ≤ r + 3 then (1 : ℝ) else 0) +
        |driftDynkin ε ξ (fun z => max (b z - h) 0) X n ω| := by
  let φ : Site d → ℝ := fun z => max (b z - h) 0
  let x : ℕ → Site d := fun j => X j ω
  let K : ℝ := (1 + ε * Λ * Real.sqrt d) * Cg * (r - 1) ^ (1 - (d : ℝ))
  let T : ℕ → ℝ := fun j => walkOp φ (x j) - φ (x j)
  let S : ℕ → ℝ := fun j => if x j ≠ 0 ∧ x j ∉ (range j).image x then
      ε * inner ℝ (ξ (x j)) (centralDiff φ (x j)) else 0
  let c : ℕ → ℝ := fun j => if r + 3 < euclidNorm (x j) ∧ x j ≠ 0 ∧
      x j ∉ (range j).image x then
      ε * (cΨ * (unitBallVolume d)⁻¹) * euclidNorm (x j) ^ (1 - (d : ℝ)) else 0
  let sh : ℕ → ℝ := fun j =>
    if r - 2 < euclidNorm (x j) ∧ euclidNorm (x j) ≤ r + 3 then (1 : ℝ) else 0
  change ε * (cΨ * (unitBallVolume d)⁻¹) *
      ∑ z ∈ (departureRange x n).filter (fun z => r + 3 < euclidNorm z),
        euclidNorm z ^ (1 - (d : ℝ)) ≤
      K * ∑ j ∈ range n, sh j + |driftDynkin ε ξ φ X n ω|
  have hCg : 0 ≤ Cg := cg_nonneg hd hgrad
  have hr0 : 0 ≤ r := by linarith
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hnorm 0)
  have hnext : ∀ j, driftNextMean ε ξ φ x j - φ (x j) = T j - S j := by
    intro j
    change (∑ e ∈ unitSteps d, driftStepProb d ε ξ x j e * φ (x j + e)) - φ (x j) =
      (walkOp φ (x j) - φ (x j)) -
        (if x j ≠ 0 ∧ x j ∉ (range j).image x then
          ε * inner ℝ (ξ (x j)) (centralDiff φ (x j)) else 0)
    rw [sum_driftStepProb_mul]
    ring
  have hterm : ∀ j, c j - K * sh j ≤ S j - T j := by
    intro j
    by_cases hA : euclidNorm (x j) ≤ r - 2
    · -- inside: both terms vanish
      have hne : ∀ i : Fin d, φ (x j + unit i) = 0 ∧ φ (x j - unit i) = 0 := by
        intro i
        exact ⟨(max_sub_eq_zero_of_le hin hA (mem_unitSteps.mpr ⟨i, Or.inl rfl⟩)).1,
          (max_sub_eq_zero_of_le hin hA (mem_unitSteps.mpr ⟨i, Or.inr rfl⟩)).1⟩
      have hφx : φ (x j) = 0 :=
        max_eq_right (sub_nonpos.mpr (hin (x j) (by linarith)))
      have hwalk : walkOp φ (x j) = 0 := walkOp_eq_zero_of_nbr_eq_zero hne
      have hcd : centralDiff φ (x j) = 0 := by
        apply centralDiff_eq_zero_of_nbr
        intro i
        rw [(hne i).1, (hne i).2]
      have hT : T j = 0 := by
        change walkOp φ (x j) - φ (x j) = 0
        rw [hwalk, hφx, sub_zero]
      have hS : S j = 0 := by
        change (if x j ≠ 0 ∧ x j ∉ (range j).image x then
            ε * inner ℝ (ξ (x j)) (centralDiff φ (x j)) else 0) = 0
        rw [hcd, inner_zero_right, mul_zero]
        split_ifs <;> rfl
      have hlt3 : ¬ r + 3 < euclidNorm (x j) := by linarith
      have hc0 : c j = 0 := by
        change (if r + 3 < euclidNorm (x j) ∧ x j ≠ 0 ∧
            x j ∉ (range j).image x then
            ε * (cΨ * (unitBallVolume d)⁻¹) * euclidNorm (x j) ^ (1 - (d : ℝ)) else 0) = 0
        rw [if_neg (fun hh => hlt3 hh.1)]
      have hsh : sh j = 0 := by
        change (if r - 2 < euclidNorm (x j) ∧ euclidNorm (x j) ≤ r + 3 then
          (1 : ℝ) else 0) = 0
        rw [if_neg (fun hh => (not_lt_of_ge hA) hh.1)]
      rw [hc0, hsh, hT, hS]
      simp
    · rw [not_le] at hA
      by_cases hC : r + 3 < euclidNorm (x j)
      · -- beyond the shell
        have hxC : Λ * Ca * unitBallVolume d ≤ cΨ * euclidNorm (x j) :=
          hCa.trans (mul_le_mul_of_nonneg_left hC.le hcΨ)
        have hrd := radial_drift_field (d := d) hd hr0 hEuler hnorm hout hb hgradA hC
          (by linarith) hxC
        have hT : T j = 0 := by
          change walkOp φ (x j) - φ (x j) = 0
          exact hrd.1
        have hS_ge : c j ≤ S j := by
          by_cases hcond : x j ≠ 0 ∧ x j ∉ (range j).image x
          · have hc : c j =
                ε * (cΨ * (unitBallVolume d)⁻¹) * euclidNorm (x j) ^ (1 - (d : ℝ)) := by
              change (if r + 3 < euclidNorm (x j) ∧ x j ≠ 0 ∧
                  x j ∉ (range j).image x then
                  ε * (cΨ * (unitBallVolume d)⁻¹) * euclidNorm (x j) ^ (1 - (d : ℝ))
                    else 0) = _
              rw [if_pos ⟨hC, hcond⟩]
            have hS : S j = ε * inner ℝ (ξ (x j)) (centralDiff φ (x j)) := by
              change (if x j ≠ 0 ∧ x j ∉ (range j).image x then
                  ε * inner ℝ (ξ (x j)) (centralDiff φ (x j)) else 0) = _
              rw [if_pos hcond]
            rw [hc, hS]
            calc ε * (cΨ * (unitBallVolume d)⁻¹) * euclidNorm (x j) ^ (1 - (d : ℝ))
                = ε * (cΨ * (unitBallVolume d)⁻¹ * euclidNorm (x j) ^ (1 - (d : ℝ))) := by
                  ring
              _ ≤ ε * inner ℝ (ξ (x j)) (centralDiff φ (x j)) :=
                  mul_le_mul_of_nonneg_left hrd.2 hε
          · have hc : c j = 0 := by
              change (if r + 3 < euclidNorm (x j) ∧ x j ≠ 0 ∧
                  x j ∉ (range j).image x then
                  ε * (cΨ * (unitBallVolume d)⁻¹) * euclidNorm (x j) ^ (1 - (d : ℝ))
                    else 0) = 0
              rw [if_neg (fun hh => hcond ⟨hh.2.1, hh.2.2⟩)]
            have hS : S j = 0 := by
              change (if x j ≠ 0 ∧ x j ∉ (range j).image x then
                  ε * inner ℝ (ξ (x j)) (centralDiff φ (x j)) else 0) = 0
              rw [if_neg hcond]
            rw [hc, hS]
        have hsh : sh j = 0 := by
          change (if r - 2 < euclidNorm (x j) ∧ euclidNorm (x j) ≤ r + 3 then
            (1 : ℝ) else 0) = 0
          rw [if_neg (fun hh => not_lt_of_ge hh.2 hC)]
        rw [hsh, hT]
        simp only [mul_zero, sub_zero]
        exact hS_ge
      · -- on the shell
        rw [not_lt] at hC
        have hincr : ∀ e ∈ unitSteps d,
            |φ (x j + e) - φ (x j)| ≤ Cg * (r - 1) ^ (1 - (d : ℝ)) :=
          fun e he => max_sub_increment_le hd hr hCg hgrad hA he
        have hcc : 0 ≤ Cg * (r - 1) ^ (1 - (d : ℝ)) :=
          mul_nonneg hCg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ r - 1) _)
        have hTle : |T j| ≤ Cg * (r - 1) ^ (1 - (d : ℝ)) := by
          change |walkOp φ (x j) - φ (x j)| ≤ Cg * (r - 1) ^ (1 - (d : ℝ))
          exact abs_walkOp_sub_le hd hincr
        have hSle : |S j| ≤ ε * Λ * Real.sqrt d * (Cg * (r - 1) ^ (1 - (d : ℝ))) := by
          change |(if x j ≠ 0 ∧ x j ∉ (range j).image x then
              ε * inner ℝ (ξ (x j)) (centralDiff φ (x j)) else 0)| ≤ _
          apply abs_ite_le_of_abs_le
          · exact abs_smul_inner_field_le hε hcc (hnorm (x j))
              (fun i => abs_centralDiff_coord_le hincr i)
          · positivity
        have hbound : |T j - S j| ≤ K := by
          have hTS : |T j - S j| ≤ |T j| + |S j| := by
            have hh := abs_sub_le (T j) 0 (S j)
            simpa only [sub_zero, zero_sub, abs_neg] using hh
          calc |T j - S j| ≤ |T j| + |S j| := hTS
            _ ≤ Cg * (r - 1) ^ (1 - (d : ℝ)) +
                  ε * Λ * Real.sqrt d * (Cg * (r - 1) ^ (1 - (d : ℝ))) :=
                add_le_add hTle hSle
            _ = K := by
                change Cg * (r - 1) ^ (1 - (d : ℝ)) +
                    ε * Λ * Real.sqrt d * (Cg * (r - 1) ^ (1 - (d : ℝ))) =
                  (1 + ε * Λ * Real.sqrt d) * Cg * (r - 1) ^ (1 - (d : ℝ))
                ring
        have hc0 : c j = 0 := by
          change (if r + 3 < euclidNorm (x j) ∧ x j ≠ 0 ∧
              x j ∉ (range j).image x then
              ε * (cΨ * (unitBallVolume d)⁻¹) * euclidNorm (x j) ^ (1 - (d : ℝ)) else 0) = 0
          rw [if_neg (fun hh => not_lt_of_ge hC hh.1)]
        have hsh1 : sh j = 1 := by
          change (if r - 2 < euclidNorm (x j) ∧ euclidNorm (x j) ≤ r + 3 then
            (1 : ℝ) else 0) = 1
          rw [if_pos ⟨hA, hC⟩]
        rw [hc0, hsh1, mul_one, zero_sub]
        have : T j - S j ≤ K := (le_abs_self _).trans hbound
        linarith
  have hdyn : driftDynkin ε ξ φ X n ω = φ (x n) - φ (x 0) - ∑ j ∈ range n, (T j - S j) := by
    have hsum_eq : (∑ j ∈ range n,
        (driftNextMean ε ξ φ (fun i => X i ω) j - φ (X j ω))) =
        ∑ j ∈ range n, (T j - S j) :=
      Finset.sum_congr rfl fun j _ => hnext j
    change φ (X n ω) - φ (X 0 ω) -
        (∑ j ∈ range n, (driftNextMean ε ξ φ (fun i => X i ω) j - φ (X j ω))) =
      φ (x n) - φ (x 0) - ∑ j ∈ range n, (T j - S j)
    rw [hsum_eq]
  have hφ0 : φ (x 0) = 0 := by
    have hx0 : x 0 = 0 := h0
    change max (b (x 0) - h) 0 = 0
    rw [hx0]
    exact max_eq_right (sub_nonpos.mpr (hin 0 (by rw [euclidNorm_zero]; linarith)))
  have hST : ∑ j ∈ range n, (S j - T j) ≤ |driftDynkin ε ξ φ X n ω| := by
    have hsum : ∑ j ∈ range n, (S j - T j) = -∑ j ∈ range n, (T j - S j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hdyn' : driftDynkin ε ξ φ X n ω = φ (x n) - ∑ j ∈ range n, (T j - S j) := by
      rw [hdyn, hφ0, sub_zero]
    have hrew : -∑ j ∈ range n, (T j - S j) =
        driftDynkin ε ξ φ X n ω - φ (x n) := by
      linarith
    rw [hsum, hrew]
    exact (sub_le_self _ (le_max_right _ _)).trans (le_abs_self _)
  have hsum_c : ∑ j ∈ range n, c j =
      ε * (cΨ * (unitBallVolume d)⁻¹) *
        ∑ z ∈ (departureRange x n).filter (fun z => r + 3 < euclidNorm z),
          euclidNorm z ^ (1 - (d : ℝ)) := by
    let g : Site d → ℝ := fun z => if r + 3 < euclidNorm z then
        ε * (cΨ * (unitBallVolume d)⁻¹) * euclidNorm z ^ (1 - (d : ℝ)) else 0
    have h1 : ∑ j ∈ range n, c j =
        ∑ j ∈ range n, (if x j ≠ 0 ∧ x j ∉ (range j).image x then g (x j) else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      change (if r + 3 < euclidNorm (x j) ∧ x j ≠ 0 ∧
          x j ∉ (range j).image x then
          ε * (cΨ * (unitBallVolume d)⁻¹) * euclidNorm (x j) ^ (1 - (d : ℝ)) else 0) =
        (if x j ≠ 0 ∧ x j ∉ (range j).image x then g (x j) else 0)
      by_cases hcond : x j ≠ 0 ∧ x j ∉ (range j).image x
      · rw [if_pos hcond]
        simp only [g]
        by_cases hlt : r + 3 < euclidNorm (x j)
        · rw [if_pos hlt, if_pos ⟨hlt, hcond⟩]
        · rw [if_neg hlt, if_neg (fun hh => hlt hh.1)]
      · rw [if_neg hcond, if_neg (fun hh => hcond ⟨hh.2.1, hh.2.2⟩)]
    rw [h1, sum_fresh_ne_zero_eq_sum_departureRange x n g,
      Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z = 0
    · subst z
      rw [if_neg (by simp), if_neg (by rw [euclidNorm_zero]; linarith)]
    · rw [if_pos hz]
  have hterm_sum : ∑ j ∈ range n, (c j - K * sh j) ≤ ∑ j ∈ range n, (S j - T j) :=
    Finset.sum_le_sum fun j _ => hterm j
  have hcsh : ∑ j ∈ range n, (c j - K * sh j) =
      ∑ j ∈ range n, c j - K * ∑ j ∈ range n, sh j := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  calc ε * (cΨ * (unitBallVolume d)⁻¹) *
        ∑ z ∈ (departureRange x n).filter (fun z => r + 3 < euclidNorm z),
          euclidNorm z ^ (1 - (d : ℝ))
      = ∑ j ∈ range n, c j := hsum_c.symm
    _ = (∑ j ∈ range n, (c j - K * sh j)) + K * ∑ j ∈ range n, sh j := by
        rw [hcsh]
        ring
    _ ≤ (∑ j ∈ range n, (S j - T j)) + K * ∑ j ∈ range n, sh j :=
        by linarith [hterm_sum]
    _ ≤ |driftDynkin ε ξ φ X n ω| + K * ∑ j ∈ range n, sh j := by linarith [hST]
    _ = K * ∑ j ∈ range n, sh j + |driftDynkin ε ξ φ X n ω| := by ring

/-! ### The bracket of the radial martingale -/

/-- The Dynkin martingale of the drift walk is linear: a constant factor passes through. -/
private lemma driftDynkin_const_mul {Ω : Type*} (ε c : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (g : Site d → ℝ) (X : ℕ → Ω → Site d) (t : ℕ)
    (ω : Ω) :
    driftDynkin ε ξ (fun z => c * g z) X t ω = c * driftDynkin ε ξ g X t ω := by
  have hnext : ∀ j, driftNextMean ε ξ (fun z => c * g z) (fun i => X i ω) j =
      c * driftNextMean ε ξ g (fun i => X i ω) j := by
    intro j
    simp only [driftNextMean, mul_sum]
    exact sum_congr rfl fun e _ => by ring
  have hsum : ∑ j ∈ range t,
      (driftNextMean ε ξ (fun z => c * g z) (fun i => X i ω) j - c * g (X j ω)) =
      c * ∑ j ∈ range t, (driftNextMean ε ξ g (fun i => X i ω) j - g (X j ω)) := by
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by rw [hnext j]; ring
  rw [driftDynkin, driftDynkin, hsum]
  ring

/-- The increment of the scaled radial test at `x`: it vanishes for `|x| ≤ r - 2` and is at most
`c C_g (1 + |x|)^{1-d}` otherwise. -/
private lemma abs_osc_le {b : Site d → ℝ} {h r Cg c : ℝ} (hc : 0 ≤ c)
    (hin : ∀ x, euclidNorm x ≤ r - 1 → b x ≤ h)
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (x e : Site d) (he : e ∈ unitSteps d) :
    |c * max (b (x + e) - h) 0 - c * max (b x - h) 0| ≤
      if r - 2 < euclidNorm x then c * (Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) else 0 := by
  split_ifs with hx
  · rw [← mul_sub, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left
      ((abs_max_sub_add_sub_le b h x e).trans (hgrad x e he)) hc
  · obtain ⟨h1, h2⟩ := max_sub_eq_zero_of_le hin (not_lt.mp hx) he
    simp [h1, h2]

/-- The radial bracket term at a site: `(1 + |x|)^{2-2d}` when `|x| > r - 2` and `0` otherwise. -/
private noncomputable def radialTerm (d : ℕ) (r : ℝ) (x : Site d) : ℝ :=
  if r - 2 < euclidNorm x then (1 + euclidNorm x) ^ (2 - 2 * (d : ℝ)) else 0

/-- The radial bracket term is nonnegative. -/
private lemma radialTerm_nonneg (r : ℝ) (x : Site d) : 0 ≤ radialTerm d r x := by
  unfold radialTerm
  split_ifs
  · exact Real.rpow_nonneg (by linarith [euclidNorm_nonneg x]) _
  · exact le_rfl

/-- The square of `a^{1-d}` is `a^{2-2d}`. -/
private lemma rpow_one_sub_sq {a : ℝ} (ha : 0 ≤ a) :
    (a ^ (1 - (d : ℝ))) ^ 2 = a ^ (2 - 2 * (d : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  congr 1
  push_cast
  ring

/-- The squared increment of the scaled radial test is at most `c² C_g²` times the bracket term. -/
private lemma sq_osc_le {b : Site d → ℝ} {h r Cg c : ℝ} (hc : 0 ≤ c)
    (hin : ∀ x, euclidNorm x ≤ r - 1 → b x ≤ h)
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (x e : Site d) (he : e ∈ unitSteps d) :
    (c * max (b (x + e) - h) 0 - c * max (b x - h) 0) ^ 2 ≤
      c ^ 2 * Cg ^ 2 * radialTerm d r x := by
  have h1 := abs_osc_le hc hin hgrad x e he
  rw [← sq_abs]
  unfold radialTerm
  split_ifs at h1 ⊢ with hx
  · have h0 := abs_nonneg (c * max (b (x + e) - h) 0 - c * max (b x - h) 0)
    have hsq := pow_le_pow_left₀ h0 h1 2
    refine hsq.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, rpow_one_sub_sq (by linarith [euclidNorm_nonneg x])]
    ring
  · have h0 := abs_nonneg (c * max (b (x + e) - h) 0 - c * max (b x - h) 0)
    have : |c * max (b (x + e) - h) 0 - c * max (b x - h) 0| = 0 := le_antisymm h1 h0
    rw [this]
    simp

/-- The increment of the scaled radial test is at most `c C_g (r - 1)^{1-d}` at every site. -/
private lemma abs_osc_le_uniform {b : Site d → ℝ} {h r Cg c : ℝ} (hd : 1 ≤ d) (hc : 0 ≤ c)
    (hCg : 0 ≤ Cg) (hr : 1 < r) (hin : ∀ x, euclidNorm x ≤ r - 1 → b x ≤ h)
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (x e : Site d) (he : e ∈ unitSteps d) :
    |c * max (b (x + e) - h) 0 - c * max (b x - h) 0| ≤ c * (Cg * (r - 1) ^ (1 - (d : ℝ))) := by
  have h1 := abs_osc_le hc hin hgrad x e he
  refine h1.trans ?_
  split_ifs with hx
  · refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hCg) hc
    exact rpow_one_sub_le_of_le (by linarith) (by linarith) hd
  · exact mul_nonneg hc (mul_nonneg hCg (Real.rpow_nonneg (by linarith) _))

/-- The bracket terms along a path sum to at most the local-time weighted sum over the
departure sites beyond `r - 2`, with the largest local time taken over those sites. -/
private theorem sum_localTime_rpow_le_tail_local (hd : 1 ≤ d) (X : ℕ → Site d) (n : ℕ)
    {r b : ℝ} {M : ℕ}
    (hM : ∀ x ∈ departureRange X n, r - 2 < euclidNorm x → localTime X n x ≤ M)
    (hb : 2 + Real.sqrt d / 2 < b) (hrb : b < r) (hr : Real.sqrt d + 2 ≤ r) :
    ∑ x ∈ (departureRange X n).filter (fun x => r - 2 < euclidNorm x),
        (localTime X n x : ℝ) * euclidNorm x ^ (2 - 2 * (d : ℝ)) ≤
      2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) * (r - 2) ^ (1 - (d : ℝ)) *
        M * tail d (cellSet X n) (r - b) := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hc : 1 - (d : ℝ) ≤ 0 := by linarith
  have hr2 : 0 < r - 2 := by
    have hsp : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
    linarith
  have hrb_pos : 0 < r - b := by linarith
  have hw : 0 < (d : ℝ) * unitBallVolume d := mul_pos hdR (unitBallVolume_pos d)
  set S : Finset (Site d) :=
    (departureRange X n).filter (fun x => r - 2 < euclidNorm x) with hSdef
  have hSmem : ∀ x : Site d, x ∈ S ↔
      x ∈ departureRange X n ∧ r - 2 < euclidNorm x := by
    intro x
    rw [hSdef, Finset.mem_filter]
  have hC_nonneg : 0 ≤ (M : ℝ) * (r - 2) ^ (1 - (d : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (le_of_lt hr2) _)
  have hC_nonneg_full :
      0 ≤ (M : ℝ) * (r - 2) ^ (1 - (d : ℝ)) * (2 : ℝ) ^ ((d : ℝ) - 1) :=
    mul_nonneg hC_nonneg (Real.rpow_nonneg (by norm_num) _)
  have hterm_pow : ∀ x ∈ S,
      (localTime X n x : ℝ) * euclidNorm x ^ (2 - 2 * (d : ℝ)) ≤
        (M : ℝ) * (r - 2) ^ (1 - (d : ℝ)) * euclidNorm x ^ (1 - (d : ℝ)) := by
    intro x hx
    rw [hSmem] at hx
    obtain ⟨hxdep, hxgt⟩ := hx
    have hxpos : 0 < euclidNorm x := by linarith
    have hrpow : euclidNorm x ^ (2 - 2 * (d : ℝ)) =
        euclidNorm x ^ (1 - (d : ℝ)) * euclidNorm x ^ (1 - (d : ℝ)) := by
      rw [show (2 : ℝ) - 2 * (d : ℝ) = (1 - (d : ℝ)) + (1 - (d : ℝ)) by ring,
        Real.rpow_add hxpos]
    have hle_rpow : euclidNorm x ^ (1 - (d : ℝ)) ≤ (r - 2) ^ (1 - (d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hr2 (le_of_lt hxgt) hc
    have hMx : (localTime X n x : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast hM x hxdep hxgt
    have h1d : 0 ≤ euclidNorm x ^ (1 - (d : ℝ)) :=
      Real.rpow_nonneg (euclidNorm_nonneg x) _
    calc (localTime X n x : ℝ) * euclidNorm x ^ (2 - 2 * (d : ℝ))
        = ((localTime X n x : ℝ) * euclidNorm x ^ (1 - (d : ℝ))) *
            euclidNorm x ^ (1 - (d : ℝ)) := by rw [hrpow]; ring
      _ ≤ ((M : ℝ) * euclidNorm x ^ (1 - (d : ℝ))) *
            euclidNorm x ^ (1 - (d : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMx h1d) h1d
      _ = (M : ℝ) * (euclidNorm x ^ (1 - (d : ℝ)) *
            euclidNorm x ^ (1 - (d : ℝ))) := by ring
      _ ≤ (M : ℝ) * ((r - 2) ^ (1 - (d : ℝ)) *
            euclidNorm x ^ (1 - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle_rpow h1d)
            (Nat.cast_nonneg _)
      _ = (M : ℝ) * (r - 2) ^ (1 - (d : ℝ)) *
            euclidNorm x ^ (1 - (d : ℝ)) := by ring
  have hcell_weight : ∀ x ∈ S,
      euclidNorm x ^ (1 - (d : ℝ)) ≤
        (2 : ℝ) ^ ((d : ℝ) - 1) * ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) := by
    intro x hx
    rw [hSmem] at hx
    obtain ⟨_hxdep, hxgt⟩ := hx
    have hxge : Real.sqrt d ≤ euclidNorm x := by linarith
    have h := (setIntegral_rpow_mem_Icc (d := d) hd hxge).1
    have hfac : (2 : ℝ) ^ ((d : ℝ) - 1) * (2 : ℝ) ^ (1 - (d : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show ((d : ℝ) - 1) + (1 - (d : ℝ)) = 0 by ring, Real.rpow_zero]
    calc euclidNorm x ^ (1 - (d : ℝ))
        = (2 : ℝ) ^ ((d : ℝ) - 1) *
            ((2 : ℝ) ^ (1 - (d : ℝ)) * euclidNorm x ^ (1 - (d : ℝ))) := by
          rw [← mul_assoc, hfac, one_mul]
      _ ≤ (2 : ℝ) ^ ((d : ℝ) - 1) * ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) :=
          mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hterm : ∀ x ∈ S,
      (localTime X n x : ℝ) * euclidNorm x ^ (2 - 2 * (d : ℝ)) ≤
        ((M : ℝ) * (r - 2) ^ (1 - (d : ℝ)) * (2 : ℝ) ^ ((d : ℝ) - 1)) *
          ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) := by
    intro x hx
    calc (localTime X n x : ℝ) * euclidNorm x ^ (2 - 2 * (d : ℝ))
        ≤ (M : ℝ) * (r - 2) ^ (1 - (d : ℝ)) * euclidNorm x ^ (1 - (d : ℝ)) := hterm_pow x hx
      _ ≤ (M : ℝ) * (r - 2) ^ (1 - (d : ℝ)) *
            ((2 : ℝ) ^ ((d : ℝ) - 1) * ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left (hcell_weight x hx) hC_nonneg
      _ = ((M : ℝ) * (r - 2) ^ (1 - (d : ℝ)) * (2 : ℝ) ^ ((d : ℝ) - 1)) *
          ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) := by ring
  have hDmeas : MeasurableSet (cellSet X n) := measurableSet_cellSet X n
  have hDbdd : Bornology.IsBounded (cellSet X n) :=
    Metric.isBounded_ball.subset (cellSet_subset_ball hd X n)
  have hintD : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ)))
      (cellSet X n ∩ {v | r - b < ‖v‖}) :=
    CERW.Support.Geometry.integrableOn_tail hDmeas hDbdd hrb_pos
  have hcell_sub : ∀ x ∈ S, cell x ⊆ cellSet X n ∩ {v | r - b < ‖v‖} := by
    intro x hx v hv
    rw [hSmem] at hx
    obtain ⟨hxdep, hxgt⟩ := hx
    refine ⟨?_, ?_⟩
    · rw [cellSet]
      exact Set.mem_iUnion₂.mpr ⟨x, hxdep, hv⟩
    · have hdiff : |euclidNorm x - ‖v‖| ≤ Real.sqrt d / 2 := by
        calc |euclidNorm x - ‖v‖| = |‖toSpace x‖ - ‖v‖| := by rw [norm_toSpace]
          _ ≤ ‖toSpace x - v‖ := abs_norm_sub_norm_le (toSpace x) v
          _ = ‖v - toSpace x‖ := norm_sub_rev (toSpace x) v
          _ ≤ Real.sqrt d / 2 := norm_sub_toSpace_le_of_mem_cell hv
      have hlow : euclidNorm x - Real.sqrt d / 2 ≤ ‖v‖ := by
        have h' : euclidNorm x - ‖v‖ ≤ Real.sqrt d / 2 := (abs_le.mp hdiff).2
        linarith
      calc r - b < r - 2 - Real.sqrt d / 2 := by linarith
        _ < euclidNorm x - Real.sqrt d / 2 := by linarith
        _ ≤ ‖v‖ := hlow
  have hUnion_sub : (⋃ x ∈ S, cell x) ⊆ cellSet X n ∩ {v | r - b < ‖v‖} := by
    intro v hv
    rw [Set.mem_iUnion₂] at hv
    obtain ⟨x, hx, hvx⟩ := hv
    exact hcell_sub x hx hvx
  have hbiUnion : ∫ v in (⋃ x ∈ S, cell x), ‖v‖ ^ (1 - (d : ℝ)) =
      ∑ x ∈ S, ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) := by
    refine integral_biUnion_finset S (fun x _ => measurableSet_cell x) ?_ ?_
    · intro x _ y _ hxy
      exact cell_disjoint hxy
    · intro x hx
      exact hintD.mono_set (hcell_sub x hx)
  have hmono : ∫ v in (⋃ x ∈ S, cell x), ‖v‖ ^ (1 - (d : ℝ)) ≤
      ∫ v in cellSet X n ∩ {v | r - b < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ)) := by
    refine setIntegral_mono_set hintD (Filter.Eventually.of_forall fun v => ?_) ?_
    · exact Real.rpow_nonneg (norm_nonneg v) _
    · exact Filter.Eventually.of_forall fun v hv => hUnion_sub hv
  have htail : ∫ v in cellSet X n ∩ {v | r - b < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ)) =
      ((d : ℝ) * unitBallVolume d) * tail d (cellSet X n) (r - b) := by
    rw [tail]
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hw), one_mul]
  calc ∑ x ∈ S, (localTime X n x : ℝ) * euclidNorm x ^ (2 - 2 * (d : ℝ))
      ≤ ∑ x ∈ S, ((M : ℝ) * (r - 2) ^ (1 - (d : ℝ)) * (2 : ℝ) ^ ((d : ℝ) - 1)) *
            ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) := Finset.sum_le_sum hterm
    _ = ((M : ℝ) * (r - 2) ^ (1 - (d : ℝ)) * (2 : ℝ) ^ ((d : ℝ) - 1)) *
          ∑ x ∈ S, ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)) :=
        (Finset.mul_sum S (fun x => ∫ v in cell x, ‖v‖ ^ (1 - (d : ℝ)))
          ((M : ℝ) * (r - 2) ^ (1 - (d : ℝ)) * (2 : ℝ) ^ ((d : ℝ) - 1))).symm
    _ = ((M : ℝ) * (r - 2) ^ (1 - (d : ℝ)) * (2 : ℝ) ^ ((d : ℝ) - 1)) *
          ∫ v in (⋃ x ∈ S, cell x), ‖v‖ ^ (1 - (d : ℝ)) := by rw [hbiUnion]
    _ ≤ ((M : ℝ) * (r - 2) ^ (1 - (d : ℝ)) * (2 : ℝ) ^ ((d : ℝ) - 1)) *
          ∫ v in cellSet X n ∩ {v | r - b < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hmono hC_nonneg_full
    _ = ((M : ℝ) * (r - 2) ^ (1 - (d : ℝ)) * (2 : ℝ) ^ ((d : ℝ) - 1)) *
          (((d : ℝ) * unitBallVolume d) * tail d (cellSet X n) (r - b)) := by rw [htail]
    _ = 2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) * (r - 2) ^ (1 - (d : ℝ)) *
          M * tail d (cellSet X n) (r - b) := by ring

/-- The sum of the bracket terms along a path is at most the tail bound of the radial bracket,
with the largest local time over the departure sites with `|x| ≥ r - b`. -/
private lemma sum_radialTerm_le_local (hd : 1 ≤ d) (x : ℕ → Site d) (n : ℕ) {r bd : ℝ}
    (hbd : 2 + Real.sqrt d / 2 < bd) (hrb : bd < r) (hr : Real.sqrt d + 2 ≤ r) :
    ∑ j ∈ range n, radialTerm d r (x j) ≤
      2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) * (r - 2) ^ (1 - (d : ℝ)) *
        (((departureRange x n).filter (fun z => r - bd ≤ euclidNorm z)).sup
          (localTime x n) : ℕ) * tail d (cellSet x n) (r - bd) := by
  classical
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1
  rw [sum_range_eq_sum_localTime x n (radialTerm d r)]
  have hsum := sum_localTime_rpow_le_tail_local hd x n (r := r) (b := bd)
    (M := ((departureRange x n).filter (fun z => r - bd ≤ euclidNorm z)).sup (localTime x n))
    (fun z hz hzr => Finset.le_sup (f := localTime x n)
      (Finset.mem_filter.mpr ⟨hz, by linarith⟩)) hbd hrb hr
  refine le_trans ?_ hsum
  rw [sum_filter]
  refine sum_le_sum fun z _ => ?_
  unfold radialTerm
  split_ifs with hz
  · have hpos : 0 < euclidNorm z := by linarith
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)) (Nat.cast_nonneg _)
  · simp

/-- If `r / a ≤ s`, `c ≥ 0` and `c r^z = 1` with `z ≤ 0`, then `c s^z ≤ (a^z)⁻¹`. -/
private lemma mul_rpow_le_inv_rpow {r s a c z : ℝ} (hz : z ≤ 0) (hr : 0 < r) (ha : 0 < a)
    (hc : 0 ≤ c) (hs : r / a ≤ s) (hcr : c * r ^ z = 1) : c * s ^ z ≤ (a ^ z)⁻¹ := by
  have h1 : s ^ z ≤ (r / a) ^ z := Real.rpow_le_rpow_of_nonpos (div_pos hr ha) hs hz
  rw [Real.div_rpow hr.le ha.le] at h1
  calc c * s ^ z ≤ c * (r ^ z / a ^ z) := mul_le_mul_of_nonneg_left h1 hc
    _ = (c * r ^ z) / a ^ z := by ring
    _ = (a ^ z)⁻¹ := by rw [hcr, one_div]

/-- The arithmetic of the deterministic step: on the good event of Freedman's inequality for the
scaled martingale `κ W`, with `κ = c / B` and `c ρ = 1`, and the predictable bracket at most
`κ² C_g² S` with `S ≤ K ρ M F`, the martingale `W` is at most
`C_F (C_g √K + B) (√(M ρ F L) + ρ L)`. -/
private lemma radial_arith {W pb S K κ c B ρ CF Cg M F L : ℝ} (hρ : 0 < ρ) (hc : c * ρ = 1)
    (hB : 0 < B) (hκ : κ = c / B) (hCF : 0 ≤ CF) (hCg : 0 ≤ Cg) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hF : 0 ≤ F) (hL : 0 ≤ L) (hpb : pb ≤ κ ^ 2 * Cg ^ 2 * S) (hS : S ≤ K * ρ * (M * F))
    (hle : |κ * W| ≤ CF * (Real.sqrt (pb * L) + L)) :
    |W| ≤ CF * (Cg * Real.sqrt K + B) * (Real.sqrt (M * ρ * F * L) + ρ * L) := by
  have hc0 : 0 < c := by
    rcases (mul_pos_iff.mp (hc ▸ one_pos : 0 < c * ρ)) with h | h
    · exact h.1
    · exact absurd h.2 (not_lt.mpr hρ.le)
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hY : 0 ≤ M * ρ * F * L := by positivity
  have hpbL : pb * L ≤ (κ * Cg) ^ 2 * K * (M * ρ * F * L) := by
    have h1 : pb ≤ κ ^ 2 * Cg ^ 2 * (K * ρ * (M * F)) :=
      hpb.trans (mul_le_mul_of_nonneg_left hS (by positivity))
    calc pb * L ≤ κ ^ 2 * Cg ^ 2 * (K * ρ * (M * F)) * L := mul_le_mul_of_nonneg_right h1 hL
      _ = (κ * Cg) ^ 2 * K * (M * ρ * F * L) := by ring
  have hsq : Real.sqrt (pb * L) ≤ κ * Cg * Real.sqrt K * Real.sqrt (M * ρ * F * L) := by
    calc Real.sqrt (pb * L) ≤ Real.sqrt ((κ * Cg) ^ 2 * K * (M * ρ * F * L)) :=
          Real.sqrt_le_sqrt hpbL
      _ = κ * Cg * Real.sqrt K * Real.sqrt (M * ρ * F * L) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg _),
            Real.sqrt_sq (by positivity)]
  have hBρκ : B * ρ * κ = 1 := by
    rw [hκ]
    field_simp
    linarith
  have h1 : κ * |W| ≤ CF * (κ * Cg * Real.sqrt K * Real.sqrt (M * ρ * F * L) + L) := by
    rw [← abs_of_pos hκ0, ← abs_mul, abs_of_pos hκ0]
    refine hle.trans (mul_le_mul_of_nonneg_left ?_ hCF)
    linarith
  have hW : |W| = (B * ρ) * (κ * |W|) := by
    rw [← mul_assoc, hBρκ, one_mul]
  have hSq0 := Real.sqrt_nonneg K
  have hSY0 := Real.sqrt_nonneg (M * ρ * F * L)
  have hBρ : 0 ≤ B * ρ := by positivity
  calc |W| = (B * ρ) * (κ * |W|) := hW
    _ ≤ (B * ρ) * (CF * (κ * Cg * Real.sqrt K * Real.sqrt (M * ρ * F * L) + L)) :=
        mul_le_mul_of_nonneg_left h1 hBρ
    _ = CF * (Cg * Real.sqrt K * Real.sqrt (M * ρ * F * L) + B * ρ * L) := by
        have : B * ρ * κ = 1 := hBρκ
        calc (B * ρ) * (CF * (κ * Cg * Real.sqrt K * Real.sqrt (M * ρ * F * L) + L))
            = CF * ((B * ρ * κ) * (Cg * Real.sqrt K * Real.sqrt (M * ρ * F * L)) +
                B * ρ * L) := by ring
          _ = _ := by rw [this, one_mul]
    _ ≤ CF * (Cg * Real.sqrt K + B) * (Real.sqrt (M * ρ * F * L) + ρ * L) := by
        have hρL : 0 ≤ ρ * L := by positivity
        have h2 : Cg * Real.sqrt K * Real.sqrt (M * ρ * F * L) + B * ρ * L ≤
            (Cg * Real.sqrt K + B) * (Real.sqrt (M * ρ * F * L) + ρ * L) := by
          nlinarith [mul_nonneg (mul_nonneg hCg hSq0) hρL, mul_nonneg hB.le hSY0,
            mul_nonneg hCg hSq0, hSY0]
        calc CF * (Cg * Real.sqrt K * Real.sqrt (M * ρ * F * L) + B * ρ * L)
            ≤ CF * ((Cg * Real.sqrt K + B) * (Real.sqrt (M * ρ * F * L) + ρ * L)) :=
              mul_le_mul_of_nonneg_left h2 hCF
          _ = _ := by ring

/-! ### The radial martingale -/

/-- One radius: Freedman's inequality for the scaled Dynkin martingale of `φ_r`, together with
the deterministic step, bounds the probability that `|W^{(r)}_n|` exceeds the threshold, for every
`r ≥ r₀`. The threshold involves the largest local time over the departure sites with
`|x| ≥ r - b_d`. -/
private lemma exists_radius_bound (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {b : Site d → ℝ} {h : ℝ → ℝ} {Cg r₀ bd : ℝ} (hbd : 2 + Real.sqrt d / 2 < bd)
    (hr₀ : bd < r₀) (hr₀' : Real.sqrt d + 2 ≤ r₀)
    (hin : ∀ r : ℝ, r₀ ≤ r → ∀ x, euclidNorm x ≤ r - 1 → b x ≤ h r)
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {p : ℝ} (hp : 0 < p) :
    ∃ Cdet CF : ℝ, 0 < Cdet ∧ 0 < CF ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        {ξ : Site d → EuclideanSpace ℝ (Fin d)}, (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
        ∀ {X : ℕ → Ω → Site d}, IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n → ∀ r : ℕ, r₀ ≤ r →
          μ {ω | Cdet * (Real.sqrt ((((departureRange (fun j => X j ω) n).filter
                    (fun z => (r : ℝ) - bd ≤ euclidNorm z)).sup
                      (localTime (fun j => X j ω) n) : ℕ)
                  * (r : ℝ) ^ (1 - (d : ℝ)) * tail d (cellSet (fun j => X j ω) n) ((r : ℝ) - bd)
                  * Real.log n) + (r : ℝ) ^ (1 - (d : ℝ)) * Real.log n) <
            |driftDynkin ε ξ (fun z => max (b z - h r) 0) X n ω|} ≤
          ENNReal.ofReal (CF * (n : ℝ) ^ (-(p + 1))) := by
  have hd1 : 1 ≤ d := by omega
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hsq : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1'
  have hCg := cg_nonneg hd1 hgrad
  obtain ⟨CF, hCF0, hCF⟩ := freedman_bound.{u} (p + 1) (by linarith)
  set Q : ℝ := ((2 : ℝ) ^ (1 - (d : ℝ)))⁻¹ with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set K' : ℝ := 2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) * ((3 : ℝ) ^ (1 - (d : ℝ)))⁻¹
    with hK'
  have hK'0 : 0 ≤ K' := by
    have := unitBallVolume_pos d
    positivity
  set B : ℝ := 2 * (Cg * Q) + 1 with hBdef
  have hB : 0 < B := by
    have := mul_nonneg hCg hQ0
    linarith
  refine ⟨CF * (Cg * Real.sqrt K' + B), CF, by positivity, hCF0, ?_⟩
  intro Ω _ μ _ ξ hξ X hX n hn r hr
  have hrR : (3 : ℝ) ≤ r := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hexp : 1 - (d : ℝ) ≤ 0 := by linarith
  set ρr : ℝ := (r : ℝ) ^ (1 - (d : ℝ)) with hρr
  have hρ0 : 0 < ρr := Real.rpow_pos_of_pos hrpos _
  set c : ℝ := ρr⁻¹ with hcdef
  have hc0 : 0 < c := inv_pos.mpr hρ0
  have hcr : c * ρr = 1 := inv_mul_cancel₀ hρ0.ne'
  have hQc : c * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) ≤ Q :=
    mul_rpow_le_inv_rpow hexp hrpos (by norm_num) hc0.le (by linarith) hcr
  have hQ3 : c * ((r : ℝ) - 2) ^ (1 - (d : ℝ)) ≤ ((3 : ℝ) ^ (1 - (d : ℝ)))⁻¹ :=
    mul_rpow_le_inv_rpow hexp hrpos (by norm_num) hc0.le (by linarith) hcr
  set κ : ℝ := c / B with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set f : Site d → ℝ := fun z => κ * max (b z - h r) 0 with hf
  have hZ : Martingale (driftDynkin ε ξ f X) (pathFiltration hX.measurable) μ :=
    martingale_driftDynkin hd1 hε hξ hX f
  have hinc : ∀ᵐ ω ∂μ, ∀ t, |driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω| ≤ 1 := by
    filter_upwards [ae_abs_driftDynkin_succ_sub_le hd1 hε hξ hX f] with ω hω t
    have h1 := hω t (κ * (Cg * ((r : ℝ) - 1) ^ (1 - (d : ℝ)))) fun e he =>
      abs_osc_le_uniform hd1 hκ0 hCg (by linarith) (hin r hr) hgrad (X t ω) e he
    refine h1.trans ?_
    calc 2 * (κ * (Cg * ((r : ℝ) - 1) ^ (1 - (d : ℝ))))
        = 2 * (Cg * (c * ((r : ℝ) - 1) ^ (1 - (d : ℝ)))) / B := by
          rw [hκ]
          ring
      _ ≤ 2 * (Cg * Q) / B := by
          gcongr
      _ ≤ 1 := by
          rw [div_le_one hB]
          linarith
  have hfree := hCF n hn μ (pathFiltration hX.measurable) (driftDynkin ε ξ f X) hZ hinc
  have hvar : ∀ t, ∀ᵐ ω ∂μ,
      μ[fun ω => (driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω) *
          (driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω) |
        pathFiltration hX.measurable t] ω ≤ κ ^ 2 * Cg ^ 2 * radialTerm d r (X t ω) := by
    intro t
    have hsqf : (fun ω => (driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω) *
          (driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω)) =
        fun ω => (driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω) ^ 2 := by
      funext ω
      ring
    rw [hsqf]
    filter_upwards [condExp_sq_driftDynkin_succ_sub_le hd1 hε hξ hX f t] with ω hω
    refine hω.trans ?_
    calc ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
          (f (X t ω + e) - f (X t ω)) ^ 2
        ≤ ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
            (κ ^ 2 * Cg ^ 2 * radialTerm d r (X t ω)) := by
          refine sum_le_sum fun e he => mul_le_mul_of_nonneg_left ?_
            (driftStepProb_nonneg hε hξ _ t e)
          exact sq_osc_le hκ0 (hin r hr) hgrad (X t ω) e he
      _ = κ ^ 2 * Cg ^ 2 * radialTerm d r (X t ω) := by
          rw [← sum_mul, sum_driftStepProb hd1 ε ξ _ t, one_mul]
  have hpred : ∀ᵐ ω ∂μ, CERW.predBracket μ (pathFiltration hX.measurable)
      (driftDynkin ε ξ f X) (driftDynkin ε ξ f X) n ω ≤
      κ ^ 2 * Cg ^ 2 * ∑ j ∈ range n, radialTerm d r (X j ω) := by
    filter_upwards [ae_all_iff.mpr hvar] with ω hω
    unfold CERW.predBracket
    rw [Finset.sum_apply, mul_sum]
    exact sum_le_sum fun t _ => hω t
  refine le_trans (measure_mono_ae ?_) hfree
  filter_upwards [hpred] with ω hpω hE
  intro hle
  have hWn : driftDynkin ε ξ f X n ω - driftDynkin ε ξ f X 0 ω =
      κ * driftDynkin ε ξ (fun z => max (b z - h r) 0) X n ω := by
    rw [driftDynkin_zero, sub_zero]
    exact driftDynkin_const_mul ε κ ξ (fun z => max (b z - h r) 0) X n ω
  rw [hWn] at hle
  have hSle := sum_radialTerm_le_local hd1 (fun j => X j ω) n hbd (hr₀.trans_le hr)
    (hr₀'.trans hr)
  have hMF : 0 ≤ ((((departureRange (fun j => X j ω) n).filter
      (fun z => (r : ℝ) - bd ≤ euclidNorm z)).sup (localTime (fun j => X j ω) n) : ℕ) : ℝ) *
        tail d (cellSet (fun j => X j ω) n) ((r : ℝ) - bd) :=
    mul_nonneg (Nat.cast_nonneg _) (CERW.Support.Geometry.tail_nonneg _ _)
  have hω0 : 0 < unitBallVolume d := unitBallVolume_pos d
  have hKr : 2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) * ((r : ℝ) - 2) ^ (1 - (d : ℝ)) ≤
      K' * ρr := by
    have h2 : (0 : ℝ) ≤ 2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) := by positivity
    calc 2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) * ((r : ℝ) - 2) ^ (1 - (d : ℝ))
        = ρr * (2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
            (c * ((r : ℝ) - 2) ^ (1 - (d : ℝ)))) := by
          calc _ = (c * ρr) * (2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
                ((r : ℝ) - 2) ^ (1 - (d : ℝ))) := by rw [hcr, one_mul]
            _ = _ := by ring
      _ ≤ ρr * (2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
            ((3 : ℝ) ^ (1 - (d : ℝ)))⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ3 h2) hρ0.le
      _ = K' * ρr := by rw [hK']; ring
  have hS : ∑ j ∈ range n, radialTerm d r (X j ω) ≤ K' * ρr *
      (((((departureRange (fun j => X j ω) n).filter
        (fun z => (r : ℝ) - bd ≤ euclidNorm z)).sup (localTime (fun j => X j ω) n) : ℕ) : ℝ) *
          tail d (cellSet (fun j => X j ω) n) ((r : ℝ) - bd)) := by
    refine hSle.trans ?_
    calc _ = (2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) * ((r : ℝ) - 2) ^ (1 - (d : ℝ))) *
          (((((departureRange (fun j => X j ω) n).filter
            (fun z => (r : ℝ) - bd ≤ euclidNorm z)).sup (localTime (fun j => X j ω) n) : ℕ) : ℝ) *
              tail d (cellSet (fun j => X j ω) n) ((r : ℝ) - bd)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hKr hMF
  have hL : 0 ≤ Real.log (n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    exact Real.log_nonneg hn1
  have hfin := radial_arith (W := driftDynkin ε ξ (fun z => max (b z - h r) 0) X n ω)
    (κ := κ) (c := c) (B := B) (ρ := ρr) hρ0 hcr hB hκ hCF0.le hCg hK'0 (Nat.cast_nonneg _)
    (CERW.Support.Geometry.tail_nonneg _ _) hL hpω hS hle
  exact absurd hE (not_lt.mpr hfin)

/-- `eq:radialmart`: with probability at least `1 - Cn^{-p}`, simultaneously for all integers
`r₀ ≤ r ≤ n`, `|W^{(r)}_n| ≤ C [√(M_{r-b_d} r^{1-d} F(r - b_d) log n) + r^{1-d} log n]`, where
`M_{r-b_d}` is the largest local time over the departure sites with `|x| ≥ r - b_d`. -/
private theorem exists_radial_mart_field (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {b : Site d → ℝ} {h : ℝ → ℝ} {Cg r₀ bd : ℝ} (hbd : 2 + Real.sqrt d / 2 < bd)
    (hr₀ : bd < r₀) (hr₀' : Real.sqrt d + 2 ≤ r₀)
    (hin : ∀ r : ℝ, r₀ ≤ r → ∀ x, euclidNorm x ≤ r - 1 → b x ≤ h r)
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        {ξ : Site d → EuclideanSpace ℝ (Fin d)}, (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
        ∀ {X : ℕ → Ω → Site d}, IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ∃ r : ℕ, r₀ ≤ r ∧ r ≤ n ∧
            C * (Real.sqrt ((((departureRange (fun j => X j ω) n).filter
                    (fun z => (r : ℝ) - bd ≤ euclidNorm z)).sup
                      (localTime (fun j => X j ω) n) : ℕ)
                  * (r : ℝ) ^ (1 - (d : ℝ)) * tail d (cellSet (fun j => X j ω) n) ((r : ℝ) - bd)
                  * Real.log n) + (r : ℝ) ^ (1 - (d : ℝ)) * Real.log n) <
            |driftDynkin ε ξ (fun z => max (b z - h r) 0) X n ω|} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨Cdet, CF, hCdet0, hCF0, hCdet⟩ := exists_radius_bound.{u} hd hε hbd hr₀ hr₀' hin hgrad hp
  refine ⟨Cdet + 2 * CF, by positivity, ?_⟩
  intro Ω _ μ _ ξ hξ X hX n hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  set R : Finset ℕ := (range (n + 1)).filter (fun r => r₀ ≤ (r : ℝ)) with hR
  set E : ℕ → Set Ω := fun r =>
    {ω | Cdet * (Real.sqrt ((((departureRange (fun j => X j ω) n).filter
                    (fun z => (r : ℝ) - bd ≤ euclidNorm z)).sup
                      (localTime (fun j => X j ω) n) : ℕ)
                  * (r : ℝ) ^ (1 - (d : ℝ)) * tail d (cellSet (fun j => X j ω) n) ((r : ℝ) - bd)
                  * Real.log n) + (r : ℝ) ^ (1 - (d : ℝ)) * Real.log n) <
            |driftDynkin ε ξ (fun z => max (b z - h r) 0) X n ω|} with hE
  have hbound : ∀ r ∈ R, μ (E r) ≤ ENNReal.ofReal (CF * (n : ℝ) ^ (-(p + 1))) :=
    fun r hr => hCdet hξ hX n hn r (mem_filter.mp hr).2
  have hRcard : (R.card : ℝ) ≤ (n : ℝ) + 1 := by
    have h1 : R.card ≤ n + 1 := (card_filter_le _ _).trans (by simp)
    exact_mod_cast h1
  set a : ℝ := CF * (n : ℝ) ^ (-(p + 1)) with ha
  have ha0 : 0 ≤ a := by positivity
  refine (measure_mono (t := ⋃ r ∈ R, E r) ?_).trans ?_
  · rintro ω ⟨r, hr, hrn, hlt⟩
    simp only [Set.mem_iUnion]
    refine ⟨r, ?_, ?_⟩
    · simp only [hR, mem_filter, mem_range]
      exact ⟨by omega, hr⟩
    · have he : 0 ≤ Real.sqrt ((((departureRange (fun j => X j ω) n).filter
                    (fun z => (r : ℝ) - bd ≤ euclidNorm z)).sup
                      (localTime (fun j => X j ω) n) : ℕ)
                  * (r : ℝ) ^ (1 - (d : ℝ)) * tail d (cellSet (fun j => X j ω) n) ((r : ℝ) - bd)
                  * Real.log n) + (r : ℝ) ^ (1 - (d : ℝ)) * Real.log n :=
        add_nonneg (Real.sqrt_nonneg _)
          (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hL0)
      refine lt_of_le_of_lt ?_ hlt
      exact mul_le_mul_of_nonneg_right (by linarith) he
  · calc μ (⋃ r ∈ R, E r) ≤ ∑ r ∈ R, μ (E r) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _r ∈ R, ENNReal.ofReal a := sum_le_sum hbound
      _ = ENNReal.ofReal ((R.card : ℝ) * a) := by
          simp only [sum_const, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul (p := (R.card : ℝ)) (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((Cdet + 2 * CF) * (n : ℝ) ^ (-p)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (R.card : ℝ) * a ≤ ((n : ℝ) + 1) * a :=
            mul_le_mul_of_nonneg_right hRcard ha0
          have h2 := CERW.Generic.Martingale.pow_mul_rpow_neg_le hn1 1 p
          simp only [Nat.cast_one, pow_one] at h2
          have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg hnR.le _
          have h4 : ((n : ℝ) + 1) * a ≤ 2 * CF * (n : ℝ) ^ (-p) := by
            rw [ha]
            calc ((n : ℝ) + 1) * (CF * (n : ℝ) ^ (-(p + 1)))
                = CF * (((n : ℝ) + 1) * (n : ℝ) ^ (-(p + 1))) := by ring
              _ ≤ CF * (2 * (n : ℝ) ^ (-p)) := mul_le_mul_of_nonneg_left h2 hCF0.le
              _ = 2 * CF * (n : ℝ) ^ (-p) := by ring
          have h5 : 0 ≤ Cdet * (n : ℝ) ^ (-p) := mul_nonneg hCdet0.le h3
          linarith

/-! ### The pathwise inequality -/

/-- The visits of the path to the shell `r - 2 < |x| ≤ r + 3` number at most `M_sh(r)` times
the number of shell sites in the departure range. -/
private lemma shell_visits_le {d : ℕ} (x : ℕ → Site d) (n r : ℕ) :
    ∑ j ∈ range n, (if (r : ℝ) - 2 < euclidNorm (x j) ∧ euclidNorm (x j) ≤ (r : ℝ) + 3
        then (1 : ℝ) else 0) ≤
      (shellMax x n r : ℝ) *
        (((departureRange x n).filter (fun z => |euclidNorm z - r| ≤ 3)).card : ℝ) := by
  classical
  rw [sum_range_eq_sum_localTime x n
    (fun z => if (r : ℝ) - 2 < euclidNorm z ∧ euclidNorm z ≤ (r : ℝ) + 3 then (1 : ℝ) else 0)]
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  by_cases hc : (r : ℝ) - 2 < euclidNorm z ∧ euclidNorm z ≤ (r : ℝ) + 3
  · have hz : |euclidNorm z - r| ≤ 3 := abs_le.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩
    have hl : (localTime x n z : ℝ) ≤ (shellMax x n r : ℝ) :=
      Nat.cast_le.mpr (localTime_le_shellMax x n r hz)
    simpa [hc, hz] using hl
  · simp only [hc, if_false, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The ratio bound `a^{1-d} c^{d-1} ≤ 3^{d-1}` for `0 < a` and `0 ≤ c ≤ 3a`. -/
private lemma rpow_mul_rpow_le {d : ℕ} (hd : 1 ≤ d) {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hac : c ≤ 3 * a) :
    a ^ (1 - (d : ℝ)) * c ^ ((d : ℝ) - 1) ≤ 3 ^ ((d : ℝ) - 1) := by
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h1 : a ^ (1 - (d : ℝ)) = (a ^ ((d : ℝ) - 1))⁻¹ := by
    rw [← Real.rpow_neg ha.le]
    congr 1
    ring
  rw [h1, ← div_eq_inv_mul, ← Real.div_rpow hc ha.le]
  exact Real.rpow_le_rpow (div_nonneg hc ha.le) ((div_le_iff₀ ha).mpr hac) hd1

/-- The pathwise inequality of the radial test at one integer radius `r`: the source
inequality, the lower bound of the source sum by `F(r + b_d)`, the shell visit count and the
shell count combine, given the bound on the radial martingale. -/
private lemma radial_pathwise_field {d : ℕ} (hd : 2 ≤ d) {b : Site d → ℝ}
    {h R Ca Cg ε bd Cm C cΨ Λ : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (r : ℕ) (hε : 0 < ε) (hcΨ : 0 < cΨ)
    (hEuler : ∀ x, cΨ * euclidNorm x ≤ inner ℝ (ξ x) (toSpace x))
    (hnorm : ∀ x, ‖ξ x‖ ≤ Λ) (hbd : 3 + Real.sqrt d / 2 < bd) (hr : 2 * bd + 1 ≤ (r : ℝ))
    (hin : ∀ x, euclidNorm x ≤ (r : ℝ) - 1 → b x ≤ h)
    (hout : ∀ x, (r : ℝ) + 1 ≤ euclidNorm x → h ≤ b x)
    (hpois : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0)
    (hgradA : ∀ x, R ≤ euclidNorm x →
      ‖centralDiff b x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x‖ ≤
        Ca * euclidNorm x ^ (-(d : ℝ)))
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (hR : R ≤ r + 3) (hCa : Λ * Ca * unitBallVolume d ≤ cΨ * (r + 3))
    {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (h0 : X 0 ω = 0) (n : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hW : |driftDynkin ε ξ (fun z => max (b z - h) 0) X n ω| ≤
      Cm * (Real.sqrt ((((departureRange (fun j => X j ω) n).filter
            (fun z => (r : ℝ) - bd ≤ euclidNorm z)).sup (localTime (fun j => X j ω) n) : ℕ)
              * (r : ℝ) ^ (1 - (d : ℝ))
              * tail d (cellSet (fun j => X j ω) n) ((r : ℝ) - bd) * L)
          + (r : ℝ) ^ (1 - (d : ℝ)) * L))
    (hCA : 2 ^ ((d : ℝ) - 1) * (d * ε * cΨ)⁻¹ *
      ((1 + ε * Λ * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d)) ≤ C)
    (hCB : 2 ^ ((d : ℝ) - 1) * (d * ε * cΨ)⁻¹ * Cm ≤ C) :
    tail d (cellSet (fun j => X j ω) n) ((r : ℝ) + bd)
      ≤ C * (shellMax (fun j => X j ω) n r : ℝ)
            * (tail d (cellSet (fun j => X j ω) n) ((r : ℝ) - bd)
              - tail d (cellSet (fun j => X j ω) n) ((r : ℝ) + bd))
        + C * Real.sqrt ((((departureRange (fun j => X j ω) n).filter
            (fun z => (r : ℝ) - bd ≤ euclidNorm z)).sup (localTime (fun j => X j ω) n) : ℕ)
              * (r : ℝ) ^ (1 - (d : ℝ))
              * tail d (cellSet (fun j => X j ω) n) ((r : ℝ) - bd) * L)
        + C * (r : ℝ) ^ (1 - (d : ℝ)) * L := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hω0 : 0 < unitBallVolume d := unitBallVolume_pos d
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hσ : 0 < (d : ℝ) * unitBallVolume d := mul_pos hdpos hω0
  have hsqrt0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hnorm 0)
  have hbd0 : 0 < bd := by linarith
  have hr2 : (2 : ℝ) ≤ r := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hrb : bd < (r : ℝ) := by linarith
  have hsrc := radial_source_field (d := d) hd1 hr2 hε.le hcΨ.le hEuler hnorm hin hout hpois
    hgradA hgrad hR hCa X ω h0 n
  have htail := tail_le_sum_rpow hd1 (fun j => X j ω) n hbd (by linarith : Real.sqrt d ≤ r)
  have hvis := shell_visits_le (fun j => X j ω) n r
  have hcard := card_shell_le hd1 (fun j => X j ω) n hbd hrb
  set T₁ := tail d (cellSet (fun j => X j ω) n) ((r : ℝ) + bd) with hT₁
  set T₂ := tail d (cellSet (fun j => X j ω) n) ((r : ℝ) - bd) with hT₂
  set M : ℝ := (shellMax (fun j => X j ω) n r : ℝ) with hM
  set S : ℝ := Real.sqrt ((((departureRange (fun j => X j ω) n).filter
            (fun z => (r : ℝ) - bd ≤ euclidNorm z)).sup (localTime (fun j => X j ω) n) : ℕ)
              * (r : ℝ) ^ (1 - (d : ℝ)) * T₂ * L)
    + (r : ℝ) ^ (1 - (d : ℝ)) * L with hS
  set s : ℝ := ∑ z ∈ (departureRange (fun j => X j ω) n).filter
      (fun z => (r : ℝ) + 3 < euclidNorm z), euclidNorm z ^ (1 - (d : ℝ)) with hs
  set N : ℝ := ∑ j ∈ range n, (if (r : ℝ) - 2 < euclidNorm (X j ω) ∧
    euclidNorm (X j ω) ≤ (r : ℝ) + 3 then (1 : ℝ) else 0) with hN
  set W : ℝ := |driftDynkin ε ξ (fun z => max (b z - h) 0) X n ω| with hW'
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hS0 : 0 ≤ S := add_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (Real.rpow_nonneg hrpos.le _) hL)
  have hQ : 0 < (d : ℝ) * unitBallVolume d * ((r : ℝ) + bd) ^ ((d : ℝ) - 1) :=
    mul_pos hσ (Real.rpow_pos_of_pos (by linarith) _)
  have hΔ : 0 ≤ T₂ - T₁ := by
    have h1 : 0 ≤ (d : ℝ) * unitBallVolume d * ((r : ℝ) + bd) ^ ((d : ℝ) - 1) * (T₂ - T₁) :=
      (Nat.cast_nonneg _).trans hcard
    exact (mul_nonneg_iff_of_pos_left hQ).mp h1
  have hMΔ : 0 ≤ M * (T₂ - T₁) := mul_nonneg hM0 hΔ
  have hεΛ : 0 ≤ 1 + ε * Λ * Real.sqrt d := by positivity
  have hK0 : 0 ≤ (1 + ε * Λ * Real.sqrt d) * |Cg| * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) :=
    mul_nonneg (mul_nonneg hεΛ (abs_nonneg _))
      (Real.rpow_nonneg (by linarith) _)
  have hKle : (1 + ε * Λ * Real.sqrt d) * Cg * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) ≤
      (1 + ε * Λ * Real.sqrt d) * |Cg| * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_abs_self Cg) hεΛ)
      (Real.rpow_nonneg (by linarith) _)
  have hrat := rpow_mul_rpow_le hd1 (a := (r : ℝ) - 1) (c := (r : ℝ) + bd) (by linarith)
    (by linarith) (by linarith)
  have hkey : (1 + ε * Λ * Real.sqrt d) * Cg * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) * N ≤
      (1 + ε * Λ * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
        (M * (T₂ - T₁)) := by
    calc (1 + ε * Λ * Real.sqrt d) * Cg * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) * N
        ≤ (1 + ε * Λ * Real.sqrt d) * |Cg| * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) * N :=
          mul_le_mul_of_nonneg_right hKle hN0
      _ ≤ (1 + ε * Λ * Real.sqrt d) * |Cg| * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) *
            (M * (((departureRange (fun j => X j ω) n).filter
              (fun z => |euclidNorm z - r| ≤ 3)).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hvis hK0
      _ ≤ (1 + ε * Λ * Real.sqrt d) * |Cg| * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) *
            (M * ((d : ℝ) * unitBallVolume d * ((r : ℝ) + bd) ^ ((d : ℝ) - 1) *
              (T₂ - T₁))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcard hM0) hK0
      _ = (1 + ε * Λ * Real.sqrt d) * |Cg| * (d * unitBallVolume d) *
            (((r : ℝ) - 1) ^ (1 - (d : ℝ)) * ((r : ℝ) + bd) ^ ((d : ℝ) - 1)) *
              (M * (T₂ - T₁)) := by ring
      _ ≤ (1 + ε * Λ * Real.sqrt d) * |Cg| * (d * unitBallVolume d) * 3 ^ ((d : ℝ) - 1) *
            (M * (T₂ - T₁)) := by
          gcongr
      _ = (1 + ε * Λ * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
            (M * (T₂ - T₁)) := by ring
  have hY : (1 + ε * Λ * Real.sqrt d) * Cg * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) * N + W ≤
      (1 + ε * Λ * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
        (M * (T₂ - T₁)) + Cm * S := add_le_add hkey hW
  have hεc : 0 < ε * cΨ := mul_pos hε hcΨ
  have hs' : s ≤ unitBallVolume d * (ε * cΨ)⁻¹ *
      ((1 + ε * Λ * Real.sqrt d) * Cg * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) * N + W) := by
    calc s = unitBallVolume d * (ε * cΨ)⁻¹ * (ε * (cΨ * (unitBallVolume d)⁻¹) * s) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsrc (by positivity)
  have h2 : (0 : ℝ) ≤ 2 ^ ((d : ℝ) - 1) := by positivity
  have hmain : (d : ℝ) * unitBallVolume d * T₁ ≤ (d : ℝ) * unitBallVolume d *
      (2 ^ ((d : ℝ) - 1) * (d * ε * cΨ)⁻¹ *
        ((1 + ε * Λ * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
          (M * (T₂ - T₁)) + Cm * S)) := by
    calc (d : ℝ) * unitBallVolume d * T₁ ≤ 2 ^ ((d : ℝ) - 1) * s := htail
      _ ≤ 2 ^ ((d : ℝ) - 1) * (unitBallVolume d * (ε * cΨ)⁻¹ *
            ((1 + ε * Λ * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
              (M * (T₂ - T₁)) + Cm * S)) :=
          mul_le_mul_of_nonneg_left (hs'.trans (mul_le_mul_of_nonneg_left hY (by positivity)))
            h2
      _ = _ := by field_simp
  have hfin := le_of_mul_le_mul_left hmain hσ
  calc T₁ ≤ 2 ^ ((d : ℝ) - 1) * (d * ε * cΨ)⁻¹ *
        ((1 + ε * Λ * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
          (M * (T₂ - T₁)) + Cm * S) := hfin
    _ = 2 ^ ((d : ℝ) - 1) * (d * ε * cΨ)⁻¹ *
        ((1 + ε * Λ * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d)) *
          (M * (T₂ - T₁)) + 2 ^ ((d : ℝ) - 1) * (d * ε * cΨ)⁻¹ * Cm * S := by ring
    _ ≤ C * (M * (T₂ - T₁)) + C * S := by
        refine add_le_add (mul_le_mul_of_nonneg_right hCA hMΔ) (mul_le_mul_of_nonneg_right hCB hS0)
    _ = C * M * (T₂ - T₁) + C * Real.sqrt ((((departureRange (fun j => X j ω) n).filter
            (fun z => (r : ℝ) - bd ≤ euclidNorm z)).sup (localTime (fun j => X j ω) n) : ℕ)
              * (r : ℝ) ^ (1 - (d : ℝ)) * T₂ * L) + C * (r : ℝ) ^ (1 - (d : ℝ)) * L := by
        rw [hS]
        ring

/-! ### The radial test for the norm -/

/-- `lem:radial` for the walk with drift field the subgradients of a norm `Ψ`: with probability
at least `1 - Cn^{-p}`, simultaneously for all integers `ρ₀ ≤ ρ ≤ n`,
`F(ρ + 4d) ≤ C M_sh(ρ) [F(ρ - 4d) - F(ρ + 4d)]
  + C √(M_{ρ-4d} ρ^{1-d} F(ρ - 4d) log n) + C ρ^{1-d} log n`. -/
theorem norm_radial_test_holds : norm_radial_test.{u} := by
  intro d hd Ψ hΨ
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨b, h, hK⟩ := exists_kernelFacts hd
  obtain ⟨r₁, hr₁⟩ := hK.levels
  obtain ⟨R, Ca, -, hgradA⟩ := hK.gradAsymp
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  have hcΨ : 0 < normMin Ψ := (CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1).1
  have hΛ0 : 0 ≤ normMax Ψ := normMax_nonneg hΨ
  have hω0 : 0 < unitBallVolume d := unitBallVolume_pos d
  have hsqd : Real.sqrt d ≤ d := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hsq1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by linarith)
  set cΨ : ℝ := normMin Ψ with hcΨdef
  set Λ : ℝ := normMax Ψ with hΛdef
  set ρ₀ : ℝ := 8 * d + 1 + |r₁| + |R| + |Λ * Ca * unitBallVolume d / cΨ| + Real.sqrt d + 2
    with hρ₀def
  have hρ₀ : ∀ r : ℝ, ρ₀ ≤ r → r₁ ≤ r ∧ R ≤ r + 3 ∧ Λ * Ca * unitBallVolume d ≤ cΨ * (r + 3) ∧
      Real.sqrt d + 2 ≤ r ∧ 2 * (4 * (d : ℝ)) + 1 ≤ r := by
    intro r hr
    have h1 := le_abs_self r₁
    have h2 := le_abs_self R
    have h3 := abs_nonneg r₁
    have h4 := abs_nonneg R
    have h5 := abs_nonneg (Λ * Ca * unitBallVolume d / cΨ)
    have h6 := le_abs_self (Λ * Ca * unitBallVolume d / cΨ)
    have hq : Λ * Ca * unitBallVolume d / cΨ ≤ r := by linarith
    have hq' := (div_le_iff₀ hcΨ).mp hq
    refine ⟨by linarith, by linarith, by nlinarith, by linarith, by linarith⟩
  have hbd1 : 3 + Real.sqrt d / 2 < 4 * (d : ℝ) := by linarith
  have hbd2 : 2 + Real.sqrt d / 2 < 4 * (d : ℝ) := by linarith
  have hbdr : 4 * (d : ℝ) < ρ₀ := by
    have h3 := abs_nonneg r₁
    have h4 := abs_nonneg R
    have h5 := abs_nonneg (Λ * Ca * unitBallVolume d / cΨ)
    linarith
  have hρ₀' : Real.sqrt d + 2 ≤ ρ₀ := by
    have h3 := abs_nonneg r₁
    have h4 := abs_nonneg R
    have h5 := abs_nonneg (Λ * Ca * unitBallVolume d / cΨ)
    linarith
  refine ⟨ρ₀, by
    have h3 := abs_nonneg r₁
    have h4 := abs_nonneg R
    have h5 := abs_nonneg (Λ * Ca * unitBallVolume d / cΨ)
    linarith, ?_⟩
  intro ε hε hεΨ p hp
  obtain ⟨Cm, hCm0, hCm⟩ := exists_radial_mart_field.{u} hd hε.le hbd2 hbdr hρ₀' (b := b)
    (h := h) (Cg := Cg) (fun r hr x hx => (hr₁ r (hρ₀ r hr).1 x).1 hx) hgrad hp
  set c₁ : ℝ := 2 ^ ((d : ℝ) - 1) * (d * ε * cΨ)⁻¹ *
    ((1 + ε * Λ * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d)) with hc₁
  set c₂ : ℝ := 2 ^ ((d : ℝ) - 1) * (d * ε * cΨ)⁻¹ * Cm with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  refine ⟨Cm + c₁ + c₂ + 1, by positivity, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hell := drift_coord_bound hΨ hε hεΨ hξ hξ0
  have hEuler := euler_lower hΨ hd1 hξ hξ0
  have hnorm := norm_field_le hΨ hξ hξ0
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  refine measure_le_of_subset_union (fun ω hω => ?_) (hCm hell hX n hn) hX.start
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  by_contra hcon
  refine hω ?_
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨hA', hN'⟩ := hcon
  have h0 : X 0 ω = 0 := by simpa using hN'
  simp only [Set.mem_setOf_eq, not_exists, not_and, not_lt] at hA'
  intro r hr₀r hrn
  have hthr := hρ₀ (r : ℝ) hr₀r
  exact radial_pathwise_field hd r hε hcΨ hEuler hnorm hbd1 hthr.2.2.2.2
    (fun x hx => (hr₁ r hthr.1 x).1 hx) (fun x hx => (hr₁ r hthr.1 x).2 hx) hK.poisson hgradA
    hgrad hthr.2.1 hthr.2.2.1 X ω h0 n (Real.log (n : ℝ)) hL0 (hA' r hr₀r hrn)
    (by linarith) (by linarith)

end CERW.Support.Norm
