module

public import CERW.Support.Outer.Radius.HigherDimensionProfile

@[expose] public section

/-!
# Planar Profile Bounds

The planar potential is controlled on the boundary and across the outer annulus. Separate bounds
inside, between and outside the radii prepare the uniform profile estimate.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- If `w ≤ Kw √r lg^{5/2}` then `(r lg)^{1/4} √w ≤ √Kw √r lg^{3/2}`. -/
lemma co_planar_bd {Kw lg r w : ℝ} (hKw : 0 ≤ Kw) (hlg : 1 ≤ lg) (hr : 1 ≤ r)
    (h : w ≤ Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2))) :
    (r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w ≤ Real.sqrt Kw * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) := by
  have hr0 : 0 ≤ r := by linarith
  have hlg0 : 0 < lg := by linarith
  set t : ℝ := (r * lg) ^ ((1 : ℝ) / 4) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by positivity) _
  have ht2 : t ^ 2 = Real.sqrt r * lg ^ ((1 : ℝ) / 2) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    rw [show ((1 : ℝ) / 4) * ((2 : ℕ) : ℝ) = 1 / 2 by push_cast; ring,
      Real.mul_rpow hr0 hlg0.le, Real.sqrt_eq_rpow]
  have hZ : (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) ^ 2 = r * lg ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hr0, ← Real.rpow_natCast, ← Real.rpow_mul hlg0.le]
    norm_num
  have h1 : t ^ 2 * w ≤ Kw * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) ^ 2 := by
    rw [hZ, ht2]
    have e : Real.sqrt r * lg ^ ((1 : ℝ) / 2) * (Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2))) =
        Kw * (r * lg ^ 3) := by
      have e1 : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0
      have e2 : lg ^ ((1 : ℝ) / 2) * lg ^ ((5 : ℝ) / 2) = lg ^ 3 := by
        rw [← Real.rpow_add hlg0, ← Real.rpow_natCast]; norm_num
      calc Real.sqrt r * lg ^ ((1 : ℝ) / 2) * (Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)))
          = Kw * ((Real.sqrt r * Real.sqrt r) * (lg ^ ((1 : ℝ) / 2) * lg ^ ((5 : ℝ) / 2))) := by
            ring
        _ = Kw * (r * lg ^ 3) := by rw [e1, e2]
    rw [← e]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have h2 : t * Real.sqrt w = Real.sqrt (t ^ 2 * w) := by
    rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht0]
  rw [h2]
  calc Real.sqrt (t ^ 2 * w) ≤ Real.sqrt (Kw * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = Real.sqrt Kw * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) := by
        rw [Real.sqrt_mul hKw, Real.sqrt_sq (by positivity)]

/-- The width of the range in the plane: from the crossing bound and the inner radius bound,
`R - b + 2√d` is at most `Kw √r (log n)^{5/2}` and `r / log n`, and `b ≥ r/2`. -/
lemma co_planar_width {Cin Cout Kw sd r lg R b : ℝ} (hCin : 0 < Cin) (hsd : 0 < sd)
    (hKw : Kw = Cin + max Cout 0 + 2 * sd) (hr : 1 ≤ r) (hlg : 1 ≤ lg)
    (h1 : Kw * lg ^ ((7 : ℝ) / 2) ≤ r ^ ((1 : ℝ) / 2))
    (h2 : 2 * Cin * lg ^ ((1 : ℝ) / 2) ≤ r ^ ((1 : ℝ) / 2))
    (hbr : |b - r| ≤ Cin * Real.sqrt (r * lg))
    (hout : R ≤ r + Cout * (Real.sqrt r * lg ^ ((5 : ℝ) / 2))) :
    R - b + 2 * sd ≤ Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) ∧ R - b + 2 * sd ≤ r / lg ∧
      r / 2 ≤ b := by
  have hr0 : 0 < r := by linarith
  have hlg0 : 0 < lg := by linarith
  have hbr1 := abs_le.mp hbr
  have hsq1 : Real.sqrt lg ≤ lg ^ ((5 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hlg (by norm_num)
  have hT5 : Real.sqrt (r * lg) ≤ Real.sqrt r * lg ^ ((5 : ℝ) / 2) := by
    rw [Real.sqrt_mul hr0.le]
    exact mul_le_mul_of_nonneg_left hsq1 (Real.sqrt_nonneg _)
  have hZ5 : 1 ≤ Real.sqrt r * lg ^ ((5 : ℝ) / 2) := by
    have h5 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
    have h6 : 1 ≤ lg ^ ((5 : ℝ) / 2) := Real.one_le_rpow hlg (by norm_num)
    exact one_le_mul_of_one_le_of_one_le h5 h6
  have hwb : R - b + 2 * sd ≤ Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) := by
    have hc : Cout * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) ≤
        max Cout 0 * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    have h4 : Cin * Real.sqrt (r * lg) ≤ Cin * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hT5 hCin.le
    have h5 : 2 * sd ≤ 2 * sd * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) :=
      le_mul_of_one_le_right (by positivity) hZ5
    have h6 : Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) =
        Cin * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) +
          max Cout 0 * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) +
            2 * sd * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) := by rw [hKw]; ring
    rw [h6]
    linarith [hbr1.1]
  have hpr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0.le
  refine ⟨hwb, ?_, ?_⟩
  · rw [le_div_iff₀ hlg0]
    have hq : lg ^ ((5 : ℝ) / 2) * lg = lg ^ ((7 : ℝ) / 2) := by
      rw [← Real.rpow_add_one hlg0.ne']; norm_num
    calc (R - b + 2 * sd) * lg ≤ Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) * lg :=
          mul_le_mul_of_nonneg_right hwb hlg0.le
      _ = Real.sqrt r * (Kw * lg ^ ((7 : ℝ) / 2)) := by rw [← hq]; ring
      _ ≤ Real.sqrt r * Real.sqrt r := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          rw [Real.sqrt_eq_rpow]
          simpa using h1
      _ = r := hpr
  · have h7 : Cin * Real.sqrt (r * lg) ≤ r / 2 := by
      rw [Real.sqrt_mul hr0.le, Real.sqrt_eq_rpow lg]
      have h8 : 2 * Cin * lg ^ ((1 : ℝ) / 2) ≤ Real.sqrt r := by
        rw [Real.sqrt_eq_rpow]; simpa using h2
      calc Cin * (Real.sqrt r * lg ^ ((1 : ℝ) / 2)) =
          Real.sqrt r * (Cin * lg ^ ((1 : ℝ) / 2)) := by ring
        _ ≤ Real.sqrt r * (Real.sqrt r / 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
            linarith
        _ = (Real.sqrt r * Real.sqrt r) / 2 := by ring
        _ = r / 2 := by rw [hpr]
    linarith [hbr1.1]

/-- The bound on the error of the global local-time approximation in the plane. -/
lemma co_planar_delta {C₀ C₁ a r lg M L' : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 < C₁)
    (ha : 0 < a) (hr : 1 ≤ r) (hlg : 1 ≤ lg) (hM : M ≤ C₀ * (r / a))
    (hL'0 : 0 ≤ L') (hL' : L' ≤ 2 * lg) :
    C₁ * (Real.sqrt M * L' + L') ≤
      C₁ * (2 * Real.sqrt (C₀ / a) + 2) * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) := by
  have hr0 : 0 ≤ r := by linarith
  have hlg32 : lg ≤ lg ^ ((3 : ℝ) / 2) := by
    calc lg = lg ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ lg ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hlg (by norm_num)
  have hsr1 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
  have hZ0 : 0 ≤ Real.sqrt r * lg ^ ((3 : ℝ) / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by linarith) _)
  have hlgZ : lg ≤ Real.sqrt r * lg ^ ((3 : ℝ) / 2) := by
    calc lg ≤ 1 * lg ^ ((3 : ℝ) / 2) := by rw [one_mul]; exact hlg32
      _ ≤ Real.sqrt r * lg ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hsr1 (Real.rpow_nonneg (by linarith) _)
  have hsq : Real.sqrt M ≤ Real.sqrt (C₀ / a) * Real.sqrt r := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    calc M ≤ C₀ * (r / a) := hM
      _ = C₀ / a * r := by ring
  have h1 : Real.sqrt M * L' ≤ Real.sqrt (C₀ / a) * Real.sqrt r * (2 * lg) :=
    mul_le_mul hsq hL' hL'0 (by positivity)
  have h2 : Real.sqrt (C₀ / a) * Real.sqrt r * (2 * lg) ≤
      2 * Real.sqrt (C₀ / a) * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) := by
    have : Real.sqrt r * lg ≤ Real.sqrt r * lg ^ ((3 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hlg32 (Real.sqrt_nonneg _)
    calc Real.sqrt (C₀ / a) * Real.sqrt r * (2 * lg)
        = 2 * Real.sqrt (C₀ / a) * (Real.sqrt r * lg) := by ring
      _ ≤ 2 * Real.sqrt (C₀ / a) * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
  have h3 : L' ≤ 2 * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) := by linarith
  have h4 : Real.sqrt M * L' + L' ≤
      (2 * Real.sqrt (C₀ / a) + 2) * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) := by
    rw [add_mul]; linarith
  exact (mul_le_mul_of_nonneg_left h4 hC₁.le).trans_eq (by ring)

/-- Inside the inner ball the local time is within `C Z` of the cone. -/
lemma co_planar_inside {ℓ U Ub UE cone δ Bd Cδ Cbd Z T D Cin C : ℝ} (hD : 0 ≤ D)
    (hg : |ℓ - U| ≤ δ) (hU : U = Ub + UE) (hdiff : |Ub - cone| ≤ D * (Cin * T))
    (hUE0 : 0 ≤ UE) (hUE : UE ≤ Bd) (hδ : δ ≤ Cδ * Z) (hBd : Bd ≤ Cbd * Z) (hT : T ≤ Z)
    (hCin : 0 ≤ Cin) (hC : Cδ * Z + D * (Cin * Z) + Cbd * Z ≤ C * Z) : |ℓ - cone| ≤ C * Z := by
  have h1 : D * (Cin * T) ≤ D * (Cin * Z) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT hCin) hD
  have h2 : ℓ - cone = (ℓ - U) + (Ub - cone) + UE := by rw [hU]; ring
  rw [h2]
  have h3 := abs_add_le ((ℓ - U) + (Ub - cone)) UE
  have h4 := abs_add_le (ℓ - U) (Ub - cone)
  rw [abs_of_nonneg hUE0] at h3
  linarith

/-- Between the inner ball and the outer radius the local time and the cone are nonnegative and
bounded by `C Z`. -/
lemma co_planar_between {ℓ UE cone Bd Cδ Cbd Z T D Cin C : ℝ} (hD : 0 ≤ D)
    (hℓ0 : 0 ≤ ℓ) (hcone0 : 0 ≤ cone) (hℓ : ℓ ≤ Cδ * Z + UE) (hUE : UE ≤ Bd)
    (hcone : cone ≤ D * (Cin * T)) (hBd : Bd ≤ Cbd * Z) (hT : T ≤ Z) (hCin : 0 ≤ Cin)
    (hZ0 : 0 ≤ Z)
    (hC : Cδ * Z + D * (Cin * Z) + Cbd * Z ≤ C * Z) : |ℓ - cone| ≤ C * Z := by
  have h1 : D * (Cin * T) ≤ D * (Cin * Z) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT hCin) hD
  have h2 : 0 ≤ D * (Cin * Z) := mul_nonneg hD (mul_nonneg hCin hZ0)
  rw [abs_le]
  constructor <;> linarith

/-- Beyond the outer radius the local time vanishes and the cone is at most `C Z`. -/
lemma co_planar_outside {D Cin sd r lg Z b R ν Cδ Cbd C : ℝ} (hD : 0 ≤ D)
    (hCin : 0 < Cin) (hsd : 0 < sd) (hlg : 1 ≤ lg) (hlgZ : lg ≤ Z)
    (hT : Real.sqrt (r * lg) ≤ Z) (hbr : |b - r| ≤ Cin * Real.sqrt (r * lg))
    (hbR : b ≤ R + sd / 2) (hν : R < ν)
    (hC : C * Z = Cδ * Z + D * ((Cin + sd) * Z) + Cbd * Z) (hCδZ : 0 ≤ Cδ * Z)
    (hCbdZ : 0 ≤ Cbd * Z) : D * max (r - ν) 0 ≤ C * Z := by
  have hZ1 : 1 ≤ Z := hlg.trans hlgZ
  have hr1 := (abs_le.mp hbr).1
  have hrν : r - ν ≤ (Cin + sd) * Z := by
    have h1 : r - R ≤ r - b + sd / 2 := by linarith
    have h3 : sd / 2 ≤ sd * Z := by
      calc sd / 2 ≤ sd * 1 := by linarith
        _ ≤ sd * Z := mul_le_mul_of_nonneg_left hZ1 hsd.le
    have h4 : Cin * Real.sqrt (r * lg) ≤ Cin * Z := mul_le_mul_of_nonneg_left hT hCin.le
    have h5 : (Cin + sd) * Z = Cin * Z + sd * Z := by ring
    rw [h5]
    linarith
  have hmax : max (r - ν) 0 ≤ (Cin + sd) * Z :=
    max_le hrν (by positivity)
  calc D * max (r - ν) 0 ≤ D * ((Cin + sd) * Z) := mul_le_mul_of_nonneg_left hmax hD
    _ ≤ C * Z := by rw [hC]; linarith

end CERW.Support.Outer.Radius
