import CERW.Support.Outer.Radius.NewtonConvolution

/-!
# Lattice Kernel

The lattice kernel satisfies convolution and summation bounds. A discrete absorption estimate
controls the weighted local-time sum.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- Young's inequality for a square root: `A √(B L) ≤ λ B + A² L / (4 λ)`. -/
lemma ev_mul_sqrt_le_add (B L A lam : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) (hA : 0 ≤ A)
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
noncomputable def ev_kern (d : ℕ) (w : Site d) : ℝ :=
  (1 + euclidNorm w) ^ (2 - 2 * (d : ℝ))

/-- The lattice weight is nonnegative. -/
lemma ev_kern_nonneg (w : Site d) : 0 ≤ ev_kern d w :=
  Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg w]) _

/-- The lattice weight is symmetric: `k(x - y) = k(y - x)`. -/
lemma ev_kern_sub_comm (x y : Site d) : ev_kern d (x - y) = ev_kern d (y - x) := by
  unfold ev_kern
  rw [← neg_sub y x, CERW.Generic.Lattice.euclidNorm_neg]

/-- Comparison of powers with a nonpositive exponent: if `1 + f ≤ c (1 + e)` then
`(1 + e)^q ≤ c^{-q} (1 + f)^q`. -/
lemma ev_rpow_le_mul_rpow_of_le {e f c q : ℝ} (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < c)
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
lemma ev_euclidNorm_sub_le_add (z y x : Site d) :
    euclidNorm (z - x) ≤ euclidNorm (z - y) + euclidNorm (y - x) := by
  have h := CERW.Support.Occupation.euclidNorm_add_le (z - y) (y - x)
  rwa [sub_add_sub_cancel] at h

/-- If `e ≥ ρ / 2` then the weight at `e` is at most `2^{2d-2}` times the weight at `ρ`. -/
lemma ev_rpow_le_two_rpow_mul {e ρ q : ℝ} (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hq : q ≤ 0)
    (h : ρ / 2 ≤ e) : (1 + e) ^ q ≤ (2 : ℝ) ^ (-q) * (1 + ρ) ^ q :=
  ev_rpow_le_mul_rpow_of_le he hρ (by norm_num) hq (by linarith)

/-- Each term of the lattice convolution of two weights is at most `2^{2d-2} k(z - x)` times
the sum of the two weights. -/
lemma ev_kern_mul_le (hd : 1 ≤ d) (z y x : Site d) :
    ev_kern d (z - y) * ev_kern d (y - x) ≤
      (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) *
        (ev_kern d (z - y) + ev_kern d (y - x)) := by
  have hq : 2 - 2 * (d : ℝ) ≤ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hk1 := ev_kern_nonneg (z - y)
  have hk2 := ev_kern_nonneg (y - x)
  have hk3 := ev_kern_nonneg (z - x)
  have hc : 0 ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have htri := ev_euclidNorm_sub_le_add z y x
  have hn1 := LatticeProb.euclidNorm_nonneg (z - y)
  have hn2 := LatticeProb.euclidNorm_nonneg (y - x)
  have hn3 := LatticeProb.euclidNorm_nonneg (z - x)
  by_cases hcase : euclidNorm (z - x) / 2 ≤ euclidNorm (y - x)
  · have hb : ev_kern d (y - x) ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) :=
      ev_rpow_le_two_rpow_mul hn2 hn3 hq hcase
    calc ev_kern d (z - y) * ev_kern d (y - x)
        ≤ ev_kern d (z - y) * ((2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x)) :=
          mul_le_mul_of_nonneg_left hb hk1
      _ = (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) * ev_kern d (z - y) := by ring
      _ ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) *
            (ev_kern d (z - y) + ev_kern d (y - x)) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc hk3)
  · have hcase' : euclidNorm (z - x) / 2 ≤ euclidNorm (z - y) := by
      rw [not_le] at hcase
      linarith
    have ha : ev_kern d (z - y) ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) :=
      ev_rpow_le_two_rpow_mul hn1 hn3 hq hcase'
    calc ev_kern d (z - y) * ev_kern d (y - x)
        ≤ ((2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x)) * ev_kern d (y - x) :=
          mul_le_mul_of_nonneg_right ha hk2
      _ ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) *
            (ev_kern d (z - y) + ev_kern d (y - x)) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc hk3)

/-- The lattice convolution of the weight with itself, over any finite set, is bounded by a
constant multiple of the weight. -/
lemma ev_sum_kern_mul_kern_le (hd : 1 ≤ d) {K₀ : ℝ}
    (hK₀ : ∀ (F : Finset (Site d)) (u : Site d), ∑ y ∈ F, ev_kern d (y - u) ≤ K₀)
    (F : Finset (Site d)) (z x : Site d) :
    ∑ y ∈ F, ev_kern d (z - y) * ev_kern d (y - x) ≤
      (2 * (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * K₀) * ev_kern d (z - x) := by
  have hk3 := ev_kern_nonneg (z - x)
  have hc : 0 ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hsum1 : ∑ y ∈ F, ev_kern d (z - y) ≤ K₀ := by
    have := hK₀ F z
    simpa only [ev_kern_sub_comm z] using this
  have hsum2 := hK₀ F x
  calc ∑ y ∈ F, ev_kern d (z - y) * ev_kern d (y - x)
      ≤ ∑ y ∈ F, (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) *
          (ev_kern d (z - y) + ev_kern d (y - x)) :=
        Finset.sum_le_sum fun y _ => ev_kern_mul_le hd z y x
    _ = (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) *
          (∑ y ∈ F, ev_kern d (z - y) + ∑ y ∈ F, ev_kern d (y - x)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) * (K₀ + K₀) :=
        mul_le_mul_of_nonneg_left (add_le_add hsum1 hsum2) (mul_nonneg hc hk3)
    _ = (2 * (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * K₀) * ev_kern d (z - x) := by ring

/-- The lattice absorption estimate: if the local time satisfies the pointwise bound on `S`
with a square root of the kernel sum, and `a` is comparable to the kernel at `z`, then the
`a`-weighted local time sum is bounded by twice the `a`-weighted potential sum, up to a
multiple of `L`. -/
lemma ev_absorb_sum {ℓ U a : Site d → ℝ} {S : Finset (Site d)} {z : Site d}
    {c₀ c₁ K₀ A₀ C₁ L γ : ℝ}
    (hK₀ : ∀ (F : Finset (Site d)) (u : Site d), ∑ y ∈ F, ev_kern d (y - u) ≤ K₀)
    (hconv : ∀ (F : Finset (Site d)) (x : Site d),
      ∑ y ∈ F, ev_kern d (z - y) * ev_kern d (y - x) ≤ A₀ * ev_kern d (z - x))
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hA₀ : 0 ≤ A₀)
    (ha : ∀ y, c₀ * ev_kern d (z - y) ≤ a y ∧ a y ≤ c₁ * ev_kern d (z - y))
    (hℓ0 : ∀ y, 0 ≤ ℓ y) (hC₁ : 0 ≤ C₁) (hL : 0 ≤ L) (hγ : 0 < γ)
    (hγ' : γ * (c₁ * A₀) ≤ c₀ / 2)
    (hfine : ∀ y ∈ S,
      ℓ y ≤ U y + C₁ * (Real.sqrt ((∑ x ∈ S, ℓ x * ev_kern d (x - y)) * L) + L)) :
    ∑ y ∈ S, a y * ℓ y ≤
      2 * ∑ y ∈ S, a y * U y + 2 * ((C₁ + C₁ ^ 2 / (4 * γ)) * L) * (c₁ * K₀) := by
  have ha0 : ∀ y, 0 ≤ a y := fun y => (mul_nonneg hc₀.le (ev_kern_nonneg _)).trans (ha y).1
  set W : Site d → ℝ := fun y => ∑ x ∈ S, ℓ x * ev_kern d (x - y) with hW
  have hW0 : ∀ y, 0 ≤ W y := fun y =>
    Finset.sum_nonneg fun x _ => mul_nonneg (hℓ0 x) (ev_kern_nonneg _)
  set Cg : ℝ := C₁ + C₁ ^ 2 / (4 * γ) with hCg
  have hCg0 : 0 ≤ Cg := by rw [hCg]; positivity
  have h1 : ∀ y ∈ S, ℓ y ≤ U y + Cg * L + γ * W y := by
    intro y hy
    have h := hfine y hy
    have hyoung := ev_mul_sqrt_le_add (W y) L C₁ γ (hW0 y) hL hC₁ hγ
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
    calc ∑ y ∈ S, a y ≤ ∑ y ∈ S, c₁ * ev_kern d (y - z) :=
          Finset.sum_le_sum fun y _ => by rw [← ev_kern_sub_comm z y]; exact (ha y).2
      _ = c₁ * ∑ y ∈ S, ev_kern d (y - z) := by rw [Finset.mul_sum]
      _ ≤ c₁ * K₀ := mul_le_mul_of_nonneg_left (hK₀ S z) hc₁.le
  have hswap : ∑ y ∈ S, a y * W y = ∑ x ∈ S, ℓ x * ∑ y ∈ S, a y * ev_kern d (x - y) := by
    simp only [hW, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have hinner : ∀ x, ∑ y ∈ S, a y * ev_kern d (x - y) ≤ c₁ * A₀ * ev_kern d (z - x) := by
    intro x
    calc ∑ y ∈ S, a y * ev_kern d (x - y)
        ≤ ∑ y ∈ S, c₁ * (ev_kern d (z - y) * ev_kern d (y - x)) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [ev_kern_sub_comm x y]
          calc a y * ev_kern d (y - x) ≤ (c₁ * ev_kern d (z - y)) * ev_kern d (y - x) :=
                mul_le_mul_of_nonneg_right (ha y).2 (ev_kern_nonneg _)
            _ = c₁ * (ev_kern d (z - y) * ev_kern d (y - x)) := by ring
      _ = c₁ * ∑ y ∈ S, ev_kern d (z - y) * ev_kern d (y - x) := by rw [Finset.mul_sum]
      _ ≤ c₁ * (A₀ * ev_kern d (z - x)) := mul_le_mul_of_nonneg_left (hconv S x) hc₁.le
      _ = c₁ * A₀ * ev_kern d (z - x) := by ring
  have hAW : c₀ * ∑ y ∈ S, a y * W y ≤ c₁ * A₀ * ∑ x ∈ S, a x * ℓ x := by
    rw [hswap, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have hnn : 0 ≤ c₁ * A₀ * ℓ x := mul_nonneg (mul_nonneg hc₁.le hA₀) (hℓ0 x)
    calc c₀ * (ℓ x * ∑ y ∈ S, a y * ev_kern d (x - y))
        ≤ c₀ * (ℓ x * (c₁ * A₀ * ev_kern d (z - x))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hinner x) (hℓ0 x)) hc₀.le
      _ = c₁ * A₀ * ℓ x * (c₀ * ev_kern d (z - x)) := by ring
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

end CERW.Support.Outer.Radius
