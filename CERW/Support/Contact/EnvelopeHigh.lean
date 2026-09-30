import CERW.Generic.Lattice.Resolvent
import CERW.Generic.Lattice.SummableSums
import CERW.Generic.Lattice.WeightSums
import CERW.Model.Occupation
import CERW.Support.Occupation.SiteArith

/-!
# The local-time envelope in dimensions three and higher

`eq:resolvent`, `eq:envelopehigh` and `eq:holebracket`, deterministically, for `d ≥ 3`.
Suppose that at every departure site
`ℓ_n(y) ≤ c₀ s_b(y) + A₁ + A₂ √(B_y L)`, where `s_b(y) = (b - |y|)_+`,
`k(w) = (1 + |w|)^{2-2d}` and `B_y = Σ_x ℓ_n(x) k(x - y)`. Young's inequality turns the
square root into `λ B_y + A₂² L/(4λ)`. The kernel `k` has bounded mass `k₀` and first moment
`J = O(L)`. The resolvent bound therefore gives
`ℓ_n ≤ C (c₀ s_b + A₁ + A₂² L + c₀ L)` everywhere. At a site
`z` with `b ≤ |z| ≤ n`, `s_b(x) ≤ |x - z|`, so `B_z ≤ C (A₁ + A₂² L + c₀ L)`.
-/

namespace CERW.Support.Contact

open LatticeProb Finset CERW CERW.Generic.Lattice
open CERW.Support.Occupation

variable {d : ℕ}

/-- The Euclidean norm is `1`-Lipschitz with respect to itself. -/
private lemma abs_euclidNorm_sub_le (x y : Site d) :
    |euclidNorm x - euclidNorm y| ≤ euclidNorm (x - y) := by
  have h := abs_norm_sub_norm_le (toSpace x) (toSpace y)
  rw [norm_toSpace, norm_toSpace] at h
  rwa [show euclidNorm (x - y) = ‖toSpace x - toSpace y‖ by
        rw [← norm_toSpace (x - y), toSpace_sub]]

/-- The profile `s_b(u) = (b - |u|)_+` is `1`-Lipschitz. -/
private lemma max_sub_max_le_euclidNorm (b : ℝ) (u v : Site d) :
    max (b - euclidNorm u) 0 - max (b - euclidNorm v) 0 ≤ euclidNorm (u - v) := by
  have h1 : |max (b - euclidNorm u) 0 - max (b - euclidNorm v) 0|
      ≤ |(b - euclidNorm u) - (b - euclidNorm v)| :=
    abs_max_sub_max_le_abs _ _ _
  have h2 : (b - euclidNorm u) - (b - euclidNorm v) = euclidNorm v - euclidNorm u := by ring
  have h3 : |euclidNorm v - euclidNorm u| ≤ euclidNorm (u - v) := by
    have h := abs_euclidNorm_sub_le v u
    rwa [show v - u = -(u - v) by abel, euclidNorm_neg] at h
  calc max (b - euclidNorm u) 0 - max (b - euclidNorm v) 0
      ≤ |max (b - euclidNorm u) 0 - max (b - euclidNorm v) 0| := le_abs_self _
    _ ≤ |(b - euclidNorm u) - (b - euclidNorm v)| := h1
    _ = |euclidNorm v - euclidNorm u| := by rw [h2]
    _ ≤ euclidNorm (u - v) := h3

/-- The departure local time at a site is at most the time horizon. -/
private lemma localTime_cast_le (X : ℕ → Site d) (n : ℕ) (y : Site d) :
    (localTime X n y : ℝ) ≤ n := by
  have h : localTime X n y ≤ n := by
    rw [localTime]
    calc ((Finset.range n).filter fun j => X j = y).card ≤ (Finset.range n).card :=
          Finset.card_filter_le _ _
      _ = n := Finset.card_range n
  exact_mod_cast h

/-- Every departure site lies within the radius bound. -/
private lemma euclidNorm_le_of_mem_departureRange {X : ℕ → Site d} {n : ℕ}
    (hXn : ∀ j < n, euclidNorm (X j) ≤ n) {y : Site d}
    (hy : y ∈ departureRange X n) : euclidNorm y ≤ n := by
  obtain ⟨j, hj, hjy⟩ := Finset.mem_image.mp hy
  rw [← hjy]
  exact hXn j (Finset.mem_range.mp hj)

/-- Off the departure range the departure local time vanishes. -/
private lemma localTime_eq_zero_of_not_mem {X : ℕ → Site d} {n : ℕ} {y : Site d}
    (hy : y ∉ departureRange X n) : localTime X n y = 0 := by
  rw [mem_departureRange_iff, not_lt] at hy
  exact Nat.le_zero.mp hy

/-- Young's inequality in the form `A √(B L) ≤ λ B + A² L/(4λ)`. -/
private lemma sqrt_young (B L A lam : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) (hA : 0 ≤ A)
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

/-- The bracket `B_y` at a departure site is bounded by the convolution of the kernel against the
local time. -/
private lemma localTime_bracket_le_conv {X : ℕ → Site d} {n : ℕ}
    (hXn : ∀ j < n, euclidNorm (X j) ≤ n) {y : Site d}
    (hy : y ∈ departureRange X n) :
    (∑ x ∈ departureRange X n, (localTime X n x : ℝ) *
        (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)))
      ≤ ∑ w ∈ ballFinset d (2 * (n : ℝ)),
          (1 + euclidNorm w) ^ (2 - 2 * (d : ℝ)) *
            (localTime X n (y - w) : ℝ) := by
  have hinj : Set.InjOn (fun x : Site d => y - x) (departureRange X n) :=
    fun a ha b hb hab => sub_right_injective hab
  have hEq : (∑ x ∈ departureRange X n, (localTime X n x : ℝ) *
        (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)))
      = ∑ w ∈ (departureRange X n).image (fun x => y - x),
          (1 + euclidNorm w) ^ (2 - 2 * (d : ℝ)) *
            (localTime X n (y - w) : ℝ) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [show y - (y - x) = x by abel]
    have hxy : euclidNorm (x - y) = euclidNorm (y - x) := by
      rw [show x - y = -(y - x) by abel, euclidNorm_neg]
    rw [hxy]
    ring
  rw [hEq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w hw
    rcases Finset.mem_image.mp hw with ⟨x, hx, rfl⟩
    rw [mem_ballFinset_iff]
    calc euclidNorm (y - x) ≤ euclidNorm y + euclidNorm x := euclidNorm_sub_le y x
      _ ≤ (n : ℝ) + (n : ℝ) :=
            add_le_add (euclidNorm_le_of_mem_departureRange hXn hy)
              (euclidNorm_le_of_mem_departureRange hXn hx)
      _ = 2 * (n : ℝ) := by ring
  · intro w hwS hwnot
    exact mul_nonneg (Real.rpow_nonneg (by linarith [euclidNorm_nonneg w]) _)
      (Nat.cast_nonneg _)

/-- Linearity of `Σ_x (a f x + c) g x`. -/
private lemma sum_mul_add_mul (s : Finset (Site d)) (f g : Site d → ℝ) (a c : ℝ) :
    ∑ x ∈ s, (a * f x + c) * g x = a * (∑ x ∈ s, f x * g x) + c * ∑ x ∈ s, g x := by
  have h : ∑ x ∈ s, (a * f x + c) * g x = ∑ x ∈ s, (a * f x * g x + c * g x) :=
    Finset.sum_congr rfl (fun x hx => by rw [add_mul])
  rw [h, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x hx => by ring)
  · rw [Finset.mul_sum]

/-- Pulling a constant out of `Σ_x Cp (a f x + c) g x`. -/
private lemma sum_Cp_mul (s : Finset (Site d)) (f g : Site d → ℝ) (a c Cp : ℝ) :
    ∑ x ∈ s, Cp * (a * f x + c) * g x
      = Cp * (a * (∑ x ∈ s, f x * g x) + c * (∑ x ∈ s, g x)) := by
  rw [show ∑ x ∈ s, Cp * (a * f x + c) * g x
        = Cp * ∑ x ∈ s, (a * f x + c) * g x by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x hx => by ring)]
  rw [sum_mul_add_mul]

/-- Bounds the bracket sum at an interior site from a pointwise envelope. -/
private lemma bracket_sum_le (S : Finset (Site d)) (k s ℓ : Site d → ℝ) (z : Site d)
    (c₀ A₁ A₂ Cp Ck Cj Cfin L : ℝ)
    (hpoint : ∀ y, ℓ y ≤ Cp * (c₀ * s y + A₁ + A₂ ^ 2 * L + c₀ * L))
    (hk_nonneg : ∀ w, 0 ≤ k w)
    (hSumS : ∑ x ∈ S, s x * k (x - z) ≤ 2 * Cj * L)
    (hSumK : ∑ x ∈ S, k (x - z) ≤ Ck)
    (hE : 0 ≤ A₁ + A₂ ^ 2 * L + c₀ * L)
    (hc0 : 0 ≤ c₀) (hA₁ : 0 ≤ A₁) (hL0 : 0 ≤ L)
    (hCjpos : 0 < Cj) (hCp : 0 < Cp)
    (hcoefle : Cp * (Ck + 2 * Cj) ≤ Cfin) :
    ∑ x ∈ S, ℓ x * k (x - z) ≤ Cfin * (A₁ + A₂ ^ 2 * L + c₀ * L) := by
  have hmain : ∑ x ∈ S, ℓ x * k (x - z)
      ≤ Cp * (c₀ * (∑ x ∈ S, s x * k (x - z)) +
          (A₁ + A₂ ^ 2 * L + c₀ * L) * (∑ x ∈ S, k (x - z))) := by
    have h1 : ∑ x ∈ S, ℓ x * k (x - z)
        ≤ ∑ x ∈ S, Cp * (c₀ * s x + (A₁ + A₂ ^ 2 * L + c₀ * L)) * k (x - z) := by
      refine Finset.sum_le_sum fun x hx => ?_
      have hxle := hpoint x
      have hkx : 0 ≤ k (x - z) := hk_nonneg _
      calc ℓ x * k (x - z)
          ≤ (Cp * (c₀ * s x + A₁ + A₂ ^ 2 * L + c₀ * L)) * k (x - z) :=
            mul_le_mul_of_nonneg_right hxle hkx
        _ = Cp * (c₀ * s x + (A₁ + A₂ ^ 2 * L + c₀ * L)) * k (x - z) := by ring
    calc ∑ x ∈ S, ℓ x * k (x - z)
        ≤ ∑ x ∈ S, Cp * (c₀ * s x + (A₁ + A₂ ^ 2 * L + c₀ * L)) * k (x - z) := h1
      _ = Cp * (c₀ * (∑ x ∈ S, s x * k (x - z)) +
            (A₁ + A₂ ^ 2 * L + c₀ * L) * (∑ x ∈ S, k (x - z))) :=
          sum_Cp_mul _ _ _ c₀ (A₁ + A₂ ^ 2 * L + c₀ * L) Cp
  have hfinal : ∑ x ∈ S, ℓ x * k (x - z) ≤ Cfin * (A₁ + A₂ ^ 2 * L + c₀ * L) := by
    have hs1 : c₀ * (∑ x ∈ S, s x * k (x - z)) ≤ c₀ * (2 * Cj * L) :=
      mul_le_mul_of_nonneg_left hSumS hc0
    have hs2 : (A₁ + A₂ ^ 2 * L + c₀ * L) * (∑ x ∈ S, k (x - z))
        ≤ (A₁ + A₂ ^ 2 * L + c₀ * L) * Ck :=
      mul_le_mul_of_nonneg_left hSumK hE
    have hstep1 : Cp * (c₀ * (∑ x ∈ S, s x * k (x - z)) +
          (A₁ + A₂ ^ 2 * L + c₀ * L) * (∑ x ∈ S, k (x - z)))
        ≤ Cp * (c₀ * (2 * Cj * L) + (A₁ + A₂ ^ 2 * L + c₀ * L) * Ck) :=
      mul_le_mul_of_nonneg_left (add_le_add hs1 hs2) hCp.le
    have hstep2 : Cp * (c₀ * (2 * Cj * L) + (A₁ + A₂ ^ 2 * L + c₀ * L) * Ck)
        = Cp * (Ck * A₁ + Ck * (A₂ ^ 2 * L) + (Ck + 2 * Cj) * (c₀ * L)) := by ring
    have hstep3 : Cp * (Ck * A₁ + Ck * (A₂ ^ 2 * L) + (Ck + 2 * Cj) * (c₀ * L))
        ≤ Cp * (Ck + 2 * Cj) * (A₁ + A₂ ^ 2 * L + c₀ * L) := by
      have h2 : 0 ≤ A₂ ^ 2 * L := mul_nonneg (sq_nonneg A₂) hL0
      have hinner : Ck * A₁ + Ck * (A₂ ^ 2 * L) + (Ck + 2 * Cj) * (c₀ * L)
          ≤ (Ck + 2 * Cj) * (A₁ + A₂ ^ 2 * L + c₀ * L) := by
        have h1 : 0 ≤ 2 * Cj * A₁ := by positivity
        have h2 : 0 ≤ 2 * Cj * (A₂ ^ 2 * L) := by positivity
        calc Ck * A₁ + Ck * (A₂ ^ 2 * L) + (Ck + 2 * Cj) * (c₀ * L)
            = (Ck + 2 * Cj) * (A₁ + A₂ ^ 2 * L + c₀ * L)
              - (2 * Cj * A₁ + 2 * Cj * (A₂ ^ 2 * L)) := by ring
          _ ≤ (Ck + 2 * Cj) * (A₁ + A₂ ^ 2 * L + c₀ * L) := by linarith
      calc Cp * (Ck * A₁ + Ck * (A₂ ^ 2 * L) + (Ck + 2 * Cj) * (c₀ * L))
          ≤ Cp * ((Ck + 2 * Cj) * (A₁ + A₂ ^ 2 * L + c₀ * L)) :=
            mul_le_mul_of_nonneg_left hinner hCp.le
        _ = Cp * (Ck + 2 * Cj) * (A₁ + A₂ ^ 2 * L + c₀ * L) := by ring
    calc ∑ x ∈ S, ℓ x * k (x - z)
        ≤ Cp * (c₀ * (2 * Cj * L) + (A₁ + A₂ ^ 2 * L + c₀ * L) * Ck) :=
          le_trans hmain hstep1
      _ = Cp * (Ck * A₁ + Ck * (A₂ ^ 2 * L) + (Ck + 2 * Cj) * (c₀ * L)) := hstep2
      _ ≤ Cp * (Ck + 2 * Cj) * (A₁ + A₂ ^ 2 * L + c₀ * L) := hstep3
      _ ≤ Cfin * (A₁ + A₂ ^ 2 * L + c₀ * L) :=
          mul_le_mul_of_nonneg_right hcoefle hE
  exact hfinal

/-- The pointwise envelope bound follows from the convolution inequality. -/
private lemma pointwise_bound (ℓ s : Site d → ℝ)
    (c₀ A₁ A₂ Cp L J c lam Ck Cj : ℝ)
    (hconv : ∀ y, ℓ y ≤ 2 * c₀ * s y + 2 * c + 4 * lam * c₀ * J)
    (hJle : J ≤ 2 * Cj * L)
    (hcdef : c = A₁ + A₂ ^ 2 * L / (4 * lam))
    (hlam_eq : lam = 1 / (2 * (Ck + 1)))
    (hCp_eq : Cp = 2 + (Ck + 1) + 2 * (2 * Cj) / (Ck + 1))
    (hL0 : 0 ≤ L) (hc0 : 0 ≤ c₀) (hA₁ : 0 ≤ A₁)
    (hs0 : ∀ y, 0 ≤ s y) (hlam : 0 < lam) (hCkpos : 0 < Ck) (hCjpos : 0 < Cj) :
    ∀ y, ℓ y ≤ Cp * (c₀ * s y + A₁ + A₂ ^ 2 * L + c₀ * L) := by
  intro y
  have hJterm : 4 * lam * c₀ * J ≤ (4 * Cj / (Ck + 1)) * (c₀ * L) := by
    have hcoef : 4 * lam * (2 * Cj) = 4 * Cj / (Ck + 1) := by
      rw [hlam_eq]
      field_simp
    calc 4 * lam * c₀ * J ≤ 4 * lam * c₀ * (2 * Cj * L) := by
          have h4 : 0 ≤ 4 * lam * c₀ := by positivity
          have hmul := mul_le_mul_of_nonneg_left hJle h4
          nlinarith
      _ = (4 * Cj / (Ck + 1)) * (c₀ * L) := by
          rw [← hcoef]
          ring
  have hcterm : 2 * c = 2 * A₁ + (Ck + 1) * A₂ ^ 2 * L := by
    rw [hcdef, hlam_eq]
    field_simp
    ring
  have hmid : ℓ y ≤ 2 * (c₀ * s y) + 2 * A₁ + (Ck + 1) * (A₂ ^ 2 * L) +
      (4 * Cj / (Ck + 1)) * (c₀ * L) := by
    nlinarith only [hconv y, hcterm, hJterm]
  have hCp2 : 2 ≤ Cp := by
    rw [hCp_eq]
    have h1 : (0 : ℝ) ≤ Ck + 1 := by linarith only [hCkpos]
    have h2 : (0 : ℝ) ≤ 2 * (2 * Cj) / (Ck + 1) := by positivity
    linarith only [h1, h2]
  have hCpCk : Ck + 1 ≤ Cp := by
    rw [hCp_eq]
    have h1 : (0 : ℝ) ≤ Ck + 1 := by linarith only [hCkpos]
    have h2 : (0 : ℝ) ≤ 2 * (2 * Cj) / (Ck + 1) := by positivity
    linarith only [h1, h2]
  have hCpCj : 4 * Cj / (Ck + 1) ≤ Cp := by
    rw [hCp_eq]
    have h1 : (0 : ℝ) ≤ Ck + 1 := by linarith only [hCkpos]
    have : 4 * Cj / (Ck + 1) = 2 * (2 * Cj) / (Ck + 1) := by ring
    rw [this]
    linarith only [h1]
  have h0 : 0 ≤ c₀ * s y := mul_nonneg hc0 (hs0 y)
  have h2 : 0 ≤ A₂ ^ 2 * L := mul_nonneg (sq_nonneg A₂) hL0
  have h3 : 0 ≤ c₀ * L := mul_nonneg hc0 hL0
  have e1 : 2 * (c₀ * s y) ≤ Cp * (c₀ * s y) := mul_le_mul_of_nonneg_right hCp2 h0
  have e2 : 2 * A₁ ≤ Cp * A₁ := mul_le_mul_of_nonneg_right hCp2 hA₁
  have e3 : (Ck + 1) * (A₂ ^ 2 * L) ≤ Cp * (A₂ ^ 2 * L) :=
    mul_le_mul_of_nonneg_right hCpCk h2
  have e4 : (4 * Cj / (Ck + 1)) * (c₀ * L) ≤ Cp * (c₀ * L) :=
    mul_le_mul_of_nonneg_right hCpCj h3
  have hexp : Cp * (c₀ * s y + A₁ + A₂ ^ 2 * L + c₀ * L)
      = Cp * (c₀ * s y) + Cp * A₁ + Cp * (A₂ ^ 2 * L) + Cp * (c₀ * L) := by ring
  rw [hexp]
  linarith only [e1, e2, e3, e4, hmid]

/-- `eq:envelopehigh` and `eq:holebracket` for `d ≥ 3`, from the pointwise envelope at departure
sites. -/
theorem exists_envelope_high (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ → Site d) (n : ℕ) (c₀ b A₁ A₂ : ℝ), 1 ≤ n → 0 ≤ c₀ → 0 ≤ A₁ →
      0 ≤ A₂ → (∀ j < n, euclidNorm (X j) ≤ n) →
      (∀ y ∈ departureRange X n, (localTime X n y : ℝ) ≤ c₀ * max (b - euclidNorm y) 0 + A₁ +
        A₂ * Real.sqrt ((∑ x ∈ departureRange X n,
          (localTime X n x : ℝ) * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ))) *
            Real.log (n + 2))) →
      (∀ y : Site d, (localTime X n y : ℝ) ≤
        C * (c₀ * max (b - euclidNorm y) 0 + A₁ + A₂ ^ 2 * Real.log (n + 2) +
          c₀ * Real.log (n + 2))) ∧
      ∀ z : Site d, b ≤ euclidNorm z → euclidNorm z ≤ n →
        ∑ x ∈ departureRange X n,
            (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (2 - 2 * (d : ℝ))
          ≤ C * (A₁ + A₂ ^ 2 * Real.log (n + 2) + c₀ * Real.log (n + 2)) := by
  obtain ⟨Ck, hCkpos, hCk⟩ := sum_ballFinset_rpow_two_sub_two_mul_le hd
  obtain ⟨Cj, hCjpos, hJbound⟩ : ∃ Cj : ℝ, 0 < Cj ∧ ∀ R : ℝ, 1 ≤ R →
      ∑ z ∈ ballFinset d R, euclidNorm z * (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ))
        ≤ Cj * Real.log (R + 2) := by
    by_cases h3 : d = 3
    · subst h3
      obtain ⟨C, hC, hb⟩ := sum_ballFinset_norm_mul_rpow_le_log_three
      refine ⟨2 * C, by positivity, fun R hR => ?_⟩
      have hlog : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
      calc ∑ z ∈ ballFinset 3 R, euclidNorm z * (1 + euclidNorm z) ^ (2 - 2 * (3 : ℝ))
          = ∑ z ∈ ballFinset 3 R, euclidNorm z * (1 + euclidNorm z) ^ (-4 : ℝ) := by
            norm_num
        _ ≤ C * Real.log (R + 2) := hb R hR
        _ ≤ 2 * C * Real.log (R + 2) := by nlinarith [hC.le, hlog]
    · have h4 : 4 ≤ d := by omega
      obtain ⟨C, hC, hb⟩ := sum_ballFinset_norm_mul_rpow_le h4
      refine ⟨C, hC, fun R hR => ?_⟩
      have hlog : 1 ≤ Real.log (R + 2) := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        have hlt := Real.exp_one_lt_three
        linarith
      calc ∑ z ∈ ballFinset d R, euclidNorm z * (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ))
          ≤ C := hb R
        _ ≤ C * Real.log (R + 2) := by nlinarith [hC.le, hlog]
  let lam : ℝ := 1 / (2 * (Ck + 1))
  have hlam : 0 < lam := by positivity
  have hlam_eq : lam = 1 / (2 * (Ck + 1)) := rfl
  let Cp : ℝ := 2 + (Ck + 1) + 2 * (2 * Cj) / (Ck + 1)
  have hCppos : 0 < Cp := by positivity
  have hCp_eq : Cp = 2 + (Ck + 1) + 2 * (2 * Cj) / (Ck + 1) := rfl
  let Cfin : ℝ := Cp * (Ck + 2 * Cj + 1)
  have hCfinpos : 0 < Cfin := by positivity
  have hCfin_eq : Cfin = Cp * (Ck + 2 * Cj + 1) := rfl
  refine ⟨Cfin, hCfinpos, ?_⟩
  intro X n c₀ b A₁ A₂ hn hc0 hA₁ hA₂ hXn hpt
  let L : ℝ := Real.log (n + 2)
  let S : Finset (Site d) := ballFinset d (2 * (n : ℝ))
  let k : Site d → ℝ := fun w => (1 + euclidNorm w) ^ (2 - 2 * (d : ℝ))
  let ℓ : Site d → ℝ := fun y => (localTime X n y : ℝ)
  let s : Site d → ℝ := fun y => max (b - euclidNorm y) 0
  let J : ℝ := ∑ w ∈ S, euclidNorm w * k w
  let c : ℝ := A₁ + A₂ ^ 2 * L / (4 * lam)
  have hLdef : L = Real.log (n + 2) := rfl
  have hSdef : S = ballFinset d (2 * (n : ℝ)) := rfl
  have hkdef : ∀ w, k w = (1 + euclidNorm w) ^ (2 - 2 * (d : ℝ)) := fun w => rfl
  have hℓdef : ∀ y, ℓ y = (localTime X n y : ℝ) := fun y => rfl
  have hsdef : ∀ y, s y = max (b - euclidNorm y) 0 := fun y => rfl
  have hJdef : J = ∑ w ∈ S, euclidNorm w * k w := rfl
  have hcdef : c = A₁ + A₂ ^ 2 * L / (4 * lam) := rfl
  clear_value lam Cp Cfin L S k ℓ s J c
  have hL1 : 1 ≤ L := by
    have hy : (0 : ℝ) < (n : ℝ) + 2 := by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [hLdef, Real.le_log_iff_exp_le hy]
    have hlt := Real.exp_one_lt_three
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hℓb : BddAbove (Set.range ℓ) := by
    refine ⟨(n : ℝ), ?_⟩
    rintro _ ⟨y, rfl⟩
    simpa only [hℓdef y] using localTime_cast_le X n y
  have hs0 : ∀ y, 0 ≤ s y := by
    intro y
    rw [hsdef y]
    exact le_max_right _ _
  have hs_lip : ∀ u v, s u - s v ≤ euclidNorm (u - v) := by
    intro u v
    rw [hsdef u, hsdef v]
    exact max_sub_max_le_euclidNorm b u v
  have hk_nonneg : ∀ w, 0 ≤ k w := by
    intro w
    rw [hkdef w]
    exact Real.rpow_nonneg (by linarith [euclidNorm_nonneg w]) _
  have hsumK : ∑ x ∈ S, k x ≤ Ck := by
    rw [hSdef]
    refine le_trans (Finset.sum_le_sum fun x hx => le_of_eq (hkdef x)) (hCk (2 * (n : ℝ)))
  have hsmall : lam * ∑ x ∈ S, k x ≤ 1 / 2 := by
    have hCk1 : (0 : ℝ) < Ck + 1 := by linarith
    calc lam * ∑ x ∈ S, k x
        ≤ lam * Ck := mul_le_mul_of_nonneg_left hsumK hlam.le
      _ = Ck / (2 * (Ck + 1)) := by
            rw [hlam_eq]
            field_simp
      _ ≤ 1 / 2 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
  have hJle : J ≤ 2 * Cj * L := by
    have hR1 : (1 : ℝ) ≤ 2 * (n : ℝ) := by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h1 : J ≤ Cj * Real.log (2 * (n : ℝ) + 2) := by
      rw [hJdef, hSdef]
      calc ∑ w ∈ ballFinset d (2 * (n : ℝ)), euclidNorm w * k w
          ≤ ∑ w ∈ ballFinset d (2 * (n : ℝ)),
              euclidNorm w * (1 + euclidNorm w) ^ (2 - 2 * (d : ℝ)) :=
            Finset.sum_le_sum fun w hw => by rw [hkdef w]
        _ ≤ Cj * Real.log (2 * (n : ℝ) + 2) := hJbound (2 * (n : ℝ)) hR1
    have h2 : Real.log (2 * (n : ℝ) + 2) ≤ 2 * L := by
      have hle : 2 * (n : ℝ) + 2 ≤ ((n : ℝ) + 2) ^ 2 := by
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith [sq_nonneg ((n : ℝ)), hn']
      have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 * (n : ℝ) + 2) hle
      rw [Real.log_pow] at hlog
      norm_num at hlog
      have hlogL : Real.log ((n : ℝ) + 2) = L := by
        rw [hLdef]
      linarith [hlog, hlogL]
    nlinarith [hCjpos.le, h1, h2]
  have hJnonneg : 0 ≤ J := by
    rw [hJdef]
    exact Finset.sum_nonneg fun w hw => mul_nonneg (euclidNorm_nonneg w) (hk_nonneg w)
  have hc_nonneg : 0 ≤ c := by
    rw [hcdef]
    have hnum : 0 ≤ A₂ ^ 2 * L := mul_nonneg (sq_nonneg A₂) hL0
    have hden : 0 < 4 * lam := by positivity
    have := div_nonneg hnum hden.le
    linarith
  have hℓ : ∀ y, ℓ y ≤ c₀ * s y + c + lam * ∑ w ∈ S, k w * ℓ (y - w) := by
    intro y
    by_cases hy : y ∈ departureRange X n
    · set B : ℝ := ∑ x ∈ departureRange X n, (localTime X n x : ℝ) *
        (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)) with hB
      have hpt' : ℓ y ≤ c₀ * s y + A₁ + A₂ * Real.sqrt (B * L) := by
        have h := hpt y hy
        rw [← hB, ← hLdef, ← hsdef y] at h
        simpa only [hℓdef y] using h
      have hB0 : 0 ≤ B := by
        rw [hB]
        exact Finset.sum_nonneg fun x hx => mul_nonneg (by positivity)
          (Real.rpow_nonneg (by linarith [euclidNorm_nonneg (x - y)]) _)
      have hBconv : B ≤ ∑ w ∈ S, k w * ℓ (y - w) := by
        rw [hB]
        have h := localTime_bracket_le_conv hXn hy
        simpa only [hSdef, hkdef, hℓdef] using h
      have hℓy : ℓ y ≤ c₀ * s y + c + lam * ∑ w ∈ S, k w * ℓ (y - w) :=
        calc ℓ y ≤ c₀ * s y + A₁ + A₂ * Real.sqrt (B * L) := hpt'
          _ ≤ c₀ * s y + A₁ + (lam * B + A₂ ^ 2 * L / (4 * lam)) := by
                linarith [sqrt_young B L A₂ lam hB0 hL0 hA₂ hlam]
          _ ≤ c₀ * s y + A₁ + (lam * (∑ w ∈ S, k w * ℓ (y - w)) +
                A₂ ^ 2 * L / (4 * lam)) := by
                have hmul := mul_le_mul_of_nonneg_left hBconv hlam.le
                linarith
          _ = c₀ * s y + c + lam * ∑ w ∈ S, k w * ℓ (y - w) := by
                rw [hcdef]
                ring
      exact hℓy
    · have hy0 : localTime X n y = 0 := localTime_eq_zero_of_not_mem hy
      have hℓy0 : ℓ y = 0 := by rw [hℓdef, hy0]; norm_num
      rw [hℓy0]
      have h1 : 0 ≤ c₀ * s y := mul_nonneg hc0 (hs0 y)
      have h3 : 0 ≤ lam * ∑ w ∈ S, k w * ℓ (y - w) := by
        refine mul_nonneg hlam.le ?_
        exact Finset.sum_nonneg fun w hw => mul_nonneg (hk_nonneg w) (by rw [hℓdef]; positivity)
      linarith
  have hsK : ∀ y, ∑ x ∈ S, k x * s (y - x) ≤ (∑ x ∈ S, k x) * s y + J := by
    intro y
    have h := sum_mul_le_of_lipschitz S k hk_nonneg s hs_lip y
    simpa only [hJdef] using h
  have hconv : ∀ y, ℓ y ≤ 2 * c₀ * s y + 2 * c + 4 * lam * c₀ * J :=
    le_of_le_add_conv S k hk_nonneg hlam.le hc0 hc_nonneg hJnonneg hsmall s ℓ hs0 hsK hℓb hℓ
  have hpoint : ∀ y, ℓ y ≤ Cp * (c₀ * s y + A₁ + A₂ ^ 2 * L + c₀ * L) :=
    pointwise_bound ℓ s c₀ A₁ A₂ Cp L J c lam Ck Cj hconv hJle hcdef hlam_eq hCp_eq
      hL0 hc0 hA₁ hs0 hlam hCkpos hCjpos
  refine ⟨?_, ?_⟩
  · intro y
    have hbracket : 0 ≤ c₀ * s y + A₁ + A₂ ^ 2 * L + c₀ * L := by
      have h1 : 0 ≤ c₀ * s y := mul_nonneg hc0 (hs0 y)
      have h2 : 0 ≤ A₂ ^ 2 * L := mul_nonneg (sq_nonneg A₂) hL0
      have h3 : 0 ≤ c₀ * L := mul_nonneg hc0 hL0
      linarith
    have hCpCfin : Cp ≤ Cfin := by
      rw [hCfin_eq]
      have hone : (1 : ℝ) ≤ Ck + 2 * Cj + 1 := by linarith [hCkpos.le, hCjpos.le]
      calc Cp = Cp * 1 := by ring
        _ ≤ Cp * (Ck + 2 * Cj + 1) := mul_le_mul_of_nonneg_left hone hCppos.le
    calc (localTime X n y : ℝ) = ℓ y := (hℓdef y).symm
      _ ≤ Cp * (c₀ * s y + A₁ + A₂ ^ 2 * L + c₀ * L) := hpoint y
      _ ≤ Cfin * (c₀ * s y + A₁ + A₂ ^ 2 * L + c₀ * L) :=
            mul_le_mul_of_nonneg_right hCpCfin hbracket
      _ = Cfin * (c₀ * max (b - euclidNorm y) 0 + A₁ + A₂ ^ 2 * Real.log (n + 2) +
            c₀ * Real.log (n + 2)) := by
            rw [hsdef y, hLdef]
  · intro z hz1 hz2
    have hzk : ∀ x ∈ departureRange X n, euclidNorm (x - z) ≤ 2 * (n : ℝ) := by
      intro x hx
      calc euclidNorm (x - z) ≤ euclidNorm x + euclidNorm z := euclidNorm_sub_le x z
        _ ≤ (n : ℝ) + (n : ℝ) :=
              add_le_add (euclidNorm_le_of_mem_departureRange hXn hx) hz2
        _ = 2 * (n : ℝ) := by ring
    have hsubset : (departureRange X n).image (fun x => x - z) ⊆ S := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨x, hx, rfl⟩
      rw [hSdef, mem_ballFinset_iff]
      exact hzk x hx
    have hinj : Set.InjOn (fun x : Site d => x - z) (departureRange X n) :=
      fun a ha b hb hab => sub_left_injective hab
    have hSumK : ∑ x ∈ departureRange X n, k (x - z) ≤ Ck := by
      rw [← Finset.sum_image hinj]
      calc ∑ w ∈ (departureRange X n).image (fun x => x - z), k w
          ≤ ∑ w ∈ S, k w :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun w _ _ => hk_nonneg w)
        _ ≤ Ck := hsumK
    have hSumNK : ∑ x ∈ departureRange X n, euclidNorm (x - z) * k (x - z)
        ≤ 2 * Cj * L := by
      have hEq := Finset.sum_image (s := departureRange X n) (g := fun x => x - z)
        (f := fun w => euclidNorm w * k w) hinj
      rw [← hEq]
      calc ∑ w ∈ (departureRange X n).image (fun x => x - z), euclidNorm w * k w
          ≤ ∑ w ∈ S, euclidNorm w * k w :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubset
              (fun w _ _ => mul_nonneg (euclidNorm_nonneg w) (hk_nonneg w))
        _ = J := hJdef.symm
        _ ≤ 2 * Cj * L := hJle
    have hSumS : ∑ x ∈ departureRange X n, s x * k (x - z) ≤ 2 * Cj * L := by
      have hle : ∀ x ∈ departureRange X n,
          s x * k (x - z) ≤ euclidNorm (x - z) * k (x - z) := by
        intro x hx
        have hsle : s x ≤ euclidNorm (x - z) := by
          rw [hsdef x]
          refine max_le ?_ (euclidNorm_nonneg _)
          calc b - euclidNorm x ≤ euclidNorm z - euclidNorm x := by linarith
            _ ≤ |euclidNorm z - euclidNorm x| := le_abs_self _
            _ ≤ euclidNorm (z - x) := abs_euclidNorm_sub_le z x
            _ = euclidNorm (x - z) := by
                  rw [show z - x = -(x - z) by abel, euclidNorm_neg]
        exact mul_le_mul_of_nonneg_right hsle (hk_nonneg _)
      calc ∑ x ∈ departureRange X n, s x * k (x - z)
          ≤ ∑ x ∈ departureRange X n, euclidNorm (x - z) * k (x - z) :=
            Finset.sum_le_sum hle
        _ ≤ 2 * Cj * L := hSumNK
    have hE : 0 ≤ A₁ + A₂ ^ 2 * L + c₀ * L := by
      have h2 : 0 ≤ A₂ ^ 2 * L := mul_nonneg (sq_nonneg A₂) hL0
      have h3 : 0 ≤ c₀ * L := mul_nonneg hc0 hL0
      linarith
    have hcoefle : Cp * (Ck + 2 * Cj) ≤ Cfin := by
      rw [hCfin_eq]
      have hone : Ck + 2 * Cj ≤ Ck + 2 * Cj + 1 := by linarith
      exact mul_le_mul_of_nonneg_left hone hCppos.le
    have hcore := bracket_sum_le (departureRange X n) k s ℓ z c₀ A₁ A₂ Cp Ck Cj Cfin L
      hpoint hk_nonneg hSumS hSumK hE hc0 hA₁ hL0 hCjpos hCppos hcoefle
    calc ∑ x ∈ departureRange X n,
            (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (2 - 2 * (d : ℝ))
        = ∑ x ∈ departureRange X n, ℓ x * k (x - z) := by
            refine Finset.sum_congr rfl fun x hx => ?_
            rw [hℓdef, hkdef]
      _ ≤ Cfin * (A₁ + A₂ ^ 2 * L + c₀ * L) := hcore
      _ = Cfin * (A₁ + A₂ ^ 2 * Real.log (n + 2) + c₀ * Real.log (n + 2)) := by
            rw [hLdef]

end CERW.Support.Contact
