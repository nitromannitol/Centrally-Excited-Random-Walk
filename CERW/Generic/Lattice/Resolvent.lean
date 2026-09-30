import LatticeProb.Walk.Ball

/-!
# A resolvent bound for local times

In dimension `d ≥ 3` the local time satisfies `ℓ ≤ a s + c + λ k * ℓ` on all of `ℤ^d`, with a
summable kernel of mass `k₀`, `λ k₀ ≤ 1/2`, and a profile `s` with `k * s ≤ k₀ s + J`
(`eq:resolvent`). Then `ℓ ≤ 2a s + 2c + 4λaJ` (`eq:envelopehigh`). The paper sums the Neumann
series. Here the same bound comes from the supremum `D` of `ℓ - A s` with `A = a/(1 - λk₀)`,
which satisfies `D ≤ c + λAJ + λk₀D`.
-/

namespace CERW.Generic.Lattice

open LatticeProb

variable {d : ℕ}

/-- Resolvent bound: if `ℓ` is bounded above, `ℓ ≤ a s + c + λ Σ_{x∈S} K(x) ℓ(· - x)`,
`K ≥ 0` with `λ Σ K ≤ 1/2`, `s ≥ 0` with `Σ_{x∈S} K(x) s(y - x) ≤ (Σ K) s(y) + J`, and
`a, c, J, λ ≥ 0`, then `ℓ ≤ 2a s + 2c + 4λaJ` everywhere. -/
theorem le_of_le_add_conv (S : Finset (Site d)) (K : Site d → ℝ) (hK : ∀ x, 0 ≤ K x)
    {lam a c J : ℝ} (hlam : 0 ≤ lam) (ha : 0 ≤ a) (hc : 0 ≤ c) (hJ : 0 ≤ J)
    (hsmall : lam * ∑ x ∈ S, K x ≤ 1 / 2) (s ℓ : Site d → ℝ) (hs0 : ∀ y, 0 ≤ s y)
    (hsK : ∀ y, ∑ x ∈ S, K x * s (y - x) ≤ (∑ x ∈ S, K x) * s y + J)
    (hℓb : BddAbove (Set.range ℓ))
    (hℓ : ∀ y, ℓ y ≤ a * s y + c + lam * ∑ x ∈ S, K x * ℓ (y - x)) :
    ∀ y, ℓ y ≤ 2 * a * s y + 2 * c + 4 * lam * a * J := by
  haveI : Nonempty (Site d) := ⟨fun _ => 0⟩
  set k0 : ℝ := ∑ x ∈ S, K x with hk0def
  set q : ℝ := lam * k0 with hqdef
  have hk0 : 0 ≤ k0 := by
    rw [hk0def]
    exact Finset.sum_nonneg (fun x _ => hK x)
  have hq0 : 0 ≤ q := by
    rw [hqdef]
    exact mul_nonneg hlam hk0
  have hqhalf : q ≤ 1 / 2 := hsmall
  have hpos : 0 < 1 - q := by linarith
  set A : ℝ := a / (1 - q) with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact div_nonneg ha (le_of_lt hpos)
  have hA1 : A * (1 - q) = a := by
    rw [hAdef]
    exact div_mul_cancel₀ a (ne_of_gt hpos)
  have hAeq : a + q * A = A := by nlinarith [hA1]
  have hA2 : A ≤ 2 * a := by
    rw [hAdef, div_le_iff₀ hpos]
    nlinarith
  let g : Site d → ℝ := fun y => ℓ y - A * s y
  have hg_bdd : BddAbove (Set.range g) := by
    rcases hℓb with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rintro _ ⟨y, rfl⟩
    simp only [g]
    have h1 : ℓ y ≤ B := hB (Set.mem_range_self y)
    have h2 : 0 ≤ A * s y := mul_nonneg hA0 (hs0 y)
    linarith
  set D : ℝ := sSup (Set.range g) with hDdef
  have hgD : ∀ z, g z ≤ D := by
    intro z
    rw [hDdef]
    exact le_csSup hg_bdd (Set.mem_range_self z)
  have hℓD : ∀ z, ℓ z ≤ A * s z + D := by
    intro z
    have h := hgD z
    simp only [g] at h
    linarith
  have hstep2 : ∀ y, ∑ x ∈ S, K x * ℓ (y - x) ≤ A * (k0 * s y + J) + D * k0 := by
    intro y
    have h1 : ∑ x ∈ S, K x * ℓ (y - x) ≤ ∑ x ∈ S, K x * (A * s (y - x) + D) := by
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hℓD (y - x)) (hK x))
    have h2 : ∑ x ∈ S, K x * (A * s (y - x) + D)
        = A * (∑ x ∈ S, K x * s (y - x)) + D * k0 := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      · rw [← Finset.sum_mul, ← hk0def]
        ring
    have h3 : A * (∑ x ∈ S, K x * s (y - x)) ≤ A * (k0 * s y + J) :=
      mul_le_mul_of_nonneg_left (hsK y) hA0
    calc ∑ x ∈ S, K x * ℓ (y - x)
        ≤ ∑ x ∈ S, K x * (A * s (y - x) + D) := h1
      _ = A * (∑ x ∈ S, K x * s (y - x)) + D * k0 := h2
      _ ≤ A * (k0 * s y + J) + D * k0 := by linarith
  have hg_ub : ∀ y, g y ≤ c + lam * A * J + q * D := by
    intro y
    have hℓy := hℓ y
    have hs2 : lam * (∑ x ∈ S, K x * ℓ (y - x))
        ≤ lam * (A * (k0 * s y + J) + D * k0) :=
      mul_le_mul_of_nonneg_left (hstep2 y) hlam
    have hexp : a * s y + c + lam * (A * (k0 * s y + J) + D * k0)
        = (a + q * A) * s y + c + lam * A * J + q * D := by
      rw [hqdef]
      ring
    have hle : ℓ y ≤ (a + q * A) * s y + c + lam * A * J + q * D := by
      linarith
    rw [hAeq] at hle
    simp only [g]
    linarith
  have hD_bound : D ≤ c + lam * A * J + q * D := by
    rw [hDdef]
    refine csSup_le (Set.range_nonempty g) ?_
    rintro _ ⟨y, rfl⟩
    exact hg_ub y
  have hD_le : D ≤ (c + lam * A * J) / (1 - q) := by
    rw [le_div_iff₀ hpos]
    nlinarith [hD_bound]
  have hnum_nonneg : 0 ≤ c + lam * A * J := by
    have h1 : 0 ≤ lam * A := mul_nonneg hlam hA0
    have h2 : 0 ≤ lam * A * J := mul_nonneg h1 hJ
    linarith
  have hquot : (c + lam * A * J) / (1 - q) ≤ 2 * (c + lam * A * J) := by
    rw [div_le_iff₀ hpos]
    have key : 0 ≤ (c + lam * A * J) * (2 * (1 - q) - 1) :=
      mul_nonneg hnum_nonneg (by linarith)
    nlinarith [key]
  have hAJ_le : lam * A * J ≤ lam * (2 * a) * J := by
    have h1 : lam * A ≤ lam * (2 * a) := mul_le_mul_of_nonneg_left hA2 hlam
    exact mul_le_mul_of_nonneg_right h1 hJ
  have hD_final : D ≤ 2 * c + 4 * lam * a * J := by
    have h2 : 2 * (c + lam * A * J) ≤ 2 * c + 4 * lam * a * J := by
      nlinarith [hAJ_le]
    linarith [hD_le, hquot, h2]
  intro y
  have hgy : ℓ y - A * s y ≤ D := by
    have h := hgD y
    simpa only [g] using h
  have hAs : A * s y ≤ 2 * a * s y := mul_le_mul_of_nonneg_right hA2 (hs0 y)
  linarith

end CERW.Generic.Lattice
