import CERW.LimitShapes.Crossing.Directional
import CERW.Support.Norm.Section5Localization

/-!
# Distances to norm balls from projection estimates

The projection cap geometry and the directional crossing bound control every
path point's distance to a fixed norm ball. All martingale estimates use the
logarithm of a terminal horizon rather than the current path time.
-/

open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes.Crossing.Projection

open CERW CERW.Support.Norm.ProjectionGeometry
open private toSpace_zero_eq sup_localTime_le from CERW.Support.Norm.OuterProjection

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- Projection geometry converts the directional crossing estimates through an earlier
time into a distance bound for every path point relative to a fixed norm ball. -/
theorem distance_le_of_projection_estimates (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    {C₁ : ℝ} (hC₁ : 0 < C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ N : ℕ, 2 ≤ N → ∀ n : ℕ, n ≤ N → ∀ (x : ℕ → Site d), x 0 = 0 →
      (∀ j, x (j + 1) - x j ∈ unitSteps d) → ∀ (r Lb : ℝ), 0 ≤ r → 0 ≤ Lb →
      ∀ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        (∀ y, Ψ (P y) ≤ r) →
        (∀ y v, Ψ v ≤ r → ‖y - P y‖ ≤ ‖y - v‖) →
        (∀ y v, Ψ v ≤ r → inner ℝ (y - P y) (v - P y) ≤ 0) →
      (∀ z : Site d, r ≤ Ψ (toSpace z) → (localTime x n z : ℝ) ≤ Lb) →
      (∀ s t : ℕ, s < t → t ≤ n →
        ‖(toSpace (x t) + ε • ∑ j ∈ Finset.range t,
            if x j ∉ departureRange x j then ξ (x j) else 0) -
          (toSpace (x s) + ε • ∑ j ∈ Finset.range s,
            if x j ∉ departureRange x j then ξ (x j) else 0)‖ ≤
          C₁ * Real.sqrt (((t : ℝ) - s) * Real.log N)) →
      (∀ j : ℕ, j ≤ n → r < Ψ (toSpace (x j)) → ∀ k : ℕ, k ≤ n →
        |dynkinMart (driftStepProb d ε ξ)
            (fun z => max (inner ℝ ((normMax Ψ / ‖toSpace (x j) - P (toSpace (x j))‖) •
                (toSpace (x j) - P (toSpace (x j)))) (toSpace z) - k * normMax Ψ) 0) x n| ≤
          C₁ * (Real.sqrt (Real.log N * ∑ z ∈ (departureRange x n).filter
              (fun z => (k : ℝ) * normMax Ψ - normMax Ψ <
                inner ℝ ((normMax Ψ / ‖toSpace (x j) - P (toSpace (x j))‖) •
                  (toSpace (x j) - P (toSpace (x j)))) (toSpace z)),
            (localTime x n z : ℝ)) + Real.log N)) →
      ∀ j : ℕ, j ≤ n →
        ‖toSpace (x j) - P (toSpace (x j))‖ ≤ C * (1 + Lb) * Real.log N := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hc, hcmul⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hcΛ := normMin_le_normMax hΨ hd1
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc hcΛ
  have hα : 0 < normMax Ψ * normMin Ψ / 2 := by positivity
  obtain ⟨C₀, hC₀, hC⟩ := Directional.directional_crossing hd1 hε hα hC₁ hΛ
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = normMin Ψ ^ 2 / (8 * normMax Ψ ^ 2) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one (by positivity)]
    have h1 : normMin Ψ ^ 2 ≤ normMax Ψ ^ 2 := pow_le_pow_left₀ hc.le hcΛ 2
    nlinarith [pow_pos hΛ 2]
  refine ⟨C₀ / θ / normMax Ψ, div_pos (div_pos hC₀ hθ0) hΛ, ?_⟩
  intro ξ hξ hξ0 N hN n hnN x hx0 hstep r Lb hr hLb P hPmem hPmin hPvar hloc hZ hmart
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hnonneg : 0 ≤ C₀ / θ / normMax Ψ * (1 + Lb) * Real.log N := by positivity
  -- the path point farthest from `K`
  obtain ⟨j₀, hj₀mem, hj₀max⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun j => ‖toSpace (x j) - P (toSpace (x j))‖)
    ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
  have hj₀n : j₀ ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj₀mem)
  have hmax : ∀ j ≤ n, ‖toSpace (x j) - P (toSpace (x j))‖ ≤
      ‖toSpace (x j₀) - P (toSpace (x j₀))‖ :=
    fun j hj => hj₀max j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  by_cases hw0 : ‖toSpace (x j₀) - P (toSpace (x j₀))‖ = 0
  · intro j hj
    exact (hmax j hj).trans (by rw [hw0]; exact hnonneg)
  have hwpos : 0 < ‖toSpace (x j₀) - P (toSpace (x j₀))‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
  -- the point `X_{j₀}` lies outside `K`
  have hr₀ : r < Ψ (toSpace (x j₀)) := by
    by_contra hnot
    have h1 := hPmin (toSpace (x j₀)) (toSpace (x j₀)) (not_lt.1 hnot)
    rw [sub_self, norm_zero] at h1
    exact hw0 (le_antisymm h1 (norm_nonneg _))
  -- the direction `q`
  have hmart₀ := hmart j₀ hj₀n hr₀
  obtain ⟨q, hqdef⟩ : ∃ q : EuclideanSpace ℝ (Fin d),
      q = (normMax Ψ / ‖toSpace (x j₀) - P (toSpace (x j₀))‖) •
        (toSpace (x j₀) - P (toSpace (x j₀))) := ⟨_, rfl⟩
  rw [← hqdef] at hmart₀
  have hne : toSpace (x j₀) - P (toSpace (x j₀)) ≠ 0 := norm_pos_iff.1 hwpos
  have hqnorm : ‖q‖ = normMax Ψ := by
    rw [hqdef]
    exact norm_scaledDirection hΛ.le hne
  have hqa : inner ℝ q (toSpace (x j₀) - P (toSpace (x j₀))) =
      normMax Ψ * ‖toSpace (x j₀) - P (toSpace (x j₀))‖ := by
    rw [hqdef]
    exact inner_scaledDirection_self hne
  -- `q` is bounded by `β` on `K`
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = inner ℝ q (P (toSpace (x j₀))) := ⟨_, rfl⟩
  have hsup : ∀ v : EuclideanSpace ℝ (Fin d), Ψ v ≤ r → inner ℝ q v ≤ β := by
    intro v hv
    have h1 := hPvar (toSpace (x j₀)) v hv
    have hfac : 0 ≤ normMax Ψ / ‖toSpace (x j₀) - P (toSpace (x j₀))‖ :=
      div_nonneg hΛ.le hwpos.le
    have h2 : inner ℝ q (v - P (toSpace (x j₀))) ≤ 0 := by
      rw [hqdef, real_inner_smul_left]
      have := mul_le_mul_of_nonneg_left h1 hfac
      rwa [mul_zero] at this
    rw [inner_sub_right] at h2
    rw [hβdef]
    linarith
  have hβ0 : 0 ≤ β := by
    have h1 := hsup 0 (by rw [(CERW.Generic.Norm.map_zero_nonneg_neg hΨ).1]; exact hr)
    simpa using h1
  -- `X_{j₀}` attains the maximum `β + Λ_Ψ w` of the pairing with `q`
  have hT : inner ℝ q (toSpace (x j₀)) =
      β + normMax Ψ * ‖toSpace (x j₀) - P (toSpace (x j₀))‖ := by
    have h1 := inner_add_right (𝕜 := ℝ) q (P (toSpace (x j₀))) (toSpace (x j₀) - P (toSpace (x j₀)))
    rw [add_sub_cancel, hqa] at h1
    rw [h1, hβdef]
  -- the cap: subgradients pair positively with `q`
  obtain ⟨h, hhdef⟩ : ∃ h : ℝ,
      h = θ * (normMax Ψ * ‖toSpace (x j₀) - P (toSpace (x j₀))‖) := ⟨_, rfl⟩
  have hh : 0 < h := by rw [hhdef]; exact mul_pos hθ0 (mul_pos hΛ hwpos)
  have hdrift : ∀ j ≤ n, inner ℝ q (toSpace (x j₀)) - h < inner ℝ q (toSpace (x j)) →
      normMax Ψ * normMin Ψ / 2 ≤ inner ℝ q (ξ (x j)) := by
    intro j hj hlt
    have hgap : β ≤ inner ℝ q (toSpace (x j₀)) - h := by
      rw [hT, hhdef]
      have : 0 ≤ (1 - θ) * (normMax Ψ * ‖toSpace (x j₀) - P (toSpace (x j₀))‖) :=
        mul_nonneg (sub_nonneg.2 hθ1) (mul_nonneg hΛ.le hwpos.le)
      linarith
    have hyr : r < Ψ (toSpace (x j)) := by
      by_contra hnot
      have := hsup _ (not_lt.1 hnot)
      linarith
    have hxj : x j ≠ 0 := by
      intro h0
      rw [h0, toSpace_zero_eq, (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).1] at hyr
      linarith
    have h1 := inner_add_right (𝕜 := ℝ) q (P (toSpace (x j))) (toSpace (x j) - P (toSpace (x j)))
    rw [add_sub_cancel] at h1
    have h2 := hsup _ (hPmem (toSpace (x j)))
    refine cap_drift hΨ hd1 hr (hPmem (toSpace (x j))) (hPmin (toSpace (x j))) hyr hqnorm
      (hmax j hj) ?_ (hξ (x j) hxj)
    rw [← hθdef]
    rw [hT, hhdef] at hlt
    linarith
  -- the half-space crossing lemma at the threshold `β`
  have hcross := hC ξ
    (CERW.Support.Norm.ContactAssembly.drift_coord_le hΨ hε hell hξ hξ0)
    N hN n hnN q hqnorm.le x hx0 hstep hZ hmart₀ j₀ hj₀n h hh hdrift
    β hβ0
  have hsupLb := sup_localTime_le (q := q) (β := β) hLb x n
    (fun z hz => hloc z (le_of_support_le_inner hΨ hΛ hqnorm hsup hz))
  have hgap : β ≤ inner ℝ q (toSpace (x j₀)) - h := by
    rw [hT, hhdef]
    have : 0 ≤ (1 - θ) * (normMax Ψ * ‖toSpace (x j₀) - P (toSpace (x j₀))‖) :=
      mul_nonneg (sub_nonneg.2 hθ1) (mul_nonneg hΛ.le hwpos.le)
    linarith
  rw [max_eq_left hgap] at hcross
  have hE : C₀ * (1 + ((((departureRange x n).filter
        (fun z => β ≤ inner ℝ q (toSpace z))).sup (localTime x n) : ℕ) : ℝ)) * Real.log N ≤
      C₀ * (1 + Lb) * Real.log N :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : 1 + ((((departureRange x n).filter
        (fun z => β ≤ inner ℝ q (toSpace z))).sup (localTime x n) : ℕ) : ℝ) ≤ 1 + Lb) hC₀.le)
      hlog
  have hhle : h ≤ C₀ * (1 + Lb) * Real.log N := by linarith
  have hΛw : normMax Ψ * ‖toSpace (x j₀) - P (toSpace (x j₀))‖ ≤
      C₀ / θ * (1 + Lb) * Real.log N := by
    have e : C₀ / θ * (1 + Lb) * Real.log N = C₀ * (1 + Lb) * Real.log N / θ := by ring
    rw [e, le_div_iff₀ hθ0]
    rw [hhdef] at hhle
    linarith
  intro j hj
  have hjw := hmax j hj
  have hwbound : ‖toSpace (x j₀) - P (toSpace (x j₀))‖ ≤
      C₀ / θ / normMax Ψ * (1 + Lb) * Real.log N := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hΛ]
    nlinarith
  exact hjw.trans hwbound

end CERW.LimitShapes.Crossing.Projection
