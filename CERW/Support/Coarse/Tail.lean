import CERW.Generic.Halving.Levels
import CERW.Generic.Halving.Cost
import CERW.Support.Geometry.TailBounds
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Occupation.CellNorm
import CERW.Support.Main.ScaleLimits

/-!
# The coarse tail

`eq:floor` through `eq:halving-cost` and `eq:coarse-tail`, deterministically. Let `s = R_n^{1/d}`,
with `F ≤ s/σ_d` at radius `s`. Suppose `eq:radial` holds at every integer radius `r₀ ≤ r ≤ n`,
`M_n ≤ C₁ s`, `δ ≤ C₁ √s L`, and `eq:shell` holds in the window `[s, B₀ s]` with a constant
independent of `B₀`. From the dyadic level `A`, the radial error is at most `A/4` as long as
`A ≥ Λ = C s^{2-d} L`. Unless `F` halves, each grid step of length `2 b_d` lowers `F` by at least
`cA/K(A)`, where `K(A) = C B₀^β s^{1-α}(A + δ)^α + 1`. Summing the halving costs over the `O(L)`
dyadic levels, `F` reaches `Λ` within the window once `B₀` is large. So
`F((B₀ - 2) s) ≤ C_t s^{2-d} L`.
-/

namespace CERW.Support.Coarse

open LatticeProb CERW CERW.Support.Occupation

variable {d : ℕ}

/-- A window factor: for `0 ≤ β < 1` and `Cw ≥ 0` there is `B₀ ≥ 3` with
`Cw B₀^β + 6 ≤ B₀`. -/
private lemma exists_window {β Cw : ℝ} (hβ1 : β < 1) (hCw : 0 ≤ Cw) :
    ∃ B₀ : ℝ, 3 ≤ B₀ ∧ Cw * B₀ ^ β + 6 ≤ B₀ := by
  set x : ℝ := max 12 ((2 * Cw + 1) ^ (1 / (1 - β))) with hx
  have hx12 : 12 ≤ x := le_max_left _ _
  have hxpos : 0 < x := by linarith
  have h1β : 0 < 1 - β := by linarith
  have hz : 2 * Cw + 1 ≤ x ^ (1 - β) := by
    calc 2 * Cw + 1 = ((2 * Cw + 1) ^ (1 / (1 - β))) ^ (1 - β) := by
          rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ h1β.ne', Real.rpow_one]
      _ ≤ x ^ (1 - β) := Real.rpow_le_rpow (by positivity) (le_max_right _ _) h1β.le
  have hsplit : x = x ^ β * x ^ (1 - β) := by
    rw [← Real.rpow_add hxpos]
    simp
  have hy : 0 < x ^ β := Real.rpow_pos_of_pos hxpos β
  refine ⟨x, by linarith, ?_⟩
  have h2 : Cw * x ^ β ≤ x / 2 := by
    have h3 : 2 * Cw ≤ x ^ (1 - β) := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hy.le
    nlinarith [hsplit]
  linarith

/-- The radial error is at most `A/4` from a level `A ≥ Ct w L` with `Fm ≤ A`. -/
private lemma radial_error_le {Crad Cr C₁ s L Mx ρ Fm A w Ct : ℝ} (hCrad : 0 < Crad)
    (hCrad' : Crad ≤ Cr) (hCr : 1 ≤ Cr) (hC₁ : 0 < C₁) (hCt : Ct = 64 * Cr ^ 2 * (1 + C₁))
    (hL : 0 ≤ L) (hMx : Mx ≤ C₁ * s) (hρ0 : 0 ≤ ρ) (hρs : s * ρ ≤ w) (hρw : ρ ≤ w)
    (hFm0 : 0 ≤ Fm) (hFm : Fm ≤ A) (hA : Ct * (w * L) ≤ A) :
    Crad * (Real.sqrt (Mx * ρ * Fm * L) + ρ * L) ≤ A / 4 := by
  have hw0 : 0 ≤ w := le_trans hρ0 hρw
  have hA0 : 0 ≤ A := le_trans hFm0 hFm
  have hCr0 : 0 < Cr := by linarith
  have hwL : 0 ≤ w * L := mul_nonneg hw0 hL
  have h1 : Mx * ρ * Fm * L ≤ C₁ * (w * L) * A := by
    have e1 : Mx * ρ ≤ C₁ * w := by
      calc Mx * ρ ≤ (C₁ * s) * ρ := mul_le_mul_of_nonneg_right hMx hρ0
        _ = C₁ * (s * ρ) := by ring
        _ ≤ C₁ * w := mul_le_mul_of_nonneg_left hρs hC₁.le
    calc Mx * ρ * Fm * L = (Mx * ρ) * (Fm * L) := by ring
      _ ≤ (C₁ * w) * (A * L) :=
          mul_le_mul e1 (mul_le_mul_of_nonneg_right hFm hL) (mul_nonneg hFm0 hL)
            (mul_nonneg hC₁.le hw0)
      _ = C₁ * (w * L) * A := by ring
  have h2 : Real.sqrt (Mx * ρ * Fm * L) ≤ A / (8 * Cr) := by
    rw [Real.sqrt_le_left (by positivity), div_pow, le_div_iff₀ (by positivity)]
    have h3 : 64 * Cr ^ 2 * C₁ * (w * L) ≤ A := by
      have : 64 * Cr ^ 2 * C₁ * (w * L) ≤ Ct * (w * L) := by
        rw [hCt]
        have : 0 ≤ 64 * Cr ^ 2 * (w * L) := by positivity
        nlinarith
      linarith
    calc Mx * ρ * Fm * L * (8 * Cr) ^ 2 ≤ C₁ * (w * L) * A * (8 * Cr) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = A * (64 * Cr ^ 2 * C₁ * (w * L)) := by ring
      _ ≤ A * A := mul_le_mul_of_nonneg_left h3 hA0
      _ = A ^ 2 := by ring
  have h4 : Cr * (ρ * L) ≤ A / 8 := by
    have h5 : 64 * Cr * (w * L) ≤ Ct * (w * L) := by
      rw [hCt]
      have : 0 ≤ Cr * (w * L) := by positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr hCr) this]
    have h6 : ρ * L ≤ w * L := mul_le_mul_of_nonneg_right hρw hL
    have h7 : Cr * (ρ * L) ≤ Cr * (w * L) := mul_le_mul_of_nonneg_left h6 hCr0.le
    linarith
  have h8 : Cr * Real.sqrt (Mx * ρ * Fm * L) ≤ A / 8 := by
    calc Cr * Real.sqrt (Mx * ρ * Fm * L) ≤ Cr * (A / (8 * Cr)) :=
          mul_le_mul_of_nonneg_left h2 hCr0.le
      _ = A / 8 := by field_simp
  have hX : 0 ≤ Real.sqrt (Mx * ρ * Fm * L) + ρ * L :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hρ0 hL)
  calc Crad * (Real.sqrt (Mx * ρ * Fm * L) + ρ * L)
      ≤ Cr * (Real.sqrt (Mx * ρ * Fm * L) + ρ * L) := mul_le_mul_of_nonneg_right hCrad' hX
    _ = Cr * Real.sqrt (Mx * ρ * Fm * L) + Cr * (ρ * L) := by ring
    _ ≤ A / 4 := by linarith

/-- Either `F(r + b')` is at most `A/2`, or the drop across the grid cell is at least
`A / K` with `K = 4 Cr (S + 1)`. -/
private lemma step_dichotomy {Crad Cr S Ssh Fm Fp Fm' Fp' A err : ℝ} (hCrad : 0 < Crad)
    (hCrad' : Crad ≤ Cr) (hS0 : 0 ≤ S) (hS : S ≤ Ssh) (hFp' : Fp' ≤ Fp)
    (hFm : Fm ≤ Fm') (hFpm : Fp ≤ Fm) (hrad : Fp ≤ Crad * S * (Fm - Fp) + err)
    (herr : err ≤ A / 4) :
    Fp' ≤ A / 2 ∨ A / (4 * Cr * (Ssh + 1)) ≤ Fm' - Fp' := by
  rcases le_or_gt Fp' (A / 2) with h | h
  · exact Or.inl h
  · right
    have hCr0 : 0 < Cr := lt_of_lt_of_le hCrad hCrad'
    have hD : 0 ≤ Fm - Fp := sub_nonneg.mpr hFpm
    have h1 : A / 4 < Crad * S * (Fm - Fp) := by linarith
    have h2 : Crad * S * (Fm - Fp) ≤ Cr * (Ssh + 1) * (Fm - Fp) := by
      apply mul_le_mul_of_nonneg_right _ hD
      exact mul_le_mul hCrad' (by linarith) hS0 hCr0.le
    have h3 : Fm - Fp ≤ Fm' - Fp' := by linarith
    have hSsh0 : 0 ≤ Ssh := le_trans hS0 hS
    have h4 : Cr * (Ssh + 1) * (Fm - Fp) ≤ Cr * (Ssh + 1) * (Fm' - Fp') :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have hpos : 0 < 4 * Cr * (Ssh + 1) := by positivity
    rw [div_le_iff₀ hpos]
    nlinarith

/-- The number of grid steps used by the halving levels is at most the sum of the level
budgets plus two per level. -/
private lemma budget_le {K : ℝ → ℝ} {Cr P α δ A₀ : ℝ} (hCr : 0 ≤ Cr) (hP : 0 ≤ P)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hA₀ : 0 ≤ A₀) (hδ : 0 ≤ δ)
    (hK : ∀ A, 0 ≤ A → K A = 4 * Cr * (P * (A + δ) ^ α + 1)) (M : ℕ) :
    ((∑ k ∈ Finset.range M, (⌈K (A₀ / 2 ^ k)⌉₊ + 1) : ℕ) : ℝ) ≤
      4 * Cr * (P * (A₀ ^ α / (1 - (2 : ℝ) ^ (-α)) + M * δ ^ α) + M) + 2 * M := by
  have hterm : ∀ k ∈ Finset.range M, ((⌈K (A₀ / 2 ^ k)⌉₊ : ℝ) + 1) ≤
      4 * Cr * (P * (A₀ / 2 ^ k + δ) ^ α + 1) + 2 := by
    intro k _
    have hA : 0 ≤ A₀ / 2 ^ k := by positivity
    have hKk := hK _ hA
    have hKnn : 0 ≤ K (A₀ / 2 ^ k) := by
      rw [hKk]
      have : 0 ≤ (A₀ / 2 ^ k + δ) ^ α := Real.rpow_nonneg (by positivity) α
      positivity
    have := Nat.ceil_lt_add_one hKnn
    rw [hKk] at this ⊢
    linarith
  have hsum := CERW.Generic.Halving.sum_rpow_halvings_le hα0 hα1 hA₀ hδ M
  push_cast
  calc ∑ k ∈ Finset.range M, ((⌈K (A₀ / 2 ^ k)⌉₊ : ℝ) + 1)
      ≤ ∑ k ∈ Finset.range M, (4 * Cr * (P * (A₀ / 2 ^ k + δ) ^ α + 1) + 2) :=
        Finset.sum_le_sum hterm
    _ = 4 * Cr * (P * ∑ k ∈ Finset.range M, (A₀ / 2 ^ k + δ) ^ α + M) + 2 * M := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        ring
    _ ≤ 4 * Cr * (P * (A₀ ^ α / (1 - (2 : ℝ) ^ (-α)) + M * δ ^ α) + M) + 2 * M := by
        have := mul_le_mul_of_nonneg_left hsum hP
        have h4Cr : 0 ≤ 4 * Cr := by positivity
        have := mul_le_mul_of_nonneg_left (add_le_add_right this (M : ℝ)) h4Cr
        linarith

/-- The number of dyadic levels is at most a constant multiple of `L = log (n + 2)`. -/
private lemma levels_bound {σ Ct s L : ℝ} {n M : ℕ} (hσ : 0 < σ) (hCt : 0 < Ct) (hs : 1 ≤ s)
    (hd : 1 ≤ d) (hsd : s ^ d ≤ n) (hL : L = Real.log (n + 2)) (hL1 : 1 ≤ L)
    (hM : (M : ℝ) ≤ max 0 (Real.logb 2 ((s / σ) / (Ct * s ^ (2 - (d : ℝ)) * L))) + 1) :
    (M : ℝ) ≤ ((1 + |Real.log (σ * Ct)|) / Real.log 2 + 1) * L := by
  have hs0 : 0 < s := by linarith
  have hw : 0 < s ^ (2 - (d : ℝ)) := Real.rpow_pos_of_pos hs0 _
  have hL0 : 0 < L := by linarith
  have hσCt : 0 < σ * Ct := mul_pos hσ hCt
  have hden : 0 < Ct * s ^ (2 - (d : ℝ)) * L := by positivity
  have hQ0 : 0 < (s / σ) / (Ct * s ^ (2 - (d : ℝ)) * L) := by positivity
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow : s ^ ((d : ℝ) - 1) ≤ n := by
    calc s ^ ((d : ℝ) - 1) ≤ s ^ (d : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hs (by linarith)
      _ = s ^ d := Real.rpow_natCast s d
      _ ≤ n := hsd
  have e : s ^ ((d : ℝ) - 1) * s ^ (2 - (d : ℝ)) = s := by
    rw [← Real.rpow_add hs0, show ((d : ℝ) - 1) + (2 - d) = 1 by ring, Real.rpow_one]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hQle : (s / σ) / (Ct * s ^ (2 - (d : ℝ)) * L) ≤ ((n : ℝ) + 2) / (σ * Ct) := by
    rw [div_le_iff₀ hden]
    have h1 : s ≤ ((n : ℝ) + 2) * (s ^ (2 - (d : ℝ)) * L) := by
      calc s = s ^ ((d : ℝ) - 1) * s ^ (2 - (d : ℝ)) := e.symm
        _ ≤ n * s ^ (2 - (d : ℝ)) := mul_le_mul_of_nonneg_right hpow hw.le
        _ ≤ n * (s ^ (2 - (d : ℝ)) * L) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hw.le hL1) hn0
        _ ≤ ((n : ℝ) + 2) * (s ^ (2 - (d : ℝ)) * L) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc s / σ = s / (σ * Ct) * Ct := by field_simp
      _ ≤ ((n : ℝ) + 2) * (s ^ (2 - (d : ℝ)) * L) / (σ * Ct) * Ct := by gcongr
      _ = ((n : ℝ) + 2) / (σ * Ct) * (Ct * s ^ (2 - (d : ℝ)) * L) := by field_simp
  have hlog : Real.log ((s / σ) / (Ct * s ^ (2 - (d : ℝ)) * L)) ≤ L + |Real.log (σ * Ct)| := by
    have h1 := Real.log_le_log hQ0 hQle
    rw [Real.log_div (by positivity) hσCt.ne', ← hL] at h1
    have := neg_abs_le (Real.log (σ * Ct))
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb : Real.logb 2 ((s / σ) / (Ct * s ^ (2 - (d : ℝ)) * L)) ≤
      (L + |Real.log (σ * Ct)|) / Real.log 2 := by
    rw [Real.logb]
    exact div_le_div_of_nonneg_right hlog hlog2.le
  have hnn : 0 ≤ (L + |Real.log (σ * Ct)|) / Real.log 2 := by positivity
  have hmax : max 0 (Real.logb 2 ((s / σ) / (Ct * s ^ (2 - (d : ℝ)) * L))) ≤
      (L + |Real.log (σ * Ct)|) / Real.log 2 := max_le hnn hlogb
  have habs : 0 ≤ |Real.log (σ * Ct)| := abs_nonneg _
  have hfin : (L + |Real.log (σ * Ct)|) / Real.log 2 ≤
      (1 + |Real.log (σ * Ct)|) / Real.log 2 * L := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hlog2.le
    nlinarith
  calc (M : ℝ) ≤ (L + |Real.log (σ * Ct)|) / Real.log 2 + 1 := by linarith
    _ ≤ (1 + |Real.log (σ * Ct)|) / Real.log 2 * L + 1 * L := by linarith
    _ = ((1 + |Real.log (σ * Ct)|) / Real.log 2 + 1) * L := by ring

/-- The shell error times `s^(1-α)`, with `δ ≤ C₁ √s L` and `M ≤ cM L`, is a power of `s`
times a power of `L`. -/
private lemma shell_delta_le {s L δ C₁ α cM M : ℝ} (hs : 0 < s) (hL : 0 < L) (hα : 0 < α)
    (hC₁ : 0 < C₁) (hδ0 : 0 ≤ δ) (hδ : δ ≤ C₁ * Real.sqrt s * L)
    (hM : M ≤ cM * L) (hcM : 0 ≤ cM) :
    s ^ (1 - α) * (M * δ ^ α) ≤ cM * C₁ ^ α * (s ^ (1 - α / 2) * L ^ (1 + α)) := by
  have hδα : δ ^ α ≤ C₁ ^ α * s ^ (α / 2) * L ^ α := by
    calc δ ^ α ≤ (C₁ * Real.sqrt s * L) ^ α := Real.rpow_le_rpow hδ0 hδ hα.le
      _ = C₁ ^ α * (Real.sqrt s) ^ α * L ^ α := by
          rw [Real.mul_rpow (by positivity) hL.le, Real.mul_rpow hC₁.le (Real.sqrt_nonneg s)]
      _ = C₁ ^ α * s ^ (α / 2) * L ^ α := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le, show 1 / 2 * α = α / 2 by ring]
  have h1 : M * δ ^ α ≤ (cM * L) * (C₁ ^ α * s ^ (α / 2) * L ^ α) := by
    apply mul_le_mul hM hδα (Real.rpow_nonneg hδ0 α) (by positivity)
  have e1 : s ^ (1 - α) * s ^ (α / 2) = s ^ (1 - α / 2) := by
    rw [← Real.rpow_add hs]
    ring_nf
  have e2 : L * L ^ α = L ^ (1 + α) := by
    rw [Real.rpow_add hL, Real.rpow_one]
  calc s ^ (1 - α) * (M * δ ^ α) ≤ s ^ (1 - α) * ((cM * L) * (C₁ ^ α * s ^ (α / 2) * L ^ α)) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hs.le _)
    _ = cM * C₁ ^ α * ((s ^ (1 - α) * s ^ (α / 2)) * (L * L ^ α)) := by ring
    _ = cM * C₁ ^ α * (s ^ (1 - α / 2) * L ^ (1 + α)) := by rw [e1, e2]

/-- The leading term of the halving cost: `P (s/σ)^α = C B₀^β s`. -/
private lemma lead_term {s σ α β B₀ Csh : ℝ} (hs : 0 < s) (hσ : 0 < σ) (hα : 0 < α) :
    Csh * B₀ ^ β * s ^ (1 - α) * ((s / σ) ^ α / (1 - (2 : ℝ) ^ (-α))) =
      Csh * B₀ ^ β * s / (σ ^ α * (1 - (2 : ℝ) ^ (-α))) := by
  have e : s ^ (1 - α) * s ^ α = s := by
    rw [← Real.rpow_add hs]
    simp
  have hσα : 0 < σ ^ α := Real.rpow_pos_of_pos hσ α
  have hden : 0 < 1 - (2 : ℝ) ^ (-α) := by
    have : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  rw [Real.div_rpow hs.le hσ.le]
  field_simp
  rw [mul_assoc (Csh * B₀ ^ β), e]

/-- The total halving distance `⌈s⌉ + 2 b Σ` fits inside `(C_w B₀^β + 3) s`. -/
private lemma cost_le {s σ α β B₀ Csh Cr Cw b δ C₁ L cM M Sg : ℝ} (hs : 1 ≤ s) (hσ : 0 < σ)
    (hα : 0 < α) (hb : 0 ≤ b) (hCr : 1 ≤ Cr) (hCsh : 0 < Csh) (hB₀ : 0 < B₀) (hC₁ : 0 < C₁)
    (hL : 1 ≤ L) (hcM : 0 ≤ cM) (hδ0 : 0 ≤ δ) (hδ : δ ≤ C₁ * Real.sqrt s * L)
    (hM : M ≤ cM * L)
    (hbud : Sg ≤ 4 * Cr * (Csh * B₀ ^ β * s ^ (1 - α) *
      ((s / σ) ^ α / (1 - (2 : ℝ) ^ (-α)) + M * δ ^ α) + M) + 2 * M)
    (hCw : 8 * b * Cr * Csh / (σ ^ α * (1 - (2 : ℝ) ^ (-α))) ≤ Cw)
    (hE4 : (8 * b * Cr + 4 * b) * cM * L ≤ s / 2)
    (hE5 : 2 * (8 * b * Cr * Csh * B₀ ^ β * cM * C₁ ^ α) * L ^ (1 + α) ≤ s ^ (α / 2)) :
    (⌈s⌉₊ : ℝ) + 2 * b * Sg ≤ (Cw * B₀ ^ β + 3) * s := by
  have hs0 : 0 < s := by linarith
  have hL0 : 0 < L := by linarith
  have hBβ : 0 < B₀ ^ β := Real.rpow_pos_of_pos hB₀ β
  have hden : 0 < 1 - (2 : ℝ) ^ (-α) := by
    have : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  have hσα : 0 < σ ^ α := Real.rpow_pos_of_pos hσ α
  have hlead := lead_term (Csh := Csh) (β := β) (B₀ := B₀) hs0 hσ hα
  have hdel := shell_delta_le hs0 hL0 hα hC₁ hδ0 hδ hM hcM
  have hSsp : 0 < s ^ (1 - α) := Real.rpow_pos_of_pos hs0 _
  have hb2 : 0 ≤ 2 * b := by linarith
  have h1 : 2 * b * Sg ≤ 2 * b * (4 * Cr * (Csh * B₀ ^ β * s ^ (1 - α) *
      ((s / σ) ^ α / (1 - (2 : ℝ) ^ (-α)) + M * δ ^ α) + M) + 2 * M) :=
    mul_le_mul_of_nonneg_left hbud hb2
  have h2 : 2 * b * (4 * Cr * (Csh * B₀ ^ β * s ^ (1 - α) *
      ((s / σ) ^ α / (1 - (2 : ℝ) ^ (-α)) + M * δ ^ α) + M) + 2 * M) =
      8 * b * Cr * (Csh * B₀ ^ β * s ^ (1 - α) * ((s / σ) ^ α / (1 - (2 : ℝ) ^ (-α)))) +
      8 * b * Cr * (Csh * B₀ ^ β) * (s ^ (1 - α) * (M * δ ^ α)) +
      (8 * b * Cr + 4 * b) * M := by ring
  have hT1 : 8 * b * Cr * (Csh * B₀ ^ β * s ^ (1 - α) * ((s / σ) ^ α / (1 - (2 : ℝ) ^ (-α)))) ≤
      Cw * B₀ ^ β * s := by
    rw [hlead]
    have : 8 * b * Cr * (Csh * B₀ ^ β * s / (σ ^ α * (1 - (2 : ℝ) ^ (-α)))) =
        8 * b * Cr * Csh / (σ ^ α * (1 - (2 : ℝ) ^ (-α))) * (B₀ ^ β * s) := by
      field_simp
    rw [this]
    calc _ ≤ Cw * (B₀ ^ β * s) := mul_le_mul_of_nonneg_right hCw (by positivity)
      _ = Cw * B₀ ^ β * s := by ring
  have hT2 : 8 * b * Cr * (Csh * B₀ ^ β) * (s ^ (1 - α) * (M * δ ^ α)) ≤ s / 2 := by
    have hcoef : 0 ≤ 8 * b * Cr * (Csh * B₀ ^ β) := by positivity
    have h3 := mul_le_mul_of_nonneg_left hdel hcoef
    have hs2 : 0 ≤ s ^ (1 - α / 2) := Real.rpow_nonneg hs0.le _
    have e : s ^ (1 - α / 2) * s ^ (α / 2) = s := by
      rw [← Real.rpow_add hs0]
      ring_nf
      exact Real.rpow_one s
    have h4 := mul_le_mul_of_nonneg_left hE5 hs2
    calc _ ≤ 8 * b * Cr * (Csh * B₀ ^ β) * (cM * C₁ ^ α * (s ^ (1 - α / 2) * L ^ (1 + α))) := h3
      _ = (8 * b * Cr * Csh * B₀ ^ β * cM * C₁ ^ α) * L ^ (1 + α) * s ^ (1 - α / 2) := by ring
      _ ≤ s / 2 := by nlinarith
  have hT3 : (8 * b * Cr + 4 * b) * M ≤ s / 2 := by
    have : (8 * b * Cr + 4 * b) * M ≤ (8 * b * Cr + 4 * b) * (cM * L) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    linarith
  have hceil : (⌈s⌉₊ : ℝ) ≤ 2 * s := by
    have := Nat.ceil_lt_add_one hs0.le
    linarith
  have hT : 2 * b * Sg ≤ Cw * B₀ ^ β * s + s := by
    rw [h2] at h1
    calc 2 * b * Sg
        ≤ 8 * b * Cr * (Csh * B₀ ^ β * s ^ (1 - α) *
              ((s / σ) ^ α / (1 - (2 : ℝ) ^ (-α)))) +
            8 * b * Cr * (Csh * B₀ ^ β) * (s ^ (1 - α) * (M * δ ^ α)) +
            (8 * b * Cr + 4 * b) * M := h1
      _ ≤ Cw * B₀ ^ β * s + s / 2 + s / 2 := add_le_add (add_le_add hT1 hT2) hT3
      _ = Cw * B₀ ^ β * s + s := by ring
  calc (⌈s⌉₊ : ℝ) + 2 * b * Sg ≤ 2 * s + (Cw * B₀ ^ β * s + s) :=
        add_le_add hceil hT
    _ = (Cw * B₀ ^ β + 3) * s := by ring

/-- Every real power of `log (n + 2)` is eventually at most `ε` times a positive power of `n`. -/
private lemma eventually_log_rpow_le (a : ℝ) {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, Real.log (n + 2) ^ a ≤ ε * (n : ℝ) ^ p := by
  have h := CERW.Support.Main.tendsto_log_rpow_div_rpow a hp
  filter_upwards [h.eventually (gt_mem_nhds hε), Filter.eventually_ge_atTop 1] with n hn hn1
  have hnp : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos (by exact_mod_cast hn1) p
  rw [div_lt_iff₀ hnp] at hn
  exact hn.le

/-- If `x² ≤ n` and `y² ≤ n`, then `x y ≤ n`. -/
private lemma mul_le_of_sq_le {x y n : ℝ} (hx : x ^ 2 ≤ n) (hy : y ^ 2 ≤ n) : x * y ≤ n := by
  nlinarith [sq_nonneg (x - y)]

/-- One grid cell: at an integer radius `r` with `s + b ≤ r`, the radial inequality and the shell
bound give the halving alternative for the level `A`. -/
private lemma grid_step (hd : 2 ≤ d) {Crad Cr C₁ Csh bd B₀ α β Ct s L δ Mx A P : ℝ}
    {b : ℕ} {F : ℝ → ℝ} {Sh : ℕ → ℝ} {r : ℕ} (hCrad : 0 < Crad) (hCrad' : Crad ≤ Cr)
    (hCr1 : 1 ≤ Cr) (hC₁ : 0 < C₁) (hCsh : 0 < Csh) (hB₀ : 0 < B₀)
    (hCt : Ct = 64 * Cr ^ 2 * (1 + C₁)) (hα0 : 0 < α) (hbd1 : 1 ≤ bd)
    (hbd : bd ≤ b) (hFanti : AntitoneOn F (Set.Ioi 0)) (hF0 : ∀ t, 0 ≤ F t)
    (hSh0 : 0 ≤ Sh r) (hs1 : 1 ≤ s) (hrs : s + b ≤ (r : ℝ))
    (hL0 : 0 ≤ L) (hMx : Mx ≤ C₁ * s) (hδ0 : 0 ≤ δ)
    (hP : P = Csh * B₀ ^ β * s ^ (1 - α))
    (hrad : F (r + bd) ≤ Crad * Sh r * (F (r - bd) - F (r + bd)) +
      Crad * (Real.sqrt (Mx * (r : ℝ) ^ (1 - (d : ℝ)) * F (r - bd) * L) +
        (r : ℝ) ^ (1 - (d : ℝ)) * L))
    (hshell : Sh r ≤ Csh * B₀ ^ β * s ^ (1 - α) * (F (r - bd) + δ) ^ α)
    (hA : Ct * s ^ (2 - (d : ℝ)) * L ≤ A) (hFA : F (r - b) ≤ A) :
    F (r + b) ≤ A / 2 ∨ A / (4 * Cr * (P * (A + δ) ^ α + 1)) ≤ F (r - b) - F (r + b) := by
  have hb0 : (0 : ℝ) ≤ b := by linarith
  have hspos : 0 < s := by linarith
  have hrpos : 0 < (r : ℝ) := by linarith
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hmem : ∀ t : ℝ, s ≤ t → t ∈ Set.Ioi (0 : ℝ) := fun t ht => Set.mem_Ioi.2 (by linarith)
  have hFm : F (r - bd) ≤ F (r - b) :=
    hFanti (hmem _ (by linarith)) (hmem _ (by linarith)) (by linarith)
  have hFp' : F (r + b) ≤ F (r + bd) :=
    hFanti (hmem _ (by linarith)) (hmem _ (by linarith)) (by linarith)
  have hFpm : F (r + bd) ≤ F (r - bd) :=
    hFanti (hmem _ (by linarith)) (hmem _ (by linarith)) (by linarith)
  have hw : 0 < s ^ (2 - (d : ℝ)) := Real.rpow_pos_of_pos hspos _
  have hρ : (r : ℝ) ^ (1 - (d : ℝ)) ≤ s ^ (1 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hspos (by linarith) (by linarith)
  have hρ0 : 0 ≤ (r : ℝ) ^ (1 - (d : ℝ)) := Real.rpow_nonneg hrpos.le _
  have hw' : s ^ (2 - (d : ℝ)) = s * s ^ (1 - (d : ℝ)) := by
    rw [show (2 : ℝ) - d = 1 + (1 - d) by ring, Real.rpow_add hspos, Real.rpow_one]
  have hρw : s ^ (1 - (d : ℝ)) ≤ s ^ (2 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  have herr := radial_error_le hCrad hCrad' hCr1 hC₁ hCt hL0 hMx hρ0
    (by rw [hw']; exact mul_le_mul_of_nonneg_left hρ hspos.le) (hρ.trans hρw) (hF0 _)
    (hFm.trans hFA) (by rw [← mul_assoc]; exact hA)
  have hS : Sh r ≤ P * (A + δ) ^ α := by
    rw [hP]
    refine hshell.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Real.rpow_le_rpow (add_nonneg (hF0 _) hδ0) (by linarith [hFm.trans hFA]) hα0.le
  exact step_dichotomy hCrad hCrad' hSh0 hS hFp' hFm hFpm hrad herr

/-- The dyadic halving on the grid `⌈s⌉ + b + 2bj`: from the grid-step alternative and the
budget estimates, `F((B₀ - 2) s) ≤ Ct s^(2-d) L`. -/
private lemma halving_bound (hd : 2 ≤ d) {Cr C₁ Csh σ B₀ Cw α β Ct s L δ cM : ℝ} {b n : ℕ}
    {F : ℝ → ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hCr1 : 1 ≤ Cr) (hC₁ : 0 < C₁) (hCsh : 0 < Csh)
    (hσ : 0 < σ) (hB₀ : 3 ≤ B₀) (hb0 : 0 < (b : ℝ)) (hcM0 : 0 < cM)
    (hCt : Ct = 64 * Cr ^ 2 * (1 + C₁)) (hcM : cM = (1 + |Real.log (σ * Ct)|) / Real.log 2 + 1)
    (hCw : 8 * b * Cr * Csh / (σ ^ α * (1 - (2 : ℝ) ^ (-α))) ≤ Cw)
    (hwin : Cw * B₀ ^ β + 6 ≤ B₀) (hFanti : AntitoneOn F (Set.Ioi 0)) (hF0 : ∀ t, 0 ≤ F t)
    (hFs : F s ≤ s / σ) (hs1 : 1 ≤ s) (hbs : (b : ℝ) ≤ s) (hsd : s ^ d ≤ n)
    (hL : L = Real.log (n + 2)) (hL1 : 1 ≤ L) (hδ0 : 0 ≤ δ) (hδ : δ ≤ C₁ * Real.sqrt s * L)
    (hE4 : (8 * b * Cr + 4 * b) * cM * L ≤ s / 2)
    (hE5 : 2 * (8 * b * Cr * Csh * B₀ ^ β * cM * C₁ ^ α) * L ^ (1 + α) ≤ s ^ (α / 2))
    (hstep : ∀ r : ℕ, s + b ≤ (r : ℝ) → (r : ℝ) ≤ (B₀ - 2) * s → ∀ A : ℝ,
      Ct * s ^ (2 - (d : ℝ)) * L ≤ A → F (r - b) ≤ A → F (r + b) ≤ A / 2 ∨
        A / (4 * Cr * (Csh * B₀ ^ β * s ^ (1 - α) * (A + δ) ^ α + 1)) ≤
          F (r - b) - F (r + b)) :
    F ((B₀ - 2) * s) ≤ Ct * s ^ (2 - (d : ℝ)) * L := by
  have hspos : 0 < s := by linarith
  have hL0 : 0 < L := by linarith
  have hCr0 : 0 < Cr := by linarith
  have hCtpos : 0 < Ct := by rw [hCt]; positivity
  have hB₀0 : 0 < B₀ := by linarith
  have hBβ : 0 < B₀ ^ β := Real.rpow_pos_of_pos hB₀0 β
  have hG : ∀ t, 0 ≤ F (max t s) := fun t => hF0 _
  set G : ℝ → ℝ := fun t => F (max t s) with hGdef
  have hGanti : Antitone G := by
    intro x y hxy
    exact hFanti (Set.mem_Ioi.2 (lt_of_lt_of_le hspos (le_max_right x s)))
      (Set.mem_Ioi.2 (lt_of_lt_of_le hspos (le_max_right y s))) (max_le_max hxy le_rfl)
  have hGeq : ∀ t, s ≤ t → G t = F t := fun t ht => by simp only [hGdef, max_eq_left ht]
  set Λ : ℝ := Ct * s ^ (2 - (d : ℝ)) * L with hΛ
  have hw : 0 < s ^ (2 - (d : ℝ)) := Real.rpow_pos_of_pos hspos _
  have hΛpos : 0 < Λ := by positivity
  set P : ℝ := Csh * B₀ ^ β * s ^ (1 - α) with hP
  have hP0 : 0 < P := by positivity
  set K : ℝ → ℝ := fun A => 4 * Cr * (P * (max A 0 + δ) ^ α + 1) with hK
  have hK' : ∀ A, 0 ≤ A → K A = 4 * Cr * (P * (A + δ) ^ α + 1) := by
    intro A hA
    simp only [hK, max_eq_left hA]
  have hKge : ∀ A, 1 ≤ K A := by
    intro A
    have hpow : 0 ≤ P * (max A 0 + δ) ^ α :=
      mul_nonneg hP0.le (Real.rpow_nonneg (add_nonneg (le_max_right _ _) hδ0) α)
    simp only [hK]
    calc (1 : ℝ) ≤ 4 * Cr * 1 := by linarith
      _ ≤ 4 * Cr * (P * (max A 0 + δ) ^ α + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  set A₀ : ℝ := s / σ with hA₀
  have hA₀pos : 0 < A₀ := by positivity
  obtain ⟨M, hM1, hM2⟩ := CERW.Generic.Halving.exists_halvings_le hA₀pos hΛpos
  set Sg : ℕ := ∑ k ∈ Finset.range M, (⌈K (A₀ / 2 ^ k)⌉₊ + 1) with hSg
  have hbud := budget_le (K := K) hCr0.le hP0.le hα0 hα1 hA₀pos.le hδ0 hK' M
  have hMcM : (M : ℝ) ≤ cM * L := by
    rw [hcM]
    exact levels_bound hσ hCtpos hs1 (by omega) hsd hL hL1 hM2
  have hT := cost_le hs1 hσ hα0 hb0.le hCr1 hCsh hB₀0 hC₁ hL1 hcM0.le hδ0 hδ hMcM hbud hCw
    hE4 hE5
  have hTle : (⌈s⌉₊ : ℝ) + 2 * b * Sg + b ≤ (B₀ - 2) * s := by
    have h1 := mul_le_mul_of_nonneg_right (show Cw * B₀ ^ β + 4 ≤ B₀ - 2 by linarith)
      hspos.le
    linarith
  have hstep' : ∀ j : ℕ, j ≤ Sg → ∀ A : ℝ, Λ ≤ A → G ((⌈s⌉₊ : ℝ) + b + 2 * b * j - b) ≤ A →
      G ((⌈s⌉₊ : ℝ) + b + 2 * b * j + b) ≤ A / 2 ∨
        A / K A ≤ G ((⌈s⌉₊ : ℝ) + b + 2 * b * j - b) -
          G ((⌈s⌉₊ : ℝ) + b + 2 * b * j + b) := by
    intro j hj A hA hGA
    have hApos : 0 < A := lt_of_lt_of_le hΛpos hA
    have hjle : (j : ℝ) ≤ Sg := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hceil := Nat.le_ceil s
    have hbj : 0 ≤ 2 * (b : ℝ) * j := by positivity
    have hbj' : 2 * (b : ℝ) * j ≤ 2 * b * Sg := mul_le_mul_of_nonneg_left hjle (by positivity)
    have hrs : s + b ≤ (⌈s⌉₊ : ℝ) + b + 2 * b * j := by linarith
    have hrB : (⌈s⌉₊ : ℝ) + b + 2 * b * j ≤ (B₀ - 2) * s := by linarith
    have hG1 : G ((⌈s⌉₊ : ℝ) + b + 2 * b * j - b) = F ((⌈s⌉₊ : ℝ) + b + 2 * b * j - b) :=
      hGeq _ (by linarith)
    have hG2 : G ((⌈s⌉₊ : ℝ) + b + 2 * b * j + b) = F ((⌈s⌉₊ : ℝ) + b + 2 * b * j + b) :=
      hGeq _ (by linarith)
    rw [hG1] at hGA
    rw [hG1, hG2]
    have hr := hstep (⌈s⌉₊ + b + 2 * b * j) (by push_cast; exact hrs) (by push_cast; exact hrB) A
      hA (by push_cast; exact hGA)
    push_cast at hr
    rcases hr with h | h
    · exact Or.inl h
    · right
      rw [hK' A hApos.le]
      exact h
  have hstart : G ((⌈s⌉₊ : ℝ) + b - b) ≤ A₀ := by
    have e : (⌈s⌉₊ : ℝ) + b - b = ⌈s⌉₊ := by ring
    rw [e, hGeq _ (Nat.le_ceil s)]
    calc F ⌈s⌉₊ ≤ F s := hFanti (Set.mem_Ioi.2 hspos)
          (Set.mem_Ioi.2 (lt_of_lt_of_le hspos (Nat.le_ceil s))) (Nat.le_ceil s)
      _ ≤ s / σ := hFs
  have hmain := CERW.Generic.Halving.halving_iterate hGanti hG hb0 hΛpos K hKge Sg hstep' M hM1
    hstart (Nat.le_succ _)
  have hge : s ≤ (B₀ - 2) * s := by
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ B₀ - 2 by linarith) hspos.le
    linarith
  rw [← hGeq _ hge]
  calc G ((B₀ - 2) * s) ≤ G ((⌈s⌉₊ : ℝ) + b + 2 * b * Sg - b) := hGanti (by linarith)
    _ ≤ Λ := hmain

/-- The deterministic core: the coarse tail bound for an abstract nonincreasing `F` and abstract
occupation data. -/
private lemma core_bound (hd : 2 ≤ d) {Crad C₁ Csh c bd r₀ σ B₀ Cw α β : ℝ}
    (hα : α = 1 / (2 * (d : ℝ) - 1))
    (hCrad : 0 < Crad) (hC₁ : 0 < C₁) (hCsh : 0 < Csh) (hc : 0 < c) (hbd : 1 ≤ bd)
    (hσ : 0 < σ) (hB₀ : 3 ≤ B₀)
    (hCw : 8 * (⌈bd⌉₊ : ℝ) * max 1 Crad * Csh / (σ ^ α * (1 - (2 : ℝ) ^ (-α))) ≤ Cw)
    (hwin : Cw * B₀ ^ β + 6 ≤ B₀) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (s L δ Mx : ℝ) (F : ℝ → ℝ) (Sh : ℕ → ℝ), n₀ ≤ n →
      L = Real.log (n + 2) → AntitoneOn F (Set.Ioi 0) → (∀ t, 0 ≤ F t) → (∀ r, 0 ≤ Sh r) →
      s ^ d ≤ n → (0 < s → F s ≤ s / σ) →
      c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ≤ s → Mx ≤ C₁ * s → 0 ≤ δ →
      δ ≤ C₁ * Real.sqrt s * L →
      (∀ r : ℕ, r₀ ≤ r → r ≤ n →
        F (r + bd) ≤ Crad * Sh r * (F (r - bd) - F (r + bd)) +
          Crad * (Real.sqrt (Mx * (r : ℝ) ^ (1 - (d : ℝ)) * F (r - bd) * L) +
            (r : ℝ) ^ (1 - (d : ℝ)) * L)) →
      (∀ r : ℕ, s ≤ r → (r : ℝ) ≤ B₀ * s →
        Sh r ≤ Csh * B₀ ^ β * s ^ (1 - α) * (F (r - bd) + δ) ^ α) →
      F ((B₀ - 2) * s) ≤ 64 * (max 1 Crad) ^ 2 * (1 + C₁) * s ^ (2 - (d : ℝ)) * L := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hα0 : 0 < α := by
    rw [hα]
    apply div_pos one_pos
    linarith
  have hα1 : α ≤ 1 := by
    rw [hα, div_le_one (by linarith)]
    linarith
  set b : ℕ := ⌈bd⌉₊ with hb
  have hbd_le : bd ≤ (b : ℝ) := Nat.le_ceil bd
  have hb1 : (1 : ℝ) ≤ b := le_trans hbd hbd_le
  have hb0 : (0 : ℝ) < b := by linarith
  set Cr : ℝ := max 1 Crad with hCr
  have hCr1 : 1 ≤ Cr := le_max_left _ _
  have hCrad' : Crad ≤ Cr := le_max_right _ _
  have hCr0 : 0 < Cr := by linarith
  set Ct : ℝ := 64 * Cr ^ 2 * (1 + C₁) with hCt
  have hCtpos : 0 < Ct := by positivity
  set cM : ℝ := (1 + |Real.log (σ * Ct)|) / Real.log 2 + 1 with hcM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcM0 : 0 < cM := by positivity
  set K₁ : ℝ := 8 * b * Cr * Csh * B₀ ^ β * cM * C₁ ^ α with hK₁
  set K₂ : ℝ := (8 * b * Cr + 4 * b) * cM with hK₂
  set T₁ : ℝ := max 1 (max b r₀) with hT₁
  have hB₀0 : 0 < B₀ := by linarith
  have hBβ : 0 < B₀ ^ β := Real.rpow_pos_of_pos hB₀0 β
  have hK₁0 : 0 < K₁ := by positivity
  have hK₂0 : 0 < K₂ := by positivity
  have hT₁0 : 0 < T₁ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hp : (0 : ℝ) < 1 / (d + 1) := by positivity
  have hevA := eventually_log_rpow_le 0 hp (ε := c / T₁) (by positivity)
  have hevB := eventually_log_rpow_le 1 hp (ε := c / (2 * K₂)) (by positivity)
  have hp3 : (0 : ℝ) < 1 / (d + 1) * (α / 2) := by positivity
  have hevC := eventually_log_rpow_le (1 + α) hp3 (ε := c ^ (α / 2) / (2 * K₁))
    (by positivity)
  have hevD := Filter.eventually_ge_atTop ⌈B₀ ^ 2⌉₊
  have hevE := Filter.eventually_ge_atTop (1 : ℕ)
  obtain ⟨n₀, hn₀⟩ :=
    Filter.eventually_atTop.1 (hevA.and (hevB.and (hevC.and (hevD.and hevE))))
  refine ⟨n₀, ?_⟩
  intro n s L δ Mx F Sh hn hL hFanti hF0 hSh0 hsd hFs hcs hMx hδ0 hδ hrad hshell
  obtain ⟨e1, e2, e3, e4, e5⟩ := hn₀ n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast e5
  set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1)) with hN
  have hN0 : 0 ≤ N := Real.rpow_nonneg hn0 _
  have hT₁s : T₁ ≤ s := by
    have e1' : (1 : ℝ) ≤ c / T₁ * N := by simpa only [Real.rpow_zero] using e1
    calc T₁ = T₁ * 1 := (mul_one _).symm
      _ ≤ T₁ * (c / T₁ * N) := mul_le_mul_of_nonneg_left e1' hT₁0.le
      _ = c * N := by field_simp
      _ ≤ s := hcs
  have hs1 : 1 ≤ s := le_trans (le_max_left _ _) hT₁s
  have hbs : (b : ℝ) ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT₁s
  have hr₀s : r₀ ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT₁s
  have hspos : 0 < s := by linarith
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_three
    linarith
  have hL0 : 0 < L := by linarith
  have hE4 : (8 * b * Cr + 4 * b) * cM * L ≤ s / 2 := by
    have e2' : 2 * K₂ * L ≤ c * N := by
      have h1 : L ≤ c / (2 * K₂) * N := by
        rw [hL]
        simpa only [Real.rpow_one] using e2
      calc 2 * K₂ * L ≤ 2 * K₂ * (c / (2 * K₂) * N) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = c * N := by field_simp
    have : K₂ * L ≤ s / 2 := by linarith
    simpa only [hK₂] using this
  have hE5 : 2 * K₁ * L ^ (1 + α) ≤ s ^ (α / 2) := by
    have h1 : 2 * K₁ * L ^ (1 + α) ≤ c ^ (α / 2) * (n : ℝ) ^ (1 / ((d : ℝ) + 1) * (α / 2)) := by
      calc 2 * K₁ * L ^ (1 + α)
          ≤ 2 * K₁ * (c ^ (α / 2) / (2 * K₁) * (n : ℝ) ^ (1 / ((d : ℝ) + 1) * (α / 2))) := by
            rw [hL]
            exact mul_le_mul_of_nonneg_left e3 (by positivity)
        _ = _ := by field_simp
    have h2 : c ^ (α / 2) * (n : ℝ) ^ (1 / ((d : ℝ) + 1) * (α / 2)) = (c * N) ^ (α / 2) := by
      rw [Real.mul_rpow hc.le hN0, hN, ← Real.rpow_mul hn0]
    rw [h2] at h1
    exact le_trans h1 (Real.rpow_le_rpow (by positivity) hcs (by positivity))
  have hs2 : s ^ 2 ≤ s ^ d := pow_le_pow_right₀ hs1 hd
  have hB2 : B₀ ^ 2 ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast e4)
  have hBs : B₀ * s ≤ n := mul_le_of_sq_le hB2 (le_trans hs2 hsd)
  have hstep : ∀ r : ℕ, s + b ≤ (r : ℝ) → (r : ℝ) ≤ (B₀ - 2) * s → ∀ A : ℝ,
      Ct * s ^ (2 - (d : ℝ)) * L ≤ A → F (r - b) ≤ A → F (r + b) ≤ A / 2 ∨
        A / (4 * Cr * (Csh * B₀ ^ β * s ^ (1 - α) * (A + δ) ^ α + 1)) ≤
          F (r - b) - F (r + b) := by
    intro r hrs hrB A hA hFA
    have hr₀ : r₀ ≤ (r : ℝ) := by linarith
    have hB2' : (B₀ - 2) * s ≤ B₀ * s := mul_le_mul_of_nonneg_right (by linarith) hspos.le
    have hrn : r ≤ n := by exact_mod_cast hrB.trans (hB2'.trans hBs)
    exact grid_step hd hCrad hCrad' hCr1 hC₁ hCsh hB₀0 hCt hα0 hbd hbd_le hFanti hF0 (hSh0 r)
      hs1 hrs hL0.le hMx hδ0 rfl (hrad r hr₀ hrn) (hshell r (by linarith) (hrB.trans hB2')) hA hFA
  exact halving_bound hd hα0 hα1 hCr1 hC₁ hCsh hσ hB₀ hb0 hcM0 hCt hcM hCw hwin hFanti hF0
    (hFs hspos) hs1 hbs hsd hL hL1 hδ0 hδ hE4 hE5 hstep

/-- `eq:coarse-tail`: for constants `C_rad, C₁, C_sh, c > 0`, a grid half-width `b_d ≥ 1` and a
start radius `r₀`, there are a window factor `B₀ ≥ 3` and `C_t` such that, for all large `n`,
the displayed hypotheses imply `F((B₀ - 2) s) ≤ C_t s^{2-d} L`. -/
theorem exists_coarse_tail (hd : 2 ≤ d) {Crad C₁ Csh c bd r₀ : ℝ} (hCrad : 0 < Crad)
    (hC₁ : 0 < C₁) (hCsh : 0 < Csh) (hc : 0 < c) (hbd : 1 ≤ bd) :
    ∃ B₀ Ct : ℝ, 3 ≤ B₀ ∧ 0 < Ct ∧ ∃ n₀ : ℕ, ∀ (X : ℕ → Site d) (n : ℕ) (δ : ℝ), n₀ ≤ n →
      let s : ℝ := ((departureRange X n).card : ℝ) ^ ((1 : ℝ) / d)
      let L : ℝ := Real.log (n + 2)
      let F : ℝ → ℝ := tail d (cellSet X n)
      c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ≤ s → (maxLocalTime X n : ℝ) ≤ C₁ * s → 0 ≤ δ →
      δ ≤ C₁ * Real.sqrt s * L →
      (∀ r : ℕ, r₀ ≤ r → r ≤ n →
        F (r + bd) ≤ Crad * shellMax X n r * (F (r - bd) - F (r + bd)) +
          Crad * (Real.sqrt (maxLocalTime X n * (r : ℝ) ^ (1 - (d : ℝ)) * F (r - bd) * L) +
            (r : ℝ) ^ (1 - (d : ℝ)) * L)) →
      (∀ r : ℕ, s ≤ r → (r : ℝ) ≤ B₀ * s →
        (shellMax X n r : ℝ) ≤ Csh * B₀ ^ (((d : ℝ) - 1) / (2 * d - 1)) *
          s ^ (1 - 1 / (2 * (d : ℝ) - 1)) * (F (r - bd) + δ) ^ (1 / (2 * (d : ℝ) - 1))) →
        F ((B₀ - 2) * s) ≤ Ct * s ^ (2 - (d : ℝ)) * L := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < 2 * (d : ℝ) - 1 := by linarith
  have hα0 : 0 < 1 / (2 * (d : ℝ) - 1) := one_div_pos.2 hd1
  have hβ1 : ((d : ℝ) - 1) / (2 * d - 1) < 1 := (div_lt_one hd1).2 (by linarith)
  have hσ : 0 < (d : ℝ) * unitBallVolume d := mul_pos (by linarith) (unitBallVolume_pos d)
  have h2α : (2 : ℝ) ^ (-(1 / (2 * (d : ℝ) - 1))) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hCw0 : 0 ≤ 8 * (⌈bd⌉₊ : ℝ) * max 1 Crad * Csh /
      (((d : ℝ) * unitBallVolume d) ^ (1 / (2 * (d : ℝ) - 1)) *
        (1 - (2 : ℝ) ^ (-(1 / (2 * (d : ℝ) - 1))))) :=
    div_nonneg (by positivity) (mul_nonneg (Real.rpow_nonneg hσ.le _) (by linarith))
  obtain ⟨B₀, hB₀, hwin⟩ := exists_window hβ1 hCw0
  obtain ⟨n₀, hn₀⟩ := core_bound hd (α := 1 / (2 * (d : ℝ) - 1))
    (β := ((d : ℝ) - 1) / (2 * d - 1)) rfl hCrad hC₁ hCsh hc hbd hσ hB₀ le_rfl hwin
  refine ⟨B₀, 64 * (max 1 Crad) ^ 2 * (1 + C₁), hB₀, by positivity, n₀, ?_⟩
  intro X n δ hn s L F hs hM hδ0 hδ hrad hshell
  have hbdd : Bornology.IsBounded (cellSet X n) :=
    Metric.isBounded_ball.subset (cellSet_subset_ball (by omega) X n)
  have hsd : s ^ d = ((departureRange X n).card : ℝ) := by
    show (((departureRange X n).card : ℝ) ^ ((1 : ℝ) / d)) ^ d = _
    rw [one_div]
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)
  have hsn : s ^ d ≤ n := by
    rw [hsd]
    exact_mod_cast card_departureRange_le X n
  have hFs : 0 < s → F s ≤ s / ((d : ℝ) * unitBallVolume d) := by
    intro hspos
    have h := CERW.Support.Geometry.tail_le (d := d) (by omega) (measurableSet_cellSet X n) hbdd
      hspos
    rw [volume_cellSet, ENNReal.toReal_natCast, ← hsd] at h
    have e : s ^ ((d : ℝ) - 1) = s ^ d / s := by
      rw [Real.rpow_sub_one hspos.ne', Real.rpow_natCast]
    rw [e] at h
    refine h.trans_eq ?_
    field_simp
  exact hn₀ n s L δ (maxLocalTime X n) F (fun r => (shellMax X n r : ℝ)) hn rfl
    (CERW.Support.Geometry.tail_antitoneOn (measurableSet_cellSet X n) hbdd)
    (CERW.Support.Geometry.tail_nonneg _) (fun r => Nat.cast_nonneg _) hsn hFs hs hM hδ0 hδ
    hrad hshell

end CERW.Support.Coarse
