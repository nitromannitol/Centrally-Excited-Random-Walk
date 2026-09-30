import CERW.Generic.Halving.Levels
import CERW.Generic.Halving.Cost
import CERW.Support.Geometry.TailBounds
import CERW.Support.Main.ScaleLimits
import CERW.Model.Occupation
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Occupation.CellNorm
import CERW.Support.Coarse.CrossingArith

/-!
# The tail end beyond the inradius

`eq:tailend`, deterministically. Let `W = N Q^{1/d}` and `Λ = C N^{2-d} L`. Suppose
`c₁ N ≤ b ≤ c₂ N`, `M_n ≤ C₁ N`, `F(b) ≤ C₁ N Q`, and `eq:shellW` (`M_sh(r) ≤ C_sh W` for
`r ≥ b + 3`), and that `eq:radial` holds at every integer radius `r₀ ≤ r ≤ n`. At a dyadic level
`A ≥ Λ`, the radial error is at most `A/4`. Unless `F` halves, each grid step lowers `F` by at
least `cA/(W + 1)`. A halving therefore costs `O(W + 1)` steps. There are `O(L)` levels between
`C₁ N Q` and `Λ`. Hence `F(b + K₀ W L) ≤ C_t N^{2-d} L`.
-/

namespace CERW.Support.Coarse

open LatticeProb CERW

variable {d : ℕ}

/-- The weighted exterior volume of the cell set is nonincreasing on positive radii. -/
private lemma cellSet_tail_antitoneOn (hd : 1 ≤ d) (X : ℕ → Site d) (n : ℕ) :
    AntitoneOn (tail d (cellSet X n)) (Set.Ioi 0) :=
  CERW.Support.Geometry.tail_antitoneOn (CERW.Support.Occupation.measurableSet_cellSet X n)
    (Metric.isBounded_ball.subset (CERW.Support.Occupation.cellSet_subset_ball hd X n))

/-- The number of dyadic levels is at most a constant multiple of `L = log (n + 2)`. -/
private lemma levels_count {γ ρ L : ℝ} {n M : ℕ} (hγ : 0 < γ) (hρ : 0 < ρ)
    (hL : L = Real.log (n + 2)) (hL1 : 1 ≤ L) (hρle : ρ ≤ γ * (n + 2))
    (hM : (M : ℝ) ≤ max 0 (Real.logb 2 ρ) + 1) :
    (M : ℝ) ≤ ((1 + |Real.log γ|) / Real.log 2 + 1) * L := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog : Real.log ρ ≤ L + |Real.log γ| := by
    have h1 := Real.log_le_log hρ hρle
    rw [Real.log_mul hγ.ne' (by positivity), ← hL] at h1
    linarith [le_abs_self (Real.log γ)]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb : Real.logb 2 ρ ≤ (L + |Real.log γ|) / Real.log 2 := by
    rw [Real.logb]
    exact div_le_div_of_nonneg_right hlog hlog2.le
  have hnn : 0 ≤ (L + |Real.log γ|) / Real.log 2 := by positivity
  have hmax : max 0 (Real.logb 2 ρ) ≤ (L + |Real.log γ|) / Real.log 2 := max_le hnn hlogb
  have habs : 0 ≤ |Real.log γ| := abs_nonneg _
  have hfin : (L + |Real.log γ|) / Real.log 2 ≤ (1 + |Real.log γ|) / Real.log 2 * L := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hlog2.le
    nlinarith
  calc (M : ℝ) ≤ (L + |Real.log γ|) / Real.log 2 + 1 := by linarith
    _ ≤ (1 + |Real.log γ|) / Real.log 2 * L + 1 * L := by linarith
    _ = ((1 + |Real.log γ|) / Real.log 2 + 1) * L := by ring

/-- One grid cell: at an integer radius `r` with `b + b' + 3 ≤ r` and `c₁ N ≤ b`, the radial
inequality and the shell bound give the halving alternative for every level `A ≥ Ct N^(2-d) L`. -/
private lemma grid_step (hd : 2 ≤ d) {Crad Cr C₁ c₁ bd N L Mx A Sh Ssh Ct b : ℝ} {b' : ℕ}
    {F : ℝ → ℝ} {r : ℕ} (hCrad : 0 < Crad) (hCrad' : Crad ≤ Cr) (hCr1 : 1 ≤ Cr)
    (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hCt : Ct = 64 * Cr ^ 2 * (1 + C₁) * c₁ ^ (1 - (d : ℝ)))
    (hbd0 : 0 ≤ bd) (hbd : bd ≤ b') (hFanti : AntitoneOn F (Set.Ioi 0)) (hF0 : ∀ t, 0 ≤ F t)
    (hSh0 : 0 ≤ Sh) (hSh : Sh ≤ Ssh) (hN1 : 1 ≤ N) (hL0 : 0 ≤ L) (hMx : Mx ≤ C₁ * N)
    (hcb : c₁ * N ≤ b) (hrb : b + b' + 3 ≤ (r : ℝ))
    (hrad : F (r + bd) ≤ Crad * Sh * (F (r - bd) - F (r + bd)) +
      Crad * (Real.sqrt (Mx * (r : ℝ) ^ (1 - (d : ℝ)) * F (r - bd) * L) +
        (r : ℝ) ^ (1 - (d : ℝ)) * L))
    (hA : Ct * N ^ (2 - (d : ℝ)) * L ≤ A) (hFA : F (r - b') ≤ A) :
    F (r + b') ≤ A / 2 ∨ A / (4 * Cr * (Ssh + 1)) ≤ F (r - b') - F (r + b') := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hb'0 : (0 : ℝ) ≤ b' := Nat.cast_nonneg b'
  have hN0 : 0 < N := by linarith
  have hb0 : 0 < b := lt_of_lt_of_le (mul_pos hc₁ hN0) hcb
  have hrpos : 0 < (r : ℝ) := by linarith
  have hcr : c₁ * N ≤ (r : ℝ) := by linarith
  have hmem : ∀ t : ℝ, b ≤ t → t ∈ Set.Ioi (0 : ℝ) := fun t ht => Set.mem_Ioi.2 (by linarith)
  have hFm : F (r - bd) ≤ F (r - b') :=
    hFanti (hmem _ (by linarith)) (hmem _ (by linarith)) (by linarith)
  have hFp' : F (r + b') ≤ F (r + bd) :=
    hFanti (hmem _ (by linarith)) (hmem _ (by linarith)) (by linarith)
  have hFpm : F (r + bd) ≤ F (r - bd) :=
    hFanti (hmem _ (by linarith)) (hmem _ (by linarith)) (by linarith)
  have hκ : 0 < c₁ ^ (1 - (d : ℝ)) := Real.rpow_pos_of_pos hc₁ _
  have hρ : (r : ℝ) ^ (1 - (d : ℝ)) ≤ c₁ ^ (1 - (d : ℝ)) * N ^ (1 - (d : ℝ)) := by
    rw [← Real.mul_rpow hc₁.le hN0.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hc₁ hN0) hcr (by linarith)
  have hρ0 : 0 ≤ (r : ℝ) ^ (1 - (d : ℝ)) := Real.rpow_nonneg hrpos.le _
  have hw' : N ^ (2 - (d : ℝ)) = N * N ^ (1 - (d : ℝ)) := by
    rw [show (2 : ℝ) - d = 1 + (1 - d) by ring, Real.rpow_add hN0, Real.rpow_one]
  have hρN : N ^ (1 - (d : ℝ)) ≤ N ^ (2 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have herr := radial_error_le (s := N) (w := c₁ ^ (1 - (d : ℝ)) * N ^ (2 - (d : ℝ))) hCrad
    hCrad' hCr1 hC₁ rfl hL0 hMx hρ0
    (by
      calc N * (r : ℝ) ^ (1 - (d : ℝ)) ≤ N * (c₁ ^ (1 - (d : ℝ)) * N ^ (1 - (d : ℝ))) :=
            mul_le_mul_of_nonneg_left hρ hN0.le
        _ = c₁ ^ (1 - (d : ℝ)) * N ^ (2 - (d : ℝ)) := by rw [hw']; ring)
    (hρ.trans (mul_le_mul_of_nonneg_left hρN hκ.le)) (hF0 _) (hFm.trans hFA)
    (by
      have e : 64 * Cr ^ 2 * (1 + C₁) * (c₁ ^ (1 - (d : ℝ)) * N ^ (2 - (d : ℝ)) * L) =
          Ct * N ^ (2 - (d : ℝ)) * L := by rw [hCt]; ring
      rw [e]
      exact hA)
  exact step_dichotomy hCrad hCrad' hSh0 hSh hFp' hFm hFpm hrad herr

/-- The dyadic halving on the grid `⌈b⌉ + b' + 3 + 2 b' j`: the halving alternative at every
grid point with budget `Kc` and a start at most `A₀` force `F` below the floor `Λ` after
`M (⌈Kc⌉ + 1)` grid steps. -/
private lemma halving_const {F : ℝ → ℝ} (hFanti : AntitoneOn F (Set.Ioi 0))
    (hF0 : ∀ t, 0 ≤ F t) {b Λ A₀ Kc : ℝ} {b' : ℕ} (hb : 0 < b) (hb' : 1 ≤ b') (hΛ : 0 < Λ)
    (hKc : 1 ≤ Kc) (M : ℕ) (hM : A₀ / 2 ^ M ≤ Λ) (hstart : F ((⌈b⌉₊ : ℝ) + 3) ≤ A₀)
    (hstep : ∀ j : ℕ, j ≤ M * (⌈Kc⌉₊ + 1) → ∀ A : ℝ, Λ ≤ A →
      F ((⌈b⌉₊ : ℝ) + b' + 3 + 2 * b' * j - b') ≤ A →
      F ((⌈b⌉₊ : ℝ) + b' + 3 + 2 * b' * j + b') ≤ A / 2 ∨
        A / Kc ≤ F ((⌈b⌉₊ : ℝ) + b' + 3 + 2 * b' * j - b') -
          F ((⌈b⌉₊ : ℝ) + b' + 3 + 2 * b' * j + b')) :
    F ((⌈b⌉₊ : ℝ) + 3 + 2 * b' * ((M * (⌈Kc⌉₊ + 1) : ℕ) : ℝ)) ≤ Λ := by
  have hb'0 : (0 : ℝ) < b' := by exact_mod_cast hb'
  have hceil : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
  have hGanti : Antitone fun t : ℝ => F (max t b) := by
    intro x y hxy
    exact hFanti (Set.mem_Ioi.2 (lt_of_lt_of_le hb (le_max_right x b)))
      (Set.mem_Ioi.2 (lt_of_lt_of_le hb (le_max_right y b))) (max_le_max hxy le_rfl)
  have hGeq : ∀ t, b ≤ t → F (max t b) = F t := fun t ht => by rw [max_eq_left ht]
  have hsum : ∑ k ∈ Finset.range M, (⌈(fun _ : ℝ => Kc) (A₀ / 2 ^ k)⌉₊ + 1) =
      M * (⌈Kc⌉₊ + 1) := by
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hmain := CERW.Generic.Halving.halving_iterate (F := fun t : ℝ => F (max t b)) hGanti
    (fun t => hF0 _) (b := (b' : ℝ)) (Λ := Λ) (r₁ := (⌈b⌉₊ : ℝ) + b' + 3) (A₀ := A₀) hb'0 hΛ
    (fun _ => Kc) (fun _ => hKc) (M * (⌈Kc⌉₊ + 1))
    (by
      intro j _ A hA hGA
      have hj0 : (0 : ℝ) ≤ 2 * b' * j := by positivity
      rw [hGeq _ (by linarith)] at hGA
      rw [hGeq _ (by linarith), hGeq _ (by linarith)]
      exact hstep j ‹_› A hA hGA)
    M hM
    (by
      rw [hGeq _ (by linarith)]
      have e : (⌈b⌉₊ : ℝ) + b' + 3 - b' = ⌈b⌉₊ + 3 := by ring
      rw [e]
      exact hstart)
    (by rw [hsum]; omega)
  simp only [hsum] at hmain
  rw [hGeq _ (by nlinarith [sq_nonneg (b' : ℝ)])] at hmain
  have e : (⌈b⌉₊ : ℝ) + b' + 3 + 2 * b' * ((M * (⌈Kc⌉₊ + 1) : ℕ) : ℝ) - b' =
      ⌈b⌉₊ + 3 + 2 * b' * ((M * (⌈Kc⌉₊ + 1) : ℕ) : ℝ) := by ring
  rwa [e] at hmain

/-- The deterministic core: the tail bound for an abstract nonincreasing `F`, abstract
occupation data and abstract scales. -/
private lemma core_tailend (hd : 2 ≤ d) {Crad C₁ Csh c₁ bd r₀ : ℝ} (hCrad : 0 < Crad)
    (hC₁ : 0 < C₁) (hCsh : 0 < Csh) (hc₁ : 0 < c₁) (hbd : 1 ≤ bd) :
    ∃ K₀ Ct : ℝ, 0 < K₀ ∧ 0 < Ct ∧ ∀ (n : ℕ) (N L Q W Mx b : ℝ) (F : ℝ → ℝ) (Sh : ℕ → ℝ),
      AntitoneOn F (Set.Ioi 0) → (∀ t, 0 ≤ F t) → (∀ r, 0 ≤ Sh r) → 1 ≤ N → N ^ d ≤ n →
      r₀ ≤ c₁ * N → L = Real.log (n + 2) → 0 < Q → Q ≤ 1 → 1 ≤ W → b + K₀ * W * L ≤ n →
      c₁ * N ≤ b → Mx ≤ C₁ * N → F b ≤ C₁ * N * Q →
      (∀ r : ℕ, b + 3 ≤ r → Sh r ≤ Csh * W) →
      (∀ r : ℕ, r₀ ≤ r → r ≤ n →
        F (r + bd) ≤ Crad * Sh r * (F (r - bd) - F (r + bd)) +
          Crad * (Real.sqrt (Mx * (r : ℝ) ^ (1 - (d : ℝ)) * F (r - bd) * L) +
            (r : ℝ) ^ (1 - (d : ℝ)) * L)) →
      F (b + K₀ * W * L) ≤ Ct * N ^ (2 - (d : ℝ)) * L := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set b' : ℕ := ⌈bd⌉₊ with hb'
  have hbd_le : bd ≤ (b' : ℝ) := Nat.le_ceil bd
  have hb'1 : (1 : ℝ) ≤ b' := le_trans hbd hbd_le
  have hb'n : 1 ≤ b' := by exact_mod_cast hb'1
  have hb'0 : (0 : ℝ) < b' := by linarith
  set Cr : ℝ := max 1 Crad with hCr
  have hCr1 : 1 ≤ Cr := le_max_left _ _
  have hCrad' : Crad ≤ Cr := le_max_right _ _
  have hCr0 : 0 < Cr := by linarith
  have hκ : 0 < c₁ ^ (1 - (d : ℝ)) := Real.rpow_pos_of_pos hc₁ _
  set Ct : ℝ := 64 * Cr ^ 2 * (1 + C₁) * c₁ ^ (1 - (d : ℝ)) with hCt
  have hCtpos : 0 < Ct := by positivity
  set γ : ℝ := C₁ / Ct with hγ
  have hγ0 : 0 < γ := div_pos hC₁ hCtpos
  set cM : ℝ := (1 + |Real.log γ|) / Real.log 2 + 1 with hcM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcM0 : 0 < cM := by positivity
  set S₁ : ℝ := cM * (4 * Cr * Csh + 4 * Cr + 2) with hS₁
  have hS₁0 : 0 < S₁ := by positivity
  set K₀ : ℝ := b' + 4 + 2 * b' * S₁ with hK₀
  refine ⟨K₀, Ct, by positivity, hCtpos, ?_⟩
  intro n N L Q W Mx b F Sh hFanti hF0 hSh0 hN1 hNd hcN hL hQ0 hQ1 hW1 hrn hcb hMx hFb hsh hrad
  have hN0 : 0 < N := by linarith
  have hn1 : (1 : ℝ) ≤ n := le_trans (one_le_pow₀ hN1) hNd
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_three
    linarith
  have hL0 : 0 < L := by linarith
  have hW0 : 0 < W := by linarith
  have hb0 : 0 < b := lt_of_lt_of_le (mul_pos hc₁ hN0) hcb
  have hw : 0 < N ^ (2 - (d : ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hΛ : 0 < Ct * N ^ (2 - (d : ℝ)) * L := by positivity
  have hA₀ : 0 < C₁ * N * Q := by positivity
  obtain ⟨M, hM1, hM2⟩ := CERW.Generic.Halving.exists_halvings_le hA₀ hΛ
  have hNX : N = N ^ ((d : ℝ) - 1) * N ^ (2 - (d : ℝ)) := by
    rw [← Real.rpow_add hN0, show ((d : ℝ) - 1) + (2 - d) = 1 by ring, Real.rpow_one]
  have hNp : N ^ ((d : ℝ) - 1) ≤ n := by
    calc N ^ ((d : ℝ) - 1) ≤ N ^ (d : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = N ^ d := Real.rpow_natCast N d
      _ ≤ n := hNd
  have hNQ : N * Q ≤ ((n : ℝ) + 2) * (N ^ (2 - (d : ℝ)) * L) := by
    calc N * Q ≤ N * 1 := mul_le_mul_of_nonneg_left hQ1 hN0.le
      _ = N := mul_one _
      _ = N ^ ((d : ℝ) - 1) * N ^ (2 - (d : ℝ)) := hNX
      _ ≤ n * N ^ (2 - (d : ℝ)) := mul_le_mul_of_nonneg_right hNp hw.le
      _ ≤ n * (N ^ (2 - (d : ℝ)) * L) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hw.le hL1) (by positivity)
      _ ≤ ((n : ℝ) + 2) * (N ^ (2 - (d : ℝ)) * L) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hratio : C₁ * N * Q / (Ct * N ^ (2 - (d : ℝ)) * L) ≤ γ * (n + 2) := by
    rw [div_le_iff₀ hΛ]
    calc C₁ * N * Q = C₁ * (N * Q) := by ring
      _ ≤ C₁ * (((n : ℝ) + 2) * (N ^ (2 - (d : ℝ)) * L)) :=
          mul_le_mul_of_nonneg_left hNQ hC₁.le
      _ = γ * (n + 2) * (Ct * N ^ (2 - (d : ℝ)) * L) := by
          rw [hγ]
          field_simp
  have hMcM : (M : ℝ) ≤ cM * L :=
    levels_count hγ0 (div_pos hA₀ hΛ) hL hL1 hratio hM2
  have hKc1 : 1 ≤ 4 * Cr * (Csh * W + 1) := by
    have h1 : 1 ≤ Csh * W + 1 := by
      have := mul_pos hCsh hW0
      linarith
    have h2 : 1 ≤ Cr * (Csh * W + 1) := one_le_mul_of_one_le_of_one_le hCr1 h1
    linarith
  have hSg : ((M * (⌈4 * Cr * (Csh * W + 1)⌉₊ + 1) : ℕ) : ℝ) ≤ S₁ * (W * L) := by
    have hceilK : (⌈4 * Cr * (Csh * W + 1)⌉₊ : ℝ) ≤ 4 * Cr * (Csh * W + 1) + 1 :=
      (Nat.ceil_lt_add_one (by linarith)).le
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have h2 : ((M * (⌈4 * Cr * (Csh * W + 1)⌉₊ + 1) : ℕ) : ℝ) ≤
        M * (4 * Cr * (Csh * W + 1) + 2) := by
      push_cast
      exact mul_le_mul_of_nonneg_left (by linarith) hM0
    have h3 : (M : ℝ) * (4 * Cr * (Csh * W + 1) + 2) ≤
        cM * L * (4 * Cr * (Csh * W + 1) + 2) :=
      mul_le_mul_of_nonneg_right hMcM (by positivity)
    have h4 : 4 * Cr * (Csh * W + 1) + 2 ≤ (4 * Cr * Csh + 4 * Cr + 2) * W := by
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * Cr + 2) (sub_nonneg.mpr hW1)
      linarith
    calc _ ≤ cM * L * (4 * Cr * (Csh * W + 1) + 2) := h2.trans h3
      _ ≤ cM * L * ((4 * Cr * Csh + 4 * Cr + 2) * W) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = S₁ * (W * L) := by rw [hS₁]; ring
  have hWL1 : 1 ≤ W * L := one_le_mul_of_one_le_of_one_le hW1 hL1
  have hceilb : (⌈b⌉₊ : ℝ) ≤ b + 1 := (Nat.ceil_lt_add_one hb0.le).le
  have hbig : (⌈b⌉₊ : ℝ) + b' + 3 +
      2 * b' * ((M * (⌈4 * Cr * (Csh * W + 1)⌉₊ + 1) : ℕ) : ℝ) ≤ b + K₀ * W * L := by
    have h1 : 2 * (b' : ℝ) * ((M * (⌈4 * Cr * (Csh * W + 1)⌉₊ + 1) : ℕ) : ℝ) ≤
        2 * b' * (S₁ * (W * L)) := mul_le_mul_of_nonneg_left hSg (by positivity)
    have h2 : (b' : ℝ) + 4 ≤ (b' + 4) * (W * L) := le_mul_of_one_le_right (by positivity) hWL1
    have h3 : K₀ * W * L = (b' + 4) * (W * L) + 2 * b' * (S₁ * (W * L)) := by
      rw [hK₀]
      ring
    linarith
  have hstep : ∀ j : ℕ, j ≤ M * (⌈4 * Cr * (Csh * W + 1)⌉₊ + 1) → ∀ A : ℝ,
      Ct * N ^ (2 - (d : ℝ)) * L ≤ A →
      F ((⌈b⌉₊ : ℝ) + b' + 3 + 2 * b' * j - b') ≤ A →
      F ((⌈b⌉₊ : ℝ) + b' + 3 + 2 * b' * j + b') ≤ A / 2 ∨
        A / (4 * Cr * (Csh * W + 1)) ≤ F ((⌈b⌉₊ : ℝ) + b' + 3 + 2 * b' * j - b') -
          F ((⌈b⌉₊ : ℝ) + b' + 3 + 2 * b' * j + b') := by
    intro j hj A hA hFA
    have hjle : (j : ℝ) ≤ ((M * (⌈4 * Cr * (Csh * W + 1)⌉₊ + 1) : ℕ) : ℝ) := by
      exact_mod_cast hj
    obtain ⟨r, hrc⟩ : ∃ r : ℕ, (r : ℝ) = (⌈b⌉₊ : ℝ) + b' + 3 + 2 * b' * j :=
      ⟨⌈b⌉₊ + b' + 3 + 2 * b' * j, by push_cast; ring⟩
    have hceil : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    have hj0 : (0 : ℝ) ≤ 2 * b' * j := by positivity
    have hjS : 2 * (b' : ℝ) * j ≤
        2 * b' * ((M * (⌈4 * Cr * (Csh * W + 1)⌉₊ + 1) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hjle (by positivity)
    have hrb : b + b' + 3 ≤ (r : ℝ) := by rw [hrc]; linarith
    have hrle : (r : ℝ) ≤ n := by rw [hrc]; linarith
    have hr₀ : r₀ ≤ (r : ℝ) := by linarith
    have hrn' : r ≤ n := by exact_mod_cast hrle
    have hr₀' : r₀ ≤ (r : ℝ) := hr₀
    rw [← hrc] at hFA ⊢
    exact grid_step hd hCrad hCrad' hCr1 hC₁ hc₁ hCt (by linarith) hbd_le hFanti hF0 (hSh0 r)
      (hsh r (by linarith)) hN1 hL0.le hMx hcb hrb (hrad r hr₀' hrn') hA hFA
  have hstart : F ((⌈b⌉₊ : ℝ) + 3) ≤ C₁ * N * Q := by
    have hceil : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    exact le_trans (hFanti (Set.mem_Ioi.2 hb0) (Set.mem_Ioi.2 (by linarith)) (by linarith)) hFb
  have hmain := halving_const hFanti hF0 hb0 hb'n hΛ hKc1 M hM1 hstart hstep
  have hceil : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
  have hj0 : (0 : ℝ) ≤ 2 * b' * ((M * (⌈4 * Cr * (Csh * W + 1)⌉₊ + 1) : ℕ) : ℝ) := by positivity
  refine le_trans (hFanti (Set.mem_Ioi.2 (by linarith)) (Set.mem_Ioi.2 (by linarith))
    ?_) hmain
  linarith

/-- The exponent of the rate `Q`: both branches are a power `x ^ a` with `0 < a ≤ 1`. -/
private lemma rate_exponent (hd : 2 ≤ d) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∀ x : ℝ,
      (if d = 2 then x ^ ((1 : ℝ) / 2) else x ^ ((d : ℝ) / (2 * d - 1))) = x ^ a := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h2d : 0 < 2 * (d : ℝ) - 1 := by linarith
  by_cases h2 : d = 2
  · exact ⟨1 / 2, by norm_num, by norm_num, fun x => by simp only [h2, if_true]⟩
  · refine ⟨(d : ℝ) / (2 * d - 1), div_pos (by linarith) h2d, ?_, fun x => by
      simp only [if_neg h2]⟩
    rw [div_le_one h2d]
    linarith

/-- For `N, L ≥ 1`, the scale `W = N Q^{1/d}` is at least one. -/
private lemma one_le_scale {N L a : ℝ} (hd : 1 ≤ d) (hN : 1 ≤ N) (hL : 1 ≤ L) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) :
    1 ≤ N * ((L / N) ^ a) ^ ((1 : ℝ) / d) := by
  have hN0 : 0 < N := by linarith
  have hiN : 0 < 1 / N := by positivity
  have hiN1 : 1 / N ≤ 1 := by
    rw [div_le_one hN0]
    exact hN
  have hxle : 1 / N ≤ L / N := div_le_div_of_nonneg_right hL hN0.le
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hQ : 1 / N ≤ (L / N) ^ a := by
    calc 1 / N = (1 / N) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 / N) ^ a := Real.rpow_le_rpow_of_exponent_ge hiN hiN1 ha1
      _ ≤ (L / N) ^ a := by
          exact Real.rpow_le_rpow hiN.le hxle ha0
  have hQd : 1 / N ≤ ((L / N) ^ a) ^ ((1 : ℝ) / d) := by
    have h1d : (1 : ℝ) / d ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hd'
    calc 1 / N = (1 / N) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 / N) ^ ((1 : ℝ) / d) := Real.rpow_le_rpow_of_exponent_ge hiN hiN1 h1d
      _ ≤ ((L / N) ^ a) ^ ((1 : ℝ) / d) := Real.rpow_le_rpow hiN.le hQ (by positivity)
  calc (1 : ℝ) = N * (1 / N) := by field_simp
    _ ≤ N * ((L / N) ^ a) ^ ((1 : ℝ) / d) := mul_le_mul_of_nonneg_left hQd hN0.le

/-- `eq:tailend`: there are `K₀` and `C_t` such that, for all large `n`, the displayed hypotheses
imply `F(b + K₀ W L) ≤ C_t N^{2-d} L`. -/
theorem exists_tailend (hd : 2 ≤ d) {Crad C₁ Csh c₁ c₂ bd r₀ : ℝ} (hCrad : 0 < Crad)
    (hC₁ : 0 < C₁) (hCsh : 0 < Csh) (hc₁ : 0 < c₁) (hbd : 1 ≤ bd) :
    ∃ K₀ Ct : ℝ, 0 < K₀ ∧ 0 < Ct ∧ ∃ n₀ : ℕ, ∀ (X : ℕ → Site d) (n : ℕ) (b : ℝ), n₀ ≤ n →
      let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
      let L : ℝ := Real.log (n + 2)
      let Q : ℝ := if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
      let W : ℝ := N * Q ^ ((1 : ℝ) / d)
      let F : ℝ → ℝ := tail d (cellSet X n)
      c₁ * N ≤ b → b ≤ c₂ * N → (maxLocalTime X n : ℝ) ≤ C₁ * N → F b ≤ C₁ * N * Q →
      (∀ r : ℕ, b + 3 ≤ r → (shellMax X n r : ℝ) ≤ Csh * W) →
      (∀ r : ℕ, r₀ ≤ r → r ≤ n →
        F (r + bd) ≤ Crad * shellMax X n r * (F (r - bd) - F (r + bd)) +
          Crad * (Real.sqrt (maxLocalTime X n * (r : ℝ) ^ (1 - (d : ℝ)) * F (r - bd) * L) +
            (r : ℝ) ^ (1 - (d : ℝ)) * L)) →
        F (b + K₀ * W * L) ≤ Ct * N ^ (2 - (d : ℝ)) * L := by
  obtain ⟨K₀, Ct, hK₀, hCt, hcore⟩ := core_tailend hd (r₀ := r₀) hCrad hC₁ hCsh hc₁ hbd
  obtain ⟨a, ha0, ha1, hQa⟩ := rate_exponent hd
  refine ⟨K₀, Ct, hK₀, hCt, ?_⟩
  have hd1 : 1 ≤ d := by omega
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hp : (0 : ℝ) < 1 / (d + 1) := by positivity
  have hNT := ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (max (max 1 (r₀ / c₁)) (|c₂| + K₀))
  have hQev := (CERW.Support.Main.tendsto_rate_zero hd).eventually (gt_mem_nhds one_pos)
  have hWev :=
    (CERW.Support.Main.tendsto_rate_rpow_mul_log_zero hd).eventually (gt_mem_nhds one_pos)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (hNT.and (hQev.and (hWev.and (Filter.eventually_ge_atTop (1 : ℕ)))))
  refine ⟨n₀, ?_⟩
  intro X n b hn N L Q W F hcb hbc hMx hFb hsh hrad
  obtain ⟨e1, e2, e3, e4⟩ := hn₀ n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast e4
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) e1
  have hN0 : 0 < N := by linarith
  have hNd1 : N ^ (d + 1) = n := by
    have h := Real.rpow_inv_natCast_pow (x := (n : ℝ)) (n := d + 1) hn0 (by omega)
    rw [show ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 by push_cast; ring, ← one_div] at h
    exact h
  have hNd : N ^ d ≤ n := by
    rw [← hNd1]
    exact pow_le_pow_right₀ hN1 (Nat.le_succ d)
  have hcN : r₀ ≤ c₁ * N := by
    have h1 : r₀ / c₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) e1
    rw [div_le_iff₀ hc₁] at h1
    linarith
  have hL1 : 1 ≤ L := by
    show 1 ≤ Real.log (n + 2)
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_three
    linarith
  have hQeq : Q = (L / N) ^ a := hQa _
  have hQ0 : 0 < Q := by
    rw [hQeq]
    exact Real.rpow_pos_of_pos (by positivity) a
  have hQ1 : Q ≤ 1 := le_of_lt e2
  have hW1 : 1 ≤ W := by
    have h := one_le_scale (d := d) (N := N) (L := L) hd1 hN1 hL1 ha0.le ha1
    rw [← hQeq] at h
    exact h
  have hWL : W * L ≤ N := by
    have h : Q ^ ((1 : ℝ) / d) * L ≤ 1 := le_of_lt e3
    calc W * L = N * (Q ^ ((1 : ℝ) / d) * L) := by
          show N * Q ^ ((1 : ℝ) / d) * L = _
          ring
      _ ≤ N * 1 := mul_le_mul_of_nonneg_left h hN0.le
      _ = N := mul_one N
  have hrn : b + K₀ * W * L ≤ n := by
    have hT : |c₂| + K₀ ≤ N := le_trans (le_max_right _ _) e1
    have h1 : b ≤ |c₂| * N :=
      hbc.trans (mul_le_mul_of_nonneg_right (le_abs_self c₂) hN0.le)
    have h2 : K₀ * W * L ≤ K₀ * N := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hWL hK₀.le
    have h3 : N * N ≤ n := by
      rw [← hNd1]
      calc N * N = N ^ 2 := (sq N).symm
        _ ≤ N ^ (d + 1) := pow_le_pow_right₀ hN1 (by omega)
    calc b + K₀ * W * L ≤ |c₂| * N + K₀ * N := add_le_add h1 h2
      _ = (|c₂| + K₀) * N := by ring
      _ ≤ N * N := mul_le_mul_of_nonneg_right hT hN0.le
      _ ≤ n := h3
  exact hcore n N L Q W (maxLocalTime X n) b F (fun r => (shellMax X n r : ℝ))
    (cellSet_tail_antitoneOn (by omega) X n) (fun t => CERW.Support.Geometry.tail_nonneg _ t)
    (fun r => Nat.cast_nonneg _) hN1 hNd hcN rfl hQ0 hQ1 hW1 hrn hcb hMx hFb hsh hrad

end CERW.Support.Coarse
