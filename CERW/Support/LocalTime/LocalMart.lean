import CERW.Support.LocalTime.Bracket
import CERW.Generic.Martingale.Dyadic
import CERW.Generic.Martingale.Clamp
import CERW.Support.Law.ScaleArith

/-!
# The local martingales at individual targets

`eq:localmart`: with probability at least `1 - Cn^{-p}`, simultaneously for all lattice targets
`|y| ≤ 3n`, `|𝓜^y_n| ≤ C (√(B_y L) + L)`, where `B_y = Σ_{j<n} (1 + |X_j - y|)^{2-2d}`. The bracket
of `𝓜^y` is at most `C_g² B_y` (`eq:bracket`), and surely at most `C_g² n`. Freedman's inequality
at dyadic brackets, and a union bound over the targets, give the claim.
-/

namespace CERW.Support.LocalTime

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law

variable {d : ℕ}

/-- A power of `1 + ρ` with nonpositive exponent is at most `1`. -/
private lemma rpow_one_add_le_one {ρ z : ℝ} (hρ : 0 ≤ ρ) (hz : z ≤ 0) : (1 + ρ) ^ z ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hz

/-- The predictable bracket `C_g² Σ_{j<t} (1 + |X_j - y|)^{2-2d}` of the translated Dynkin
martingale `𝓜^y`. -/
private noncomputable def bracket {Ω : Type*} (Cg : ℝ) (y : Site d) (X : ℕ → Ω → Site d)
    (t : ℕ) (ω : Ω) : ℝ :=
  Cg ^ 2 * ∑ j ∈ range t, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))

/-- The bracket starts at `0`. -/
private lemma bracket_zero {Ω : Type*} (Cg : ℝ) (y : Site d) (X : ℕ → Ω → Site d) (ω : Ω) :
    bracket Cg y X 0 ω = 0 := by
  simp [bracket]

/-- The increment of the bracket is `C_g² (1 + |X_j - y|)^{2-2d}`. -/
private lemma bracket_succ_sub {Ω : Type*} (Cg : ℝ) (y : Site d) (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : bracket Cg y X (j + 1) ω - bracket Cg y X j ω =
      Cg ^ 2 * (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ)) := by
  simp only [bracket, sum_range_succ]
  ring

/-- The bracket is nondecreasing. -/
private lemma bracket_mono {Ω : Type*} (Cg : ℝ) (y : Site d) (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : bracket Cg y X j ω ≤ bracket Cg y X (j + 1) ω := by
  have h := bracket_succ_sub Cg y X j ω
  have h0 : 0 ≤ Cg ^ 2 * (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ)) :=
    mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (by linarith [euclidNorm_nonneg (X j ω - y)]) _)
  linarith

/-- The bracket increment over `[s, t)` is `C_g²` times the sum over `s ≤ j < t`. -/
private lemma bracket_sub {Ω : Type*} (Cg : ℝ) (y : Site d) (X : ℕ → Ω → Site d) {s t : ℕ}
    (hst : s ≤ t) (ω : Ω) : bracket Cg y X t ω - bracket Cg y X s ω =
      Cg ^ 2 * ∑ j ∈ Ico s t, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ)) := by
  rw [bracket, bracket, ← mul_sub, ← sum_Ico_eq_sub _ hst]

/-- The bracket increment over `s < t ≤ n` is at most `C_g² n`, as `1 ≤ d`. -/
private lemma bracket_sub_le (hd : 1 ≤ d) {Ω : Type*} (Cg : ℝ) (y : Site d)
    (X : ℕ → Ω → Site d) {s t n : ℕ} (hst : s ≤ t) (htn : t ≤ n) (ω : Ω) :
    bracket Cg y X t ω - bracket Cg y X s ω ≤ Cg ^ 2 * n := by
  rw [bracket_sub Cg y X hst]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  calc ∑ j ∈ Ico s t, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))
      ≤ ∑ _j ∈ Ico s t, (1 : ℝ) := by
        refine sum_le_sum fun j _ => rpow_one_add_le_one (euclidNorm_nonneg _) ?_
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
    _ = ((t - s : ℕ) : ℝ) := by simp
    _ ≤ n := by
        have : t - s ≤ n := by omega
        exact_mod_cast this

/-- The bracket at time `j + 1` is a function of the past path up to time `j`. -/
private lemma stronglyMeasurable_bracket_succ {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ n, Measurable (X n)) (Cg : ℝ) (y : Site d) (j : ℕ) :
    StronglyMeasurable[pathFiltration hX j] (bracket Cg y X (j + 1)) := by
  have h := stronglyMeasurable_comp_pastPath hX j
    (fun q => Cg ^ 2 * ∑ i ∈ range (j + 1),
      (1 + euclidNorm (extendPath q i - y)) ^ (2 - 2 * (d : ℝ)))
  have heq : bracket Cg y X (j + 1) = fun ω => Cg ^ 2 * ∑ i ∈ range (j + 1),
      (1 + euclidNorm (extendPath (pastPath X j ω) i - y)) ^ (2 - 2 * (d : ℝ)) := by
    funext ω
    simp only [bracket]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [extendPath_pastPath X (Nat.lt_succ_iff.mp (mem_range.mp hi)) ω]
  rw [heq]
  exact h

/-- The translated Dynkin martingale `𝓜^y` agrees almost surely with a martingale whose increments
are at most `2 C_g + 1` everywhere and whose conditional variances are at most the bracket
increments. -/
private lemma exists_clamped_translate (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (y : Site d) :
    ∃ M : ℕ → Ω → ℝ, Martingale M (pathFiltration hX.measurable) μ ∧
      (∀ i ω, |M (i + 1) ω - M i ω| ≤ 2 * Cg + 1) ∧
      (∀ j, μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | pathFiltration hX.measurable j] ≤ᵐ[μ]
        fun ω => bracket Cg y X (j + 1) ω - bracket Cg y X j ω) ∧
      ∀ᵐ ω ∂μ, ∀ i, M i ω = dynkin ε (fun z => b (z - y)) X i ω := by
  have hCg := cg_nonneg hd hgrad
  have hmart := martingale_dynkin hd hε hεd hX (fun z => b (z - y))
  have hinc : ∀ i, ∀ᵐ ω ∂μ, |dynkin ε (fun z => b (z - y)) X (i + 1) ω -
      dynkin ε (fun z => b (z - y)) X i ω| ≤ 2 * Cg + 1 := fun i =>
    (ae_abs_dynkin_translate_succ_sub_le hd hε hεd hX hgrad y).mono fun ω hω => by
      have h1 : (1 + euclidNorm (X i ω - y)) ^ (1 - (d : ℝ)) ≤ 1 :=
        rpow_one_add_le_one (euclidNorm_nonneg _) (by
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd
          linarith)
      have h2 := hω i
      nlinarith
  obtain ⟨M, hM, hbd, -, hae⟩ := CERW.Generic.Martingale.exists_martingale_clamp hmart
    (b := 2 * Cg + 1) (by linarith) hinc
  refine ⟨M, hM, hbd, fun j => ?_, hae⟩
  have hsq : (fun ω => (M (j + 1) ω - M j ω) ^ 2) =ᵐ[μ]
      fun ω => (dynkin ε (fun z => b (z - y)) X (j + 1) ω -
        dynkin ε (fun z => b (z - y)) X j ω) ^ 2 := by
    filter_upwards [hae] with ω hω
    rw [hω, hω]
  refine (condExp_congr_ae hsq).trans_le ?_
  filter_upwards [condExp_sq_dynkin_translate_le hd hε hεd hX hgrad y j] with ω hω
  rw [bracket_succ_sub]
  exact hω

/-- The deterministic step: the Freedman threshold `c (√(max (C_g² B) 1 · L) + (2C_g+1) L)` is at
most `C (√(B L) + L)`. -/
private lemma threshold_arith {Cg c : ℝ} (hCg : 0 ≤ Cg) (hc : 1 ≤ c) :
    ∃ Cdet : ℝ, 0 < Cdet ∧ ∀ S L : ℝ, 0 ≤ S → 1 ≤ L →
      c * (Real.sqrt (max (Cg ^ 2 * S) 1 * L) + (2 * Cg + 1) * L) ≤
        Cdet * (Real.sqrt (S * L) + L) := by
  refine ⟨c * (3 * Cg + 2), by positivity, ?_⟩
  intro S L hS hL
  have hc0 : 0 ≤ c := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hmax : max (Cg ^ 2 * S) 1 ≤ Cg ^ 2 * S + 1 :=
    max_le (by linarith) (by nlinarith [sq_nonneg Cg, hS])
  have hsqrt : Real.sqrt (max (Cg ^ 2 * S) 1 * L) ≤ Cg * Real.sqrt (S * L) + Real.sqrt L := by
    calc Real.sqrt (max (Cg ^ 2 * S) 1 * L)
        ≤ Real.sqrt ((Cg ^ 2 * S + 1) * L) :=
            Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hmax hL0)
      _ = Real.sqrt (Cg ^ 2 * (S * L) + L) := by
            congr 1
            ring
      _ ≤ Real.sqrt (Cg ^ 2 * (S * L)) + Real.sqrt L :=
            sqrt_add_le_add (by positivity) hL0
      _ = Cg * Real.sqrt (S * L) + Real.sqrt L := by
            rw [Real.sqrt_mul (sq_nonneg Cg), Real.sqrt_sq hCg]
  have hsqrtL : Real.sqrt L ≤ L := by
    rw [Real.sqrt_le_left hL0]
    nlinarith
  have hg : 0 ≤ Real.sqrt (S * L) := Real.sqrt_nonneg _
  have hsum : Cg * Real.sqrt (S * L) + Real.sqrt L + (2 * Cg + 1) * L ≤
      (3 * Cg + 2) * (Real.sqrt (S * L) + L) := by
    have h1 : Cg * Real.sqrt (S * L) ≤ (3 * Cg + 2) * Real.sqrt (S * L) :=
      mul_le_mul_of_nonneg_right (by linarith) hg
    have h2 : Real.sqrt L ≤ (Cg + 1) * L :=
      hsqrtL.trans (le_mul_of_one_le_left hL0 (by linarith))
    nlinarith [h1, h2]
  calc c * (Real.sqrt (max (Cg ^ 2 * S) 1 * L) + (2 * Cg + 1) * L)
      ≤ c * (Cg * Real.sqrt (S * L) + Real.sqrt L + (2 * Cg + 1) * L) := by
          refine mul_le_mul_of_nonneg_left ?_ hc0
          linarith [hsqrt]
    _ ≤ c * ((3 * Cg + 2) * (Real.sqrt (S * L) + L)) :=
          mul_le_mul_of_nonneg_left hsum hc0
    _ = c * (3 * Cg + 2) * (Real.sqrt (S * L) + L) := by ring

/-- One target: Freedman's inequality at dyadic brackets, followed by the deterministic step,
bounds the probability that `|𝓜^y_n|` exceeds the threshold. -/
private lemma exists_event_bound (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ Cdet : ℝ, 0 < Cdet ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d}, IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n → ∀ y : Site d,
        μ {ω | Cdet * (Real.sqrt ((∑ j ∈ range n,
            (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) *
              Real.log (n + 2)) + Real.log (n + 2)) <
            |dynkin ε (fun z => b (z - y)) X n ω|} ≤
          ENNReal.ofReal (((Nat.clog 2 ⌈max (Cg ^ 2 * n) 1⌉₊ : ℕ) + 1) *
            (2 * Real.exp (-(K * Real.log (n + 2))))) := by
  have hd1 : 1 ≤ d := by omega
  have hCg := cg_nonneg hd1 hgrad
  obtain ⟨c, hc1, hc⟩ := CERW.Generic.Martingale.exists_dyadic_bound hK
  obtain ⟨Cdet, hCdet0, hCdet⟩ := threshold_arith hCg hc1
  refine ⟨Cdet, hCdet0, ?_⟩
  intro Ω _ μ _ X hX n hn y
  obtain ⟨M, hM, hbd, hvar, hae⟩ := exists_clamped_translate hd1 hε hεd hX hgrad y
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  have hL1 : 1 ≤ Real.log ((n : ℝ) + 2) := by
    have h4 : Real.log 4 ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith)
    have h5 : (1 : ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith [this]
    linarith
  have hW : (1 : ℝ) ≤ max (Cg ^ 2 * n) 1 := le_max_right _ _
  have hVW : ∀ ω, bracket Cg y X (0 + n) ω - bracket Cg y X 0 ω ≤ max (Cg ^ 2 * n) 1 := by
    intro ω
    rw [zero_add]
    exact (bracket_sub_le hd1 Cg y X (Nat.zero_le n) le_rfl ω).trans (le_max_left _ _)
  have hdy := hc hM (V := bracket Cg y X) (stronglyMeasurable_bracket_succ hX.measurable Cg y)
    (bracket_zero Cg y X) (bracket_mono Cg y X) hvar (b := 2 * Cg + 1) (by linarith) 0 n
    (fun i _ _ ω => hbd i ω) hW hL hVW
  refine le_trans (measure_mono_ae ?_) hdy
  filter_upwards [hae] with ω hω hE
  change _ < _ at hE
  change _ < _
  rw [zero_add, bracket_zero, sub_zero, hω n, hω 0, dynkin_zero, sub_zero]
  have hS0 : 0 ≤ ∑ j ∈ range n, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ)) :=
    sum_nonneg fun j _ => Real.rpow_nonneg (by linarith [euclidNorm_nonneg (X j ω - y)]) _
  have hthr := hCdet _ _ hS0 hL1
  simp only [bracket]
  exact lt_of_le_of_lt hthr hE

/-- The arithmetic of the union bound: `(7(n+1))^D · (G + 3)(n + 1) · 2 e^{-(p + D + 2)L}` is at
most `(7^D (G + 3) 2^{D+2}) n^{-p}`. -/
private lemma union_bound_arith {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 1 ≤ n) (D : ℕ) {G : ℝ}
    (hG : 0 ≤ G) :
    (7 * ((n : ℝ) + 1)) ^ D * (((G + 3) * ((n : ℝ) + 1)) *
      (2 * Real.exp (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))) ≤
    (7 ^ D * (G + 3) * 2 ^ (D + 3)) * (n : ℝ) ^ (-p) := by
  have h1 := CERW.Generic.Martingale.two_mul_exp_neg_mul_log_le
    (K := p + ((D + 2 : ℕ) : ℝ)) (by positivity) hn
  have h2 := CERW.Generic.Martingale.pow_mul_rpow_neg_le hn (D + 2) p
  have h3 : (0 : ℝ) ≤ 7 ^ D * (G + 3) * ((n : ℝ) + 1) ^ (D + 2) := by positivity
  calc (7 * ((n : ℝ) + 1)) ^ D * (((G + 3) * ((n : ℝ) + 1)) *
        (2 * Real.exp (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))))
      = (7 ^ D * (G + 3) * ((n : ℝ) + 1) ^ (D + 1)) *
          (2 * Real.exp (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) := by
        rw [mul_pow]
        ring
    _ ≤ (7 ^ D * (G + 3) * ((n : ℝ) + 1) ^ (D + 2)) *
          (2 * Real.exp (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) := by
        have hpow : ((n : ℝ) + 1) ^ (D + 1) ≤ ((n : ℝ) + 1) ^ (D + 2) :=
          pow_le_pow_right₀
            (show (1 : ℝ) ≤ (n : ℝ) + 1 by
              have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
              linarith) (by omega)
        have hC : (0 : ℝ) ≤ 7 ^ D * (G + 3) := by positivity
        have he : (0 : ℝ) ≤ 2 * Real.exp
            (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))) := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) he
    _ ≤ (7 ^ D * (G + 3) * ((n : ℝ) + 1) ^ (D + 2)) *
          (2 * (n : ℝ) ^ (-(p + ((D + 2 : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left h1 h3
    _ = 2 * (7 ^ D * (G + 3)) * (((n : ℝ) + 1) ^ (D + 2) *
          (n : ℝ) ^ (-(p + ((D + 2 : ℕ) : ℝ)))) := by ring
    _ ≤ 2 * (7 ^ D * (G + 3)) * (2 ^ (D + 2) * (n : ℝ) ^ (-p)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (7 ^ D * (G + 3) * 2 ^ (D + 3)) * (n : ℝ) ^ (-p) := by ring

/-- `eq:localmart`: under the one-step bound, with probability at least `1 - Cn^{-p}`,
`|𝓜^y_n| ≤ C (√(B_y L) + L)` for all lattice `|y| ≤ 3n`. -/
theorem exists_local_mart (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      {X : ℕ → Ω → Site d}, IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ∃ y : Site d, euclidNorm y ≤ 3 * n ∧
          C * (Real.sqrt ((∑ j ∈ range n, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) *
              Real.log (n + 2)) + Real.log (n + 2)) <
            |dynkin ε (fun z => b (z - y)) X n ω|} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨Cdet, hCdet0, hCdet⟩ := exists_event_bound hd hε hεd hgrad
    (K := p + ((d + 2 : ℕ) : ℝ)) (by positivity)
  refine ⟨Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 3), by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  set Y : Finset (Site d) := ballFinset d (3 * (n : ℝ)) with hY
  set B : Site d → Set Ω := fun y =>
    {ω | Cdet * (Real.sqrt ((∑ j ∈ range n, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) *
        Real.log (n + 2)) + Real.log (n + 2)) <
      |dynkin ε (fun z => b (z - y)) X n ω|} with hB
  have hbound : ∀ y ∈ Y, μ (B y) ≤ ENNReal.ofReal (((Cg ^ 2 + 3) * ((n : ℝ) + 1)) *
      (2 * Real.exp (-((p + ((d + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))) := by
    intro y _
    refine (hCdet hX n hn y).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (clog_ceil_add_one_le Cg n) (by positivity)
  have hYcard : (Y.card : ℝ) ≤ (7 * ((n : ℝ) + 1)) ^ d :=
    (card_ballFinset_le d (R := 3 * (n : ℝ)) (by positivity)).trans
      (pow_le_pow_left₀ (by positivity) (by linarith) d)
  set a : ℝ := ((Cg ^ 2 + 3) * ((n : ℝ) + 1)) *
    (2 * Real.exp (-((p + ((d + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) with ha
  have ha0 : 0 ≤ a := by positivity
  refine (measure_mono (t := ⋃ y ∈ Y, B y) ?_).trans ?_
  · rintro ω ⟨y, hy3, hlt⟩
    simp only [Set.mem_iUnion]
    refine ⟨y, ?_, ?_⟩
    · rw [hY, mem_ballFinset_iff]
      exact hy3
    · have hlog : 0 ≤ Real.log (n + 2) := by
        apply Real.log_nonneg
        exact_mod_cast (by omega : 1 ≤ n + 2)
      have hterm : 0 ≤ Real.sqrt ((∑ j ∈ range n,
          (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) *
          Real.log (n + 2)) + Real.log (n + 2) :=
        add_nonneg (Real.sqrt_nonneg _) hlog
      have hconst : 0 ≤ 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 3) := by positivity
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hconst) hterm) hlt
  · calc μ (⋃ y ∈ Y, B y) ≤ ∑ y ∈ Y, μ (B y) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _y ∈ Y, ENNReal.ofReal a := sum_le_sum hbound
      _ = ENNReal.ofReal ((Y.card : ℝ) * a) := by
          simp only [sum_const, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul (p := (Y.card : ℝ)) (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 3)) *
            (n : ℝ) ^ (-p)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (Y.card : ℝ) * a ≤ (7 * ((n : ℝ) + 1)) ^ d * a :=
            mul_le_mul_of_nonneg_right hYcard ha0
          have h2 := union_bound_arith hp.le (by omega : 1 ≤ n) d
            (G := Cg ^ 2) (sq_nonneg Cg)
          have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
          nlinarith [mul_nonneg hCdet0.le h3]

end CERW.Support.LocalTime
