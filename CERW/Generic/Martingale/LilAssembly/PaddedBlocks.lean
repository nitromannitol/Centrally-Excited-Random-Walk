import CERW.Generic.Martingale.LilAssembly.PaddedConstruction

/-!
# The block fields of the padded data

After the start time, where the padded bracket at the next time is at least one, the increment of
the padded process is bounded by the gate level times the scale of the bracket, at every point,
and the bracket jumps by at most the square of that, almost surely. While the gate is open the
padded bracket is the bracket `pathBracket` and the ratio is at most the gate level, and once it
has closed the increment is a sign and the jump is `1`.
-/

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.LilLower
open CERW.Generic.Martingale.CLT (pathBracket)

variable {Ω : Type*} {Ξ : Type*} {m0 : MeasurableSpace Ω} {mΞ : MeasurableSpace Ξ}

/-- The iterated logarithm `log log (P ∨ e^e)` is at least one. -/
private lemma one_le_log_log_max (P : ℝ) :
    1 ≤ Real.log (Real.log (max P (Real.exp (Real.exp 1)))) := by
  have h0 : 0 < max P (Real.exp (Real.exp 1)) :=
    lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  have h1 : Real.exp 1 ≤ Real.log (max P (Real.exp (Real.exp 1))) :=
    (Real.le_log_iff_exp_le h0).2 (le_max_right _ _)
  exact (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) h1)).2 h1

/-- A number `Bv` whose ratio `Bv √L / √P` is at most `εg` is at most `εg √(P / L)`. -/
private lemma le_mul_sqrt_of_ratio_le {P Bv εg L : ℝ} (hP : 0 < P) (hL : 0 < L)
    (h : Bv * Real.sqrt L / Real.sqrt P ≤ εg) : Bv ≤ εg * Real.sqrt (P / L) := by
  have hsP : 0 < Real.sqrt P := Real.sqrt_pos.2 hP
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  rw [div_le_iff₀ hsP] at h
  rw [Real.sqrt_div hP.le, ← mul_div_assoc, le_div_iff₀ hsL]
  exact h

/-- If the ratio `Bv √L / √P` is at most `εg`, then `Bv ∨ 0` is at most one or `εg √(P / L)`. -/
private lemma max_le_of_ratio_le {P Bv εg L : ℝ} (hP : 0 < P) (hL : 0 < L)
    (h : Bv * Real.sqrt L / Real.sqrt P ≤ εg) : max Bv 0 ≤ max 1 (εg * Real.sqrt (P / L)) := by
  rcases le_or_gt Bv 0 with hB | hB
  · rw [max_eq_right hB]
    exact le_max_of_le_left zero_le_one
  · rw [max_eq_left hB.le]
    exact le_max_of_le_right (le_mul_sqrt_of_ratio_le hP hL h)

/-- If the ratio `Bv √L / √P` is at most `εg`, then `(Bv ∨ 0) ^ 2` is at most `εg ^ 2 * P / L`. -/
private lemma sq_max_le_of_ratio_le {P Bv εg L : ℝ} (hP : 0 < P) (hL : 0 < L)
    (h : Bv * Real.sqrt L / Real.sqrt P ≤ εg) : (max Bv 0) ^ 2 ≤ εg ^ 2 * P / L := by
  rcases le_or_gt Bv 0 with hB | hB
  · rw [max_eq_right hB, zero_pow two_ne_zero]
    positivity
  · rw [max_eq_left hB.le]
    calc Bv ^ 2 ≤ (εg * Real.sqrt (P / L)) ^ 2 :=
          pow_le_pow_left₀ hB.le (le_mul_sqrt_of_ratio_le hP hL h) 2
      _ = εg ^ 2 * P / L := by
          rw [mul_pow, Real.sq_sqrt (div_nonneg hP.le hL.le), mul_div_assoc]

/-- If the gate is open at time `t`, it is open at every earlier time. -/
private lemma padGate_eq_one_of_le (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ)
    (εg : ℝ) (N : ℕ) {ω : Ω} {j t : ℕ} (hjt : j ≤ t) (h : padGate μ ℱ S B εg N t ω = 1) :
    padGate μ ℱ S B εg N j ω = 1 :=
  (levelGate_eq_one_iff _ _ _ _ _).2 fun i hi hij =>
    (levelGate_eq_one_iff _ _ _ _ _).1 h i hi (hij.trans hjt)

/-- If the gate is open at time `t`, the padded bracket at time `t + 1` is the bracket. -/
private lemma padBracket_eq_pathBracket_of_gate (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (S B : ℕ → Ω → ℝ) (εg : ℝ) (N : ℕ) {ω : Ω} {t : ℕ}
    (h : padGate μ ℱ S B εg N t ω = 1) :
    paddedBracket (clipVar μ ℱ S) (padGate μ ℱ S B εg N) (t + 1) ω =
      pathBracket μ ℱ S (t + 1) ω :=
  paddedBracket_eq_of_gate fun _ hj =>
    padGate_eq_one_of_le μ ℱ S B εg N (Nat.lt_succ_iff.1 hj) h

/-- If the gate is open at time `t ≥ N`, the ratio at time `t` is at most the level. -/
private lemma gateRatio_le_of_gate (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ)
    (εg : ℝ) (N : ℕ) {ω : Ω} {t : ℕ} (hNt : N ≤ t) (h : padGate μ ℱ S B εg N t ω = 1) :
    gateRatio μ ℱ S B t ω ≤ εg :=
  (levelGate_eq_one_iff _ _ _ _ _).1 h t hNt le_rfl

/-- The increment of the padded process. -/
private lemma padded_sub_eq (S G : ℕ → Ω → ℝ) (ε : ℕ → Ξ → ℝ) (n : ℕ) (z : Ω × Ξ) :
    padded S G ε (n + 1) z - padded S G ε n z =
      G n z.1 * (S (n + 1) z.1 - S n z.1) + (1 - G n z.1) * ε (n + 1) z.2 := by
  show padded S G ε n z + G n z.1 * (S (n + 1) z.1 - S n z.1) + (1 - G n z.1) * ε (n + 1) z.2 -
    padded S G ε n z = _
  ring

/-- The increment of the padded process is bounded by the gate level times the scale of the
bracket, after the start time. -/
theorem padData_blockInc
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (ℱ : Filtration ℕ m0) {𝒦 : ℕ → MeasurableSpace Ξ} {ε : ℕ → Ξ → ℝ}
    (hε : SignSequence ν 𝒦 ε) {S B : ℕ → Ω → ℝ} (hS : SureData μ ℱ S B) (εg : ℝ)
    (N : ℕ) :
    ∀ (t : ℕ) (z : Ω × Ξ), N ≤ t → 1 ≤ padVar (Ξ := Ξ) μ ℱ S B εg N (t + 1) z →
      |(padProc μ ℱ S B εg N ε) (t + 1) z - (padProc μ ℱ S B εg N ε) t z| ≤
        max 1 (εg * Real.sqrt (padVar (Ξ := Ξ) μ ℱ S B εg N (t + 1) z /
          Real.log (Real.log (max (padVar (Ξ := Ξ) μ ℱ S B εg N (t + 1) z)
            (Real.exp (Real.exp 1)))))) := by
  intro t z hNt hV
  have hinc := padded_sub_eq S (padGate μ ℱ S B εg N) ε t z
  show |padded S (padGate μ ℱ S B εg N) ε (t + 1) z - padded S (padGate μ ℱ S B εg N) ε t z|
    ≤ _
  rw [hinc]
  rcases levelGate_eq_zero_or_one (gateRatio μ ℱ S B) εg N t z.1 with h0 | h1
  · have h0' : padGate μ ℱ S B εg N t z.1 = 0 := h0
    rw [h0', zero_mul, zero_add, sub_zero, one_mul]
    exact le_max_of_le_left ((sq_le_one_iff_abs_le_one _).1 (hε.sq_eq_one (t + 1) z.2).le)
  · have h1' : padGate μ ℱ S B εg N t z.1 = 1 := h1
    have hpb := padBracket_eq_pathBracket_of_gate μ ℱ S B εg N h1'
    have hP : 1 ≤ pathBracket μ ℱ S (t + 1) z.1 := by
      rw [← hpb]
      exact hV
    have hK := gateRatio_le_of_gate μ ℱ S B εg N hNt h1'
    have hbd := max_le_of_ratio_le (L := Real.log (Real.log (max (pathBracket μ ℱ S (t + 1) z.1)
      (Real.exp (Real.exp 1))))) (lt_of_lt_of_le zero_lt_one hP)
      (lt_of_lt_of_le zero_lt_one (one_le_log_log_max _)) hK
    rw [h1', one_mul, sub_self, zero_mul, add_zero]
    refine (hS.bInc t z.1).trans ?_
    change _ ≤ max 1 (εg * Real.sqrt (paddedBracket (clipVar μ ℱ S) (padGate μ ℱ S B εg N)
      (t + 1) z.1 / Real.log (Real.log (max (paddedBracket (clipVar μ ℱ S)
      (padGate μ ℱ S B εg N) (t + 1) z.1) (Real.exp (Real.exp 1))))))
    rw [hpb]
    exact hbd

/-- The padded bracket is nonnegative along a path with nonnegative `c` and a gate with values
`0` and `1`. -/
private lemma paddedBracket_nonneg_of_gate {c G : ℕ → Ω → ℝ} {ω : Ω} (hc : ∀ j, 0 ≤ c j ω)
    (hG : ∀ j, G j ω = 0 ∨ G j ω = 1) (n : ℕ) : 0 ≤ paddedBracket c G n ω :=
  Finset.sum_nonneg fun j _ => by
    have h0 := hc j
    rcases hG j with h1 | h1 <;> rw [h1] <;> linarith

/-- The conditional variance of an increment is at most the square of the bound, almost surely,
at a fixed time. -/
private lemma ae_clipVar_le_sq (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {S B : ℕ → Ω → ℝ} (hS : SureData μ ℱ S B) (t : ℕ) :
    ∀ᵐ ω ∂μ, clipVar μ ℱ S t ω ≤ (max (B (t + 1) ω) 0) ^ 2 := by
  set f : Ω → ℝ := fun ω => (S (t + 1) ω - S t ω) ^ 2 with hf
  set g : Ω → ℝ := fun ω => (max (B (t + 1) ω) 0) ^ 2 with hg
  have hfint : Integrable f μ := ((hS.memLp (t + 1)).sub (hS.memLp t)).integrable_sq
  have hgm : StronglyMeasurable[ℱ t] g :=
    ((continuous_id.max continuous_const).comp_stronglyMeasurable (hS.bPred t)).pow 2
  have hfg : ∀ ω, f ω ≤ g ω := fun ω =>
    sq_le_sq' (abs_le.1 (hS.bInc t ω)).1 (abs_le.1 (hS.bInc t ω)).2
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => sq_nonneg _
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂μ, g ω ≤ n → (μ[f | ℱ t]) ω ≤ g ω := by
    intro n
    have hA : MeasurableSet[ℱ t] {ω | g ω ≤ n} := measurableSet_le hgm.measurable measurable_const
    set A : Set Ω := {ω | g ω ≤ n} with hAdef
    have hind : StronglyMeasurable[ℱ t] (A.indicator g) := hgm.indicator hA
    have hgint : Integrable (A.indicator g) μ :=
      Integrable.of_bound (hind.mono (ℱ.le t)).aestronglyMeasurable n (ae_of_all _ fun ω => by
        by_cases hω : ω ∈ A
        · rw [Set.indicator_of_mem hω, Real.norm_eq_abs, abs_of_nonneg (hg0 ω)]
          exact hω
        · rw [Set.indicator_of_notMem hω]
          simp)
    have h1 := condExp_indicator hfint hA
    have h2 : μ[A.indicator f | ℱ t] ≤ᵐ[μ] μ[A.indicator g | ℱ t] :=
      condExp_mono (hfint.indicator (ℱ.le t _ hA)) hgint
        (ae_of_all _ fun ω => Set.indicator_le_indicator (hfg ω))
    have h3 : μ[A.indicator g | ℱ t] = A.indicator g :=
      condExp_of_stronglyMeasurable (ℱ.le t) hind hgint
    filter_upwards [h1, h2] with ω hω1 hω2 hωA
    rw [h3] at hω2
    have h4 := hω1.symm.le.trans hω2
    rwa [Set.indicator_of_mem (show ω ∈ A from hωA),
      Set.indicator_of_mem (show ω ∈ A from hωA)] at h4
  have hall : ∀ᵐ ω ∂μ, ∀ n : ℕ, g ω ≤ n → (μ[f | ℱ t]) ω ≤ g ω := ae_all_iff.2 hn
  filter_upwards [hall] with ω hω
  exact max_le (hω ⌈g ω⌉₊ (Nat.le_ceil _)) (hg0 ω)

/-- At a point where the conditional variances are at most the squares of the bound, the padded
bracket jumps by at most the square of the gate level times the scale of the bracket, after the
start time. -/
private lemma padBracket_jump_le_of_clipVar_le (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (S B : ℕ → Ω → ℝ) (εg : ℝ) (N : ℕ) {ω : Ω}
    (hc : ∀ t, clipVar μ ℱ S t ω ≤ (max (B (t + 1) ω) 0) ^ 2) {t : ℕ} (hNt : N ≤ t) :
    paddedBracket (clipVar μ ℱ S) (padGate μ ℱ S B εg N) (t + 1) ω -
        paddedBracket (clipVar μ ℱ S) (padGate μ ℱ S B εg N) t ω ≤
      max 1 (εg ^ 2 * paddedBracket (clipVar μ ℱ S) (padGate μ ℱ S B εg N) (t + 1) ω /
        Real.log (Real.log (max (paddedBracket (clipVar μ ℱ S) (padGate μ ℱ S B εg N) (t + 1) ω)
          (Real.exp (Real.exp 1))))) := by
  have hc0 : ∀ j, 0 ≤ clipVar μ ℱ S j ω := fun j => le_max_right _ _
  have hG01 : ∀ j, padGate μ ℱ S B εg N j ω = 0 ∨ padGate μ ℱ S B εg N j ω = 1 :=
    fun j => levelGate_eq_zero_or_one _ _ _ _ _
  have hdiff := paddedBracket_succ_sub (clipVar μ ℱ S) (padGate μ ℱ S B εg N) t ω
  have hP0 := paddedBracket_nonneg_of_gate hc0 hG01 t
  by_cases hV : paddedBracket (clipVar μ ℱ S) (padGate μ ℱ S B εg N) (t + 1) ω < 1
  · refine le_max_of_le_left ?_
    linarith
  · rw [not_lt] at hV
    rcases hG01 t with h0 | h1
    · rw [h0] at hdiff
      refine le_max_of_le_left ?_
      linarith
    · have hpb := padBracket_eq_pathBracket_of_gate μ ℱ S B εg N h1
      have hP : 1 ≤ pathBracket μ ℱ S (t + 1) ω := by
        rw [← hpb]
        exact hV
      have hK := gateRatio_le_of_gate μ ℱ S B εg N hNt h1
      have hsq := sq_max_le_of_ratio_le (L := Real.log (Real.log (max (pathBracket μ ℱ S (t + 1) ω)
        (Real.exp (Real.exp 1))))) (lt_of_lt_of_le zero_lt_one hP)
        (lt_of_lt_of_le zero_lt_one (one_le_log_log_max _)) hK
      refine le_max_of_le_right ?_
      rw [hpb]
      rw [h1] at hdiff
      have h2 : clipVar μ ℱ S t ω ≤ _ := (hc t).trans hsq
      linarith

/-- The bracket of the padded process jumps by at most the square of that, after the start time,
almost surely. -/
theorem padData_jump
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (ℱ : Filtration ℕ m0) {S B : ℕ → Ω → ℝ} (hS : SureData μ ℱ S B) (εg : ℝ) (N : ℕ) :
    ∀ᵐ z ∂(μ.prod ν), ∀ t, N ≤ t →
      padVar (Ξ := Ξ) μ ℱ S B εg N (t + 1) z - padVar (Ξ := Ξ) μ ℱ S B εg N t z ≤
        max 1 (εg ^ 2 * padVar (Ξ := Ξ) μ ℱ S B εg N (t + 1) z /
          Real.log (Real.log (max (padVar (Ξ := Ξ) μ ℱ S B εg N (t + 1) z)
            (Real.exp (Real.exp 1))))) := by
  have hall : ∀ᵐ ω ∂μ, ∀ t, clipVar μ ℱ S t ω ≤ (max (B (t + 1) ω) 0) ^ 2 :=
    ae_all_iff.2 (ae_clipVar_le_sq μ ℱ hS)
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hall] with z hz t hNt
  exact padBracket_jump_le_of_clipVar_le μ ℱ S B εg N hz hNt

end CERW.Generic.Martingale.LilAssembly
