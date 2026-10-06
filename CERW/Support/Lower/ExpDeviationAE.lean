import CERW.Support.Lower.ExpDeviation

/-!
# Exponential deviations of martingales: the almost sure form

`CERW.Support.Lower.exp_deviation` asks for `S i 0 ω = 0` and `|S i (t + 1) ω - S i t ω| ≤ b` at
every sample point `ω`. Lemma 9.1 (`lem:exp-deviation`) of the paper asks for them almost surely
(a martingale identity holds up to a null set, as does a bound on its increments). The two forms
differ only on a null set, but the restricted theorem cannot be applied to a martingale that
violates the hypotheses on a null set.

This file closes the gap with a transport theorem and applies the restricted theorem.

* `exists_bounded_modification` builds from a process `S` that is a martingale up to time `n`,
  starts at `0` almost surely and has increments bounded by `b` almost surely before time `n`, a
  martingale `S'` with `S' 0 = 0` and increments bounded by `b` everywhere before time `n`, that
  agrees with `S` almost surely at all times `t ≤ n`. The increments of `S'` are the increments of
  `S` clamped to `[-b, b]` while `t < n`, and `0` afterwards.
* `predBracket_congr_ae` says that the predictable bracket up to time `n` depends only on the
  processes up to time `n`, up to a null set.
* `exp_deviation_ae_upTo` is `exp_deviation` for processes that are martingales up to time `n`
  (the source lemma has a filtration `(𝒢_t)_{0 ≤ t ≤ n}`), with the two sure hypotheses
  weakened to `∀ᵐ`. `exp_deviation_ae` is the same statement for martingales indexed by `ℕ`, the
  exact shape of `exp_deviation` with only the two sure hypotheses weakened to `∀ᵐ`: same
  constants `c(c₀, C₀)`, `C(c₀, C₀)`, same quantifier order, same conclusions. The proof applies
  `exp_deviation` to the modifications and moves the brackets and the events back.
-/

universe u

open MeasureTheory ProbabilityTheory Filter

namespace CERW.Support.Lower

section Modification

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Clamp a real number to the interval `[-b, b]`. -/
private noncomputable def clampTo (b x : ℝ) : ℝ := max (-b) (min b x)

private lemma abs_clampTo_le {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : |clampTo b x| ≤ b := by
  rw [abs_le]
  simp only [clampTo]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

private lemma clampTo_eq_self {b x : ℝ} (hx : |x| ≤ b) : clampTo b x = x := by
  rw [abs_le] at hx
  simp only [clampTo]
  rw [min_eq_right hx.2, max_eq_right hx.1]

private lemma continuous_clampTo (b : ℝ) : Continuous (clampTo b) := by
  unfold clampTo
  exact continuous_const.max (continuous_const.min continuous_id)

/-- The `t`-th increment of the modification of `S` with bound `b` and horizon `n`: the increment
`S (t + 1) - S t` clamped to `[-b, b]` while `t < n`, and `0` from time `n` on. -/
private noncomputable def modInc (b : ℝ) (n : ℕ) (S : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if t < n then clampTo b (S (t + 1) ω - S t ω) else 0

/-- The modification of `S`: the sum of its increments, started at `0`. -/
private noncomputable def modif (b : ℝ) (n : ℕ) (S : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ s ∈ Finset.range t, modInc b n S s ω

private lemma modif_zero (b : ℝ) (n : ℕ) (S : ℕ → Ω → ℝ) (ω : Ω) : modif b n S 0 ω = 0 := by
  simp [modif]

private lemma modif_succ_sub (b : ℝ) (n : ℕ) (S : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    modif b n S (t + 1) ω - modif b n S t ω = modInc b n S t ω := by
  simp only [modif, Finset.sum_range_succ]
  ring

private lemma abs_modInc_le {b : ℝ} (hb : 0 ≤ b) (n : ℕ) (S : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    |modInc b n S t ω| ≤ b := by
  unfold modInc
  split_ifs
  · exact abs_clampTo_le hb _
  · simpa using hb

/-- Before time `n`, the modification and the original process agree at a sample point where the
initial value is `0` and the increments are bounded. -/
private lemma modif_eq_of_good {b : ℝ} {n : ℕ} {S : ℕ → Ω → ℝ} {ω : Ω} (h0 : S 0 ω = 0)
    (hinc : ∀ t < n, |S (t + 1) ω - S t ω| ≤ b) : ∀ t, t ≤ n → modif b n S t ω = S t ω := by
  intro t
  induction t with
  | zero => intro _; rw [modif_zero, h0]
  | succ t ih =>
    intro ht
    have htn : t < n := Nat.lt_of_succ_le ht
    have h1 : modif b n S (t + 1) ω = modif b n S t ω + modInc b n S t ω := by
      have := modif_succ_sub b n S t ω
      linarith
    rw [h1, ih htn.le]
    simp only [modInc, if_pos htn]
    rw [clampTo_eq_self (hinc t htn)]
    ring

/-- The `s`-th increment is measurable with respect to `ℱ (s + 1)`, and so with respect to any
later stage, provided `S` is adapted up to time `n`. -/
private lemma stronglyMeasurable_modInc {ℱ : Filtration ℕ m0} {S : ℕ → Ω → ℝ} {n : ℕ}
    (hadp : ∀ t ≤ n, StronglyMeasurable[ℱ t] (S t)) (b : ℝ) {s t : ℕ} (hst : s + 1 ≤ t) :
    StronglyMeasurable[ℱ t] (fun ω => modInc b n S s ω) := by
  by_cases hs : s < n
  · have hfun : (fun ω => modInc b n S s ω) = fun ω => clampTo b (S (s + 1) ω - S s ω) := by
      funext ω
      simp only [modInc, if_pos hs]
    rw [hfun]
    exact (continuous_clampTo b).comp_stronglyMeasurable
      (((hadp (s + 1) hs).mono (ℱ.mono hst)).sub
        ((hadp s hs.le).mono (ℱ.mono (le_trans (Nat.le_succ s) hst))))
  · have hfun : (fun ω => modInc b n S s ω) = fun _ => 0 := by
      funext ω
      simp only [modInc, if_neg hs]
    rw [hfun]
    exact stronglyMeasurable_const

private lemma stronglyAdapted_modif {ℱ : Filtration ℕ m0} {S : ℕ → Ω → ℝ} {n : ℕ}
    (hadp : ∀ t ≤ n, StronglyMeasurable[ℱ t] (S t)) (b : ℝ) :
    StronglyAdapted ℱ (modif b n S) := by
  intro t
  have hfun : StronglyMeasurable[ℱ t] (∑ s ∈ Finset.range t, fun ω => modInc b n S s ω) := by
    refine Finset.stronglyMeasurable_sum (f := fun s (ω : Ω) => modInc b n S s ω)
      (Finset.range t) ?_
    intro s hs
    exact stronglyMeasurable_modInc hadp b (Nat.succ_le_of_lt (Finset.mem_range.mp hs))
  have heq : (∑ s ∈ Finset.range t, fun ω => modInc b n S s ω) = modif b n S t := by
    funext ω
    exact Finset.sum_apply ω (Finset.range t) fun s (ω : Ω) => modInc b n S s ω
  rwa [heq] at hfun

private lemma integrable_modInc {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ m0}
    {S : ℕ → Ω → ℝ} {n : ℕ} (hadp : ∀ t ≤ n, StronglyMeasurable[ℱ t] (S t)) {b : ℝ}
    (hb : 0 ≤ b) (s : ℕ) : Integrable (fun ω => modInc b n S s ω) μ :=
  Integrable.of_bound
    ((stronglyMeasurable_modInc hadp b (le_refl (s + 1))).mono (ℱ.le (s + 1))).aestronglyMeasurable
    b (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using abs_modInc_le hb n S s ω)

/-- **The modification.** A process that is a martingale up to time `n`, starts at `0` and has
increments before time `n` bounded by `b`, all three almost surely, agrees almost surely, at all
times `t ≤ n` at once, with a martingale (for all times) that starts at `0` and has increments
before time `n` bounded by `b` at every sample point. -/
theorem exists_bounded_modification {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ m0}
    {S : ℕ → Ω → ℝ} {b : ℝ} (hb : 0 ≤ b) {n : ℕ}
    (hadp : ∀ t ≤ n, StronglyMeasurable[ℱ t] (S t)) (hint : ∀ t ≤ n, Integrable (S t) μ)
    (hmart : ∀ t < n, μ[S (t + 1) | ℱ t] =ᵐ[μ] S t)
    (h0 : ∀ᵐ ω ∂μ, S 0 ω = 0) (hinc : ∀ t < n, ∀ᵐ ω ∂μ, |S (t + 1) ω - S t ω| ≤ b) :
    ∃ S' : ℕ → Ω → ℝ, Martingale S' ℱ μ ∧ (∀ ω, S' 0 ω = 0) ∧
      (∀ t < n, ∀ ω, |S' (t + 1) ω - S' t ω| ≤ b) ∧ ∀ᵐ ω ∂μ, ∀ t ≤ n, S' t ω = S t ω := by
  have hgood : ∀ᵐ ω ∂μ, ∀ t < n, |S (t + 1) ω - S t ω| ≤ b :=
    ae_all_iff.mpr fun t => by
      by_cases ht : t < n
      · exact (hinc t ht).mono fun ω hω _ => hω
      · exact ae_of_all _ fun ω h => absurd h ht
  have hmod : ∀ t, t < n → (fun ω => modInc b n S t ω) =ᵐ[μ] fun ω => S (t + 1) ω - S t ω := by
    intro t ht
    filter_upwards [hinc t ht] with ω hω
    simp only [modInc, if_pos ht]
    exact clampTo_eq_self hω
  refine ⟨modif b n S, ?_, modif_zero b n S, ?_, ?_⟩
  · refine martingale_of_condExp_sub_eq_zero_nat (stronglyAdapted_modif hadp b)
      (fun t => ?_) (fun t => ?_)
    · exact integrable_finsetSum (Finset.range t) fun s _ => integrable_modInc hadp hb s
    · have hsub : (modif b n S (t + 1) - modif b n S t) = fun ω => modInc b n S t ω := by
        funext ω
        exact modif_succ_sub b n S t ω
      rw [hsub]
      by_cases ht : t < n
      · have hcond : μ[(fun ω => S (t + 1) ω - S t ω) | ℱ t] =ᵐ[μ] 0 := by
          have h1 := condExp_sub (hint (t + 1) ht) (hint t ht.le) (ℱ t)
          have h3 : μ[S t | ℱ t] = S t :=
            condExp_of_stronglyMeasurable (ℱ.le t) (hadp t ht.le) (hint t ht.le)
          filter_upwards [h1, hmart t ht] with ω hω1 hω2
          have h4 : μ[fun ω => S (t + 1) ω - S t ω | ℱ t] ω = μ[S (t + 1) - S t | ℱ t] ω := rfl
          rw [h4, hω1, Pi.sub_apply, hω2, h3]
          simp
        exact (condExp_congr_ae (hmod t ht)).trans hcond
      · have hz : (fun ω => modInc b n S t ω) = 0 := by
          funext ω
          simp only [modInc, if_neg ht, Pi.zero_apply]
        rw [hz, condExp_zero]
  · intro t ht ω
    rw [modif_succ_sub b n S t ω]
    exact abs_modInc_le hb n S t ω
  · filter_upwards [h0, hgood] with ω hω0 hω using modif_eq_of_good hω0 hω

/-- **Bracket transport.** The predictable bracket up to time `n` of two processes depends on the
processes up to time `n` only, up to a null set. -/
theorem predBracket_congr_ae {μ : Measure Ω} {ℱ : Filtration ℕ m0}
    {S S' T T' : ℕ → Ω → ℝ} {n : ℕ} (hS : ∀ᵐ ω ∂μ, ∀ t ≤ n, S' t ω = S t ω)
    (hT : ∀ᵐ ω ∂μ, ∀ t ≤ n, T' t ω = T t ω) :
    CERW.predBracket μ ℱ S' T' n =ᵐ[μ] CERW.predBracket μ ℱ S T n := by
  have hterm : ∀ t ∈ Finset.range n,
      μ[fun ω => (S' (t + 1) ω - S' t ω) * (T' (t + 1) ω - T' t ω) | ℱ t]
        =ᵐ[μ] μ[fun ω => (S (t + 1) ω - S t ω) * (T (t + 1) ω - T t ω) | ℱ t] := by
    intro t ht
    have htn : t + 1 ≤ n := Finset.mem_range.mp ht
    refine condExp_congr_ae ?_
    filter_upwards [hS, hT] with ω h1 h2
    rw [h1 (t + 1) htn, h1 t (Nat.le_of_succ_le htn), h2 (t + 1) htn,
      h2 t (Nat.le_of_succ_le htn)]
  have hall := (eventually_all_finset (Finset.range n)).2 hterm
  filter_upwards [hall] with ω hω
  simp only [CERW.predBracket, Finset.sum_apply]
  exact Finset.sum_congr rfl hω

/-- Probabilities of events defined by almost surely equivalent conditions agree. -/
private lemma measure_setOf_congr {μ : Measure Ω} {p q : Ω → Prop}
    (h : ∀ᵐ ω ∂μ, p ω ↔ q ω) : μ {ω | p ω} = μ {ω | q ω} :=
  measure_congr (h.mono fun _ hω => propext hω)

end Modification

/-- **Lemma 9.1 (`lem:exp-deviation`), almost sure form, for martingales up to time `n`.** The
statement of `exp_deviation`, with the martingale property required only up to time `n` (as for a
filtration `(𝒢_t)_{0 ≤ t ≤ n}`) and the two sure hypotheses `S i 0 ω = 0` and
`|S i (t + 1) ω - S i t ω| ≤ b` weakened to almost sure hypotheses. The constants `c(c₀, C₀)` and
`C(c₀, C₀)`, the order of the quantifiers, the lower tails, the many-site upper tail, the cross
brackets, the window of `β` and the failure terms are those of `exp_deviation`. -/
theorem exp_deviation_ae_upTo :
    ∀ c₀ C₀ : ℝ, 0 < c₀ → c₀ ≤ C₀ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ℱ : Filtration ℕ m0) (m n : ℕ), 0 < m → 0 < n →
      ∀ b δ α : ℝ, 0 < b → 0 ≤ δ → 0 ≤ α → α ≤ 1 →
      ∀ S : Fin m → ℕ → Ω → ℝ,
        (∀ i, ∀ t ≤ n, StronglyMeasurable[ℱ t] (S i t)) → (∀ i, ∀ t ≤ n, Integrable (S i t) μ) →
        (∀ i, ∀ t < n, μ[S i (t + 1) | ℱ t] =ᵐ[μ] S i t) → (∀ i, ∀ᵐ ω ∂μ, S i 0 ω = 0) →
        (∀ i, ∀ t < n, ∀ᵐ ω ∂μ, |S i (t + 1) ω - S i t ω| ≤ b) →
      ∀ E : Set Ω, MeasurableSet E → 1 - α ≤ (μ E).toReal →
        (∀ i, ∀ᵐ ω ∂μ, ω ∈ E →
          c₀ ≤ CERW.predBracket μ ℱ (S i) (S i) n ω ∧
            CERW.predBracket μ ℱ (S i) (S i) n ω ≤ C₀) →
      ∀ β : ℝ, C ≤ β → β * b ≤ c →
        (∀ i, Real.exp (-(C * β ^ 2)) / 4 - α ≤ (μ {ω | c * β ≤ S i n ω}).toReal ∧
          Real.exp (-(C * β ^ 2)) / 4 - α ≤ (μ {ω | S i n ω ≤ -(c * β)}).toReal) ∧
        ((∀ i j, i ≠ j → ∀ᵐ ω ∂μ, ω ∈ E → |CERW.predBracket μ ℱ (S i) (S j) n ω| ≤ δ) →
          β ^ 2 * δ + β ^ 3 * b ≤ 1 →
          (μ {ω | ∀ i, S i n ω < c * β}).toReal
            ≤ C * ((m : ℝ)⁻¹ * Real.exp (C * β ^ 2) + β ^ 2 * δ + β ^ 3 * b
              + Real.exp (C * β ^ 2) * Real.sqrt α)) := by
  intro c₀ C₀ hc₀ hcC
  obtain ⟨c, C, hc, hC, H⟩ := exp_deviation.{u} c₀ C₀ hc₀ hcC
  refine ⟨c, C, hc, hC, ?_⟩
  intro Ω _ μ _ ℱ m n hm hn b δ α hb hδ hα hα1 S hadp hint hmart hS0 hinc E hE hEα hbr β hβC hβb
  choose S' hS'mart hS'0 hS'inc hS'eq using
    fun i => exists_bounded_modification hb.le (hadp i) (hint i) (hmart i) (hS0 i) (hinc i)
  have hbrEq : ∀ i j, CERW.predBracket μ ℱ (S' i) (S' j) n
      =ᵐ[μ] CERW.predBracket μ ℱ (S i) (S j) n :=
    fun i j => predBracket_congr_ae (hS'eq i) (hS'eq j)
  have hSn : ∀ i, ∀ᵐ ω ∂μ, S' i n ω = S i n ω :=
    fun i => (hS'eq i).mono fun ω h => h n le_rfl
  have hbr' : ∀ i, ∀ᵐ ω ∂μ, ω ∈ E →
      c₀ ≤ CERW.predBracket μ ℱ (S' i) (S' i) n ω ∧
        CERW.predBracket μ ℱ (S' i) (S' i) n ω ≤ C₀ := by
    intro i
    filter_upwards [hbr i, hbrEq i i] with ω h1 h2 hω
    rw [h2]
    exact h1 hω
  have key := H μ ℱ m n hm hn b δ α hb hδ hα hα1 S' hS'mart hS'0 hS'inc E hE hEα hbr' β hβC hβb
  refine ⟨fun i => ?_, fun hcr hsmall => ?_⟩
  · have h1 : μ {ω | c * β ≤ S i n ω} = μ {ω | c * β ≤ S' i n ω} :=
      measure_setOf_congr ((hSn i).mono fun ω hω => by rw [hω])
    have h2 : μ {ω | S i n ω ≤ -(c * β)} = μ {ω | S' i n ω ≤ -(c * β)} :=
      measure_setOf_congr ((hSn i).mono fun ω hω => by rw [hω])
    rw [h1, h2]
    exact key.1 i
  · have hcr' : ∀ i j, i ≠ j → ∀ᵐ ω ∂μ, ω ∈ E →
        |CERW.predBracket μ ℱ (S' i) (S' j) n ω| ≤ δ := by
      intro i j hij
      filter_upwards [hcr i j hij, hbrEq i j] with ω h1 h2 hω
      rw [h2]
      exact h1 hω
    have hall : ∀ᵐ ω ∂μ, ∀ i, S' i n ω = S i n ω := ae_all_iff.mpr hSn
    have hset : μ {ω | ∀ i, S i n ω < c * β} = μ {ω | ∀ i, S' i n ω < c * β} :=
      measure_setOf_congr (hall.mono fun ω hω => by simp only [hω])
    rw [hset]
    exact key.2 hcr' hsmall

/-- **Lemma 9.1 (`lem:exp-deviation`), almost sure form.** The statement of `exp_deviation`, with
the two sure hypotheses `S i 0 ω = 0` and `|S i (t + 1) ω - S i t ω| ≤ b` weakened to almost sure
hypotheses. The constants `c(c₀, C₀)` and `C(c₀, C₀)`, the order of the quantifiers, the lower
tails, the many-site upper tail, the cross brackets, the window of `β` and the failure terms are
those of `exp_deviation`. -/
theorem exp_deviation_ae :
    ∀ c₀ C₀ : ℝ, 0 < c₀ → c₀ ≤ C₀ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ℱ : Filtration ℕ m0) (m n : ℕ), 0 < m → 0 < n →
      ∀ b δ α : ℝ, 0 < b → 0 ≤ δ → 0 ≤ α → α ≤ 1 →
      ∀ S : Fin m → ℕ → Ω → ℝ, (∀ i, Martingale (S i) ℱ μ) → (∀ i, ∀ᵐ ω ∂μ, S i 0 ω = 0) →
        (∀ i, ∀ t < n, ∀ᵐ ω ∂μ, |S i (t + 1) ω - S i t ω| ≤ b) →
      ∀ E : Set Ω, MeasurableSet E → 1 - α ≤ (μ E).toReal →
        (∀ i, ∀ᵐ ω ∂μ, ω ∈ E →
          c₀ ≤ CERW.predBracket μ ℱ (S i) (S i) n ω ∧
            CERW.predBracket μ ℱ (S i) (S i) n ω ≤ C₀) →
      ∀ β : ℝ, C ≤ β → β * b ≤ c →
        (∀ i, Real.exp (-(C * β ^ 2)) / 4 - α ≤ (μ {ω | c * β ≤ S i n ω}).toReal ∧
          Real.exp (-(C * β ^ 2)) / 4 - α ≤ (μ {ω | S i n ω ≤ -(c * β)}).toReal) ∧
        ((∀ i j, i ≠ j → ∀ᵐ ω ∂μ, ω ∈ E → |CERW.predBracket μ ℱ (S i) (S j) n ω| ≤ δ) →
          β ^ 2 * δ + β ^ 3 * b ≤ 1 →
          (μ {ω | ∀ i, S i n ω < c * β}).toReal
            ≤ C * ((m : ℝ)⁻¹ * Real.exp (C * β ^ 2) + β ^ 2 * δ + β ^ 3 * b
              + Real.exp (C * β ^ 2) * Real.sqrt α)) := by
  intro c₀ C₀ hc₀ hcC
  obtain ⟨c, C, hc, hC, H⟩ := exp_deviation_ae_upTo.{u} c₀ C₀ hc₀ hcC
  refine ⟨c, C, hc, hC, ?_⟩
  intro Ω _ μ _ ℱ m n hm hn b δ α hb hδ hα hα1 S hS hS0 hinc E hE hEα hbr β hβC hβb
  exact H μ ℱ m n hm hn b δ α hb hδ hα hα1 S (fun i t _ => (hS i).stronglyAdapted t)
    (fun i t _ => (hS i).integrable t) (fun i t _ => (hS i).condExp_ae_eq (Nat.le_succ t)) hS0 hinc
    E hE hEα hbr β hβC hβb

end CERW.Support.Lower
