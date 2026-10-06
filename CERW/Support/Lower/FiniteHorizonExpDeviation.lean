import CERW.Support.Lower.ExpDeviationAE

/-!
# The exponential deviation lemma for a finite filtration

`lem:exp-deviation` is stated for martingales with respect to a common filtration
`(𝒢_t)_{0 ≤ t ≤ n}`. A filtration in Mathlib is indexed by an ordered type, so a finite filtration
is a `Filtration (Fin (n + 1)) m0`, while the predictable bracket `CERW.predBracket` and the
statement `CERW.Support.Lower.exp_deviation_ae_upTo` use filtrations indexed by `ℕ`. This file
proves that the two readings agree.

* `extendFiltration` and `extendProcess` extend a filtration and a process indexed by
  `Fin (n + 1)` to `ℕ` by `𝒢_t := 𝒢_{min t n}` and `S_t := S_{min t n}`. The extension of a
  martingale is a martingale (`martingale_extendProcess`), and its predictable bracket up to time
  `n` is the sum over `t < n` of the conditional covariances of the finite process
  (`predBracket_extend`).
* `restrictFiltration` restricts a filtration indexed by `ℕ` to the stages `0, …, n`. A process
  that is adapted, integrable and has conditional mean zero increments up to time `n` restricts to
  a martingale for it (`martingale_restrict`), with the same bracket (`predBracket_restrict`).
* `exp_deviation_finite` is the lemma for a filtration indexed by `Fin (n + 1)`, with the bracket
  written as the sum of the conditional covariances over `t < n`.
-/

universe u

open MeasureTheory ProbabilityTheory

namespace CERW.Support.Lower

section Cap

/-- The stage `min t n`, as an element of `Fin (n + 1)`. -/
def capIndex (n t : ℕ) : Fin (n + 1) := ⟨min t n, Nat.lt_succ_of_le (min_le_right t n)⟩

/-- `capIndex n` is monotone. -/
lemma capIndex_mono (n : ℕ) : Monotone (capIndex n) :=
  fun _ _ h => Fin.mk_le_mk.2 (min_le_min_right n h)

/-- The stage `0` is `0`. -/
lemma capIndex_zero (n : ℕ) : capIndex n 0 = 0 :=
  Fin.ext (Nat.zero_min n)

/-- The stage `n` is the last element. -/
lemma capIndex_self (n : ℕ) : capIndex n n = Fin.last n :=
  Fin.ext (min_self n)

/-- The stage `t < n` is `t`, viewed as an element of `Fin (n + 1)`. -/
lemma capIndex_castSucc {n : ℕ} (t : Fin n) : capIndex n t = t.castSucc :=
  Fin.ext (min_eq_left (Nat.le_of_lt t.isLt))

/-- The stage `t + 1 ≤ n` is `t + 1`, viewed as an element of `Fin (n + 1)`. -/
lemma capIndex_succ {n : ℕ} (t : Fin n) : capIndex n (t + 1) = t.succ :=
  Fin.ext (min_eq_left (Nat.succ_le_of_lt t.isLt))

end Cap

section Extension

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- A filtration indexed by `Fin (n + 1)`, extended to `ℕ` by `𝒢_t := 𝒢_{min t n}`. -/
def extendFiltration {n : ℕ} (𝒢 : Filtration (Fin (n + 1)) m0) : Filtration ℕ m0 where
  seq t := 𝒢 (capIndex n t)
  mono' _ _ h := 𝒢.mono (capIndex_mono n h)
  le' t := 𝒢.le (capIndex n t)

/-- A process indexed by `Fin (n + 1)`, extended to `ℕ` by `S_t := S_{min t n}`. -/
def extendProcess {n : ℕ} (S : Fin (n + 1) → Ω → ℝ) (t : ℕ) : Ω → ℝ := S (capIndex n t)

/-- The extension of a martingale indexed by `Fin (n + 1)` is a martingale for the extended
filtration. -/
theorem martingale_extendProcess {μ : Measure Ω} {n : ℕ} {𝒢 : Filtration (Fin (n + 1)) m0}
    {S : Fin (n + 1) → Ω → ℝ} (hS : Martingale S 𝒢 μ) :
    Martingale (extendProcess S) (extendFiltration 𝒢) μ :=
  ⟨fun t => hS.stronglyAdapted (capIndex n t),
    fun _ _ hst => hS.condExp_ae_eq (capIndex_mono n hst)⟩

/-- The predictable bracket up to time `n` of the extensions of two processes indexed by
`Fin (n + 1)` is the sum over `t < n` of the conditional covariances of their increments. -/
theorem predBracket_extend (μ : Measure Ω) {n : ℕ} (𝒢 : Filtration (Fin (n + 1)) m0)
    (S T : Fin (n + 1) → Ω → ℝ) :
    CERW.predBracket μ (extendFiltration 𝒢) (extendProcess S) (extendProcess T) n
      = ∑ t : Fin n, μ[fun ω => (S t.succ ω - S t.castSucc ω) * (T t.succ ω - T t.castSucc ω)
          | 𝒢 t.castSucc] := by
  unfold CERW.predBracket
  rw [← Fin.sum_univ_eq_sum_range (fun t => μ[fun ω =>
    (extendProcess S (t + 1) ω - extendProcess S t ω) *
      (extendProcess T (t + 1) ω - extendProcess T t ω) | extendFiltration 𝒢 t]) n]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [extendProcess, extendFiltration, capIndex_succ, capIndex_castSucc]

end Extension

section Restriction

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- A filtration indexed by `ℕ`, restricted to the stages `0, …, n`. -/
def restrictFiltration (ℱ : Filtration ℕ m0) (n : ℕ) : Filtration (Fin (n + 1)) m0 where
  seq k := ℱ k
  mono' _ _ h := ℱ.mono h
  le' k := ℱ.le k

/-- A process that is adapted, integrable and has conditional mean zero increments up to time
`n` restricts to a martingale for the restricted filtration. -/
theorem martingale_restrict {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ m0} {S : ℕ → Ω → ℝ} {n : ℕ}
    (hadp : ∀ t ≤ n, StronglyMeasurable[ℱ t] (S t)) (hint : ∀ t ≤ n, Integrable (S t) μ)
    (hmart : ∀ t < n, μ[S (t + 1) | ℱ t] =ᵐ[μ] S t) :
    Martingale (fun k : Fin (n + 1) => S k) (restrictFiltration ℱ n) μ := by
  have key : ∀ d i : ℕ, i + d ≤ n → μ[S (i + d) | ℱ i] =ᵐ[μ] S i := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have h : μ[S i | ℱ i] = S i :=
        condExp_of_stronglyMeasurable (ℱ.le i) (hadp i (by omega)) (hint i (by omega))
      filter_upwards with ω
      rw [Nat.add_zero, h]
    | succ d ih =>
      intro i hi
      have h1 : μ[μ[S (i + d + 1) | ℱ (i + d)] | ℱ i] =ᵐ[μ] μ[S (i + d + 1) | ℱ i] :=
        condExp_condExp_of_le (ℱ.mono (Nat.le_add_right i d)) (ℱ.le (i + d))
      have h2 : μ[μ[S (i + d + 1) | ℱ (i + d)] | ℱ i] =ᵐ[μ] μ[S (i + d) | ℱ i] :=
        condExp_congr_ae (hmart (i + d) (by omega))
      exact h1.symm.trans (h2.trans (ih i (by omega)))
  refine ⟨fun k => hadp k (Nat.lt_succ_iff.1 k.isLt), fun i j hij => ?_⟩
  obtain ⟨d, hd⟩ : ∃ d, (j : ℕ) = i + d := ⟨j - i, by have := Fin.le_def.1 hij; omega⟩
  have h := key d i (by have := j.isLt; omega)
  rw [← hd] at h
  exact h

/-- The predictable bracket up to time `n` of two processes indexed by `ℕ` is the sum over
`t < n` of the conditional covariances of their increments for the restricted filtration. -/
theorem predBracket_restrict (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S T : ℕ → Ω → ℝ) (n : ℕ) :
    CERW.predBracket μ ℱ S T n
      = ∑ t : Fin n, μ[fun ω => (S (t.succ : Fin (n + 1)) ω - S (t.castSucc : Fin (n + 1)) ω) *
          (T (t.succ : Fin (n + 1)) ω - T (t.castSucc : Fin (n + 1)) ω)
          | restrictFiltration ℱ n t.castSucc] := by
  unfold CERW.predBracket
  rw [← Fin.sum_univ_eq_sum_range (fun t => μ[fun ω =>
    (S (t + 1) ω - S t ω) * (T (t + 1) ω - T t ω) | ℱ t]) n]
  rfl

end Restriction

/-- **Lemma 9.1 (`lem:exp-deviation`) for a finite filtration.** The statement of
`exp_deviation_ae_upTo` for martingales with respect to a filtration `(𝒢_t)_{0 ≤ t ≤ n}` indexed
by `Fin (n + 1)`: the martingale property holds on the whole index set, the initial value and the
increments are bounded almost surely, and `⟨S^i, S^j⟩_n` is the sum over `t < n` of the
conditional covariances `E((S^i_{t+1} - S^i_t)(S^j_{t+1} - S^j_t) | 𝒢_t)`. -/
theorem exp_deviation_finite :
    ∀ c₀ C₀ : ℝ, 0 < c₀ → c₀ ≤ C₀ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (m n : ℕ), 0 < m → 0 < n → ∀ 𝒢 : Filtration (Fin (n + 1)) m0,
      ∀ b δ α : ℝ, 0 < b → 0 ≤ δ → 0 ≤ α → α ≤ 1 →
      ∀ S : Fin m → Fin (n + 1) → Ω → ℝ, (∀ i, Martingale (S i) 𝒢 μ) →
        (∀ i, ∀ᵐ ω ∂μ, S i 0 ω = 0) →
        (∀ i, ∀ t : Fin n, ∀ᵐ ω ∂μ, |S i t.succ ω - S i t.castSucc ω| ≤ b) →
      ∀ E : Set Ω, MeasurableSet E → 1 - α ≤ (μ E).toReal →
        (∀ i, ∀ᵐ ω ∂μ, ω ∈ E →
          c₀ ≤ (∑ t : Fin n, μ[fun ω => (S i t.succ ω - S i t.castSucc ω) *
              (S i t.succ ω - S i t.castSucc ω) | 𝒢 t.castSucc]) ω ∧
            (∑ t : Fin n, μ[fun ω => (S i t.succ ω - S i t.castSucc ω) *
              (S i t.succ ω - S i t.castSucc ω) | 𝒢 t.castSucc]) ω ≤ C₀) →
      ∀ β : ℝ, C ≤ β → β * b ≤ c →
        (∀ i, Real.exp (-(C * β ^ 2)) / 4 - α ≤ (μ {ω | c * β ≤ S i (Fin.last n) ω}).toReal ∧
          Real.exp (-(C * β ^ 2)) / 4 - α ≤ (μ {ω | S i (Fin.last n) ω ≤ -(c * β)}).toReal) ∧
        ((∀ i j, i ≠ j → ∀ᵐ ω ∂μ, ω ∈ E →
            |(∑ t : Fin n, μ[fun ω => (S i t.succ ω - S i t.castSucc ω) *
              (S j t.succ ω - S j t.castSucc ω) | 𝒢 t.castSucc]) ω| ≤ δ) →
          β ^ 2 * δ + β ^ 3 * b ≤ 1 →
          (μ {ω | ∀ i, S i (Fin.last n) ω < c * β}).toReal
            ≤ C * ((m : ℝ)⁻¹ * Real.exp (C * β ^ 2) + β ^ 2 * δ + β ^ 3 * b
              + Real.exp (C * β ^ 2) * Real.sqrt α)) := by
  intro c₀ C₀ hc₀ hcC
  obtain ⟨c, C, hc, hC, H⟩ := exp_deviation_ae.{u} c₀ C₀ hc₀ hcC
  refine ⟨c, C, hc, hC, ?_⟩
  intro Ω _ μ _ m n hm hn 𝒢 b δ α hb hδ hα hα1 S hS hS0 hinc E hE hEα hbr β hβC hβb
  have hlast : ∀ i ω, extendProcess (S i) n ω = S i (Fin.last n) ω := fun i ω => by
    simp only [extendProcess, capIndex_self]
  have hbr' : ∀ i, ∀ᵐ ω ∂μ, ω ∈ E →
      c₀ ≤ CERW.predBracket μ (extendFiltration 𝒢) (extendProcess (S i)) (extendProcess (S i)) n ω ∧
        CERW.predBracket μ (extendFiltration 𝒢) (extendProcess (S i)) (extendProcess (S i)) n ω
          ≤ C₀ := by
    intro i
    filter_upwards [hbr i] with ω h hω
    rw [predBracket_extend]
    exact h hω
  have key := H μ (extendFiltration 𝒢) m n hm hn b δ α hb hδ hα hα1 (fun i => extendProcess (S i))
    (fun i => martingale_extendProcess (hS i))
    (fun i => by
      filter_upwards [hS0 i] with ω h
      simpa only [extendProcess, capIndex_zero] using h)
    (fun i t ht => by
      filter_upwards [hinc i ⟨t, ht⟩] with ω h
      have h1 : capIndex n (t + 1) = (⟨t, ht⟩ : Fin n).succ := capIndex_succ ⟨t, ht⟩
      have h2 : capIndex n t = (⟨t, ht⟩ : Fin n).castSucc := capIndex_castSucc ⟨t, ht⟩
      simp only [extendProcess, h1, h2]
      exact h)
    E hE hEα hbr' β hβC hβb
  simp only [hlast] at key
  refine ⟨key.1, fun hcr hsmall => key.2 (fun i j hij => ?_) hsmall⟩
  filter_upwards [hcr i j hij] with ω h hω
  rw [predBracket_extend]
  exact h hω

end CERW.Support.Lower
