import CERW.Generic.Martingale.LilLower.ProdCondExp
import CERW.Generic.Martingale.LilLower.SignSequence

/-!
# Padding a martingale with independent signs where its increments are cut off

A martingale `S` on `(Ω, μ)` is cut off by a predictable `{0, 1}`-valued gate `G`: its increment at
time `j` is kept when `G j = 1`. Where the gate is zero, the increment is replaced by an adapted
sign `ε (j + 1)` from an independent coin space `(Ξ, ν)`, which has conditional variance one. The
padded process is a square-integrable martingale for the filtration that joins `ℱ` with the coin
filtration, its conditional second moment of the increment is `G j` times that of `S` plus
`1 - G j`, and it agrees with `S ∘ fst` wherever the gate is open.
-/

namespace CERW.Generic.Martingale.LilLower

open MeasureTheory

section Padding

variable {Ω : Type*} {Ξ : Type*}

/-- A function of the second coordinate whose integral vanishes over every set of a sub-σ-algebra
of the second factor has vanishing integral over every set of the join of a sub-σ-algebra of the
first factor with that sub-σ-algebra. -/
private lemma setIntegral_comp_snd_joinSigma_eq_zero {𝒢 : MeasurableSpace Ω}
    {m0 : MeasurableSpace Ω} {ℋ : MeasurableSpace Ξ} {mΞ : MeasurableSpace Ξ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (h𝒢 : 𝒢 ≤ m0) (hℋ : ℋ ≤ mΞ) {H : Ξ → ℝ} (hH : Integrable H ν)
    (h0 : ∀ B, MeasurableSet[ℋ] B → ∫ y in B, H y ∂ν = 0) :
    ∀ s, MeasurableSet[joinSigma 𝒢 ℋ] s → ∫ z in s, H z.2 ∂(μ.prod ν) = 0 := by
  have hH' : Integrable (fun z : Ω × Ξ => H z.2) (μ.prod ν) := hH.comp_snd μ
  have hJ : joinSigma 𝒢 ℋ ≤ @Prod.instMeasurableSpace Ω Ξ m0 mΞ := joinSigma_le h𝒢 hℋ
  have htot : ∫ z, H z.2 ∂(μ.prod ν) = 0 := by
    have h1 : ∫ y, H y ∂ν = 0 := by simpa using h0 Set.univ (@MeasurableSet.univ _ ℋ)
    rw [integral_fun_snd, h1, smul_zero]
  intro s hs
  refine @MeasurableSpace.induction_on_inter (Ω × Ξ) (joinSigma 𝒢 ℋ)
    (fun s _ => ∫ z in s, H z.2 ∂(μ.prod ν) = 0)
    (Set.image2 (· ×ˢ ·) {s | MeasurableSet[𝒢] s} {t | MeasurableSet[ℋ] t})
    (@generateFrom_prod Ω Ξ 𝒢 ℋ).symm (@isPiSystem_prod Ω Ξ 𝒢 ℋ) ?_ ?_ ?_ ?_ s hs
  · simp
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    have h := setIntegral_prod_mul (μ := μ) (ν := ν) (fun _ => (1 : ℝ)) H A B
    simp only [one_mul] at h
    rw [h, h0 B hB, mul_zero]
  · intro t htm ih
    rw [setIntegral_compl (hJ _ htm) hH', ih, htot, sub_zero]
  · intro g hdisj hgm ih
    rw [integral_iUnion (fun i => hJ _ (hgm i)) hdisj hH'.integrableOn]
    simp [ih]

/-- Conditioning a function of the second coordinate on the join of a sub-σ-algebra of the first
factor and a sub-σ-algebra of the second factor only uses the second sub-σ-algebra. -/
theorem condExp_comp_snd_joinSigma {𝒢 : MeasurableSpace Ω} {m0 : MeasurableSpace Ω}
    {ℋ : MeasurableSpace Ξ} {mΞ : MeasurableSpace Ξ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (h𝒢 : 𝒢 ≤ m0) (hℋ : ℋ ≤ mΞ) {g : Ξ → ℝ}
    (hg : Integrable g ν) :
    (μ.prod ν)[fun z => g z.2 | joinSigma 𝒢 ℋ] =ᵐ[μ.prod ν] fun z => (ν[g | ℋ]) z.2 := by
  have hJ : joinSigma 𝒢 ℋ ≤ @Prod.instMeasurableSpace Ω Ξ m0 mΞ := joinSigma_le h𝒢 hℋ
  have hg_int : Integrable (fun z : Ω × Ξ => (ν[g | ℋ]) z.2) (μ.prod ν) :=
    integrable_condExp.comp_snd μ
  have hsnd : @Measurable _ _ (joinSigma 𝒢 ℋ) ℋ Prod.snd := Measurable.of_comap_le le_sup_right
  refine (ae_eq_condExp_of_forall_setIntegral_eq hJ (hg.comp_snd μ)
    (fun s _ _ => hg_int.integrableOn) (fun s hs _ => ?_)
    (stronglyMeasurable_condExp.comp_measurable hsnd).aestronglyMeasurable).symm
  have h := setIntegral_comp_snd_joinSigma_eq_zero μ ν h𝒢 hℋ
    (H := fun y => g y - (ν[g | ℋ]) y) (hg.sub integrable_condExp)
    (fun B hB => by
      rw [integral_sub hg.integrableOn integrable_condExp.integrableOn,
        setIntegral_condExp hℋ hg hB, sub_self]) s hs
  rw [integral_sub (hg.comp_snd μ).integrableOn hg_int.integrableOn, sub_eq_zero] at h
  exact h.symm

/-- A function of the first coordinate that is measurable for a sub-σ-algebra of the first factor
is measurable for the join of that sub-σ-algebra with any sub-σ-algebra of the second factor. -/
private lemma stronglyMeasurable_comp_fst_joinSigma {𝒢 : MeasurableSpace Ω}
    {ℋ : MeasurableSpace Ξ} {f : Ω → ℝ} (hf : StronglyMeasurable[𝒢] f) :
    StronglyMeasurable[joinSigma 𝒢 ℋ] (fun z : Ω × Ξ => f z.1) := by
  have hfst : @Measurable _ _ (joinSigma 𝒢 ℋ) 𝒢 Prod.fst := Measurable.of_comap_le le_sup_left
  exact hf.comp_measurable hfst

/-- A function of the second coordinate that is measurable for a sub-σ-algebra of the second
factor is measurable for the join of any sub-σ-algebra of the first factor with that
sub-σ-algebra. -/
private lemma stronglyMeasurable_comp_snd_joinSigma {𝒢 : MeasurableSpace Ω}
    {ℋ : MeasurableSpace Ξ} {g : Ξ → ℝ} (hg : StronglyMeasurable[ℋ] g) :
    StronglyMeasurable[joinSigma 𝒢 ℋ] (fun z : Ω × Ξ => g z.2) := by
  have hsnd : @Measurable _ _ (joinSigma 𝒢 ℋ) ℋ Prod.snd := Measurable.of_comap_le le_sup_right
  exact hg.comp_measurable hsnd

/-- A bounded weight that is measurable for a sub-σ-algebra of the first factor comes out of the
conditional expectation of a function of the first coordinate on the join. -/
private lemma condExp_mul_comp_fst_joinSigma {𝒢 : MeasurableSpace Ω} {m0 : MeasurableSpace Ω}
    {ℋ : MeasurableSpace Ξ} {mΞ : MeasurableSpace Ξ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (h𝒢 : 𝒢 ≤ m0) (hℋ : ℋ ≤ mΞ) {w f : Ω → ℝ}
    (hw : StronglyMeasurable[𝒢] w) (hw1 : ∀ ω, ‖w ω‖ ≤ 1) (hf : Integrable f μ) :
    (μ.prod ν)[fun z => w z.1 * f z.1 | joinSigma 𝒢 ℋ] =ᵐ[μ.prod ν]
      fun z => w z.1 * (μ[f | 𝒢]) z.1 := by
  have hJ : joinSigma 𝒢 ℋ ≤ @Prod.instMeasurableSpace Ω Ξ m0 mΞ := joinSigma_le h𝒢 hℋ
  have h1 := condExp_stronglyMeasurable_mul_of_bound hJ
    (stronglyMeasurable_comp_fst_joinSigma (ℋ := ℋ) hw) (hf.comp_fst ν) 1
    (ae_of_all _ fun z => hw1 z.1)
  have h2 := condExp_comp_fst_joinSigma μ ν h𝒢 hℋ hf
  filter_upwards [h1, h2] with z hz1 hz2
  exact hz1.trans (congrArg (fun t => w z.1 * t) hz2)

/-- A bounded weight that is measurable for a sub-σ-algebra of the first factor comes out of the
conditional expectation of a function of the second coordinate on the join. -/
private lemma condExp_mul_comp_snd_joinSigma {𝒢 : MeasurableSpace Ω} {m0 : MeasurableSpace Ω}
    {ℋ : MeasurableSpace Ξ} {mΞ : MeasurableSpace Ξ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (h𝒢 : 𝒢 ≤ m0) (hℋ : ℋ ≤ mΞ) {w : Ω → ℝ}
    {g : Ξ → ℝ} (hw : StronglyMeasurable[𝒢] w) (hw1 : ∀ ω, ‖w ω‖ ≤ 1) (hg : Integrable g ν) :
    (μ.prod ν)[fun z => w z.1 * g z.2 | joinSigma 𝒢 ℋ] =ᵐ[μ.prod ν]
      fun z => w z.1 * (ν[g | ℋ]) z.2 := by
  have hJ : joinSigma 𝒢 ℋ ≤ @Prod.instMeasurableSpace Ω Ξ m0 mΞ := joinSigma_le h𝒢 hℋ
  have h1 := condExp_stronglyMeasurable_mul_of_bound hJ
    (stronglyMeasurable_comp_fst_joinSigma (ℋ := ℋ) hw) (hg.comp_snd μ) 1
    (ae_of_all _ fun z => hw1 z.1)
  have h2 := condExp_comp_snd_joinSigma μ ν h𝒢 hℋ hg
  filter_upwards [h1, h2] with z hz1 hz2
  exact hz1.trans (congrArg (fun t => w z.1 * t) hz2)

/-- The martingale `S` with the increment at time `j` kept when `G j = 1` and replaced by the sign
`ε (j + 1)` when `G j = 0`, on the product of the two spaces. -/
noncomputable def padded (S : ℕ → Ω → ℝ) (G : ℕ → Ω → ℝ) (ε : ℕ → Ξ → ℝ) :
    ℕ → Ω × Ξ → ℝ
  | 0 => fun z => S 0 z.1
  | j + 1 => fun z => padded S G ε j z + G j z.1 * (S (j + 1) z.1 - S j z.1) +
      (1 - G j z.1) * ε (j + 1) z.2

/-- The recursion step of the padded process. -/
private lemma padded_succ (S : ℕ → Ω → ℝ) (G : ℕ → Ω → ℝ) (ε : ℕ → Ξ → ℝ) (j : ℕ) :
    padded S G ε (j + 1) = fun z => padded S G ε j z + G j z.1 * (S (j + 1) z.1 - S j z.1) +
      (1 - G j z.1) * ε (j + 1) z.2 := rfl

/-- Where the gate is open at every time before `n`, the padded process is `S`. -/
theorem padded_eq_of_gate (S : ℕ → Ω → ℝ) (G : ℕ → Ω → ℝ) (ε : ℕ → Ξ → ℝ) (n : ℕ) (z : Ω × Ξ)
    (hG : ∀ j < n, G j z.1 = 1) : padded S G ε n z = S n z.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h0 : G n z.1 = 1 := hG n (Nat.lt_succ_self n)
    have h1 := ih fun j hj => hG j (Nat.lt_succ_of_lt hj)
    rw [padded_succ]
    dsimp only
    rw [h1, h0]
    ring

variable {m0 : MeasurableSpace Ω} {mΞ : MeasurableSpace Ξ}

/-- The gate and one minus the gate have absolute value at most one. -/
private lemma norm_gate_le_one {G : ℕ → Ω → ℝ} (hG01 : ∀ j ω, G j ω = 0 ∨ G j ω = 1) (j : ℕ)
    (ω : Ω) : ‖G j ω‖ ≤ 1 ∧ ‖1 - G j ω‖ ≤ 1 := by
  rcases hG01 j ω with h | h <;> simp [h]

/-- The signs of a sign sequence have absolute value at most one. -/
private lemma norm_sign_le_one {𝒦 : ℕ → MeasurableSpace Ξ} {ε : ℕ → Ξ → ℝ} {ν : Measure Ξ}
    (hε : SignSequence ν 𝒦 ε) (j : ℕ) (ξ : Ξ) : ‖ε j ξ‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  exact (sq_le_one_iff_abs_le_one _).1 (hε.sq_eq_one j ξ).le

/-- Each sign `ε (j + 1)` is square integrable. -/
private lemma memLp_sign_succ (ν : Measure Ξ) [IsProbabilityMeasure ν]
    {𝒦 : ℕ → MeasurableSpace Ξ} {ε : ℕ → Ξ → ℝ} (hε : SignSequence ν 𝒦 ε) (j : ℕ) :
    MemLp (ε (j + 1)) 2 ν :=
  MemLp.of_bound ((hε.measurable j).mono (hε.le _)).aestronglyMeasurable 1
    (ae_of_all _ fun ξ => norm_sign_le_one hε _ ξ)

/-- A square integrable function multiplied by a measurable weight of absolute value at most one
is square integrable. -/
private lemma memLp_mul_of_norm_le_one {X : Type*} {mX : MeasurableSpace X} {ρ : Measure X}
    {w f : X → ℝ} (hw : Measurable w) (hw1 : ∀ x, ‖w x‖ ≤ 1) (hf : MemLp f 2 ρ) :
    MemLp (fun x => w x * f x) 2 ρ :=
  hf.of_le_mul (c := 1) (hw.aestronglyMeasurable.mul hf.1) (ae_of_all _ fun x => by
    rw [norm_mul, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hw1 x))

/-- An integrable function of the first coordinate multiplied by a measurable weight of absolute
value at most one is integrable. -/
private lemma integrable_mul_comp_fst (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ)
    [IsProbabilityMeasure ν] {w f : Ω → ℝ} (hw : Measurable w) (hw1 : ∀ ω, ‖w ω‖ ≤ 1)
    (hf : Integrable f μ) : Integrable (fun z : Ω × Ξ => w z.1 * f z.1) (μ.prod ν) :=
  (hf.comp_fst ν).bdd_mul (hw.comp measurable_fst).aestronglyMeasurable
    (ae_of_all _ fun z => hw1 z.1)

/-- The gated sign `w z.1 * ε (j + 1) z.2` is square integrable for a measurable weight `w` of
absolute value at most one. -/
private lemma memLp_mul_sign_succ (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ)
    [IsProbabilityMeasure ν] {𝒦 : ℕ → MeasurableSpace Ξ} {ε : ℕ → Ξ → ℝ}
    (hε : SignSequence ν 𝒦 ε) {w : Ω → ℝ} (hw : Measurable w) (hw1 : ∀ ω, ‖w ω‖ ≤ 1) (j : ℕ) :
    MemLp (fun z : Ω × Ξ => w z.1 * ε (j + 1) z.2) 2 (μ.prod ν) :=
  memLp_mul_of_norm_le_one (ρ := μ.prod ν) (w := fun z => w z.1) (hw.comp measurable_fst)
    (fun z => hw1 z.1) ((memLp_sign_succ ν hε j).comp_snd μ)

/-- The padded process is square integrable. -/
private lemma memLp_padded_of_gate (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ)
    [IsProbabilityMeasure ν] {𝒦 : ℕ → MeasurableSpace Ξ} {ε : ℕ → Ξ → ℝ}
    (hε : SignSequence ν 𝒦 ε) {S : ℕ → Ω → ℝ} (hL2 : ∀ n, MemLp (S n) 2 μ) {G : ℕ → Ω → ℝ}
    (hG01 : ∀ j ω, G j ω = 0 ∨ G j ω = 1) (hGmeas : ∀ j, Measurable (G j)) (n : ℕ) :
    MemLp (padded S G ε n) 2 (μ.prod ν) := by
  induction n with
  | zero => exact (hL2 0).comp_fst ν
  | succ n ih =>
    have h1 := memLp_mul_of_norm_le_one (ρ := μ.prod ν) (w := fun z => G n z.1)
      ((hGmeas n).comp measurable_fst) (fun z => (norm_gate_le_one hG01 n z.1).1)
      (((hL2 (n + 1)).sub (hL2 n)).comp_fst ν)
    have h2 := memLp_mul_sign_succ μ ν hε (w := fun ω => 1 - G n ω)
      (measurable_const.sub (hGmeas n)) (fun ω => (norm_gate_le_one hG01 n ω).2) n
    rw [padded_succ]
    exact (ih.add h1).add h2

/-- The padded process is adapted to the joined filtration. -/
private lemma stronglyMeasurable_padded (ℱ : Filtration ℕ m0) {𝒦 : ℕ → MeasurableSpace Ξ}
    (h𝒦 : Monotone 𝒦) {ε : ℕ → Ξ → ℝ}
    (hε : ∀ j, StronglyMeasurable[𝒦 (j + 1)] (ε (j + 1))) {S : ℕ → Ω → ℝ}
    (hS : StronglyAdapted ℱ S) {G : ℕ → Ω → ℝ} (hGm : ∀ j, StronglyMeasurable[ℱ j] (G j))
    (n : ℕ) : StronglyMeasurable[joinSigma (ℱ n) (𝒦 n)] (padded S G ε n) := by
  induction n with
  | zero => exact stronglyMeasurable_comp_fst_joinSigma (hS 0)
  | succ n ih =>
    have hℱ : ℱ n ≤ ℱ (n + 1) := ℱ.mono n.le_succ
    have hmono : joinSigma (ℱ n) (𝒦 n) ≤ joinSigma (ℱ (n + 1)) (𝒦 (n + 1)) :=
      sup_le_sup (MeasurableSpace.comap_mono hℱ) (MeasurableSpace.comap_mono (h𝒦 n.le_succ))
    have h1 := ih.mono hmono
    have h2 : StronglyMeasurable[joinSigma (ℱ (n + 1)) (𝒦 (n + 1))] fun z : Ω × Ξ => G n z.1 :=
      stronglyMeasurable_comp_fst_joinSigma ((hGm n).mono hℱ)
    have h3 : StronglyMeasurable[joinSigma (ℱ (n + 1)) (𝒦 (n + 1))]
        fun z : Ω × Ξ => S (n + 1) z.1 - S n z.1 :=
      stronglyMeasurable_comp_fst_joinSigma ((hS (n + 1)).sub ((hS n).mono hℱ))
    have h4 : StronglyMeasurable[joinSigma (ℱ (n + 1)) (𝒦 (n + 1))]
        fun z : Ω × Ξ => ε (n + 1) z.2 := stronglyMeasurable_comp_snd_joinSigma (hε n)
    rw [padded_succ]
    exact (h1.add (h2.mul h3)).add ((stronglyMeasurable_const.sub h2).mul h4)

/-- The padded process is a martingale for the joined filtration. -/
theorem martingale_padded (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ)
    [IsProbabilityMeasure ν] (ℱ : Filtration ℕ m0) {𝒦 : ℕ → MeasurableSpace Ξ}
    {ε : ℕ → Ξ → ℝ} (hε : SignSequence ν 𝒦 ε) {S : ℕ → Ω → ℝ} (hS : Martingale S ℱ μ)
    (hL2 : ∀ n, MemLp (S n) 2 μ) {G : ℕ → Ω → ℝ}
    (hGm : ∀ j, StronglyMeasurable[ℱ j] (G j)) (hG01 : ∀ j ω, G j ω = 0 ∨ G j ω = 1) :
    Martingale (padded S G ε) (liftFiltration ℱ 𝒦 hε.mono hε.le) (μ.prod ν) := by
  have hGmeas : ∀ j, Measurable (G j) := fun j => ((hGm j).mono (ℱ.le j)).measurable
  refine martingale_of_condExp_sub_eq_zero_nat (fun n => ?_) (fun n => ?_) (fun j => ?_)
  · exact stronglyMeasurable_padded ℱ hε.mono hε.measurable hS.1 hGm n
  · exact (memLp_padded_of_gate μ ν hε hL2 hG01 hGmeas n).integrable one_le_two
  · show (μ.prod ν)[padded S G ε (j + 1) - padded S G ε j | joinSigma (ℱ j) (𝒦 j)] =ᵐ[μ.prod ν] 0
    have hΔ : μ[fun ω => S (j + 1) ω - S j ω | ℱ j] =ᵐ[μ] 0 := by
      have h1 : μ[fun ω => S (j + 1) ω - S j ω | ℱ j] =ᵐ[μ] μ[S (j + 1) | ℱ j] - μ[S j | ℱ j] :=
        condExp_sub (hS.integrable (j + 1)) (hS.integrable j) (ℱ j)
      have h2 := hS.2 j (j + 1) j.le_succ
      have h3 := condExp_of_stronglyMeasurable (ℱ.le j) (hS.1 j) (hS.integrable j)
      filter_upwards [h1, h2] with ω hω1 hω2
      rw [hω1, Pi.sub_apply, hω2, h3]
      simp
    have hinc : padded S G ε (j + 1) - padded S G ε j = fun z =>
        G j z.1 * (S (j + 1) z.1 - S j z.1) + (1 - G j z.1) * ε (j + 1) z.2 := by
      funext z
      simp only [padded_succ, Pi.sub_apply]
      ring
    have hΔint : Integrable (fun ω => S (j + 1) ω - S j ω) μ :=
      (hS.integrable (j + 1)).sub (hS.integrable j)
    have hA := integrable_mul_comp_fst μ ν (hGmeas j) (fun ω => (norm_gate_le_one hG01 j ω).1)
      hΔint
    have hB := (memLp_mul_sign_succ μ ν hε (w := fun ω => 1 - G j ω)
      (measurable_const.sub (hGmeas j)) (fun ω => (norm_gate_le_one hG01 j ω).2) j).integrable
      one_le_two
    have hG' : StronglyMeasurable[ℱ j] fun ω => 1 - G j ω :=
      stronglyMeasurable_const.sub (hGm j)
    have h1 := condExp_mul_comp_fst_joinSigma μ ν (ℱ.le j) (hε.le j) (hGm j)
      (fun ω => (norm_gate_le_one hG01 j ω).1) hΔint
    have h2 := condExp_mul_comp_snd_joinSigma μ ν (ℱ.le j) (hε.le j) hG'
      (fun ω => (norm_gate_le_one hG01 j ω).2) ((memLp_sign_succ ν hε j).integrable one_le_two)
    have h3 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp hΔ
    have h4 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp
      (hε.condExp_eq_zero j)
    rw [hinc]
    filter_upwards [condExp_add hA hB (joinSigma (ℱ j) (𝒦 j)), h1, h2, h3, h4]
      with z hz hz1 hz2 hz3 hz4
    refine hz.trans ?_
    rw [Pi.add_apply, hz1, hz2]
    simp only [Function.comp_apply, Pi.zero_apply] at hz3 hz4
    rw [hz3, hz4]
    simp

/-- The padded process is square integrable. -/
theorem memLp_padded (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ)
    [IsProbabilityMeasure ν] {𝒦 : ℕ → MeasurableSpace Ξ} {ε : ℕ → Ξ → ℝ}
    (hε : SignSequence ν 𝒦 ε) {S : ℕ → Ω → ℝ} (hL2 : ∀ n, MemLp (S n) 2 μ) {G : ℕ → Ω → ℝ}
    (hG01 : ∀ j ω, G j ω = 0 ∨ G j ω = 1) (hGmeas : ∀ j, Measurable (G j)) (n : ℕ) :
    MemLp (padded S G ε n) 2 (μ.prod ν) := by
  exact memLp_padded_of_gate μ ν hε hL2 hG01 hGmeas n

/-- The conditional second moment of an increment of the padded process is the gate times that of
`S` plus one minus the gate. -/
theorem condExp_sq_increment_padded (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ)
    [IsProbabilityMeasure ν] (ℱ : Filtration ℕ m0) {𝒦 : ℕ → MeasurableSpace Ξ}
    {ε : ℕ → Ξ → ℝ} (hε : SignSequence ν 𝒦 ε) {S : ℕ → Ω → ℝ}
    (hL2 : ∀ n, MemLp (S n) 2 μ) {G : ℕ → Ω → ℝ}
    (hGm : ∀ j, StronglyMeasurable[ℱ j] (G j)) (hG01 : ∀ j ω, G j ω = 0 ∨ G j ω = 1) (j : ℕ) :
    (μ.prod ν)[fun z => (padded S G ε (j + 1) z - padded S G ε j z) ^ 2 |
        liftFiltration ℱ 𝒦 hε.mono hε.le j] =ᵐ[μ.prod ν]
      fun z => G j z.1 * (μ[fun ω => (S (j + 1) ω - S j ω) ^ 2 | ℱ j]) z.1 + (1 - G j z.1) := by
  have hGmeas : ∀ j, Measurable (G j) := fun j => ((hGm j).mono (ℱ.le j)).measurable
  have hsq : (fun z : Ω × Ξ => (padded S G ε (j + 1) z - padded S G ε j z) ^ 2) = fun z =>
      G j z.1 * (S (j + 1) z.1 - S j z.1) ^ 2 + (1 - G j z.1) := by
    funext z
    simp only [padded_succ]
    rcases hG01 j z.1 with h | h
    · rw [h]
      linear_combination hε.sq_eq_one (j + 1) z.2
    · rw [h]
      ring
  have hsqint : Integrable (fun ω => (S (j + 1) ω - S j ω) ^ 2) μ :=
    ((hL2 (j + 1)).sub (hL2 j)).integrable_sq
  have hA := integrable_mul_comp_fst μ ν (hGmeas j) (fun ω => (norm_gate_le_one hG01 j ω).1)
    hsqint
  have hBsm : StronglyMeasurable[joinSigma (ℱ j) (𝒦 j)] fun z : Ω × Ξ => 1 - G j z.1 :=
    stronglyMeasurable_const.sub (stronglyMeasurable_comp_fst_joinSigma (hGm j))
  have hBint : Integrable (fun z : Ω × Ξ => 1 - G j z.1) (μ.prod ν) :=
    Integrable.of_bound (measurable_const.sub ((hGmeas j).comp measurable_fst)).aestronglyMeasurable
      1 (ae_of_all _ fun z => (norm_gate_le_one hG01 j z.1).2)
  have h1 := condExp_mul_comp_fst_joinSigma μ ν (ℱ.le j) (hε.le j) (hGm j)
    (fun ω => (norm_gate_le_one hG01 j ω).1) hsqint
  have hB := condExp_of_stronglyMeasurable (joinSigma_le (ℱ.le j) (hε.le j)) hBsm hBint
  show (μ.prod ν)[fun z => (padded S G ε (j + 1) z - padded S G ε j z) ^ 2 |
    joinSigma (ℱ j) (𝒦 j)] =ᵐ[μ.prod ν] _
  rw [hsq]
  filter_upwards [condExp_add hA hBint (joinSigma (ℱ j) (𝒦 j)), h1] with z hz hz1
  refine hz.trans ?_
  rw [Pi.add_apply, hz1, hB]

end Padding

end CERW.Generic.Martingale.LilLower
