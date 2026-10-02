import CERW.Generic.Martingale.LilAssembly.Core
import CERW.Generic.Martingale.LilAssembly.BlockArith
import CERW.Generic.Martingale.LilAssembly.BlockEventMeas
import CERW.Generic.Martingale.LilLower

/-!
# The conditional lower bound for the blocks

`BlockLower` is proved from the sharp lower tail for one block conditioned on an earlier event
(`block_lower_bound`), the bracket values at the passage times (`passage_values`), the bound on the
increments inside a block (`sqrt_scale_le`), the sums of the bracket increments over a block
(`block_sum_le`, `block_sum_eq`), the arithmetic of the blocks (`block_arith`), and the
measurability of the block events at their passage times (`measurableSet_blockEvent`).
-/

universe u

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.LilLower

/-- The level jump at the gate level is at most the level jump at the larger gate level. -/
private lemma max_scale_le {x g ε : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) (hg : 2 * g ^ 2 ≤ ε ^ 2) :
    max 1 (2 * g ^ 2 * x / Real.log (Real.log x)) ≤
      max 1 (ε ^ 2 * x / Real.log (Real.log x)) := by
  have hL : 0 < Real.log (Real.log x) := lt_of_lt_of_le one_pos (ba_ll_ge_one x hx)
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  exact max_le_max le_rfl
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hg hxpos.le) hL.le)

/-- Along one path, the window sum of the bracket increments between the two passage times is
below the level jump bound, and eventually above the deficit bound. -/
private lemma window_path {Ω : Type*} (V : ℕ → Ω → ℝ) (ω : Ω) {N : ℕ} {θ ε εg : ℝ} {k : ℕ}
    (hθ : 1 < θ) (hV0 : V 0 ω = 0) (hmono : ∀ n, V n ω ≤ V (n + 1) ω)
    (hjump : ∀ t, N ≤ t → V (t + 1) ω - V t ω ≤
      max 1 (εg ^ 2 * V (t + 1) ω /
        Real.log (Real.log (max (V (t + 1) ω) (Real.exp (Real.exp 1))))))
    (hinf : Tendsto (fun n => V n ω) atTop atTop)
    (hN : (N : WithTop ℕ) ≤ firstPassage V (θ ^ k) ω) (hx : Real.exp (Real.exp 1) ≤ θ ^ k)
    (hεg : 2 * εg ^ 2 ≤ ε ^ 2) (hεLL : ε ^ 2 ≤ Real.log (Real.log (θ ^ k))) (c : ℕ → ℝ)
    (hc : ∀ t, c t = V (t + 1) ω - V t ω) (S : ℕ → ℝ)
    (hS : ∀ n, S n = ∑ t ∈ Finset.range n,
      (if max (firstPassage V (θ ^ k) ω) (N : WithTop ℕ) ≤ (t : WithTop ℕ) ∧
          (t : WithTop ℕ) < max (firstPassage V (θ ^ (k + 1)) ω) (N : WithTop ℕ)
        then (1 : ℝ) else 0) * c t) :
    (∀ n, S n ≤ θ ^ (k + 1) - θ ^ k + max 1 (ε ^ 2 * θ ^ k / Real.log (Real.log (θ ^ k)))) ∧
      ∀ᶠ n in atTop, θ ^ (k + 1) - θ ^ k -
        max 1 (ε ^ 2 * θ ^ (k + 1) / Real.log (Real.log (θ ^ (k + 1)))) ≤ S n := by
  have hle1 : θ ^ k ≤ θ ^ (k + 1) := pow_le_pow_right₀ hθ.le (Nat.le_succ k)
  have hx' : Real.exp (Real.exp 1) ≤ θ ^ (k + 1) := hx.trans hle1
  obtain ⟨n₀, hn₀⟩ := WithTop.ne_top_iff_exists.1
    (firstPassage_ne_top_of_tendsto (x := θ ^ k) hinf)
  obtain ⟨n₁, hn₁⟩ := WithTop.ne_top_iff_exists.1
    (firstPassage_ne_top_of_tendsto (x := θ ^ (k + 1)) hinf)
  have hn₀' : firstPassage V (θ ^ k) ω = (n₀ : WithTop ℕ) := hn₀.symm
  have hn₁' : firstPassage V (θ ^ (k + 1)) ω = (n₁ : WithTop ℕ) := hn₁.symm
  have hNn₀ : N ≤ n₀ := by
    rw [hn₀'] at hN
    exact_mod_cast hN
  have hle : n₀ ≤ n₁ := by
    have h := firstPassage_mono (V := V) (ω := ω) hle1
    rw [hn₀', hn₁'] at h
    exact_mod_cast h
  have hσ : max (firstPassage V (θ ^ k) ω) (N : WithTop ℕ) = (n₀ : WithTop ℕ) := by
    rw [hn₀']
    exact max_eq_left (by exact_mod_cast hNn₀)
  have hρ : max (firstPassage V (θ ^ (k + 1)) ω) (N : WithTop ℕ) = (n₁ : WithTop ℕ) := by
    rw [hn₁']
    exact max_eq_left (by exact_mod_cast hNn₀.trans hle)
  have hsum : ∀ n, S n = ∑ t ∈ Finset.range n,
      (if (n₀ : WithTop ℕ) ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < (n₁ : WithTop ℕ)
        then (1 : ℝ) else 0) * (V (t + 1) ω - V t ω) := by
    intro n
    rw [hS n, hσ, hρ]
    exact Finset.sum_congr rfl fun t _ => by rw [hc t]
  have hg0 : εg ^ 2 ≤ Real.log (Real.log (θ ^ k)) / 2 := by linarith
  have hg1 : εg ^ 2 ≤ Real.log (Real.log (θ ^ (k + 1))) / 2 := by
    have := ba_ll_mono _ _ hx hle1
    linarith
  have hp₀ := passage_values V ω hV0 hjump hx hg0 hNn₀ hn₀'
  have hp₁ := passage_values V ω hV0 hjump hx' hg1 (hNn₀.trans hle) hn₁'
  have hJ₀ := max_scale_le hx hεg
  have hJ₁ := max_scale_le hx' hεg
  have hmono' : ∀ n, (fun m => V m ω) n ≤ (fun m => V m ω) (n + 1) := hmono
  refine ⟨fun n => ?_, ?_⟩
  · have h := block_sum_le hmono' hle n
    rw [hsum n]
    linarith [hp₀.1, hp₁.2]
  · filter_upwards [eventually_ge_atTop n₁] with n hn
    have h := block_sum_eq (V := fun m => V m ω) hle hn
    rw [hsum n]
    linarith [hp₀.2, hp₁.1]

/-- Before the first passage over a level, the process at the next time is below the level. -/
private lemma lt_of_lt_firstPassage {Ω : Type*} {V : ℕ → Ω → ℝ} {x : ℝ} {ω : Ω} {t : ℕ}
    (h : (t : WithTop ℕ) < firstPassage V x ω) : V (t + 1) ω < x := by
  cases hf : firstPassage V x ω using WithTop.recTopCoe with
  | top =>
    by_contra hc
    exact (firstPassage_ne_top_iff.2 ⟨t, not_lt.1 hc⟩) hf
  | coe n =>
    rw [hf] at h
    exact (firstPassage_spec hf).2 t (WithTop.coe_lt_coe.1 h)

/-- After the first passage over a level, the process at the next time is above the level. -/
private lemma le_of_firstPassage_le {Ω : Type*} {V : ℕ → Ω → ℝ} {x : ℝ} {ω : Ω} {t : ℕ}
    (hmono : ∀ n, V n ω ≤ V (n + 1) ω) (h : firstPassage V x ω ≤ (t : WithTop ℕ)) :
    x ≤ V (t + 1) ω := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1
    (ne_top_of_le_ne_top (WithTop.natCast_ne_top t) h)
  have hn' : firstPassage V x ω = (n : WithTop ℕ) := hn.symm
  rw [hn'] at h
  have hnt : n ≤ t := by exact_mod_cast h
  exact (firstPassage_spec hn').1.trans ((monotone_nat_of_le_succ hmono) (Nat.succ_le_succ hnt))

/-- Inside a block, between the two passage times cut off below at `N`, the increments of `M` are
bounded by `max 1 (ε √(θ^(k+1) / log log θ^k))`. -/
private lemma block_increment_bound {Ω : Type*} {M V : ℕ → Ω → ℝ} {θ ε εg : ℝ} {N k : ℕ}
    (hmono : ∀ n ω, V n ω ≤ V (n + 1) ω)
    (hinc : ∀ (t : ℕ) (ω : Ω), N ≤ t → 1 ≤ V (t + 1) ω →
      |M (t + 1) ω - M t ω| ≤ max 1 (εg * Real.sqrt (V (t + 1) ω /
        Real.log (Real.log (max (V (t + 1) ω) (Real.exp (Real.exp 1)))))))
    (hx : Real.exp (Real.exp 1) ≤ θ ^ k) (hεg : 0 ≤ εg) (hεgε : εg ≤ ε) (t : ℕ) (ω : Ω)
    (hσ : max (firstPassage V (θ ^ k) ω) (N : WithTop ℕ) ≤ (t : WithTop ℕ))
    (hρ : (t : WithTop ℕ) < max (firstPassage V (θ ^ (k + 1)) ω) (N : WithTop ℕ)) :
    |M (t + 1) ω - M t ω| ≤
      max 1 (ε * Real.sqrt (θ ^ (k + 1) / Real.log (Real.log (θ ^ k)))) := by
  have hNt : N ≤ t := by exact_mod_cast (le_max_right _ _).trans hσ
  have hτk : firstPassage V (θ ^ k) ω ≤ (t : WithTop ℕ) := (le_max_left _ _).trans hσ
  have hτk1 : (t : WithTop ℕ) < firstPassage V (θ ^ (k + 1)) ω := by
    rcases lt_max_iff.1 hρ with h | h
    · exact h
    · exact absurd (by exact_mod_cast h : t < N) (not_lt.2 hNt)
  have h1 : θ ^ k ≤ V (t + 1) ω := le_of_firstPassage_le (fun n => hmono n ω) hτk
  have h2 : V (t + 1) ω < θ ^ (k + 1) := lt_of_lt_firstPassage hτk1
  have h3 : 1 ≤ V (t + 1) ω := ((Real.one_le_exp (Real.exp_nonneg 1)).trans hx).trans h1
  exact (hinc t ω hNt h3).trans (sqrt_scale_le hx h1 h2 hεg hεgε)

/-- The conditional second moment of an increment is the increment of the bracket, at a point
where the bracket is the predictable bracket. -/
private lemma condExp_sq_eq_sub {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (M V : ℕ → Ω → ℝ) {ω : Ω}
    (h : ∀ n, V n ω = CERW.predBracket μ ℱ M M n ω) (t : ℕ) :
    (μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t]) ω = V (t + 1) ω - V t ω := by
  rw [h (t + 1), h t, predBracket_eq_sum_condExp_sq, predBracket_eq_sum_condExp_sq,
    Finset.sum_apply, Finset.sum_apply, Finset.sum_range_succ]
  ring

/-- Almost surely on `F`, the window sums of the conditional variances of `M` between the
passage times are at most the level jump bound at every time, and eventually at least the deficit
bound. -/
private lemma window_ae {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m0} {M B V : ℕ → Ω → ℝ} {εg : ℝ} {N : ℕ}
    (hP : PaddedData μ ℱ M B V εg N) {θ ε : ℝ} {k : ℕ} (hθ : 1 < θ)
    (hx : Real.exp (Real.exp 1) ≤ θ ^ k) (hεg : 2 * εg ^ 2 ≤ ε ^ 2)
    (hεLL : ε ^ 2 ≤ Real.log (Real.log (θ ^ k))) {F : Set Ω}
    (hFN : F ⊆ {ω | (N : WithTop ℕ) ≤ firstPassage V (θ ^ k) ω}) :
    ∀ᵐ ω ∂μ, ω ∈ F →
      (∀ n, ∑ t ∈ Finset.range n,
        (if max (firstPassage V (θ ^ k) ω) (N : WithTop ℕ) ≤ (t : WithTop ℕ) ∧
            (t : WithTop ℕ) < max (firstPassage V (θ ^ (k + 1)) ω) (N : WithTop ℕ)
          then (1 : ℝ) else 0) * (μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t]) ω ≤
        θ ^ (k + 1) - θ ^ k + max 1 (ε ^ 2 * θ ^ k / Real.log (Real.log (θ ^ k)))) ∧
      ∀ᶠ n in atTop, θ ^ (k + 1) - θ ^ k -
        max 1 (ε ^ 2 * θ ^ (k + 1) / Real.log (Real.log (θ ^ (k + 1)))) ≤
        ∑ t ∈ Finset.range n,
        (if max (firstPassage V (θ ^ k) ω) (N : WithTop ℕ) ≤ (t : WithTop ℕ) ∧
            (t : WithTop ℕ) < max (firstPassage V (θ ^ (k + 1)) ω) (N : WithTop ℕ)
          then (1 : ℝ) else 0) * (μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t]) ω := by
  filter_upwards [hP.vBracket, hP.vInf, hP.jump] with ω h1 h2 h3 hωF
  exact window_path V ω hθ (hP.vZero ω) (fun n => hP.vMono n ω) h3 h2 (hFN hωF) hx hεg hεLL _
    (condExp_sq_eq_sub μ ℱ M V h1) _ (fun n => rfl)

/-- On `F`, where `N` has passed, cutting the passage times off below at `N` does not change the
event that the increment between them is at least `a`: it is the block event. -/
private lemma inter_stoppedValue_eq {Ω : Type*} {M V : ℕ → Ω → ℝ} {θ δ a : ℝ} {N k : ℕ}
    (hθ : 1 ≤ θ) (hadef : a = (1 - δ / 2) * Real.sqrt (1 - 1 / θ) * lilScale (θ ^ (k + 1)))
    (F : Set Ω) (hFN : F ⊆ {ω | (N : WithTop ℕ) ≤ firstPassage V (θ ^ k) ω}) :
    F ∩ {ω | a ≤ stoppedValue M (fun ω => max (firstPassage V (θ ^ (k + 1)) ω) (N : WithTop ℕ)) ω -
      stoppedValue M (fun ω => max (firstPassage V (θ ^ k) ω) (N : WithTop ℕ)) ω} =
    F ∩ blockEvent M V θ δ (k + 1) := by
  ext ω
  refine and_congr_right fun hωF => ?_
  have h1 : max (firstPassage V (θ ^ k) ω) (N : WithTop ℕ) = firstPassage V (θ ^ k) ω :=
    max_eq_left (hFN hωF)
  have h2 : max (firstPassage V (θ ^ (k + 1)) ω) (N : WithTop ℕ) =
      firstPassage V (θ ^ (k + 1)) ω :=
    max_eq_left ((hFN hωF).trans (firstPassage_mono (pow_le_pow_right₀ hθ (Nat.le_succ k))))
  simp only [blockEvent, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, Set.mem_setOf_eq,
    stoppedValue, h1, h2, hadef]

/-- The conclusion of the conditional lower bound for one block, for fixed constants. -/
private def LowerTailBound (η ρ₀ ε₀ A₀ : ℝ) : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {M : ℕ → Ω → ℝ}, Martingale M ℱ μ → (∀ n, MemLp (M n) 2 μ) →
    ∀ {σ ρ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ), IsStoppingTime ℱ ρ →
    (∀ ω, σ ω ≤ ρ ω) → (∀ᵐ ω ∂μ, ρ ω ≠ ⊤) →
    ∀ {F : Set Ω}, MeasurableSet[hσ.measurableSpace] F → μ F ≠ 0 → ∀ {b : ℝ}, 0 ≤ b →
    (∀ (t : ℕ) (ω : Ω), σ ω ≤ (t : WithTop ℕ) → (t : WithTop ℕ) < ρ ω →
      |M (t + 1) ω - M t ω| ≤ b) → ∀ {v a r : ℝ},
    0 < v → 0 < a → 0 ≤ r → r ≤ ρ₀ →
    (∀ᵐ ω ∂μ, ω ∈ F → ∀ n, ∑ t ∈ Finset.range n,
      (if σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω then (1 : ℝ) else 0) *
        (μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t]) ω ≤ v) →
    (∀ᵐ ω ∂μ, ω ∈ F → ∀ᶠ n in atTop, v * (1 - r) ≤ ∑ t ∈ Finset.range n,
      (if σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω then (1 : ℝ) else 0) *
        (μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t]) ω) →
    A₀ * v ≤ a ^ 2 → a * b ≤ ε₀ * v →
    Real.exp (-((1 + η) * (a ^ 2 / (2 * v)))) * (μ F).toReal ≤
      (μ (F ∩ {ω | a ≤ stoppedValue M ρ ω - stoppedValue M σ ω})).toReal

/-- The bound for one block: the conditional lower bound applied to the passage times over the
levels `θ^k` and `θ^(k+1)`, cut off below at `N`. -/
private lemma block_core {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {M B V : ℕ → Ω → ℝ} {εg : ℝ} {N : ℕ}
    (hP : PaddedData μ ℱ M B V εg N) {η ρ₀ ε₀ A₀ θ ε δ w a r : ℝ}
    (H : LowerTailBound.{u} η ρ₀ ε₀ A₀) (hθ : 1 < θ) (hεg0 : 0 < εg)
    (hεg : 2 * εg ^ 2 ≤ ε ^ 2) (hεgε : εg ≤ ε) {k : ℕ} (hx : Real.exp (Real.exp 1) ≤ θ ^ k)
    (hεLL : ε ^ 2 ≤ Real.log (Real.log (θ ^ k))) (hw : 0 < w)
    (hwdef : w = θ ^ (k + 1) - θ ^ k + max 1 (ε ^ 2 * θ ^ k / Real.log (Real.log (θ ^ k))))
    (hr : 0 ≤ r) (hrρ : r ≤ ρ₀)
    (hwr : w * (1 - r) = θ ^ (k + 1) - θ ^ k -
      max 1 (ε ^ 2 * θ ^ (k + 1) / Real.log (Real.log (θ ^ (k + 1)))))
    (ha : 0 < a) (hadef : a = (1 - δ / 2) * Real.sqrt (1 - 1 / θ) * lilScale (θ ^ (k + 1)))
    (hA : A₀ * w ≤ a ^ 2)
    (hab : a * max 1 (ε * Real.sqrt (θ ^ (k + 1) / Real.log (Real.log (θ ^ k)))) ≤ ε₀ * w)
    (hτk : IsStoppingTime ℱ (firstPassage V (θ ^ k)))
    (hτk1 : IsStoppingTime ℱ (firstPassage V (θ ^ (k + 1)))) {F : Set Ω}
    (hF : MeasurableSet[hτk.measurableSpace] F)
    (hFN : F ⊆ {ω | (N : WithTop ℕ) ≤ firstPassage V (θ ^ k) ω}) :
    Real.exp (-((1 + η) * (a ^ 2 / (2 * w)))) * (μ F).toReal ≤
      (μ (F ∩ blockEvent M V θ δ (k + 1))).toReal := by
  by_cases hμF : μ F = 0
  · rw [hμF, ENNReal.toReal_zero, mul_zero]
    exact ENNReal.toReal_nonneg
  have hσ := hτk.max_const N
  have hρ := hτk1.max_const N
  have hle1 : θ ^ k ≤ θ ^ (k + 1) := pow_le_pow_right₀ hθ.le (Nat.le_succ k)
  have hσρ : ∀ ω, max (firstPassage V (θ ^ k) ω) (N : WithTop ℕ) ≤
      max (firstPassage V (θ ^ (k + 1)) ω) (N : WithTop ℕ) :=
    fun ω => max_le_max (firstPassage_mono hle1) le_rfl
  have hfin : ∀ᵐ ω ∂μ, max (firstPassage V (θ ^ (k + 1)) ω) (N : WithTop ℕ) ≠ ⊤ := by
    filter_upwards [hP.vInf] with ω h
    exact (max_lt (lt_top_iff_ne_top.2 (firstPassage_ne_top_of_tendsto h))
      (WithTop.natCast_lt_top N)).ne
  have hF' : MeasurableSet[hσ.measurableSpace] F :=
    hτk.measurableSpace_mono hσ (fun ω => le_max_left _ _) F hF
  have hb : 0 ≤ max 1 (ε * Real.sqrt (θ ^ (k + 1) / Real.log (Real.log (θ ^ k)))) :=
    le_max_of_le_left zero_le_one
  have hbound := fun t ω => block_increment_bound (M := M) hP.vMono hP.blockInc hx hεg0.le hεgε
    t ω
  have hwin := window_ae hP hθ hx hεg hεLL hFN
  have key := H μ ℱ hP.mart hP.memLp hσ hρ hσρ hfin hF' hμF hb hbound hw ha hr hrρ
    (hwin.mono fun ω h hω => hwdef ▸ (h hω).1)
    (hwin.mono fun ω h hω => hwr ▸ (h hω).2) hA hab
  rw [← inter_stoppedValue_eq (M := M) hθ.le hadef F hFN]
  exact key

/-- A gate level at most `ε / √2` has `2 εg² ≤ ε²` and `εg ≤ ε`. -/
private lemma gate_le {εg ε : ℝ} (hεg : 0 < εg) (h : εg ≤ ε / Real.sqrt 2) :
    2 * εg ^ 2 ≤ ε ^ 2 ∧ εg ≤ ε := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hs1 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.2 one_le_two
  have h1 : εg * Real.sqrt 2 ≤ ε := (le_div_iff₀ hs).1 h
  have h2 : (εg * Real.sqrt 2) ^ 2 ≤ ε ^ 2 :=
    pow_le_pow_left₀ (mul_pos hεg hs).le h1 2
  rw [mul_pow, Real.sq_sqrt two_pos.le] at h2
  exact ⟨by linarith, (le_mul_of_one_le_right hεg.le hs1).trans h1⟩

/-- `log log (θ^k)` is eventually above any bound. -/
private lemma exists_le_loglog_pow {θ : ℝ} (hθ : 1 < θ) (c : ℝ) :
    ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → c ≤ Real.log (Real.log (θ ^ k)) := by
  have h1 : Tendsto (fun k : ℕ => θ ^ k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hθ
  have h2 := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h1)
  exact eventually_atTop.1 (h2.eventually_ge_atTop c)

/-- **The conditional lower bound for the blocks.** -/
theorem block_lower : BlockLower.{u} := by
  intro δ hδ0 hδ1
  obtain ⟨θ, η, δ', hθ, hη, hδ', hc, hBA⟩ := block_arith δ hδ0 hδ1
  obtain ⟨ρ₀, ε₀, A₀, hρ₀, hε₀, H⟩ := block_lower_bound.{u} hη
  obtain ⟨ε, hε, k₀, hk, hsum⟩ := hBA ρ₀ ε₀ A₀ hρ₀ hε₀
  obtain ⟨k₁, hk₁⟩ := exists_le_loglog_pow hθ (ε ^ 2)
  refine ⟨θ, δ', ε / Real.sqrt 2, hθ, hδ', by positivity, hc, ?_⟩
  intro Ω m0 μ _ ℱ M B V εg N hεg hεgε hP
  have hτ : ∀ k, IsStoppingTime ℱ (firstPassage V (θ ^ k)) :=
    fun j => isStoppingTime_firstPassage hP.vPred (θ ^ j)
  obtain ⟨hεg2, hεgε'⟩ := gate_le hεg hεgε
  refine ⟨hτ, max k₀ k₁, _, ?_, ?_, hsum, measurableSet_blockEvent δ hP.mart.1 hθ.le hτ, ?_⟩
  · intro k
    dsimp only
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  · intro k
    dsimp only
    split_ifs with hk0
    · obtain ⟨hw, -⟩ := hk k hk0
      exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (by linarith)
        (div_nonneg (sq_nonneg _) (by linarith))))
    · exact zero_le_one
  · intro k hKk F hF hFN
    have hk0 : k₀ ≤ k := (le_max_left _ _).trans hKk
    have hk1 : k₁ ≤ k := (le_max_right _ _).trans hKk
    obtain ⟨hw, ha, hr, hrρ, hwr, hA, hab, hx⟩ := hk k hk0
    dsimp only
    rw [if_pos hk0]
    exact block_core hP H hθ hεg hεg2 hεgε' hx (hk₁ k hk1) hw rfl hr hrρ hwr ha rfl hA hab
      (hτ k) (hτ (k + 1)) hF hFN

end CERW.Generic.Martingale.LilAssembly
