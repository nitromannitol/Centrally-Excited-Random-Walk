import CERW.Support.Outer.Radius.PlanarProfile

/-!
# Probability Assembly

Union bounds assemble the outer-radius estimate with its polynomial exceptional probability. The
radius and profile estimates then give the fluctuation rates and their almost-sure form.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- A set covered by three sets of small measure has small measure. -/
lemma measure_le_union_three {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S E₁ E₂ E₃ : Set Ω} {a₁ a₂ a₃ C : ℝ} (hS : S ⊆ E₁ ∪ E₂ ∪ E₃)
    (h₁ : μ E₁ ≤ ENNReal.ofReal a₁) (h₂ : μ E₂ ≤ ENNReal.ofReal a₂)
    (h₃ : μ E₃ ≤ ENNReal.ofReal a₃) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hC : a₁ + a₂ + a₃ ≤ C)
    (ha₃ : 0 ≤ a₃) : μ S ≤ ENNReal.ofReal C := by
  calc μ S ≤ μ (E₁ ∪ E₂ ∪ E₃) := measure_mono hS
    _ ≤ μ (E₁ ∪ E₂) + μ E₃ := measure_union_le _ _
    _ ≤ (μ E₁ + μ E₂) + μ E₃ := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ (ENNReal.ofReal a₁ + ENNReal.ofReal a₂) + ENNReal.ofReal a₃ := by gcongr
    _ = ENNReal.ofReal (a₁ + a₂ + a₃) := by
        rw [ENNReal.ofReal_add (add_nonneg ha₁ ha₂) ha₃, ENNReal.ofReal_add ha₁ ha₂]
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC

/-- If `n < n₀` the bound `C n^{-p}` with `C ≥ (n₀+1)^p` is at least `1`. -/
lemma one_le_ofReal_mul_rpow {C p : ℝ} {n n₀ : ℕ} (hp : 0 < p) (hn : 0 < n)
    (hnn : n < n₀) (hC : ((n₀ : ℝ) + 1) ^ p ≤ C) :
    (1 : ENNReal) ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  rw [ENNReal.one_le_ofReal]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos hn0 p
  have hnle : (n : ℝ) ≤ (n₀ : ℝ) + 1 := by
    have : (n : ℝ) ≤ n₀ := by exact_mod_cast hnn.le
    linarith
  have hle : (n : ℝ) ^ p ≤ ((n₀ : ℝ) + 1) ^ p := Real.rpow_le_rpow hn0.le hnle hp.le
  rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, le_div_iff₀ hnp, one_mul]
  linarith

/-- Proposition `prop:stronger-outer` (the outer radius), from Proposition `prop:inner`, the
near-far lemma and the
outer-crossing lemma. -/
theorem outer_radius_of (hinner : inner_radius.{u}) (hnear : near_far)
    (houter : outer_crossing) : outer_radius.{u} := by
  intro d hd ωd ε hε hεd r p hp
  obtain ⟨C₀, C₁, Cf, hC₀, hC₁, hCf, hfl⟩ := exists_pathFacts_prob hd hε hεd hp
  obtain ⟨Cin, hCin, hin⟩ := hinner hd ε hε hεd p hp
  obtain ⟨Cl, hCl, hlin⟩ := exists_linOK_prob hd hε hεd hp
  have hC₁' : 0 < max C₁ Cl := lt_max_of_lt_left hC₁
  obtain ⟨Ccr, hCcr, hcr⟩ := euclid_crossing houter hd hε hεd C₀ (max C₁ Cl) hC₁'
  obtain ⟨C, hC, n₀, hcore⟩ : ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      PathFacts d ε C₀ (max C₁ Cl) Y n → InnerOK d ε Cin Y n → CrossOK d Ccr Y n →
      maxRadius Y n ≤ radius d ε n + C * (if d = 2 then Real.sqrt (radius d ε n) *
        Real.log n ^ ((5 : ℝ) / 2) else Real.log n ^ ((d : ℝ) + 1)) := by
    by_cases h2 : d = 2
    · obtain ⟨C, hC, n₀, h⟩ := outer_core_planar h2 hnear hε hεd C₀ (max C₁ Cl) Cin Ccr hCin hCcr
      exact ⟨C, hC, n₀, fun Y n hn h1 h3 h4 => by rw [if_pos h2]; exact h Y n hn h1 h3 h4⟩
    · obtain ⟨C, hC, n₀, h⟩ := outer_core_high (by omega) (newton_conv (by omega)) hnear hε hεd
        C₀ (max C₁ Cl) Cin Ccr hCin hCcr
      exact ⟨C, hC, n₀, fun Y n hn h1 h3 h4 => by rw [if_neg h2]; exact h Y n hn h1 h3 h4⟩
  have hn₀p : 0 < ((n₀ : ℝ) + 1) ^ p := Real.rpow_pos_of_pos (by positivity) p
  set Cfin : ℝ := C + Cf + Cin + Cl + ((n₀ : ℝ) + 1) ^ p with hCfin
  have hCfin0 : 0 < Cfin := by positivity
  refine ⟨Cfin, hCfin0, ?_⟩
  intro Ω _ μ _ X hX n hn2
  have hnp0 : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  by_cases hnb : n₀ ≤ n
  · have h1 : μ {ω | ¬ PathFacts d ε C₀ C₁ (fun j => X j ω) n} ≤ _ := hfl μ X hX n hn2
    have h2 : μ {ω | ¬ InnerOK d ε Cin (fun j => X j ω) n} ≤ _ := hin μ X hX n hn2
    have h3 : μ {ω | ¬ LinOK d ε Cl (fun j => X j ω) n} ≤ _ := hlin μ X hX n hn2
    refine measure_le_union_three (hS := ?_) h1 h2 h3 (mul_nonneg hCf.le hnp0)
      (mul_nonneg hCin.le hnp0) ?_ (mul_nonneg hCl.le hnp0)
    · intro ω hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
      obtain ⟨⟨hA, hB⟩, hD⟩ := hcon
      apply hω
      have hA' := hA.mono (le_max_left C₁ Cl)
      have hD' := hD.mono (le_max_right C₁ Cl)
      have hmain := hcore (fun j => X j ω) n hnb hA' hB (hcr _ n hn2 hA' hD')
      refine hmain.trans ?_
      have hrhs : 0 ≤ (if d = 2 then Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)
          else Real.log n ^ ((d : ℝ) + 1)) := by
        have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
        split_ifs
        · exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlog _)
        · exact Real.rpow_nonneg hlog _
      have hCle : C ≤ Cfin := by
        rw [hCfin]
        linarith [hCf, hCin, hCl, hn₀p]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hCle hrhs)
    · calc Cf * (n : ℝ) ^ (-p) + Cin * (n : ℝ) ^ (-p) + Cl * (n : ℝ) ^ (-p)
          = (Cf + Cin + Cl) * (n : ℝ) ^ (-p) := by ring
        _ ≤ Cfin * (n : ℝ) ^ (-p) := by
          refine mul_le_mul_of_nonneg_right ?_ hnp0
          rw [hCfin]
          linarith [hC, hn₀p]
  · rw [not_le] at hnb
    exact (prob_le_one).trans (one_le_ofReal_mul_rpow hp (by omega) hnb
      (by rw [hCfin]; linarith [hC, hCf, hCin, hCl]))


/-! ### Theorem `thm:fluctuations` -/

/-- Proposition `prop:stronger-outer` and Theorem `thm:fluctuations`: the clauses of the good event
from the three inputs. -/
theorem fluctuation_rates_of (hinner : inner_radius.{u}) (houter : outer_radius.{u})
    (hnear : near_far) : fluctuation_rates.{u} := by
  intro d hd ωd ε hε hεd r Good p hp
  have hd1 : 1 ≤ d := by omega
  have hmono : ∀ C C' : ℝ, C ≤ C' → ∀ (Y : ℕ → Site d) (n : ℕ), 1 ≤ n →
      Good C Y n → Good C' Y n := by
    intro C C' hCC Y n hn hG
    have hr : 0 < radius d ε n := radius_pos hd1 hε hn
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have hq : 0 ≤ qrate d ε n := qrate_nonneg hd1 hε hn
    obtain ⟨h1, h2, h3⟩ := hG
    refine ⟨?_, ?_, ?_⟩
    · by_cases h : d = 2
      · simp only [if_pos h] at h1 ⊢
        obtain ⟨a, b⟩ := h1
        refine ⟨a.trans ?_, b.trans ?_⟩ <;> gcongr
      · simp only [if_neg h] at h1 ⊢
        obtain ⟨a, b⟩ := h1
        refine ⟨a.trans ?_, b.trans ?_⟩ <;> gcongr
    · refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
      have : 0 ≤ (if d = 2 then Real.sqrt (Real.log n / radius d ε n)
          else Real.log n / radius d ε n) := hq
      gcongr
    · intro x
      refine (h3 x).trans ?_
      by_cases h : d = 2
      · simp only [if_pos h]
        gcongr
      · simp only [if_neg h]
        gcongr
  have key : ∀ q : ℝ, 0 < q → ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ Good C (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-q)) := by
    intro q hq
    obtain ⟨C₀, C₁, Cf, hC₀, hC₁, hCf, hfl⟩ := exists_pathFacts_prob.{u} hd hε hεd hq
    obtain ⟨Cin, hCin, hin⟩ := hinner hd ε hε hεd q hq
    obtain ⟨Co, hCo, hout⟩ := houter hd ε hε hεd q hq
    obtain ⟨Cl, hCl, n₀, hcore⟩ : ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ),
        n₀ ≤ n → PathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n →
        maxRadius Y n ≤ radius d ε n + Co * (if d = 2 then Real.sqrt (radius d ε n) *
          Real.log n ^ ((5 : ℝ) / 2) else Real.log n ^ ((d : ℝ) + 1)) →
        ∀ x : Site d, |(localTime Y n x : ℝ) - 2 * d * ε * max (radius d ε n - euclidNorm x) 0| ≤
          C * (if d = 2 then Real.sqrt (radius d ε n) * Real.log n ^ ((3 : ℝ) / 2)
            else Real.sqrt (radius d ε n * Real.log n)) := by
      by_cases h2 : d = 2
      · obtain ⟨C, hC, n₀, h⟩ := local_core_planar h2 hnear hε hεd C₀ C₁ Cin Co hC₀ hC₁ hCin
        exact ⟨C, hC, n₀, fun Y n hn h1 h3 h4 x => by
          rw [if_pos h2]
          exact h Y n hn h1 h3 (by rw [if_pos h2] at h4; exact h4) x⟩
      · obtain ⟨C, hC, n₀, h⟩ := local_core_high (d := d) (by omega) hε C₀ C₁ Cin Co hC₀ hC₁ hCin
        exact ⟨C, hC, n₀, fun Y n hn h1 h3 h4 x => by
          rw [if_neg h2]
          exact h Y n hn h1 h3 (by rw [if_neg h2] at h4; exact h4) x⟩
    set Cg : ℝ := max (max Cin Co) Cl with hCg
    have hCin_g : Cin ≤ Cg := (le_max_left _ _).trans (le_max_left _ _)
    have hCo_g : Co ≤ Cg := (le_max_right _ _).trans (le_max_left _ _)
    have hCl_g : Cl ≤ Cg := le_max_right _ _
    have hdet : ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n → 2 ≤ n → PathFacts d ε C₀ C₁ Y n →
        InnerOK d ε Cin Y n →
        maxRadius Y n ≤ radius d ε n + Co * (if d = 2 then Real.sqrt (radius d ε n) *
          Real.log n ^ ((5 : ℝ) / 2) else Real.log n ^ ((d : ℝ) + 1)) → Good Cg Y n := by
      intro Y n hn0 hn2 h1 h2 h3
      have hloc := hcore Y n hn0 h1 h2 h3
      have hrq := radius_mul_qrate hd1 hε (by omega : 1 ≤ n)
      have hr : 0 < radius d ε n := radius_pos hd1 hε (by omega : 1 ≤ n)
      have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      obtain ⟨i1, i2, -⟩ := h2
      refine ⟨?_, ?_, fun x => (hloc x).trans ?_⟩
      · by_cases h : d = 2
        · simp only [if_pos h]
          refine ⟨?_, ?_⟩
          · calc |innerRadius Y n - radius d ε n| ≤ Cin * radius d ε n * qrate d ε n := i1
              _ = Cin * (radius d ε n * qrate d ε n) := by ring
              _ = Cin * Real.sqrt (radius d ε n * Real.log n) := by rw [hrq, if_pos h]
              _ ≤ Cg * Real.sqrt (radius d ε n * Real.log n) := by gcongr
          · rw [if_pos h] at h3
            have hnn : 0 ≤ Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2) :=
              mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlog _)
            calc maxRadius Y n - radius d ε n
                ≤ Co * (Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)) := by linarith
              _ ≤ Cg * (Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)) := by gcongr
              _ = Cg * Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2) := by ring
        · simp only [if_neg h]
          refine ⟨?_, ?_⟩
          · calc |innerRadius Y n - radius d ε n| ≤ Cin * radius d ε n * qrate d ε n := i1
              _ = Cin * (radius d ε n * qrate d ε n) := by ring
              _ = Cin * Real.log n := by rw [hrq, if_neg h]
              _ ≤ Cg * Real.log n := by gcongr
          · rw [if_neg h] at h3
            have hnn : 0 ≤ Real.log n ^ ((d : ℝ) + 1) := Real.rpow_nonneg hlog _
            calc maxRadius Y n - radius d ε n ≤ Co * Real.log n ^ ((d : ℝ) + 1) := by linarith
              _ ≤ Cg * Real.log n ^ ((d : ℝ) + 1) := by gcongr
      · refine i2.trans (ENNReal.ofReal_le_ofReal ?_)
        have hq : 0 ≤ qrate d ε n := qrate_nonneg hd1 hε (by omega)
        show Cin * qrate d ε n ≤ Cg * qrate d ε n
        exact mul_le_mul_of_nonneg_right hCin_g hq
      · have hnn : 0 ≤ (if d = 2 then Real.sqrt (radius d ε n) * Real.log n ^ ((3 : ℝ) / 2)
            else Real.sqrt (radius d ε n * Real.log n)) := by
          split_ifs
          · exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlog _)
          · exact Real.sqrt_nonneg _
        exact mul_le_mul_of_nonneg_right hCl_g hnn
    have hn₀ : 0 < (((max n₀ 2 : ℕ) : ℝ) + 1) ^ q :=
      Real.rpow_pos_of_pos (by positivity) q
    set Cfin : ℝ := Cg + Cf + Cin + Co + (((max n₀ 2 : ℕ) : ℝ) + 1) ^ q with hCfin
    have hCg0 : 0 < Cg := lt_of_lt_of_le hCin hCin_g
    have hCfin0 : 0 < Cfin := by positivity
    refine ⟨Cfin, hCfin0, ?_⟩
    intro Ω _ μ _ X hX n hn2
    have hnp0 : 0 ≤ (n : ℝ) ^ (-q) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    by_cases hnb : max n₀ 2 ≤ n
    · have e1 : μ {ω | ¬ PathFacts d ε C₀ C₁ (fun j => X j ω) n} ≤ _ := hfl μ X hX n hn2
      have e2 : μ {ω | ¬ InnerOK d ε Cin (fun j => X j ω) n} ≤ _ := hin μ X hX n hn2
      have e3 := hout μ X hX n hn2
      refine measure_le_union_three (hS := ?_) e1 e2 e3 (mul_nonneg hCf.le hnp0)
        (mul_nonneg hCin.le hnp0) ?_ (mul_nonneg hCo.le hnp0)
      · intro ω hω
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
        obtain ⟨⟨hA, hB⟩, hD⟩ := hcon
        apply hω
        have hG := hdet (fun j => X j ω) n (le_trans (le_max_left _ _) hnb) hn2 hA hB hD
        exact hmono _ _ (by rw [hCfin]; linarith [hCf, hCin, hCo, hn₀]) _ n (by omega) hG
      · calc Cf * (n : ℝ) ^ (-q) + Cin * (n : ℝ) ^ (-q) + Co * (n : ℝ) ^ (-q)
            = (Cf + Cin + Co) * (n : ℝ) ^ (-q) := by ring
          _ ≤ Cfin * (n : ℝ) ^ (-q) := by
            refine mul_le_mul_of_nonneg_right ?_ hnp0
            rw [hCfin]
            linarith [hCg0, hn₀]
    · rw [not_le] at hnb
      exact (prob_le_one).trans (one_le_ofReal_mul_rpow hq (by omega) hnb
        (by rw [hCfin]; linarith [hCg0, hCf, hCin, hCo]))
  obtain ⟨Cp, hCp, hprob⟩ := key p hp
  obtain ⟨C2, hC2, hprob2⟩ := key 2 (by norm_num)
  refine ⟨max Cp C2, lt_max_of_lt_left hCp, ?_, ?_⟩
  · intro Ω _ μ _ X hX n hn
    have hnp0 : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    refine (measure_mono ?_).trans ((hprob μ X hX n hn).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hnp0)))
    intro ω hω hG
    exact hω (hmono _ _ (le_max_left _ _) _ n (by omega) hG)
  · intro Ω _ μ _ X hX
    have hbc := CERW.Support.Main.ae_eventually_of_le_rpow (μ := μ) (C := C2) (p := 2)
      (P := fun n ω => Good C2 (X · ω) n) (by norm_num) (n₀ := 2) (fun n hn => by
        simpa using hprob2 μ X hX n hn)
    filter_upwards [hbc] with ω hω
    filter_upwards [hω, Filter.eventually_ge_atTop 1] with n hGn hn1
    exact hmono _ _ (le_max_right _ _) _ n hn1 hGn

end CERW.Support.Outer.Radius
