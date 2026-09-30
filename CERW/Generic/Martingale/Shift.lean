import CERW.Generic.Martingale.FreedmanEvent

/-!
# Martingales seen from a later time

For a martingale `M` and a time `s`, the process `k ↦ M_{s+k} - M_s` is a martingale for the
filtration `k ↦ ℱ_{s+k}`, and it starts at `0`. Freedman's inequality on the event of a small
bracket therefore applies to every interval increment `M_{s+k} - M_s`, with the bracket increment
`V_{s+k} - V_s`. This is the form used for the interval martingales of `eq:interval-mart` and
for `eq:vector`.
-/

namespace CERW.Generic.Martingale

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The filtration `k ↦ ℱ_{s+k}` seen from time `s`. -/
def shiftFiltration (ℱ : Filtration ℕ m0) (s : ℕ) : Filtration ℕ m0 where
  seq k := ℱ (s + k)
  mono' _ _ h := ℱ.mono (Nat.add_le_add_left h s)
  le' k := ℱ.le (s + k)

/-- Seen from time `s`, a martingale minus its value at `s` is a martingale. -/
theorem martingale_shift {P : Measure Ω} {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ}
    (hmart : Martingale M ℱ P) (s : ℕ) :
    Martingale (fun k ω => M (s + k) ω - M s ω) (shiftFiltration ℱ s) P := by
  refine ⟨fun k => ?_, fun i j hij => ?_⟩
  · exact (hmart.stronglyMeasurable (s + k)).sub
      ((hmart.stronglyMeasurable s).mono (ℱ.mono (Nat.le_add_right s k)))
  · change P[fun ω => M (s + j) ω - M s ω | ℱ (s + i)] =ᵐ[P]
      fun ω => M (s + i) ω - M s ω
    have hsub : P[fun ω => M (s + j) ω - M s ω | ℱ (s + i)] =ᵐ[P]
        P[M (s + j) | ℱ (s + i)] - P[M s | ℱ (s + i)] :=
      condExp_sub (hmart.integrable (s + j)) (hmart.integrable s) (ℱ (s + i))
    have hlast : P[M (s + j) | ℱ (s + i)] =ᵐ[P] M (s + i) :=
      hmart.condExp_ae_eq (Nat.add_le_add_left hij s)
    by_cases hσ : SigmaFinite (P.trim (ℱ.le (s + i)))
    · haveI := hσ
      have hfirst : P[M s | ℱ (s + i)] = M s :=
        condExp_of_stronglyMeasurable (ℱ.le (s + i))
          ((hmart.stronglyMeasurable s).mono (ℱ.mono (Nat.le_add_right s i)))
          (hmart.integrable s)
      filter_upwards [hsub, hlast] with ω e1 e2
      rw [e1]
      simp only [Pi.sub_apply]
      rw [e2, hfirst]
    · have hfirst : P[M s | ℱ (s + i)] = 0 :=
        condExp_of_not_sigmaFinite (ℱ.le (s + i)) hσ
      have hnot : ¬ SigmaFinite (P.trim (ℱ.le s)) := by
        intro hs
        haveI := hs
        exact hσ (sigmaFiniteTrim_mono (ℱ.le (s + i))
          (ℱ.mono (Nat.le_add_right s i)))
      have hMs0 : M s =ᵐ[P] 0 := by
        have h1 : P[M s | ℱ s] =ᵐ[P] M s := hmart.condExp_ae_eq (le_refl s)
        have h2 : P[M s | ℱ s] = 0 := condExp_of_not_sigmaFinite (ℱ.le s) hnot
        rw [h2] at h1
        exact h1.symm
      filter_upwards [hsub, hlast, hMs0] with ω e1 e2 e3
      rw [e1]
      simp only [Pi.sub_apply]
      rw [e2, hfirst, e3]

/-- The bracket value at a fixed time `s` is measurable for the filtration at any later
index `s + k`. -/
theorem stronglyMeasurable_shift_V {ℱ : Filtration ℕ m0} {V : ℕ → Ω → ℝ}
    (hVpred : ∀ k, StronglyMeasurable[ℱ k] (V (k + 1))) (hV0 : ∀ ω, V 0 ω = 0)
    (s k : ℕ) : StronglyMeasurable[ℱ (s + k)] (V s) := by
  rcases s with _ | j
  · rw [show V 0 = fun _ => (0 : ℝ) from funext hV0]
    exact stronglyMeasurable_const
  · exact (hVpred j).mono
      (ℱ.mono (le_trans (Nat.le_succ j) (Nat.le_add_right (j + 1) k)))

/-- Freedman's inequality for the increment `M_{s+k} - M_s` on the event that the bracket
increases by at most `v` over `[s, s+k]`. -/
theorem measure_le_abs_sub_and_le {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ m0} {M V : ℕ → Ω → ℝ} (hmart : Martingale M ℱ P)
    (hVpred : ∀ k, StronglyMeasurable[ℱ k] (V (k + 1))) (hV0 : ∀ ω, V 0 ω = 0)
    (hVmono : ∀ k ω, V k ω ≤ V (k + 1) ω)
    (hVdom : ∀ k, P[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ≤ᵐ[P]
      fun ω => V (k + 1) ω - V k ω)
    {b : ℝ} (hb : 0 < b) (s k : ℕ)
    (hinc : ∀ i, s ≤ i → i < s + k → ∀ ω, |M (i + 1) ω - M i ω| ≤ b)
    {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    P {ω | t ≤ |M (s + k) ω - M s ω| ∧ V (s + k) ω - V s ω ≤ v} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / (2 * (v + b * t / 3))))) := by
  have hmart' : Martingale (fun k ω => M (s + k) ω - M s ω) (shiftFiltration ℱ s) P :=
    martingale_shift hmart s
  have hM0' : ∀ ω, (fun k ω => M (s + k) ω - M s ω) 0 ω = 0 := by
    intro ω
    simp
  have hVpred' : ∀ k, StronglyMeasurable[shiftFiltration ℱ s k]
      (fun ω => V (s + (k + 1)) ω - V s ω) := by
    intro k
    have h1 : StronglyMeasurable[ℱ (s + k)] (V (s + (k + 1))) :=
      hVpred (s + k)
    exact h1.sub (stronglyMeasurable_shift_V hVpred hV0 s k)
  have hV0' : ∀ ω, (fun k ω => V (s + k) ω - V s ω) 0 ω = 0 := by
    intro ω
    simp
  have hVmono' : ∀ k ω, (fun k ω => V (s + k) ω - V s ω) k ω
      ≤ (fun k ω => V (s + k) ω - V s ω) (k + 1) ω := by
    intro k ω
    have h := hVmono (s + k) ω
    simp only [Nat.add_succ]
    linarith
  have hVdom' : ∀ k, P[fun ω => ((fun k ω => M (s + k) ω - M s ω) (k + 1) ω
        - (fun k ω => M (s + k) ω - M s ω) k ω) ^ 2 | shiftFiltration ℱ s k] ≤ᵐ[P]
      fun ω => (fun k ω => V (s + k) ω - V s ω) (k + 1) ω
        - (fun k ω => V (s + k) ω - V s ω) k ω := by
    intro k
    have hMfun : (fun ω => ((fun k ω => M (s + k) ω - M s ω) (k + 1) ω
          - (fun k ω => M (s + k) ω - M s ω) k ω) ^ 2)
        = fun ω => (M ((s + k) + 1) ω - M (s + k) ω) ^ 2 := by
      funext ω
      simp only [Nat.add_succ]
      ring
    have hVfun : (fun ω => (fun k ω => V (s + k) ω - V s ω) (k + 1) ω
          - (fun k ω => V (s + k) ω - V s ω) k ω)
        = fun ω => V ((s + k) + 1) ω - V (s + k) ω := by
      funext ω
      simp only [Nat.add_succ]
      ring
    rw [hMfun, hVfun]
    exact hVdom (s + k)
  have hinc' : ∀ i < k, ∀ ω, |(fun k ω => M (s + k) ω - M s ω) (i + 1) ω
      - (fun k ω => M (s + k) ω - M s ω) i ω| ≤ b := by
    intro i hi ω
    have h1 : s + i < s + k := Nat.add_lt_add_left hi s
    have h2 := hinc (s + i) (Nat.le_add_right s i) h1 ω
    have hgoal : M (s + (i + 1)) ω - M s ω - (M (s + i) ω - M s ω)
        = M ((s + i) + 1) ω - M (s + i) ω := by
      simp only [Nat.add_succ]
      ring
    rw [hgoal]
    exact h2
  exact measure_le_abs_and_le hmart' hM0' hVpred' hV0' hVmono' hVdom' hb k hinc' hv ht

end CERW.Generic.Martingale
