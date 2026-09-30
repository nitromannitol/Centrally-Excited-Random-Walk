import CERW.Support.Main.Event
import CERW.Support.Main.MassEventHigh
import CERW.Support.Main.MassEventPlanar
import CERW.Support.Main.InnerOfMass
import CERW.Support.Main.OuterOfMass
import CERW.Support.Main.GoodMono

/-!
# The fluctuation event from the good events

Deterministically, for all large `n`, `fluctEvent` implies `fluctGood`, and some site that is not
a departure site has norm less than `aN + C N Q`. Let `b` be the inradius of `D_n`.
1. `exists_mass_of_event_planar` (`d = 2`) or `exists_mass_of_event_high` (`d ≥ 3`) gives
   `m ≤ Cm N^d Q` and `ℓ_n ≤ Cm (b - |·|)_+ + Cm N Q^{1/d}`.
2. `exists_inner_of_mass` gives `|b/N - a| ≤ C Q`, the inner inclusion, `A_n ⊆ V_n`, the volume
   and profile clauses, and the unvisited site.
3. `exists_outer_of_mass`, with the constant `max Cm C`, gives the outer inclusion.
The constant of `fluctGood` is the larger of the two, by monotonicity of each clause.
-/

namespace CERW.Support.Main

open MeasureTheory LatticeProb CERW CERW.Support.Law

variable {d : ℕ}

/-- The mass step on the event, in every dimension. -/
private theorem exists_mass_of_event (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {b : Site d → ℝ}
    {C₀ C₁ : ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) {bd r₀ : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ), n₀ ≤ n →
      let Y : ℕ → Site d := fun j => X j ω
      let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
      let L : ℝ := Real.log (n + 2)
      let Q : ℝ := if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
      let binr : ℝ := sInf ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' (cellSet Y n)ᶜ)
      fluctEvent d ε b C₀ C₁ bd r₀ X ω n →
        (volume (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) binr)).toReal
          ≤ C * N ^ d * Q ∧
        ∀ y : Site d, (localTime Y n y : ℝ) ≤
          C * max (binr - euclidNorm y) 0 + C * N * Q ^ ((1 : ℝ) / d) := by
  rcases (show d = 2 ∨ 3 ≤ d by omega) with h2 | h3
  · exact exists_mass_of_event_planar h2 hε hC₀ hC₁
  · exact exists_mass_of_event_high h3 hε hC₀ hC₁

/-- The good events imply the fluctuation event: there are `C` and `n₀` such that for `n ≥ n₀`,
`fluctEvent` implies `fluctGood d ε C` together with a site outside `A_n` of norm less than
`a N + C N Q`. -/
theorem exists_good_of_event (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {b : Site d → ℝ} {C₀ C₁ : ℝ}
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) {bd r₀ : ℕ} (hbd : 1 ≤ bd) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ), n₀ ≤ n →
      let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
      let L : ℝ := Real.log (n + 2)
      let Q : ℝ := if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
      fluctEvent d ε b C₀ C₁ bd r₀ X ω n →
        fluctGood d ε C (fun j => X j ω) n ∧
        ∃ x : Site d, x ∉ departureRange (fun j => X j ω) n ∧ euclidNorm x < a * N + C * N * Q := by
  intro ωd a
  obtain ⟨Cm, hCm, nm, hmass⟩ := exists_mass_of_event hd hε (b := b) hC₀ hC₁ (bd := bd) (r₀ := r₀)
  obtain ⟨Ci, hCi, ni, hinner⟩ :=
    exists_inner_of_mass hd hε (b := b) hC₀ hC₁ hCm.le (bd := bd) (r₀ := r₀)
  have hCmi : 0 ≤ max Cm Ci := hCm.le.trans (le_max_left _ _)
  obtain ⟨Co, hCo, no, houter⟩ :=
    exists_outer_of_mass hd hε (b := b) (C₁ := C₁) hC₀ hCmi hbd (r₀ := r₀)
  refine ⟨max Ci Co, lt_max_of_lt_left hCi, max nm (max ni no), fun X ω n hn => ?_⟩
  have hnm : nm ≤ n := le_trans (le_max_left _ _) hn
  have hni : ni ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hno : no ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  intro N L Q hE
  obtain ⟨hm, henv⟩ := hmass X ω n hnm hE
  obtain ⟨hrad, hin, hAV, hvol, hprof, x, hx, hxn⟩ := hinner X ω n hni hE hm
  have hN : (0 : ℝ) ≤ N := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hL : (0 : ℝ) ≤ L := Real.log_nonneg (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hQ : 0 ≤ Q := by
    show (0 : ℝ) ≤ if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
    split_ifs <;> exact Real.rpow_nonneg (div_nonneg hL hN) _
  have hQd : 0 ≤ Q ^ ((1 : ℝ) / d) := Real.rpow_nonneg hQ _
  have h1 : Cm ≤ max Cm Ci := le_max_left _ _
  have h2 : Ci ≤ max Cm Ci := le_max_right _ _
  have hout := houter X ω n hno hE
    (hm.trans (by have := mul_nonneg (pow_nonneg hN d) hQ; gcongr))
    (fun y => (henv y).trans (add_le_add
      (mul_le_mul_of_nonneg_right h1 (le_max_right _ _))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hN) hQd)))
    (hrad.trans (by gcongr))
  have hi : Ci ≤ max Ci Co := le_max_left _ _
  have ho : Co ≤ max Ci Co := le_max_right _ _
  refine ⟨⟨fun y hy => hin ?_, hAV, fun y hy => ?_, hvol.trans ?_, fun y => (hprof y).trans ?_⟩,
    x, hx, hxn.trans_le ?_⟩
  · simp only [Set.mem_setOf_eq] at hy ⊢
    exact lt_of_lt_of_le hy (by gcongr)
  · have := hout hy
    simp only [Set.mem_setOf_eq] at this ⊢
    exact lt_of_lt_of_le this (by gcongr)
  · exact ENNReal.ofReal_le_ofReal (by gcongr)
  · gcongr
  · gcongr


end CERW.Support.Main
