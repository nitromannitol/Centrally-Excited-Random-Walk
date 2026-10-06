import CERW.Support.Norm.Section5Localization
import CERW.Support.Norm.CoarseCrossing
import CERW.Support.Norm.OuterCrossing
import CERW.Support.Guards.NormRates
import CERW.Support.Outer.NearFar
import CERW.Support.Outer.OuterRadius
import CERW.Support.Lower.SeparatedBrackets

/-!
# The separated bracket bounds on the event of Section 5.1

`lem:separated-brackets` asserts, for the Euclidean norm and `0 < ε < 1/d`, that for all large `n`
the normalized brackets of the martingales `S^i` satisfy `c₀ ≤ ⟨S^i⟩_n ≤ C₀` and
`|⟨S^i, S^j⟩_n| ≤ C r_n^{-1/4}` on the event `Ω_n` of Section 5.1 with `p = 10`. The bound with
probability at least `1 - C n^{-10}` proved earlier does not give this inclusion; this module
proves it.

* `BracketBounds` is the conclusion of the lemma for a path at time `n`: the literal inner event
  of the lemma, with `r_n`, `σ_n`, `k`, `m`, `y_i`, `f_i` and `⟨S^i, S^j⟩_n` as in the source.
* `brackets_of_estimates7` is the deterministic implication. For the constants of the seven
  estimates of Section 5.1 and a constant of the contact estimate, a path with the typing of the
  model that satisfies the seven estimates at time `n` (for any projection `P` in the second
  family of directions) and the contact estimate has the bracket bounds, for all `n` beyond a
  threshold that depends only on `d`, `ε` and these constants. The proof is the deterministic part
  of the outer-radius and fluctuation arguments: the seven estimates give the path facts
  (`PathFacts`) of Sections 3 and 4, the inner radius estimate (`InnerOK`, from
  `inner_of_estimates7`) and the crossing bound (`CrossOK`, from the vector bound and the
  half-space martingale bounds of the radial family and the crossing lemma); these give the outer
  radius, then the profile `|ℓ_n - 2dε (r_n - |x|)_+| ≤ C √r_n (log n)^{3/2}` of the local times at
  all sites, and the bracket bounds follow from that profile.
* `separated_brackets_on_E7` is the lemma on the event: the literal event `E7` of
  `Section5Localization` with `p = 10` has complement of probability at most `C n^{-10}`, its
  legal sample points have probability one, and at every legal sample point of `E7`, for all
  large `n`, the bracket bounds hold; the same holds at every sample point of the `E7` of the
  legal carrier.
* `separated_brackets_on_E7_of_isCERW` is the first part of that statement for a process with
  `IsCERW μ ε X`, the model of the lemma.

No bracket bound, profile or radius estimate is assumed: the contact estimate and the inner radius
estimate enter through `section5_euclid_localization`.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Lower.SeparatedBracketsEvent

open CERW CERW.Support.Statements CERW.Support.Norm.ContactEvent
  CERW.Support.Norm.Section5Localization

open private PathFacts PathFacts.mk InnerOK CrossOK radius qrate outerMax braSum tk_radius_eq
  radius_pos newton_conv outer_core_high outer_core_planar local_core_high local_core_planar
  from CERW.Support.Outer.OuterRadius

open private brackets_core sqrt_mul_le_sqrt_mul_rpow from CERW.Support.Lower.SeparatedBrackets

open private normMin_euclidean normMax_euclidean from CERW.Support.Guards.NormRates

variable {d : ℕ}

/-! ## The conclusion of the lemma for a path -/

/-- The conclusion of `lem:separated-brackets` for a path `Y` at time `n`, with constants `c₀`,
`C₀`, `C`: with `r_n`, `σ_n`, `k`, `m`, `y_i`, `f_i` as in the source, the normalized bracket
`B = ⟨S^i, S^j⟩_n = ⟨𝓜^{f_i}, 𝓜^{f_j}⟩_n / σ_n²` of the Dynkin martingales of the Euclidean walk
satisfies `c₀ ≤ B ≤ C₀` for `i = j` and `|B| ≤ C r_n^{-1/4}` for `i ≠ j`, for `1 ≤ i, j ≤ m`. -/
def BracketBounds (hd : 2 ≤ d) (ε c₀ C₀ C : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
  let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
  let e₁ : Site d := LatticeProb.unit ⟨0, by omega⟩
  let g : Site d → ℝ := CERW.latticeKernel d
  let σ : ℕ → ℝ := fun n =>
    if d = 2 then Real.sqrt (r n * Real.log (r n)) else Real.sqrt (r n)
  let k : ℕ → ℕ := fun n => ⌊r n ^ ((1 : ℝ) / 8)⌋₊
  let m : ℕ → ℕ := fun n => ⌊r n ^ ((1 : ℝ) / 8)⌋₊
  let y : ℕ → ℕ → Site d := fun n i => ((i * ⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℤ) • e₁
  let f : ℕ → ℕ → Site d → ℝ := fun n i z =>
    if d = 2 then g (z - (y n i + (k n : ℤ) • e₁)) - g (z - y n i) else g (z - y n i)
  ∀ i j : ℕ, 1 ≤ i → i ≤ m n → 1 ≤ j → j ≤ m n →
    let B : ℝ := CERW.dynkinBracket (CERW.stepProb d ε) (f n i) (f n j) Y n / σ n ^ 2
    (i = j → c₀ ≤ B ∧ B ≤ C₀) ∧ (i ≠ j → |B| ≤ C * r n ^ (-(1 : ℝ) / 4))

/-! ## The scale and the rates of the Euclidean norm -/

/-- For the Euclidean norm the scale of the event is the radius `r_n`. -/
private lemma scale_eq_radius (ε : ℝ) (n : ℕ) :
    scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n = radius d ε n := by
  unfold scale radius
  rw [normBallVolume_norm]

/-- For the Euclidean norm the contact rate of the event is the rate `q_n`. -/
private lemma contactRate_eq_qrate (ε : ℝ) (n : ℕ) :
    contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n = qrate d ε n := by
  unfold contactRate qrate
  rw [scale_eq_radius]

/-- The conclusions of `prop:inner` on the event are the clauses of the inner radius estimate
`InnerOK` of the outer radius argument. -/
private lemma innerOK_of_innerConclusion {ε C : ℝ} {Y : ℕ → Site d} {n : ℕ}
    (h : InnerConclusion d ε C Y n) : InnerOK d ε C Y n := by
  unfold InnerConclusion at h
  simp only [scale_eq_radius, contactRate_eq_qrate] at h
  exact h

/-! ## The path facts -/

/-- The arithmetic of the global approximation: the bound with `log n` and the constant `c` of the
event implies the bound with `log (n + 2)` and any larger nonnegative constant. -/
private lemma glob_arith {c C lg lg2 S S2 : ℝ} (hc : c ≤ C) (hC : 0 ≤ C) (hlg : 0 ≤ lg)
    (hl : lg ≤ lg2) (hS : 0 ≤ S) (hSS : S ≤ S2) : c * lg + c * S ≤ C * (S2 + lg2) := by
  have h1 : c * lg ≤ C * lg := mul_le_mul_of_nonneg_right hc hlg
  have h2 : C * lg ≤ C * lg2 := mul_le_mul_of_nonneg_left hl hC
  have h3 : c * S ≤ C * S := mul_le_mul_of_nonneg_right hc hS
  have h4 : C * S ≤ C * S2 := mul_le_mul_of_nonneg_left hSS hC
  nlinarith

/-- A pointwise bound `|a + m| ≤ c₁ L` and a bound `|m| ≤ c₂ (s + L)` give
`|a| ≤ (c₁ + c₂) (s + L)`. -/
private lemma abs_le_of_abs_add_le {a m L s c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hs : 0 ≤ s)
    (h1 : |a + m| ≤ c₁ * L) (h2 : |m| ≤ c₂ * (s + L)) : |a| ≤ (c₁ + c₂) * (s + L) := by
  have h3 : |a| ≤ |a + m| + |m| := by
    calc |a| = |(a + m) - m| := by ring_nf
      _ ≤ |a + m| + |m| := abs_sub _ _
  have h4 : c₁ * L ≤ c₁ * (s + L) := mul_le_mul_of_nonneg_left (by linarith) hc₁
  calc |a| ≤ c₁ * L + c₂ * (s + L) := h3.trans (add_le_add h1 h2)
    _ ≤ c₁ * (s + L) + c₂ * (s + L) := by linarith
    _ = (c₁ + c₂) * (s + L) := by ring

/-- **The seven estimates give the path facts.** For the Euclidean norm, `d ≥ 2`, `ε > 0` and the
constants `K` of the event of Section 5.1 there are constants `C₀`, `C₁` such that every path with
the typing of the model that satisfies the seven estimates at a time `n ≥ 2` (for any
projection `P`) has the path facts of the outer radius argument: the coarse upper bounds, the
approximation of the local times by the potential, the local martingale bounds in the form of the
bracket sum, and the vector bound. -/
private theorem pathFacts_of_estimates7 (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (K : EventConstants) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (Y : ℕ → Site d) (n : ℕ),
        2 ≤ n → PathTyping d Y →
        Estimates7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K P Y n →
        PathFacts d ε C₀ C₁ Y n := by
  have hd1 : 1 ≤ d := by omega
  have hΨ : IsNorm (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) := isNorm_euclidean
  obtain ⟨a, ha, hra⟩ := tk_radius_eq hd1 hε
  obtain ⟨_, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  have hB : CERW.Support.Norm.ContactShared.BregmanSumBound d
      (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) :=
    CERW.Support.Norm.ContactBregman.bregmanSumBound_of hd hΨ
      (fun φ h1 h2 h3 =>
        CERW.Support.Norm.ContactWeakLap.inner_gradient_integral_nonpos hΨ h1 h2 h3)
      (CERW.Support.Norm.ContactCellTest.cellTestBound hd hΨ)
  obtain ⟨C_pt, hCpt, hpt⟩ :=
    CERW.Support.Norm.ContactPointwise.exists_abs_localTime_sub_normPotential_add_driftDynkin_le.{0}
      hd hΨ hB hK
  set Cco : ℝ := max K.C_co 0 with hCco
  set Cl : ℝ := max K.C_loc 0 with hCl
  set Cm : ℝ := max K.C_mart 0 with hCm
  set Cv : ℝ := max K.C_vec 0 with hCv
  have hCco0 : 0 ≤ Cco := le_max_right _ _
  have hCl0 : 0 ≤ Cl := le_max_right _ _
  have hCm0 : 0 ≤ Cm := le_max_right _ _
  have hCv0 : 0 ≤ Cv := le_max_right _ _
  have hCp1 : 0 ≤ C_pt * (1 + ε) := by positivity
  refine ⟨Cco * a + 1, Cl + (C_pt * (1 + ε) + Cm) + Cv + 1, by positivity, by positivity, ?_⟩
  intro ξ hξ hξ0 P Y n hn2 hty hE
  obtain ⟨hco, hloc, hvec, hlm, -, -, -⟩ := hE
  obtain ⟨hY0, hsteps⟩ := hty
  have hnorm : ∀ j, euclidNorm (Y j) ≤ j :=
    CERW.Support.Occupation.euclidNorm_le_of_steps Y hY0 hsteps
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_nonneg hn0.le _
  have hL0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hLL : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log hn0 (by linarith)
  have hL2 : 0 ≤ Real.log ((n : ℝ) + 2) := le_trans hL0 hLL
  obtain ⟨-, -, -, hM, -, hR⟩ := hco
  have hrn : scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n =
      a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by rw [scale_eq_radius, hra n]
  have hsc : K.C_co * scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n ≤
      (Cco * a + 1) * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    rw [hrn]
    have h1 : K.C_co * (a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ≤
        Cco * (a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) :=
      mul_le_mul_of_nonneg_right (le_max_left K.C_co 0) (mul_nonneg ha.le hN)
    nlinarith
  refine PathFacts.mk hY0 hsteps (hM.trans hsc) (hR.trans hsc) (fun y hy => ?_)
    (fun x hx => ?_) (fun s t hst htn => ?_)
  · -- the global approximation of the local times by the potential
    have h := hloc.2.2 y hy
    rw [normPotential_norm_eq hd1] at h
    have hS0 : 0 ≤ (if d = 2 then Real.sqrt (maxLocalTime Y n) * Real.log (n : ℝ)
        else Real.sqrt (maxLocalTime Y n * Real.log (n : ℝ))) := by
      split_ifs
      · exact mul_nonneg (Real.sqrt_nonneg _) hL0
      · exact Real.sqrt_nonneg _
    refine h.trans ?_
    have hC1 : K.C_loc ≤ Cl + (C_pt * (1 + ε) + Cm) + Cv + 1 :=
      (le_max_left K.C_loc 0).trans (by linarith)
    have hC1' : 0 ≤ Cl + (C_pt * (1 + ε) + Cm) + Cv + 1 := by positivity
    split_ifs with h2
    · have := glob_arith (c := K.C_loc) (C := Cl + (C_pt * (1 + ε) + Cm) + Cv + 1)
        (lg := Real.log (n : ℝ)) (lg2 := Real.log ((n : ℝ) + 2))
        (S := Real.sqrt (maxLocalTime Y n) * Real.log (n : ℝ))
        (S2 := Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2)) hC1 hC1' hL0 hLL
        (by rw [if_pos h2] at hS0; exact hS0)
        (mul_le_mul_of_nonneg_left hLL (Real.sqrt_nonneg _))
      exact this
    · have := glob_arith (c := K.C_loc) (C := Cl + (C_pt * (1 + ε) + Cm) + Cv + 1)
        (lg := Real.log (n : ℝ)) (lg2 := Real.log ((n : ℝ) + 2))
        (S := Real.sqrt (maxLocalTime Y n * Real.log (n : ℝ)))
        (S2 := Real.sqrt (maxLocalTime Y n * Real.log ((n : ℝ) + 2))) hC1 hC1' hL0 hLL
        (by rw [if_neg h2] at hS0; exact hS0)
        (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hLL (Nat.cast_nonneg _)))
      exact this
  · -- the pointwise bound at lattice sites, with the local martingale bound
    have hW : braSum Y n x = ∑ j ∈ Finset.range n,
        (1 + euclidNorm (Y j - x)) ^ (2 - 2 * (d : ℝ)) := rfl
    have hW' : (∑ j ∈ Finset.range n, (1 + euclidNorm (Y j - x)) ^ (2 - 2 * (d : ℝ))) =
        ∑ z ∈ departureRange Y n,
          (localTime Y n z : ℝ) * (1 + euclidNorm (z - x)) ^ (2 - 2 * (d : ℝ)) :=
      CERW.Support.LocalTime.sum_range_eq_sum_localTime Y n
        (fun z => (1 + euclidNorm (z - x)) ^ (2 - 2 * (d : ℝ)))
    have hW0 : 0 ≤ ∑ z ∈ departureRange Y n,
        (localTime Y n z : ℝ) * (1 + euclidNorm (z - x)) ^ (2 - 2 * (d : ℝ)) :=
      Finset.sum_nonneg fun z _ => mul_nonneg (Nat.cast_nonneg _)
        (Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg (z - x)]) _)
    have hmart : |CERW.Support.Drift.driftDynkin ε ξ (fun z => latticeKernel d (z - x))
          (fun j (_ : Unit) => Y j) n ()| ≤
        Cm * (Real.sqrt (braSum Y n x * Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2)) := by
      rw [← CERW.Support.Drift.dynkinMart_driftStepProb_eq_driftDynkin hd1 ε ξ
        (fun z => latticeKernel d (z - x)) (fun j (_ : Unit) => Y j) n ()]
      refine (hlm x hx).trans (mul_le_mul (le_max_left _ _) (add_le_add ?_ hLL)
        (add_nonneg (Real.sqrt_nonneg _) hL0) hCm0)
      rw [hW, hW']
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hLL hW0)
    have h1 := hpt ε hε.le ξ hξ hξ0 (fun j (_ : Unit) => Y j) () hY0 hnorm n (by omega) x hx
    rw [normPotential_norm_eq hd1] at h1
    have hS : 0 ≤ Real.sqrt (braSum Y n x * Real.log ((n : ℝ) + 2)) := Real.sqrt_nonneg _
    have h3 := abs_le_of_abs_add_le (L := Real.log ((n : ℝ) + 2))
      (s := Real.sqrt (braSum Y n x * Real.log ((n : ℝ) + 2))) (by positivity) hS h1 hmart
    refine h3.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (add_nonneg hS hL2)
    linarith
  · -- the vector bound
    have hξu := field_eq_unitDir hξ hξ0
    subst hξu
    have h := hvec s t hst htn
    have hst' : (s : ℝ) < t := by exact_mod_cast hst
    have hs0 : 0 ≤ ((t : ℝ) - s) * Real.log (n : ℝ) :=
      mul_nonneg (by linarith) hL0
    have hsqrt : Real.sqrt (((t : ℝ) - s) * Real.log (n : ℝ)) ≤
        Real.sqrt (((t : ℝ) - s) * Real.log ((n : ℝ) + 2)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hLL (by linarith))
    refine h.trans (mul_le_mul ?_ hsqrt (Real.sqrt_nonneg _) (by positivity))
    exact (le_max_left K.C_vec 0).trans (by linarith)

/-! ## The crossing bound -/

/-- **The seven estimates give the crossing bound.** For the Euclidean norm, `d ≥ 2`, `0 < ε < 1/d`
and the constants `K` of the event there is `C` such that every path with the typing of the model
that satisfies the seven estimates at a time `n ≥ 2` satisfies the crossing bound
`max_{j ≤ n} |X_j| ≤ b + C (1 + max_{|x| ≥ b} ℓ_n(x)) log n` for every `b ≥ 0`. It is the rough
outer bound, applied with the vector bound and the half-space martingale bounds of the radial
family of directions. -/
private theorem crossOK_of_estimates7 (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) (K : EventConstants) :
    ∃ Ccr : ℝ, 0 < Ccr ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (Y : ℕ → Site d) (n : ℕ),
        2 ≤ n → PathTyping d Y →
        Estimates7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K P Y n →
        CrossOK d Ccr Y n := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hΨ, -, -, hell⟩ := CERW.Support.Main.euclidean_norm_hypotheses (d := d) hεd
  obtain ⟨C, hC, hmain⟩ := CERW.Support.Norm.CoarseCrossing.rough_outer_bound hd hΨ hε hell
    CERW.Support.Norm.outer_crossing_holds (C_V := max K.C_vec 1) (C_M := max K.C_lin 0)
    (lt_of_lt_of_le one_pos (le_max_right _ _))
  refine ⟨C, hC, fun ξ hξ hξ0 P Y n hn2 hty hE b hb => ?_⟩
  obtain ⟨-, -, hvec, -, -, hlin, -⟩ := hE
  have hΛ : normMax (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) = 1 := normMax_euclidean hd1
  have hc : normMin (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) = 1 := normMin_euclidean hd1
  have hL0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hvec' : ∀ s t : ℕ, s < t → t ≤ n →
      ‖CERW.Support.Norm.VectorBound.driftCompensated ε ξ Y t -
          CERW.Support.Norm.VectorBound.driftCompensated ε ξ Y s‖ ≤
        max K.C_vec 1 * Real.sqrt (((t : ℝ) - s) * Real.log n) := fun s t hst htn =>
    (hvec s t hst htn).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  have hlin' : ∀ q ∈ CERW.Support.Norm.CoarseCrossing.capDirections
      (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) n, ∀ k : ℕ, k ≤ n →
      |dynkinMart (driftStepProb d ε ξ)
          (fun z => max (inner ℝ q (toSpace z) -
            k * normMax (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)) 0) Y n| ≤
        max K.C_lin 0 * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange Y n).filter
            (fun z => (k : ℝ) * normMax (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) -
              normMax (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) < inner ℝ q (toSpace z)),
          (localTime Y n z : ℝ)) + Real.log n) := by
    intro q hq k hk
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
    by_cases hz0 : z = 0
    · subst hz0
      have h0 : CERW.Support.Norm.CoarseCrossing.capDirection
          (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (0 : Site d) = 0 := by
        unfold CERW.Support.Norm.CoarseCrossing.capDirection
        simp [CERW.Support.Occupation.toSpace_zero]
      rw [h0]
      have hf : (fun z : Site d => max (inner ℝ (0 : EuclideanSpace ℝ (Fin d)) (toSpace z) -
          k * normMax (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)) 0) = fun _ => 0 := by
        funext z
        rw [inner_zero_left, hΛ]
        simp
      rw [hf]
      have hz0' : dynkinMart (driftStepProb d ε ξ) (fun _ : Site d => (0 : ℝ)) Y n = 0 := by
        simp [dynkinMart, stepMean]
      rw [hz0', abs_zero]
      exact mul_nonneg (le_max_right _ _) (add_nonneg (Real.sqrt_nonneg _) hL0)
    · have hmem : CERW.Support.Norm.CoarseCrossing.capDirection
          (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) z ∈
          radialDirections d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) n := by
        unfold radialDirections
        refine Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hz0⟩, ?_⟩
        unfold CERW.Support.Norm.CoarseCrossing.capDirection
        rw [smul_smul, div_eq_mul_inv]
      refine (hlin _ hmem k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
      exact add_nonneg (Real.sqrt_nonneg _) hL0
  have key := hmain ξ hξ hξ0 n hn2 Y hty.1 hty.2 hvec' hlin' b hb
  rw [hc, div_one] at key
  have hsup : ((departureRange Y n).filter
      (fun z => b ≤ ‖toSpace z‖)).sup (localTime Y n) = outerMax Y n b := by
    unfold outerMax
    simp only [norm_toSpace]
  rw [hsup] at key
  exact key

/-! ## The outer radius and the profile of the local times -/

/-- **The outer radius.** The deterministic outer radius estimate: for `d ≥ 2` and `0 < ε < 1/d`,
a path that has the path facts, the inner radius estimate and the crossing bound has
`R_out(n) ≤ r_n + C (log n)^{d+1}` for `d ≥ 3` and `R_out(n) ≤ r_n + C √r_n (log n)^{5/2}` for
`d = 2`, for all large `n`. -/
private theorem outer_bound (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    (C₀ C₁ Cin Ccr : ℝ) (hCin : 0 < Cin) (hCcr : 0 < Ccr) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      PathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n → CrossOK d Ccr Y n →
      maxRadius Y n ≤ radius d ε n + C * (if d = 2 then Real.sqrt (radius d ε n) *
        Real.log n ^ ((5 : ℝ) / 2) else Real.log n ^ ((d : ℝ) + 1)) := by
  by_cases h2 : d = 2
  · obtain ⟨C, hC, n₀, h⟩ := outer_core_planar h2 CERW.Support.Outer.near_far_holds hε hεd
      C₀ C₁ Cin Ccr hCin hCcr
    exact ⟨C, hC, n₀, fun Y n hn h1 h3 h4 => by rw [if_pos h2]; exact h Y n hn h1 h3 h4⟩
  · obtain ⟨C, hC, n₀, h⟩ := outer_core_high (by omega) (newton_conv (by omega))
      CERW.Support.Outer.near_far_holds hε hεd C₀ C₁ Cin Ccr hCin hCcr
    exact ⟨C, hC, n₀, fun Y n hn h1 h3 h4 => by rw [if_neg h2]; exact h Y n hn h1 h3 h4⟩

/-- **The local times.** The deterministic profile estimate: for `d ≥ 2` and `ε > 0`, a path that
has the path facts, the inner radius estimate and the outer radius bound with constant `C_out` has,
for all large `n` and at every site `x`, `|ℓ_n(x) - 2dε (r_n - |x|)_+| ≤ C √r_n (log n)^{3/2}`
for `d = 2` and `≤ C √(r_n log n)` for `d ≥ 3`. -/
private theorem local_profile (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    (C₀ C₁ Cin Co : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hCin : 0 < Cin) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      PathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n →
      maxRadius Y n ≤ radius d ε n + Co * (if d = 2 then Real.sqrt (radius d ε n) *
        Real.log n ^ ((5 : ℝ) / 2) else Real.log n ^ ((d : ℝ) + 1)) →
      ∀ x : Site d, |(localTime Y n x : ℝ) - 2 * d * ε * max (radius d ε n - euclidNorm x) 0| ≤
        C * (if d = 2 then Real.sqrt (radius d ε n) * Real.log n ^ ((3 : ℝ) / 2)
          else Real.sqrt (radius d ε n * Real.log n)) := by
  by_cases h2 : d = 2
  · obtain ⟨C, hC, n₀, h⟩ := local_core_planar h2 CERW.Support.Outer.near_far_holds hε hεd
      C₀ C₁ Cin Co hC₀ hC₁ hCin
    exact ⟨C, hC, n₀, fun Y n hn h1 h3 h4 x => by
      rw [if_pos h2]
      exact h Y n hn h1 h3 (by rw [if_pos h2] at h4; exact h4) x⟩
  · obtain ⟨C, hC, n₀, h⟩ := local_core_high (d := d) (by omega) hε C₀ C₁ Cin Co hC₀ hC₁ hCin
    exact ⟨C, hC, n₀, fun Y n hn h1 h3 h4 x => by
      rw [if_neg h2]
      exact h Y n hn h1 h3 (by rw [if_neg h2] at h4; exact h4) x⟩

/-! ## The deterministic implication -/

/-- **The bracket bounds on the seven estimates.** Let `d ≥ 2` and `0 < ε < 1/d`, let `K` be
constants of the seven estimates of Section 5.1, and let `Cc > 0` be a constant of the contact
estimate. There are `0 < c₀ ≤ C₀`, `C > 0` and `n₀` such that, for every field `ξ` of subgradients
of the Euclidean norm with `ξ 0 = 0`, every projection `P` in the second family of directions of
the event, every path `Y` with the typing of the model and every `n ≥ n₀`: if `Y` satisfies the
seven estimates at time `n` and the contact estimate with constant `Cc`, then the normalized
brackets of `lem:separated-brackets` satisfy `c₀ ≤ ⟨S^i⟩_n ≤ C₀` and
`|⟨S^i, S^j⟩_n| ≤ C r_n^{-1/4}` for `i ≠ j`. The constants depend only on `d`, `ε`, `K` and `Cc`.
Neither the outer radius, nor the profile of the local times, nor the bracket bounds are
assumed. -/
theorem brackets_of_estimates7 (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    (K : EventConstants) {Cc : ℝ} (hCc : 0 < Cc) :
    ∃ c₀ C₀ C : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧ ∃ n₀ : ℕ,
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (Y : ℕ → Site d) (n : ℕ),
        n₀ ≤ n → PathTyping d Y →
        Estimates7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K P Y n →
        ContactBound d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε Cc Y n →
        BracketBounds hd ε c₀ C₀ C Y n := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₀, C₁, hC₀, hC₁, hPF⟩ := pathFacts_of_estimates7 hd hε K
  obtain ⟨Cin, hCin, nin, hIn⟩ := inner_of_estimates7 hd hε K hCc
  obtain ⟨Ccr, hCcr, hCr⟩ := crossOK_of_estimates7 hd hε hεd K
  obtain ⟨Co, hCo, no, hOut⟩ := outer_bound hd hε hεd C₀ C₁ Cin Ccr hCin hCcr
  obtain ⟨Cl, hCl, nl, hLoc⟩ := local_profile hd hε hεd C₀ C₁ Cin Co hC₀ hC₁ hCin
  obtain ⟨c₀, C₀', C, hc₀, hcC, hC, nb, hbr⟩ := brackets_core hd hε hεd (P := Cl) hCl.le
  refine ⟨c₀, C₀', C, hc₀, hcC, hC, max (max (max nin no) (max nl nb)) 3, ?_⟩
  intro ξ hξ hξ0 P Y n hn hty hE hct
  have hnin : nin ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hn)
  have hno : no ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hn)
  have hnl : nl ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hn)
  have hnb : nb ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hn)
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < n))]
    have := Real.exp_one_lt_d9
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  have hr0 : 0 ≤ radius d ε n := (radius_pos hd1 hε (by omega)).le
  have hP := hPF ξ hξ hξ0 P Y n (by omega) hty hE
  have hI := innerOK_of_innerConclusion (hIn ξ hξ hξ0 P Y n hnin hty hE hct)
  have hC' := hCr ξ hξ hξ0 P Y n (by omega) hty hE
  have hmax := hOut Y n hno hP hI hC'
  have hloc := hLoc Y n hnl hP hI hmax
  have hprof : ∀ x : Site d,
      |(localTime Y n x : ℝ) - 2 * d * ε * max (radius d ε n - euclidNorm x) 0| ≤
        Cl * (Real.sqrt (radius d ε n) * Real.log n ^ ((3 : ℝ) / 2)) := by
    intro x
    refine (hloc x).trans ?_
    split_ifs with h2
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_left (sqrt_mul_le_sqrt_mul_rpow hr0 hlog) hCl.le
  exact hbr n hnb Y hprof

/-! ## The lemma on the event of Section 5.1 -/

/-- **`lem:separated-brackets` on the event `Ω_n` of Section 5.1 with `p = 10`.** Let `d ≥ 2` and
`0 < ε < 1/d`. There are constants `K` of the event `E7`, `0 < c₀ ≤ C₀`, `C`, `C_p` and `n₀` such
that for every field `ξ` of subgradients of the Euclidean norm with `ξ 0 = 0`, every probability
space carrying a walk `X` with drift field `ξ`, and every `n ≥ n₀`:

* the complement of `E7` has probability at most `C_p n^{-10}`, and the sample points at which the
  path is not a nearest-neighbour path from the origin have probability zero;
* at every legal sample point of `E7` the bracket bounds hold;
* the same holds at every sample point of the event `E7` of the legal carrier of `X`, a walk with
  the same drift field that coincides with `X` almost surely and is legal at every sample point.

The inclusion is that of the lemma: the bracket bounds hold on the event, not only outside a set
of small probability. -/
theorem separated_brackets_on_E7 (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) :
    ∃ (K : EventConstants) (c₀ C₀ C Cp : ℝ) (n₀ : ℕ), 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧ 0 < Cp ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
        (μ (E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n)ᶜ ≤
            ENNReal.ofReal (Cp * (n : ℝ) ^ (-(10 : ℝ))) ∧
          μ (legalSet X)ᶜ = 0 ∧
          ∀ ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n, ω ∈ legalSet X →
            BracketBounds hd ε c₀ C₀ C (fun j => X j ω) n) ∧
        (μ (E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K
            (legalCarrier (by omega : 1 ≤ d) X) n)ᶜ ≤ ENNReal.ofReal (Cp * (n : ℝ) ^ (-(10 : ℝ))) ∧
          ∀ ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K
              (legalCarrier (by omega : 1 ≤ d) X) n,
            BracketBounds hd ε c₀ C₀ C (fun j => legalCarrier (by omega : 1 ≤ d) X j ω) n) := by
  obtain ⟨K, Cc, Cin, hCc, hCin, n₀, hn₀, hmain⟩ :=
    section5_euclid_localization.{u} hd hε hεd (p := 10) (by norm_num)
  obtain ⟨c₀, C₀, C, hc₀, hcC, hC, nb, hbr⟩ := brackets_of_estimates7 hd hε hεd K hCc
  refine ⟨K, c₀, C₀, C, Cc, max n₀ nb, hc₀, hcC, hC, hCc, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hn₀n : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hnbn : nb ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨⟨hprob, hE⟩, hleg, -, -, htyp, hprobc, hEc⟩ := hmain ξ hξ hξ0 μ X hX n hn₀n
  refine ⟨⟨hprob, hleg, fun ω hω hL => ?_⟩, hprobc, fun ω hω => ?_⟩
  · exact hbr ξ hξ hξ0 (projectionAt (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n)
      (fun j => X j ω) n hnbn hL hω (hE ω hω hL).1
  · exact hbr ξ hξ hξ0 (projectionAt (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n)
      (fun j => legalCarrier (by omega : 1 ≤ d) X j ω) n hnbn (htyp ω) hω (hEc ω hω).1

/-- **`lem:separated-brackets` on the event for the centrally excited random walk.** The first
part of `separated_brackets_on_E7` for a process `X` with `IsCERW μ ε X`, whose drift field is
`x ↦ u_x = x / |x|`: for all `n ≥ n₀`, the complement of `E7` has probability at most
`C_p n^{-10}`, the illegal sample points have probability zero, and at every legal sample point of
`E7` the bracket bounds hold. -/
theorem separated_brackets_on_E7_of_isCERW (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) :
    ∃ (K : EventConstants) (c₀ C₀ C Cp : ℝ) (n₀ : ℕ), 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧ 0 < Cp ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        μ (E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε (fun z => unitDir (toSpace z)) K X n)ᶜ ≤
            ENNReal.ofReal (Cp * (n : ℝ) ^ (-(10 : ℝ))) ∧
          μ (legalSet X)ᶜ = 0 ∧
          ∀ ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε (fun z => unitDir (toSpace z)) K X n,
            ω ∈ legalSet X → BracketBounds hd ε c₀ C₀ C (fun j => X j ω) n := by
  obtain ⟨K, c₀, C₀, C, Cp, n₀, hc₀, hcC, hC, hCp, h⟩ :=
    separated_brackets_on_E7.{u} hd hε hεd
  obtain ⟨-, hsub, hξ0, -⟩ := CERW.Support.Main.euclidean_norm_hypotheses (d := d) hεd
  refine ⟨K, c₀, C₀, C, Cp, n₀, hc₀, hcC, hC, hCp, fun μ _ X hX n hn => ?_⟩
  exact (h _ hsub hξ0 μ X ((CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).1 hX) n hn).1

end CERW.Support.Lower.SeparatedBracketsEvent
