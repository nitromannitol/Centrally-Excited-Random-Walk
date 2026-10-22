import CERW.LimitShapes.EventConsequences
import CERW.Support.Lower.SeparatedBracketsEvent

/-!
# Outer radius and local-time profiles on the common event

The coarse bounds, potential approximation and local martingale estimate on the
common event of Section `sec:norm-event` give the local-time inputs. Combining
these with the inner-radius and crossing estimates gives the outer-radius bound
of Proposition `prop:stronger-outer` and the uniform local-time profile of
Theorem `thm:fluctuations` (iii), as proved in Section `sec:global-profile`.
-/

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes.Profile

open CERW CERW.LimitShapes CERW.Support.Norm.ContactEvent
  CERW.Support.Norm.Section5Localization

open private LocalPathFacts LocalPathFacts.mk radius braSum tk_radius_eq CrossOK
  outerMax InnerOK outer_core_high outer_core_planar local_core_high local_core_planar newton_conv
  from CERW.Support.Outer.OuterRadius
open private scale_eq_radius glob_arith abs_le_of_abs_add_le innerOK_of_innerConclusion
  from CERW.Support.Lower.SeparatedBracketsEvent
open private sqrt_mul_le_sqrt_mul_rpow from CERW.Support.Lower.SeparatedBrackets

variable {d : ℕ}

/-- The local-time inputs obtained from the new common event. -/
theorem localFacts_of_event (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    (K : CERW.LimitShapes.EventConstants) (hCMart : 0 ≤ K.CMart) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (Y : ℕ → Site d) (n : ℕ),
        2 ≤ n → PathTyping d Y →
        EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K Y n →
        LocalPathFacts d ε C₀ C₁ Y n := by
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
  have hell : ∀ i : Fin d, ε * ‖coordVec i‖ < 1 / (d : ℝ) := by
    intro i
    simpa only [coordVec, PiLp.norm_single, norm_one, mul_one] using hεd
  obtain ⟨Cw, hCw, hweight⟩ := localMartingaleBound_to_weight hd hΨ hε hell hCMart
  set Cco : ℝ := max K.CCo 0 with hCco
  set Cl : ℝ := max K.CLoc 0 with hCl
  set Cm : ℝ := max Cw 0 with hCm
  set Cv : ℝ := max 0 0 with hCv
  have hCco0 : 0 ≤ Cco := le_max_right _ _
  have hCl0 : 0 ≤ Cl := le_max_right _ _
  have hCm0 : 0 ≤ Cm := le_max_right _ _
  have hCv0 : 0 ≤ Cv := le_max_right _ _
  have hCp1 : 0 ≤ C_pt * (1 + ε) := by positivity
  refine ⟨Cco * a + 1, Cl + (C_pt * (1 + ε) + Cm) + Cv + 1, by positivity, by positivity, ?_⟩
  intro ξ hξ hξ0 Y n hn2 hty hE
  obtain ⟨hco, hloc, _, _, hlm0, _⟩ := hE
  have hlm := hweight ξ hξ hξ0 Y n hn2 hlm0
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
  have hsc : K.CCo * scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n ≤
      (Cco * a + 1) * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    rw [hrn]
    have h1 : K.CCo * (a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ≤
        Cco * (a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) :=
      mul_le_mul_of_nonneg_right (le_max_left K.CCo 0) (mul_nonneg ha.le hN)
    nlinarith
  refine LocalPathFacts.mk hY0 hsteps (hM.trans hsc) (hR.trans hsc) (fun y hy => ?_)
    (fun x hx => ?_)
  · -- the global approximation of the local times by the potential
    have h := hloc y hy
    rw [normPotential_norm_eq hd1] at h
    have hS0 : 0 ≤ (if d = 2 then Real.sqrt (maxLocalTime Y n) * Real.log (n : ℝ)
        else Real.sqrt (maxLocalTime Y n * Real.log (n : ℝ))) := by
      split_ifs
      · exact mul_nonneg (Real.sqrt_nonneg _) hL0
      · exact Real.sqrt_nonneg _
    refine h.trans ?_
    have hC1 : K.CLoc ≤ Cl + (C_pt * (1 + ε) + Cm) + Cv + 1 :=
      (le_max_left K.CLoc 0).trans (by linarith)
    have hC1' : 0 ≤ Cl + (C_pt * (1 + ε) + Cm) + Cv + 1 := by positivity
    split_ifs with h2
    · have := glob_arith (c := K.CLoc) (C := Cl + (C_pt * (1 + ε) + Cm) + Cv + 1)
        (lg := Real.log (n : ℝ)) (lg2 := Real.log ((n : ℝ) + 2))
        (S := Real.sqrt (maxLocalTime Y n) * Real.log (n : ℝ))
        (S2 := Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2)) hC1 hC1' hL0 hLL
        (by rw [if_pos h2] at hS0; exact hS0)
        (mul_le_mul_of_nonneg_left hLL (Real.sqrt_nonneg _))
      exact this
    · have := glob_arith (c := K.CLoc) (C := Cl + (C_pt * (1 + ε) + Cm) + Cv + 1)
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

/-- The local-time, inner-radius and crossing estimates give the outer-radius bound
in each dimension. -/
theorem outer_bound (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    (C₀ C₁ Cin Ccr : ℝ) (hCin : 0 < Cin) (hCcr : 0 < Ccr) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      LocalPathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n → CrossOK d Ccr Y n →
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
theorem local_profile (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    (C₀ C₁ Cin Co : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hCin : 0 < Cin) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      LocalPathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n →
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

/-- The distance crossing estimate implies its Euclidean outer-radius form. -/
theorem crossOK_of_distance {C : ℝ} {Y : ℕ → Site d} {n : ℕ}
    (h : DistanceCrossingBound (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) C Y n) :
    CrossOK d C Y n := by
  intro b hb
  unfold maxRadius
  refine Finset.sup'_le _ _ fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hne : ({v : EuclideanSpace ℝ (Fin d) | ‖v‖ ≤ b}).Nonempty := ⟨0, by simpa using hb⟩
  have hdist : ‖toSpace (Y j)‖ - b ≤
      Metric.infDist (toSpace (Y j)) {v : EuclideanSpace ℝ (Fin d) | ‖v‖ ≤ b} := by
    apply (Metric.le_infDist hne).mpr
    intro v hv
    change ‖v‖ ≤ b at hv
    have hn := norm_le_norm_sub_add (toSpace (Y j)) v
    rw [dist_eq_norm]
    linarith
  have hc := h n le_rfl b hb j hjn
  have hsup : exteriorLocalTime (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) Y n b =
      outerMax Y n b := by
    unfold exteriorLocalTime outerMax
    simp only [norm_toSpace]
  rw [hsup] at hc
  rw [norm_toSpace] at hdist
  linarith

/-- The global local-time profile on the new event, at the rate used for separated brackets. -/
theorem profile_on_event (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) (K : CERW.LimitShapes.EventConstants)
    (hc : 0 < K.cCo) (hCo : 0 ≤ K.CCo) (hLoc : 0 ≤ K.CLoc)
    (hQuad : 0 ≤ K.CQuad) (hMart : 0 ≤ K.CMart) (hCross : 0 < K.CCross) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 →
          IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) →
        ξ 0 = 0 → ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n → PathTyping d X →
        EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n →
        ∀ x : Site d, |(localTime X n x : ℝ) - 2 * d * ε * max (radius d ε n - euclidNorm x) 0| ≤
          C * (Real.sqrt (radius d ε n) * Real.log n ^ ((3 : ℝ) / 2)) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hFacts⟩ := localFacts_of_event hd hε hεd K hMart
  obtain ⟨Cin, hCin, ni, hni, hInner⟩ := inner_on_event hd hε hεd K hc hCo hLoc hQuad hMart
  obtain ⟨Co, hCo', no, hOuter⟩ := outer_bound hd hε hεd C₀ C₁ Cin K.CCross hCin hCross
  obtain ⟨Cl, hCl, nl, hLocal⟩ := local_profile hd hε hεd C₀ C₁ Cin Co hC₀ hC₁ hCin
  refine ⟨Cl, hCl, max (max ni no) (max nl 3), (le_max_right nl 3).trans (le_max_right _ _), ?_⟩
  intro ξ hξ hξ0 X n hn hty hE
  have hni' : ni ≤ n := (le_max_left ni no).trans ((le_max_left _ _).trans hn)
  have hno' : no ≤ n := (le_max_right ni no).trans ((le_max_left _ _).trans hn)
  have hnl' : nl ≤ n := (le_max_left nl 3).trans ((le_max_right _ _).trans hn)
  have hn3 : 3 ≤ n := (le_max_right nl 3).trans ((le_max_right _ _).trans hn)
  have hF := hFacts ξ hξ hξ0 X n (by omega) hty hE
  have hI := innerOK_of_innerConclusion (hInner ξ hξ hξ0 X n hni' hty hE)
  have hCr := crossOK_of_distance hE.2.2.2.2.2
  have hO := hOuter X n hno' hF hI hCr
  have hL := hLocal X n hnl' hF hI hO
  have hlog : 1 ≤ Real.log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < n))]
    have he := Real.exp_one_lt_d9
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  have hr : 0 ≤ radius d ε n := by
    rw [← scale_eq_radius]
    exact (scale_pos (by omega : 1 ≤ d) isNorm_euclidean hε (by omega)).le
  intro x
  refine (hL x).trans ?_
  split_ifs
  · exact le_rfl
  · exact mul_le_mul_of_nonneg_left (sqrt_mul_le_sqrt_mul_rpow hr hlog) hCl.le

end CERW.LimitShapes.Profile
