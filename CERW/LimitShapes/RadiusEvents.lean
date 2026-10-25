module

public import CERW.LimitShapes.Profile
public import CERW.LimitShapes.ContactEvent

@[expose] public section

/-!
# Outer radius on the common event

The local-time approximation, inner estimate and distance crossing estimate on the
common event imply the deterministic outer-radius bound of Proposition `prop:stronger-outer`.
The constant and threshold are uniform over subgradients and paths.
-/

open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes.RadiusEvents

open CERW CERW.LimitShapes CERW.Support.Norm.ContactEvent
  CERW.Support.Norm.Section5Localization

open private radius from CERW.Support.Outer.OuterRadius
open private innerOK_of_innerConclusion from CERW.Support.Lower.SeparatedBracketsEvent

/-- The inner estimate, local-time approximation and crossing estimate on the common event
imply the outer-radius bound of Proposition `prop:stronger-outer`. -/
theorem outer_on_event {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) (K : CERW.LimitShapes.EventConstants)
    (hc : 0 < K.cCo) (hCo : 0 ≤ K.CCo) (hLoc : 0 ≤ K.CLoc)
    (hQuad : 0 ≤ K.CQuad) (hMart : 0 ≤ K.CMart) (hCross : 0 < K.CCross) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 →
          IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) →
        ξ 0 = 0 → ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n → PathTyping d X →
        EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n →
        maxRadius X n ≤ radius d ε n + C *
          (if d = 2 then Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)
            else Real.log n ^ ((d : ℝ) + 1)) := by
  obtain ⟨C₀, C₁, _, _, hFacts⟩ := Profile.localFacts_of_event hd hε hεd K hMart
  obtain ⟨Cin, hCin, ni, _, hInner⟩ :=
    inner_on_event hd hε hεd K hc hCo hLoc hQuad hMart
  obtain ⟨C, hC, no, hOuter⟩ :=
    Profile.outer_bound hd hε hεd C₀ C₁ Cin K.CCross hCin hCross
  refine ⟨C, hC, max (max ni no) 3, le_max_right _ _, ?_⟩
  intro ξ hξ hξ0 X n hn hty hE
  have hni : ni ≤ n := (le_max_left ni no).trans ((le_max_left _ _).trans hn)
  have hno : no ≤ n := (le_max_right ni no).trans ((le_max_left _ _).trans hn)
  have hn3 : 3 ≤ n := (le_max_right _ _).trans hn
  have hF := hFacts ξ hξ hξ0 X n (by omega) hty hE
  have hI := innerOK_of_innerConclusion (hInner ξ hξ hξ0 X n hni hty hE)
  have hCr := Profile.crossOK_of_distance hE.2.2.2.2.2
  exact hOuter X n hno hF hI hCr

/-- A common constant and threshold give the inner and outer radius estimates on the
common event, as in `prop:inner` and `prop:stronger-outer`. -/
theorem radius_bounds_on_event {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) (K : CERW.LimitShapes.EventConstants)
    (hc : 0 < K.cCo) (hCo : 0 ≤ K.CCo) (hLoc : 0 ≤ K.CLoc)
    (hQuad : 0 ≤ K.CQuad) (hMart : 0 ≤ K.CMart) (hCross : 0 < K.CCross) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 →
          IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) →
        ξ 0 = 0 → ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n → PathTyping d X →
        EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n →
        (|normInnerRadius (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) X n -
            scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n| ≤
          C * scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n *
            contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n) ∧
        maxRadius X n ≤ radius d ε n + C *
          (if d = 2 then Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)
            else Real.log n ^ ((d : ℝ) + 1)) := by
  obtain ⟨Ci, hCi, ni, _, hInner⟩ :=
    inner_on_event hd hε hεd K hc hCo hLoc hQuad hMart
  obtain ⟨Co, hCo', no, hno, hOuter⟩ :=
    outer_on_event hd hε hεd K hc hCo hLoc hQuad hMart hCross
  refine ⟨max Ci Co, lt_of_lt_of_le hCi (le_max_left _ _), max ni no,
    hno.trans (le_max_right _ _), ?_⟩
  intro ξ hξ hξ0 X n hn hty hE
  have hni : ni ≤ n := (le_max_left _ _).trans hn
  have hno' : no ≤ n := (le_max_right _ _).trans hn
  have hn3 : 3 ≤ n := hno.trans hno'
  have hr := CERW.LimitShapes.scale_pos (by omega : 1 ≤ d) isNorm_euclidean hε
    (by omega : 0 < n)
  have hrate := ContactEvent.contactRate_nonneg hr (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  constructor
  · exact (hInner ξ hξ hξ0 X n hni hty hE).1.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left Ci Co) hr.le) hrate)
  · refine (hOuter ξ hξ hξ0 X n hno' hty hE).trans (add_le_add le_rfl ?_)
    apply mul_le_mul_of_nonneg_right (le_max_right Ci Co)
    split_ifs
    · exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlog _)
    · exact Real.rpow_nonneg hlog _

end CERW.LimitShapes.RadiusEvents
