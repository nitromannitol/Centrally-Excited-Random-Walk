import CERW.Support.Outer.Radius.PlanarProbes

/-!
# Planar Exterior

The planar probe estimates bound the local times outside the inner ball. Combining the two bounds
gives the planar exterior estimate.
The section label `sec:outer-planar`
refers to the earlier source `paper/limit-shapes.tex`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

section

open Filter LatticeProb

/-- Steps 1 to 3 of `sec:outer-planar` (the planar case): with `w = R_out - b + 2√d` at most `r /
log n`,
the local times outside the inner ball are within `C √(r log n)` of the potential of `E`, and the
positive potential of `E` in the annulus is at most `C ((r log n)^{1/4} √w + √(r log n))`. -/
theorem planar_exterior (hd : d = 2) (hnear : near_far) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) (C₀ C₁ Cin Cm : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      LocalPathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n → MassOK d ε Cm Y n →
      maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d ≤ radius d ε n / Real.log n →
      (∀ x : Site d, innerRadius Y n ≤ euclidNorm x → euclidNorm x ≤ 3 * n →
        |(localTime Y n x : ℝ) - potential d ε (cellSet Y n \
            Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (innerRadius Y n)) (toSpace x)| ≤
          C * Real.sqrt (radius d ε n * Real.log n)) ∧
      (∀ y : EuclideanSpace ℝ (Fin d), innerRadius Y n ≤ ‖y‖ →
        ‖y‖ ≤ maxRadius Y n + 2 * Real.sqrt d →
        positivePotential d ε (cellSet Y n \ Metric.ball 0 (innerRadius Y n)) y ≤
          C * ((radius d ε n * Real.log n) ^ ((1 : ℝ) / 4) *
            Real.sqrt (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) +
            Real.sqrt (radius d ε n * Real.log n))) := by
  subst hd
  obtain ⟨K2, hK20, hfirst⟩ := pl_first hε C₀ C₁
  obtain ⟨Ci, hCi0, hCin⟩ : ∃ Ci : ℝ, 0 ≤ Ci ∧ Cin ≤ Ci := ⟨|Cin|, abs_nonneg _, le_abs_self _⟩
  obtain ⟨Cm', hCm0, hCm⟩ : ∃ Cm' : ℝ, 0 ≤ Cm' ∧ Cm ≤ Cm' := ⟨|Cm|, abs_nonneg _, le_abs_self _⟩
  obtain ⟨K', hK', hsecond⟩ := pl_second hnear hε hεd hK20 hCm0
  obtain ⟨θ, hθ0, hθ1, hθCi, hθC⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ Ci * θ ≤ 1 ∧
      2 * Ci * (4 * ε + 1) * θ ≤ 1 := by
    have hX : 0 ≤ 2 * Ci * (4 * ε + 1) := by positivity
    have hZ : 0 < 1 + Ci + 2 * Ci * (4 * ε + 1) := by linarith
    refine ⟨1 / (1 + Ci + 2 * Ci * (4 * ε + 1)), by positivity, ?_, ?_, ?_⟩
    · rw [div_le_one hZ]
      linarith
    · rw [mul_one_div, div_le_one hZ]
      linarith
    · rw [mul_one_div, div_le_one hZ]
      linarith
  obtain ⟨n₀, hn₀⟩ := pl_eventually hε (η := θ ^ 4) (by positivity)
  refine ⟨K2 + K', by positivity, n₀, fun Y n hn hP hI hM hw => ?_⟩
  obtain ⟨hn16, hlg4, hlg5, hrn⟩ := hn₀ n hn
  obtain ⟨hI1, -, hI3⟩ := hI
  rw [MassOK, qrate, if_pos rfl] at hM
  rw [qrate, if_pos rfl] at hI1 hI3
  have hRin := innerRadius_le (d := 2) (by norm_num) Y n
  have hlgpos : 0 < Real.log n := by linarith
  have hr0 : 0 < radius 2 ε n :=
    pos_of_mul_pos_right ((pow_pos hlgpos 5).trans_le hlg5) (by positivity)
  obtain ⟨hσ0, hσ2, hσ4, hrq⟩ := pl_scales hr0 hlgpos.le
  generalize Real.sqrt (Real.log n / radius 2 ε n) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) = σ
    at hI3 hσ0 hσ2 hσ4
  generalize Real.sqrt (Real.log n / radius 2 ε n) = q at hI1 hM hσ2 hrq
  generalize hb : innerRadius Y n = b at hI1 hM hRin hw ⊢
  generalize hR : maxRadius Y n = R at hRin hw ⊢
  generalize radius 2 ε n = r at hI1 hI3 hM hr0 hσ4 hrq hrn hlg5 hw ⊢
  generalize hlg : Real.log (n : ℝ) = lg at hlg4 hlg5 hσ4 hrq hw hlgpos ⊢
  have hq0 : 0 ≤ q := by
    rw [← hσ2]
    positivity
  have hP_eq : Real.sqrt (r * lg) = r * σ ^ 2 := by rw [hσ2, hrq]
  have hbr : |b - r| ≤ Ci * Real.sqrt (r * lg) := by
    calc |b - r| ≤ Cin * r * q := hI1
      _ ≤ Ci * r * q := by gcongr
      _ = Ci * Real.sqrt (r * lg) := by rw [← hrq]; ring
  obtain ⟨hσlg, hσ1, hb1, hb2, hPr, hlgP⟩ :=
    pl_numeric hθ0 hθ1 hCi0 hθCi hlg4 hr0 hσ0 hσ4 hlg5 hP_eq hbr
  have hs2 : 1 ≤ Real.sqrt ((2 : ℕ) : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have hw1 : R - b + 2 * Real.sqrt ((2 : ℕ) : ℝ) ≤ r / 4 :=
    hw.trans (div_le_div_of_nonneg_left hr0.le (by norm_num) hlg4)
  have hw2 : 1 ≤ R - b + 2 * Real.sqrt ((2 : ℕ) : ℝ) := by
    generalize Real.sqrt ((2 : ℕ) : ℝ) = s at hRin hs2 ⊢
    linarith
  have hR32 : R ≤ 3 * r / 2 := by
    generalize Real.sqrt ((2 : ℕ) : ℝ) = s at hw1 hs2
    linarith
  have hloc : ∀ z ∈ departureRange Y n,
      (localTime Y n z : ℝ) ≤ 4 * ε * max (r - euclidNorm z) 0 + Ci * r * σ := by
    intro z _
    have h := hI3 (toSpace z)
    rw [cellLocalTime_of_mem_cell Y n (toSpace_mem_cell z), norm_toSpace] at h
    have h' := (abs_le.mp h).2
    have e : (2 : ℝ) * ((2 : ℕ) : ℝ) * ε = 4 * ε := by norm_num
    rw [e] at h'
    have : Cin * r * σ ≤ Ci * r * σ := by gcongr
    linarith
  have hpt := hfirst Y n b r lg σ θ Ci hP hr0 hCi0 hσ0 hσ1 hσlg hθC hn16 hrn (by linarith)
    (hR ▸ hR32) hlg hlgP hP_eq hbr hloc
  have hb0 : 0 < b := by linarith
  refine ⟨fun x hbx hx3 => ?_, fun y hy1 hy2 => ?_⟩
  · rw [← pl_split Y n hb hb0 (y := toSpace x) (by rwa [norm_toSpace])]
    calc _ ≤ K2 * Real.sqrt (r * lg) := hpt x hbx hx3
      _ ≤ (K2 + K') * Real.sqrt (r * lg) := by gcongr; linarith
  · have hvolE : (volume (cellSet Y n \ Metric.ball 0 b)).toReal ≤
        Cm' * r * Real.sqrt (r * lg) := by
      calc _ ≤ Cm * r ^ 2 * q := hM
        _ ≤ Cm' * r ^ 2 * q := by gcongr
        _ = Cm' * r * Real.sqrt (r * lg) := by rw [← hrq]; ring
    have hlog3 : Real.log (3 * r + 2) ≤ Real.sqrt (r * lg) := by
      refine le_trans ?_ hlgP
      rw [← hlg]
      exact Real.log_le_log (by linarith) (by linarith)
    refine (hsecond Y n b R _ r lg hb hR rfl hb0 hb1 hb2 hw2 hw1 (by linarith) hrn hn16
      hlgpos.le (by linarith) hlog3 hvolE hpt y hy1 hy2).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)


/-! ### The maximum principle for the planar potential -/

end

end CERW.Support.Outer.Radius
