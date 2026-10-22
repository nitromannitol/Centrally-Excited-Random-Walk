import CERW.LimitShapes.Event

/-!
# The contact estimate from the local approximation

The convolution proof of the contact estimate needs the approximation clause of
`lem:local`, the coarse upper bounds, and the local martingale bound. This form does
not require bounds on interval local times.
-/

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes

open CERW CERW.Support.Statements CERW.Support.Norm CERW.Support.Norm.ContactShared
  CERW.Support.Norm.ContactAssembly CERW.Support.Norm.ContactEvent

open private abs_le_add_of_abs_add_le cell_modulus_of_path
  from CERW.Support.Norm.ContactEvent

variable {d : ℕ}

/-- The deterministic contact estimate using only the local approximation from `lem:local`. -/
theorem contact_bound_of_approximation_inputs (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε) (c_co C_co C_loc C_B : ℝ) (hC_co : 0 ≤ C_co)
    (hC_loc : 0 ≤ C_loc) (hC_B : 0 ≤ C_B) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n → PathTyping d X →
        CoarseBounds d Ψ ε c_co C_co X n → CERW.LimitShapes.LocalApproximation Ψ ε C_loc X n →
        LocalMartEstimate d ε ξ C_B X n →
        ∀ y₀ : EuclideanSpace ℝ (Fin d), Ψ y₀ = normInnerRadius Ψ X n →
          y₀ ∈ closure (cellSet X n)ᶜ →
          normPotential d ε Ψ (cellSet X n) y₀ ≤ C * scale d Ψ ε n * contactRate d Ψ ε n := by
  have hgeom : norm_potential_geometry := @CERW.Support.Norm.norm_potential_geometry
  have hball : norm_ball_potential := @CERW.Support.Norm.norm_ball_potential
  have hd1 : 1 ≤ d := by omega
  obtain ⟨h, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  have hB : BregmanSumBound d Ψ := ContactBregman.bregmanSumBound_of hd hΨ
    (fun φ h1 h2 h3 => ContactWeakLap.inner_gradient_integral_nonpos hΨ h1 h2 h3)
    (ContactCellTest.cellTestBound hd hΨ)
  have hconv : ConvBound d Ψ ε := ContactConv.convBound hd hΨ hε hgeom hball
  obtain ⟨C_pt, hCpt, hpt⟩ :=
    ContactPointwise.exists_abs_localTime_sub_normPotential_add_driftDynkin_le.{0} hd hΨ hB hK
  obtain ⟨C_mod, hCmod, hmod⟩ := ContactModulus.exists_normPotential_cell_modulus hd hΨ
  have hC₁ : 0 ≤ C_pt * (1 + ε) + C_B := by positivity
  have hC₃ : 0 ≤ C_mod * ε * (1 + Real.log (1 + Real.sqrt d)) := by
    have : 0 ≤ Real.log (1 + Real.sqrt d) :=
      Real.log_nonneg (by linarith [Real.sqrt_nonneg (d : ℝ)])
    positivity
  have hV : 0 < normBallVolume Ψ := normBallVolume_pos' hd1 hΨ
  have hrpos : ∀ n : ℕ, 0 < n → 0 < scale d Ψ ε n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    exact Real.rpow_pos_of_pos (by positivity) _
  -- the pointwise bound on `ℓ_n - U` from the decomposition and the local martingale bound
  have hfine : ∀ (X : ℕ → Site d) (n : ℕ), 2 ≤ n → PathTyping d X →
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      LocalMartEstimate d ε ξ C_B X n →
      ∀ y : Site d, euclidNorm y ≤ 3 * n →
        |(localTime X n y : ℝ) - normPotential d ε Ψ (cellSet X n) (toSpace y)| ≤
          (C_pt * (1 + ε) + C_B) * (Real.sqrt ((∑ j ∈ Finset.range n,
            (1 + euclidNorm (X j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
              Real.log ((n : ℝ) + 2)) := by
    intro X n hn2 ⟨hX0, hsteps⟩ ξ hξ hξ0 hlm y hy
    have hnorm : ∀ j, euclidNorm (X j) ≤ j :=
      CERW.Support.Occupation.euclidNorm_le_of_steps X hX0 hsteps
    have hW : (∑ j ∈ Finset.range n, (1 + euclidNorm (X j - y)) ^ (2 - 2 * (d : ℝ))) =
        ∑ x ∈ departureRange X n,
          (localTime X n x : ℝ) * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)) :=
      CERW.Support.LocalTime.sum_range_eq_sum_localTime X n
        (fun x => (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)))
    have hW0 : 0 ≤ ∑ x ∈ departureRange X n,
        (localTime X n x : ℝ) * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (Nat.cast_nonneg _)
        (Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg (x - y)]) _)
    have hL0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hLL : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by linarith)
    have hmart : |CERW.Support.Drift.driftDynkin ε ξ (fun z => latticeKernel d (z - y))
          (fun j (_ : Unit) => X j) n ()| ≤
        C_B * (Real.sqrt ((∑ j ∈ Finset.range n,
          (1 + euclidNorm (X j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2)) := by
      rw [← CERW.Support.Drift.dynkinMart_driftStepProb_eq_driftDynkin hd1 ε ξ
        (fun z => latticeKernel d (z - y)) (fun j (_ : Unit) => X j) n ()]
      refine (hlm y hy).trans (mul_le_mul_of_nonneg_left (add_le_add ?_ hLL) hC_B)
      rw [hW]
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hLL hW0)
    exact abs_le_add_of_abs_add_le (by positivity) (Real.sqrt_nonneg _)
      (hpt ε hε.le ξ hξ hξ0 (fun j (_ : Unit) => X j) () hX0 hnorm n (by omega) y hy) hmart
  rcases Nat.lt_or_ge d 3 with hd3 | hd3
  · have hd2 : d = 2 := by omega
    obtain ⟨C_G, hCG, hG⟩ := ContactPlanar.contact_bound_two hd2 hΨ hε hconv
      (C_pt * (1 + ε) + C_B) C_loc (C_mod * ε * (1 + Real.log (1 + Real.sqrt d))) C_co C_co
      hC₁ hC_loc hC₃ hC_co hC_co
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 3 / (2 * (d : ℝ) * ε * normBallVolume Ψ) := ⟨_, rfl⟩
    have hapos : 0 < a := by
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      rw [ha]
      positivity
    have hrn : ∀ n : ℕ, scale d Ψ ε n = (a * (n : ℝ)) ^ ((1 : ℝ) / 3) := by
      intro n
      have h3 : (d : ℝ) + 1 = 3 := by
        rw [hd2]
        norm_num
      show (((d : ℝ) + 1) * n / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / ((d : ℝ) + 1)) = _
      rw [h3, ha]
      congr 1
      ring
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
      ((eventually_cube_root_scale hapos (3 * C_co) (6 * Real.sqrt d)).and
        (eventually_ge_atTop 2))
    refine ⟨2 * C_G, by positivity, n₀, ?_⟩
    intro ξ hξ hξ0 X n hn hty hcoarse hlocal hlm y₀ hy₀ hcl
    obtain ⟨⟨hr1, hrlog, hrlarge⟩, hn2⟩ := hn₀ n hn
    obtain ⟨hX0, hsteps⟩ := hty
    have hnorm : ∀ j, euclidNorm (X j) ≤ j :=
      CERW.Support.Occupation.euclidNorm_le_of_steps X hX0 hsteps
    obtain ⟨-, -, -, hM, -, hRad⟩ := hcoarse
    have hcrude : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ ≤ 2 * n →
        |cellLocalTime X n v - normPotential d ε Ψ (cellSet X n) v| ≤
          C_loc * Real.log n + C_loc * (Real.sqrt (maxLocalTime X n) * Real.log n) := by
      intro v hv
      have := hlocal v hv
      rwa [if_pos hd2] at this
    have hmodω := cell_modulus_of_path hd hε.le hCmod hmod X n hn2 hnorm
    have hr1' : 1 ≤ scale d Ψ ε n := by
      rw [hrn n]
      exact hr1
    have hrlog' : Real.log ((n : ℝ) + 2) ^ 4 ≤ scale d Ψ ε n := by
      rw [hrn n]
      exact hrlog
    have hlarge : 3 * C_co * scale d Ψ ε n + 6 * Real.sqrt d ≤ n := by
      rw [hrn n]
      exact hrlarge
    have hU := hG X n (scale d Ψ ε n) hn2 hX0 hnorm hr1' hrlog' hlarge hM hRad
      (hfine X n hn2 ⟨hX0, hsteps⟩ ξ hξ hξ0 hlm) hcrude hmodω y₀ hy₀ hcl
    have hr := hrpos n (by omega)
    have hlogn := log_pos_of_two_le hn2
    have hL := log_add_two_le hn2
    have hsq : Real.sqrt (scale d Ψ ε n * Real.log ((n : ℝ) + 2)) ≤
        2 * Real.sqrt (scale d Ψ ε n * Real.log n) := by
      have h4 : scale d Ψ ε n * Real.log ((n : ℝ) + 2) ≤
          2 ^ 2 * (scale d Ψ ε n * Real.log n) := by
        have : scale d Ψ ε n * Real.log ((n : ℝ) + 2) ≤ scale d Ψ ε n * (2 * Real.log n) :=
          mul_le_mul_of_nonneg_left hL hr.le
        nlinarith [mul_nonneg hr.le hlogn.le]
      calc Real.sqrt (scale d Ψ ε n * Real.log ((n : ℝ) + 2))
          ≤ Real.sqrt (2 ^ 2 * (scale d Ψ ε n * Real.log n)) := Real.sqrt_le_sqrt h4
        _ = 2 * Real.sqrt (scale d Ψ ε n * Real.log n) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    have hsn : 0 ≤ Real.sqrt (scale d Ψ ε n * Real.log n) := Real.sqrt_nonneg _
    have hqn : contactRate d Ψ ε n = Real.sqrt (Real.log n / scale d Ψ ε n) := by
      rw [contactRate, if_pos hd2]
    rw [hqn]
    calc normPotential d ε Ψ (cellSet X n) y₀
        ≤ C_G * Real.sqrt (scale d Ψ ε n * Real.log ((n : ℝ) + 2)) := hU
      _ ≤ C_G * (2 * Real.sqrt (scale d Ψ ε n * Real.log n)) :=
          mul_le_mul_of_nonneg_left hsq hCG.le
      _ = 2 * C_G * Real.sqrt (scale d Ψ ε n * Real.log n) := by ring
      _ = 2 * C_G * (scale d Ψ ε n * Real.sqrt (Real.log n / scale d Ψ ε n)) := by
          rw [mul_sqrt_div_eq hr]
      _ = 2 * C_G * scale d Ψ ε n * Real.sqrt (Real.log n / scale d Ψ ε n) := by ring
  · obtain ⟨C_H, hCH, hH⟩ := ContactHigh.contact_bound_three_le hd3 hΨ hε hconv
      (C_pt * (1 + ε) + C_B) (C_mod * ε * (1 + Real.log (1 + Real.sqrt d))) hC₁ hC₃
    obtain ⟨n₁, hn₁⟩ := exists_nat_ge (4 * Real.sqrt d)
    refine ⟨2 * C_H, by positivity, max n₁ 2, ?_⟩
    intro ξ hξ hξ0 X n hn hty hcoarse hlocal hlm y₀ hy₀ hcl
    have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
    have hn4 : 4 * Real.sqrt d ≤ n :=
      hn₁.trans (by exact_mod_cast (le_max_left _ _).trans hn)
    obtain ⟨hX0, hsteps⟩ := hty
    have hnorm : ∀ j, euclidNorm (X j) ≤ j :=
      CERW.Support.Occupation.euclidNorm_le_of_steps X hX0 hsteps
    have hmodω := cell_modulus_of_path hd hε.le hCmod hmod X n hn2 hnorm
    have hU := hH X n hn2 hn4 hX0 hnorm
      (hfine X n hn2 ⟨hX0, hsteps⟩ ξ hξ hξ0 hlm) hmodω y₀ hy₀ hcl
    have hr := hrpos n (by omega)
    have hlogn := log_pos_of_two_le hn2
    have hL := log_add_two_le hn2
    have hqn : contactRate d Ψ ε n = Real.log n / scale d Ψ ε n := by
      rw [contactRate, if_neg (by omega)]
    rw [hqn]
    calc normPotential d ε Ψ (cellSet X n) y₀
        ≤ C_H * Real.log ((n : ℝ) + 2) := hU
      _ ≤ C_H * (2 * Real.log n) := mul_le_mul_of_nonneg_left hL hCH.le
      _ = 2 * C_H * (scale d Ψ ε n * (Real.log n / scale d Ψ ε n)) := by
          field_simp
      _ = 2 * C_H * scale d Ψ ε n * (Real.log n / scale d Ψ ε n) := by ring

end CERW.LimitShapes
