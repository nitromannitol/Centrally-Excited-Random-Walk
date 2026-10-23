import CERW.LimitShapes.SharpRadii.Arithmetic
import CERW.LimitShapes.Frozen.ExpDeviation

/-!
# Polynomial radius deviations

Theorem 1.3(i) follows from the common Euclidean event and the coarse quadratic
bracket, using Lemma 9.1(i) and the cubic identity for the moment radius.
-/

universe u

open MeasureTheory Filter Topology LatticeProb

namespace CERW.LimitShapes

open CERW CERW.Support.Law CERW.Support.Norm.ContactEvent SharpRadii
open CERW.Support.Norm.EuclideanCoarse
open private deviation_single exists_momentRadius_le_maxRadius_add
  exists_innerRadius_le_momentRadius_add rpow_third_pow eventually_ge_of_cube
  eventually_mul_log_rpow_le eventually_rpow_neg_le eventually_ge_log prob_ineq radii_events
  from CERW.Support.Lower.SharpRadii

/-- The common event and its coarse bracket imply Theorem 1.3(i). -/
theorem sharp_radii_from_common_event : CERW.Support.Statements.sharp_radii.{u} := by
  intro d hd
  subst hd
  intro ωd ε hε hεd r p hp
  have hw := unitBallVolume_pos 2
  have hrdef : ∀ n : ℕ, r n = ((((2 : ℕ) : ℝ) + 1) * n /
      (2 * ((2 : ℕ) : ℝ) * ε * unitBallVolume 2)) ^
        ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1)) := fun n => rfl
  have hr0 : ∀ n, 0 ≤ r n := fun n => by
    rw [hrdef n]
    exact Real.rpow_nonneg (by positivity) _
  have hr3 : ∀ n : ℕ, r n ^ 3 = 3 * n / (4 * ε * unitBallVolume 2) := by
    intro n
    rw [hrdef n, rpow_third_pow (by positivity)]
    push_cast
    ring
  have hscale : ∀ n, scale 2 (fun v => ‖v‖) ε n = r n := by
    intro n
    rw [scale, normBallVolume_euclidean, hrdef n]
  obtain ⟨K, _, hk, _, _, _, _, _, Cf, hCf, nf, hnf, hprob⟩ :=
    EuclideanEvent.exists_euclidean_event.{u} (by norm_num) hε hεd (p + 1) (by linarith)
  let a := (4 * ε * unitBallVolume 2 / 3) / K.CCo ^ 3
  have ha : 0 < a := by dsimp [a]; positivity
  let θ := Real.sqrt (a / 18)
  have hθ : 0 < θ := Real.sqrt_pos.mpr (by positivity)
  have hθa : θ ^ 2 = a / 18 := Real.sq_sqrt (by positivity)
  let c₀ := (θ ^ 2 * a / 2) * K.CCo ^ 5
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  obtain ⟨c₁, C₁, hc₁, hC₁, Hs⟩ :=
    deviation_single CERW.LimitShapes.exp_deviation hc₀ (le_max_left c₀ _)
  obtain ⟨CS, hCS0, hCS⟩ := exists_momentRadius_le_maxRadius_add
  obtain ⟨CI, _, hCI⟩ := exists_innerRadius_le_momentRadius_add
  let b := Real.sqrt (p / (2 * C₁))
  have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hb2 : C₁ * b ^ 2 = p / 2 := by
    dsimp [b]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  let B := K.CCo + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 1 ≤ B ^ 2 + B + 1 := by nlinarith
  let cA := c₁ * b / (8 * ε * unitBallVolume 2 * (B ^ 2 + B + 1))
  have hcA : 0 < cA := by dsimp [cA]; positivity
  have hcubic : 0 < 3 / (4 * ε * unitBallVolume 2) := by positivity
  have hrcube : ∀ n : ℕ, r n ^ 3 = 3 / (4 * ε * unitBallVolume 2) * n := by
    intro n
    rw [hr3 n]
    ring
  have hev : ∀ᶠ n : ℕ in atTop, nf ≤ n ∧ 2 ≤ n ∧
      1 ≤ r n ∧ 1 / K.CCo ≤ r n ∧ 1 / (θ * K.CCo) ≤ r n ∧
      (400 / (θ ^ 2 * a)) / K.CCo ≤ r n ∧ CS ≤ r n ∧
      (n : ℝ) ^ (-(p + 1)) ≤ 1 / Cf ∧
      (n : ℝ) ^ (-(p / 2)) ≤ 1 / (4 * (1 + 2 * Cf)) ∧
      (C₁ / b) ^ 2 ≤ Real.log n ∧
      (4 * K.CCo + 2) * b * Real.log n ^ ((1 : ℝ) / 2) ≤
        c₁ * r n ^ ((3 : ℝ) / 2) ∧
      ((2 * K.CCo ^ 2) / (c₁ * b)) ^ 2 ≤ Real.log n ∧
      (2 * max CS CI / cA) ^ 2 ≤ Real.log n := by
    filter_upwards [eventually_ge_atTop nf, eventually_ge_atTop 2,
      eventually_ge_of_cube hcubic hr0 hrcube 1,
      eventually_ge_of_cube hcubic hr0 hrcube (1 / K.CCo),
      eventually_ge_of_cube hcubic hr0 hrcube (1 / (θ * K.CCo)),
      eventually_ge_of_cube hcubic hr0 hrcube ((400 / (θ ^ 2 * a)) / K.CCo),
      eventually_ge_of_cube hcubic hr0 hrcube CS,
      eventually_rpow_neg_le (by linarith : 0 < p + 1) (by positivity : 0 < 1 / Cf),
      eventually_rpow_neg_le (by positivity : 0 < p / 2)
        (by positivity : 0 < 1 / (4 * (1 + 2 * Cf))),
      eventually_ge_log ((C₁ / b) ^ 2),
      eventually_mul_log_rpow_le hcubic hr0 hrcube (1 / 2) ((4 * K.CCo + 2) * b)
        c₁ (3 / 2) (by positivity) hc₁ (by norm_num),
      eventually_ge_log (((2 * K.CCo ^ 2) / (c₁ * b)) ^ 2),
      eventually_ge_log ((2 * max CS CI / cA) ^ 2)]
      with n h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  refine ⟨cA / 2, by positivity, n₀, ?_⟩
  intro Ω _ μ _ X hX n hn
  obtain ⟨hnf', hn2, hr1, hrk, hrθ, hr400, hCSr, hα, hpow, hβ, hinc, hq, hM⟩ :=
    hn₀ n hn
  have hr : 0 < r n := by linarith
  let R := K.CCo * r n
  have hR : 1 ≤ R := by
    dsimp [R]
    simpa only [mul_comm] using (div_le_iff₀ hk).mp hrk
  have hθR : 1 ≤ θ * R := by
    have ht := (div_le_iff₀ (mul_pos hθ hk)).mp hrθ
    dsimp [R]
    nlinarith only [ht]
  have hlarge : 400 / (θ ^ 2 * a) ≤ R := by
    simpa only [R, mul_comm] using (div_le_iff₀ hk).mp hr400
  have hnR : (n : ℝ) = a * R ^ 3 := by
    dsimp [a, R]
    rw [mul_pow, hr3 n]
    field_simp
  obtain ⟨hhalf, herror⟩ := coarse_bracket_geometry hR hθ ha hθa hθR hlarge hnR
  have hα1 : Cf * (n : ℝ) ^ (-(p + 1)) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hα hCf.le
    simpa only [mul_one_div_cancel hCf.ne'] using hh
  have hβ' : C₁ ≤ b * Real.sqrt (Real.log n) :=
    le_mul_sqrt_of_sq_le hb hC₁.le hβ
  have hq' : 2 * K.CCo ^ 2 ≤ c₁ * b * Real.sqrt (Real.log n) :=
    le_mul_sqrt_of_sq_le (mul_pos hc₁ hb) (by positivity) hq
  have hr32 : r n ^ ((3 : ℝ) / 2) = r n * Real.sqrt (r n) := by
    have he : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
    rw [he, Real.rpow_add hr, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hbinc := coarse_increment_scale hr1 hb (by
    simpa only [hr32, ← Real.sqrt_eq_rpow] using hinc)
  have hpos : 0 < c₁ * (b * Real.sqrt (Real.log n)) /
      (Real.sqrt (r n ^ 5))⁻¹ := by
    have hnreal : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hl : 0 < Real.log n := Real.log_pos hnreal
    positivity
  have hcore := coarse_radii_deviation hε hεd hX K n hr hR hθ
    (by rw [hscale n]) rfl hnR (hr3 n) hhalf herror (by positivity) hα1
    (hprob μ X hX n hnf') hβ' hbinc hpos (coarse_position_scale hr1 hq') hB
    (by dsimp [B]; nlinarith only [hCSr]) (fun Y => hCS Y n) (fun Y => hCI Y n)
    (Hs μ (pathFiltration hX.measurable) n (by omega))
  have hP := prob_ineq hb2 hCf (by omega : 1 ≤ n) hpow
  have hM' : max CS CI ≤ cA / 2 * Real.sqrt (Real.log n) := by
    have ht := le_mul_sqrt_of_sq_le hcA
      (mul_nonneg (by norm_num) (hCS0.trans (le_max_left _ _))) hM
    linarith
  have hsrL : Real.sqrt (Real.log n) ≤ Real.sqrt (r n * Real.log n) := by
    rw [Real.sqrt_mul hr.le]
    exact le_mul_of_one_le_left (Real.sqrt_nonneg _) (Real.one_le_sqrt.mpr hr1)
  have hM'' : max CS CI ≤ cA / 2 * Real.sqrt (r n * Real.log n) :=
    hM'.trans (mul_le_mul_of_nonneg_left hsrL (by positivity))
  have hth := coarse_thresholds hε hw hr hc₁ hb hD
    ((le_max_left CS CI).trans hM'') ((le_max_right CS CI).trans hM'')
  exact radii_events hX.measurable (hP.trans hcore.1) (hP.trans hcore.2) hth.1 hth.2

end CERW.LimitShapes
