import CERW.Support.Outer.Radius

/-!
# The outer radius and the fluctuation rates of the Euclidean walk

The outer-radius and local-time estimates follow from the deterministic potential and
crossing arguments. The shared radius estimates supply the two Euclidean conclusions
and the path facts used by the inner-radius and local-time arguments.
The retained labels `eq:newton-convolution`, `eq:radial-convolution` and `eq:vector`
refer to the earlier source `paper/limit-shapes.tex`.
-/

universe u

namespace CERW.Support.Outer

open CERW.Support.Statements CERW
open LatticeProb (Site euclidNorm)

variable {d : ℕ}

noncomputable section

/-- The crossing bound `eq:euclid-crossing`. -/
private abbrev CrossOK := @CERW.Support.Outer.Radius.CrossOK

/-- The clauses of Proposition `prop:inner` for a path. -/
private abbrev InnerOK := @CERW.Support.Outer.Radius.InnerOK

/-- The local-time inputs to the outer-radius and profile estimates. The crossing estimate is
supplied separately, so these inputs do not include the vector martingale bound. -/
private abbrev LocalPathFacts := @CERW.Support.Outer.Radius.LocalPathFacts

/-- The constructor of the local-time path facts. -/
private abbrev LocalPathFacts.mk := @CERW.Support.Outer.Radius.LocalPathFacts.mk

/-- The mass bound `eq:mass` for the region outside the inner ball. -/
private abbrev MassOK := @CERW.Support.Outer.Radius.MassOK

/-- `eq:newton-convolution` and `eq:radial-convolution`: for `d ≥ 3` and the kernel `χ(ζ) = (1 +
|ζ|)^{2-2d}`, `(χ * U_D)(y) ≤ ‖χ‖₁ U_D^+(y)`. -/
private abbrev NewtonConv := @CERW.Support.Outer.Radius.NewtonConv

/-- The deterministic consequences of the local-time and crossing good events
at `lem:local` and `eq:distance-crossing`. -/
private abbrev PathFacts := @CERW.Support.Outer.Radius.PathFacts

/-- The constructor of the path facts on the good events. -/
private abbrev PathFacts.mk := @CERW.Support.Outer.Radius.PathFacts.mk

/-- `lem:layer` for the Euclidean norm: a set in an annulus of width `a` has potential at most
`2dεa` in absolute value. -/
private abbrev annulus_potential_le := @CERW.Support.Outer.Radius.annulus_potential_le

/-- The ball of radius `R_in(n)` lies in `D_n`. -/
private abbrev ball_innerRadius_subset := @CERW.Support.Outer.Radius.ball_innerRadius_subset

/-- The bracket sum `W_x = Σ_{j<n} (1 + |Y_j - x|)^{2-2d}` of the local martingale at `x`. -/
private abbrev braSum := @CERW.Support.Outer.Radius.braSum

/-- For `n ≥ 2`, `log (n + 2) ≤ 2 log n`. -/
private abbrev co_log_add_two_le := @CERW.Support.Outer.Radius.co_log_add_two_le

/-- The path stays within distance `n` of the origin. -/
private abbrev co_maxRadius_le := @CERW.Support.Outer.Radius.co_maxRadius_le

/-- If `w ≤ Kw √r lg^{5/2}` then `(r lg)^{1/4} √w ≤ √Kw √r lg^{3/2}`. -/
private abbrev co_planar_bd := @CERW.Support.Outer.Radius.co_planar_bd

/-- The bound on the error of the global local-time approximation in the plane. -/
private abbrev co_planar_delta := @CERW.Support.Outer.Radius.co_planar_delta

/-- The width of the range in the plane: from the crossing bound and the inner radius bound, `R - b
+ 2√d` is at most `Kw √r (log n)^{5/2}` and `r / log n`, and `b ≥ r/2`. -/
private abbrev co_planar_width := @CERW.Support.Outer.Radius.co_planar_width

/-- The potential is at most its positive part. -/
private abbrev co_potential_le_positive := @CERW.Support.Outer.Radius.co_potential_le_positive

/-- The potential of a set outside the ball of radius `b` is nonnegative inside that ball. -/
private abbrev co_potential_nonneg_inside := @CERW.Support.Outer.Radius.co_potential_nonneg_inside

/-- The rate `q_n` is positive for `n ≥ 2`. -/
private abbrev co_qrate_pos := @CERW.Support.Outer.Radius.co_qrate_pos

/-- The lattice weight `k(w) = (1 + |w|)^{2-2d}`. -/
private abbrev ev_kern := @CERW.Support.Outer.Radius.ev_kern

/-- The bracket sum equals the local-time weighted kernel sum over any finite set of sites
containing the departure range. -/
private lemma ev_braSum_eq (X : ℕ → Site d) (n : ℕ) {S : Finset (Site d)}
    (hS : departureRange X n ⊆ S) (y : Site d) :
    braSum X n y = ∑ x ∈ S, (localTime X n x : ℝ) * ev_kern d (x - y) := by
  exact Radius.ev_braSum_eq X n hS y

/-- The cell weight `a(y) = ∫_{C_y} χ(|y₀ - ζ|) dζ`. -/
private abbrev ev_cellWeight := @CERW.Support.Outer.Radius.ev_cellWeight

/-- The radial weight `χ(s) = (1 + |s|)^{2-2d}`. -/
private abbrev ev_chi := @CERW.Support.Outer.Radius.ev_chi

/-- The radial weight is nonnegative. -/
private abbrev ev_chi_nonneg := @CERW.Support.Outer.Radius.ev_chi_nonneg

/-- The weight of a norm is `(1 + ‖ζ‖)^{2-2d}`. -/
private abbrev ev_chi_norm := @CERW.Support.Outer.Radius.ev_chi_norm

/-- For `d ≥ 3` and a measurable set `E` of finite volume, `ζ ↦ χ(|ζ|) U_E(y - ζ)` is integrable. -/
private abbrev ev_integrable_chi_mul_potential :=
  @CERW.Support.Outer.Radius.ev_integrable_chi_mul_potential

/-- For `d ≥ 3` the radial weight is integrable on `ℝ^d`. -/
private abbrev ev_integrable_chi_norm := @CERW.Support.Outer.Radius.ev_integrable_chi_norm

/-- The radial estimate `∫ χ(|ζ|) min(b, |ζ|) dζ ≤ σ_d (log(1 + T) + 1)` with `T = max 1 b` and `σ_d
= d ω_d`. -/
private abbrev ev_integral_chi_mul_min_le := @CERW.Support.Outer.Radius.ev_integral_chi_mul_min_le

/-- The lattice step: there are constants `c₀, α₁` depending only on `d` and `C₁` such that the
bracket at a site `z` whose cell is near `y₀` satisfies `c₀ W_z ≤ 2 Σ_{y} a(y) U(y) + α₁ L`. -/
private abbrev ev_kernel_sum_le := @CERW.Support.Outer.Radius.ev_kernel_sum_le

/-- The logarithm of `1 + max 1 b` is at most a constant multiple of `log (n + 2)` when `b ≤ 2 Λ n`.
-/
private abbrev ev_log_one_add_max_le := @CERW.Support.Outer.Radius.ev_log_one_add_max_le

/-- A path with `|X_j| ≤ j` has `H_n ≤ n`. -/
private abbrev ev_maxRadius_le_nat := @CERW.Support.Outer.Radius.ev_maxRadius_le_nat

/-- The far-field bound: at a point of the complement of the cells of the ball of radius `2n`, the
potential of `D_n` is at least `-4ε/ω_d`. -/
private abbrev ev_neg_le_potential_of_not_mem :=
  @CERW.Support.Outer.Radius.ev_neg_le_potential_of_not_mem

/-- The positive part `U_E^+` of the potential is nonnegative. -/
private abbrev ev_positivePotential_nonneg := @CERW.Support.Outer.Radius.ev_positivePotential_nonneg

/-- The potential is at most its positive part `U_E^+`. -/
private abbrev ev_potential_le_positivePotential :=
  @CERW.Support.Outer.Radius.ev_potential_le_positivePotential

/-- The decomposition `U_D = 2dε (b - |·|)_+ + U_{D ∖ B(0,b)}`, including the degenerate radius `b =
0`. -/
private abbrev ev_potential_split := @CERW.Support.Outer.Radius.ev_potential_split

/-- Summing over the cells of a finite set of sites: if `Uf` varies by at most `M` across each cell
and is at least `-Cf` off the union of the cells, then the cell-weighted sum of the values of `Uf`
at the sites is at most the integral of `G Uf` plus `(M + Cf) ∫ G`. -/
private abbrev ev_sum_setIntegral_mul_le := @CERW.Support.Outer.Radius.ev_sum_setIntegral_mul_le

/-- The events of `prop:coarse`, `lem:local`, `eq:pointwise`, `eq:localmart` and `eq:vector`. -/
private abbrev exists_pathFacts_prob := @CERW.Support.Outer.Radius.exists_pathFacts_prob

/-- The outer radius is nonnegative. -/
private abbrev gd_maxRadius_nonneg := @CERW.Support.Outer.Radius.gd_maxRadius_nonneg

/-- On a bounded set the function `|v - y|^{2-d}` is integrable for `d ≥ 2`. -/
private abbrev gma_integrableOn_rpow := @CERW.Support.Outer.Radius.gma_integrableOn_rpow

/-- The tail integral `(d-2) ∫_r^∞ t^{1-d} dt = r^{2-d}`. -/
private abbrev gmb_lintegral_tail := @CERW.Support.Outer.Radius.gmb_lintegral_tail

/-- For `n ≥ 3`: `1 ≤ log n` and `log (n + 2) ≤ 2 log n`. -/
private abbrev hx_log_facts := @CERW.Support.Outer.Radius.hx_log_facts

/-- For large `n`, the radius `r_n` is positive, `K log n ≤ r_n` and `4 r_n ≤ n`. -/
private abbrev hx_scales := @CERW.Support.Outer.Radius.hx_scales

/-- The inner radius is at most `R_out(n) + √d/2`. -/
private abbrev innerRadius_le := @CERW.Support.Outer.Radius.innerRadius_le

/-- The inner radius is nonnegative. -/
private abbrev innerRadius_nonneg := @CERW.Support.Outer.Radius.innerRadius_nonneg

/-- Theorem `thm:fluctuations` (iii), `d ≥ 3`, deterministically. -/
private abbrev local_core_high := @CERW.Support.Outer.Radius.local_core_high

/-- Theorem `thm:fluctuations` (iii), `d = 2`, deterministically. -/
private abbrev local_core_planar := @CERW.Support.Outer.Radius.local_core_planar

/-- `eq:mass`: the volume outside the inner ball, from the volume clause and the inner radius clause
of Proposition `prop:inner`. -/
private abbrev mass_of_inner := @CERW.Support.Outer.Radius.mass_of_inner

/-- A set covered by three sets of small measure has small measure. -/
private abbrev measure_le_union_three := @CERW.Support.Outer.Radius.measure_le_union_three

/-- The logarithm `log (n + 2)` is nonnegative. -/
private abbrev mono_log_nonneg := @CERW.Support.Outer.Radius.mono_log_nonneg

/-- The field `∫_E u_v / (v - z) dv` is complex differentiable on the disc `B(0,b)`. -/
private abbrev mp_differentiableOn_field := @CERW.Support.Outer.Radius.mp_differentiableOn_field

/-- The identification of the complex plane with the Euclidean plane. -/
private abbrev mp_e := @CERW.Support.Outer.Radius.mp_e

/-- The integral `∫_E u_v / (v - z) dv` of the complex kernel. -/
private abbrev mp_field := @CERW.Support.Outer.Radius.mp_field

/-- The planar potential is `2ε/ω_2` times the real part of the field inside the disc. -/
private abbrev mp_potential_eq := @CERW.Support.Outer.Radius.mp_potential_eq

/-- Newton's theorem for the radial convolution: `(χ * U_D)(y) ≤ ‖χ‖₁ U_D^+(y)`. -/
private abbrev newton_conv := @CERW.Support.Outer.Radius.newton_conv

/-- If `n < n₀` the bound `C n^{-p}` with `C ≥ (n₀+1)^p` is at least `1`. -/
private abbrev one_le_ofReal_mul_rpow := @CERW.Support.Outer.Radius.one_le_ofReal_mul_rpow

/-- The maximal local time over the visited sites of norm at least `b`. -/
private abbrev outerMax := @CERW.Support.Outer.Radius.outerMax

/-- Proposition `prop:stronger-outer`, `d ≥ 3`, deterministically. -/
private abbrev outer_core_high := @CERW.Support.Outer.Radius.outer_core_high

/-- Proposition `prop:stronger-outer`, `d = 2`, deterministically. -/
private abbrev outer_core_planar := @CERW.Support.Outer.Radius.outer_core_planar

/-- The radius `r_n = ((d+1) n / (2 d ε ω_d))^{1/(d+1)}` of `eq:radius`. -/
private abbrev radius := @CERW.Support.Outer.Radius.radius

/-- The planar exterior estimate of Section `sec:outer`: with `w = R_out - b + 2√d` at most `r / log
n`, the local times outside the inner ball are within `C √(r log n)` of the potential of `E`, and
the positive potential of `E` in the annulus is at most `C ((r log n)^{1/4} √w + √(r log n))`. -/
private theorem planar_exterior (hd : d = 2) (hnear : near_far) {ε : ℝ} (hε : 0 < ε)
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
  exact Radius.planar_exterior hd hnear hε hεd C₀ C₁ Cin Cm

/-- In the plane the potential of a set outside the disc `B(0,b)` is harmonic inside it, so its
supremum over the closed disc is attained on the circle. -/
private abbrev planar_max_principle := @CERW.Support.Outer.Radius.planar_max_principle

/-- `eq:ballpotential-euclid` and the decomposition `U_{D_n} = U_{B(0,b)} + U_E`. -/
private abbrev potential_split := @CERW.Support.Outer.Radius.potential_split

/-- The rate `q_n` of `eq:qn`. -/
private abbrev qrate := @CERW.Support.Outer.Radius.qrate

/-- The rate `q_n` is nonnegative for `n ≥ 1`. -/
private abbrev qrate_nonneg := @CERW.Support.Outer.Radius.qrate_nonneg

/-- `r_n q_n` is `√(r_n log n)` in the plane and `log n` in higher dimensions. -/
private abbrev radius_mul_qrate := @CERW.Support.Outer.Radius.radius_mul_qrate

/-- The radius is positive for `n ≥ 1`. -/
private abbrev radius_pos := @CERW.Support.Outer.Radius.radius_pos

/-- `E = D_n ∖ B(0,b)` lies in the annulus `{b ≤ |v| ≤ b + w}` with `w = R_out - b + 2√d`. -/
private abbrev sdiff_subset_annulus := @CERW.Support.Outer.Radius.sdiff_subset_annulus

/-- Every power of `log n` is eventually at most any positive power of the radius. -/
private abbrev tk_log_pow_le := @CERW.Support.Outer.Radius.tk_log_pow_le

/-- `q_n ≤ 1` eventually. -/
private abbrev tk_qrate_le_one := @CERW.Support.Outer.Radius.tk_qrate_le_one

/-- The radius is `a n^{1/(d+1)}` with `a > 0`. -/
private lemma tk_radius_eq (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, radius d ε n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
  exact Radius.tk_radius_eq hd hε

/-- `r_n q_n^{1/d} = r_n^{1-γ} (log n)^γ` with `γ = β/d`. -/
private abbrev tk_rq_rpow := @CERW.Support.Outer.Radius.tk_rq_rpow

/-- Proposition `prop:stronger-outer`, from Proposition `prop:inner`, the near-far lemma and the
outer-crossing lemma. -/
theorem outer_radius_of (hinner : inner_radius.{u}) (hnear : near_far)
    (houter : outer_crossing) : outer_radius.{u} := by
  exact Radius.outer_radius_of.{u} hinner hnear houter

/-- Proposition `prop:stronger-outer` and Theorem `thm:fluctuations`: the clauses of the good
event from the three inputs. -/
theorem fluctuation_rates_of (hinner : inner_radius.{u}) (houter : outer_radius.{u})
    (hnear : near_far) : fluctuation_rates.{u} := by
  exact Radius.fluctuation_rates_of.{u} hinner houter hnear

end

end CERW.Support.Outer
