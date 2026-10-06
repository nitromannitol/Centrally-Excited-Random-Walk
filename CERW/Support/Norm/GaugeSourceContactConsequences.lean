import CERW.Support.Norm.GaugeRadialNewtonConvolution
import CERW.Support.Norm.GaugeSection5Event

/-!
# The contact passage for the gauge of a convex body, on the event of Section 5.1

Let `K ⊆ ℝ^d`, `d ≥ 2`, be a compact convex set with the origin in its interior and `ψ = gauge K`
its Minkowski functional, which need not be even (the corollary for convex bodies, `oct5.tex:896`).
For a path `x` and a time `n`, `b = normInnerRadius (gauge K) x n` is the infimum of `ψ` over the
complement of the cell set `D_n`, `E = D_n ∖ {ψ < b}`, a contact point `y₀` is a point of the
closure of the complement with `ψ(y₀) = b`, and `H = U_{D_n}(y₀)` (`oct5.tex:633-655`). This module
derives, from the event `E7` of Section 5.1 and from the legality of the walk, the passage of
`lem:contact` (`oct5.tex:773-777`) together with the convolution inequality
`(χ * U_E)(y₀) ≤ ‖χ‖₁ H` (`oct5.tex:759-771`):

* `normPotential_cellSet_contact_nonneg`: `H ≥ 0` at every contact point (the integrand of `U_E`
  is nonnegative by `eq:contact-convexity`, and `U_{D_n}(y₀) = U_E(y₀)`).
* `contact_of_estimates7`: a deterministic statement on one path. Under the typing of the model and
  the three constituents of the event that the contact bound uses (the bounds of Proposition 4.1,
  the estimates of Lemma 3.1 and the local martingale bound), for every `n` beyond a threshold
  there is a contact point; at every contact point there is an unvisited cell with `y₀` in its
  closure, `0 ≤ H ≤ C r_n q_n` with the rate of `eq:qn`, and for every nonnegative integrable
  radial `f` the function `ζ ↦ f(ζ) U_E(y₀ - ζ)` is integrable and `(f * U_E)(y₀) ≤ ‖f‖₁ H ≤
  ‖f‖₁ C r_n q_n`. The hypotheses of the contact bound (the path, the coarse bounds, the local
  time bounds, the pointwise bound and the scale regime) are produced here from those constituents
  (`GaugeSection5Event.exists_pointwise_of_localMart`, `GaugeContactShape.Rates.gauge_contact_rate`
  and the threshold); the convolution inequality is the supplier
  `GaugeRadialNewtonConvolution.gauge_contact_convolution_le_cellSet`.
* `gauge_source_contact`: the probabilistic statement. For every `p > 0` there are the constants
  `E` of the event, `C` and a threshold `n₀`, chosen before the field of subgradients, the
  probability space, the walk, `n` and the weight, such that for `n ≥ n₀` the event of Section 5.1
  is in `ℱ_n`, is `E7`, and has failure probability at most `C n^{-p}` (the producer
  `GaugeSection5Event.gauge_section5_event`), and the set of sample points at which the contact
  passage fails has probability at most `C n^{-p}` (the walk is almost surely legal,
  `Section5Localization.ae_legal_of_isDriftCERW`).

No weight is bounded or has a moment, no Fubini hypothesis and no contact bound is assumed, and no
evenness or norm property of `ψ` is used.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.GaugeSourceContactConsequences

open CERW CERW.Support.Law CERW.Support.Occupation CERW.Support.Contact
  CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel CERW.Support.Norm.GaugeCoarseVolume
open CERW.Support.Norm.ContactEvent (EventConstants CoarseBounds LocalBounds LocalMartEstimate
  PathTyping)
open CERW.Support.Norm.Section5Localization (E7 legalSet)
open CERW.Support.Norm.GaugeSection5Event (EventAtScale)

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-! ## The potential at a contact point is nonnegative -/

/-- **`H ≥ 0` at a contact point.** For a path `x` and a point `y₀` with `ψ_K(y₀) =
normInnerRadius (gauge K) x n`, the potential of the cell set `D_n` at `y₀` is nonnegative:
`U_{D_n}(y₀) = U_E(y₀)` for `E = D_n ∖ {ψ_K < b}`, and the integrand of `U_E(y₀)` is nonnegative
on `E` by `eq:contact-convexity`. -/
theorem normPotential_cellSet_contact_nonneg (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 ≤ ε) (x : ℕ → Site d)
    (n : ℕ) {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : gauge K y₀ = normInnerRadius (gauge K) x n) :
    0 ≤ normPotential d ε (gauge K) (cellSet x n) y₀ := by
  obtain ⟨-, -, hUE⟩ := GaugeRadialNewtonConvolution.gauge_contact_convolution_le_cellSet hd hK hc
    h0 hε (f := fun _ => (0 : ℝ)) (fun _ _ _ => rfl) (fun _ => le_rfl) (integrable_zero _ _ _) x n
    hy₀
  rw [← hUE]
  unfold normPotential
  refine mul_nonneg (div_nonneg (mul_nonneg zero_le_two hε) (unitBallVolume_pos d).le) ?_
  refine setIntegral_nonneg ((measurableSet_cellSet x n).diff
    (measurableSet_gauge_sublevel hc h0 _)) fun v hv => ?_
  refine div_nonneg (GaugeRadialNewtonConvolution.gauge_inner_gradient_sub_nonneg hc h0 ?_)
    (pow_nonneg (norm_nonneg _) _)
  have hnot : ¬ gauge K v < normInnerRadius (gauge K) x n := hv.2
  rw [hy₀]
  exact not_lt.mp hnot

/-! ## The scale regime of the contact bound -/

/-- **The scale regime.** For `C_co ≥ 0` and all large `n`, the scale `r_n` of the walk satisfies
`1 ≤ r_n`, `log(n + 2)^4 ≤ r_n`, `3 C_co r_n + 6 √d ≤ n` and `4 √d ≤ n`: these are the conditions
of the contact bound for `d = 2` and for `d ≥ 3`. The scale is `r_n = A n^{1/(d+1)}`, so that `n` is
a power of `r_n` and every power of `log n` is negligible against `r_n`
(`GaugeCoarseVolume.eventually_mul_log_pow_le_coarseScale`). -/
private theorem scale_regime (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hV : 0 < normBallVolume (gauge K)) {C_co : ℝ} (hC_co : 0 ≤ C_co) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 2 ≤ n ∧ 1 ≤ coarseScale (gauge K) ε n ∧
      Real.log ((n : ℝ) + 2) ^ 4 ≤ coarseScale (gauge K) ε n ∧
      3 * C_co * coarseScale (gauge K) ε n + 6 * Real.sqrt d ≤ n ∧ 4 * Real.sqrt d ≤ n := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hsd : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * (d : ℝ) * ε * normBallVolume (gauge K) / ((d : ℝ) + 1) :=
    ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [ha]
    positivity
  have hR0 : 0 < max 1 ((3 * C_co + 6 * Real.sqrt d) / a) := lt_max_of_lt_left one_pos
  have hreg : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧
      max 1 ((3 * C_co + 6 * Real.sqrt d) / a) ≤ coarseScale (gauge K) ε n ∧
      16 * Real.log n ^ (d + 5) ≤ coarseScale (gauge K) ε n ∧ 1 ≤ Real.log n := by
    filter_upwards [eventually_ge_atTop 2,
      eventually_mul_log_pow_le_coarseScale (Ψ := gauge K) hd hε hV hR0 0,
      eventually_mul_log_pow_le_coarseScale (Ψ := gauge K) hd hε hV (K := 16) (by norm_num) (d + 5),
      eventually_ge_atTop 3] with n hn2 h1 h2 hn3
    refine ⟨hn2, by rwa [pow_zero, mul_one] at h1, h2, ?_⟩
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_three]
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hreg
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hn2, hr, hM16, hℓ⟩ := hn₀ n hn
  have hna : (n : ℝ) = a * coarseScale (gauge K) ε n ^ (d + 1) := by
    rw [ha]
    exact nat_eq_coarseScale_pow hd hε hV n
  set r : ℝ := coarseScale (gauge K) ε n with hrdef
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr2 : (3 * C_co + 6 * Real.sqrt d) / a ≤ r := (le_max_right _ _).trans hr
  have hr0 : 0 < r := by linarith
  have hnbig : (3 * C_co + 6 * Real.sqrt d) * r ≤ n := by
    have h1 : 3 * C_co + 6 * Real.sqrt d ≤ r * a := (div_le_iff₀ ha0).mp hr2
    have h2 : r ≤ r ^ d := le_self_pow₀ hr1 (by omega)
    have h3 : r * r ≤ r ^ (d + 1) := by rw [pow_succ]; nlinarith
    have h4 : (3 * C_co + 6 * Real.sqrt d) * r ≤ (r * a) * r :=
      mul_le_mul_of_nonneg_right h1 hr0.le
    rw [hna]
    nlinarith [mul_le_mul_of_nonneg_left h3 ha0.le]
  have hℓ2 : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n :=
    CERW.Support.Norm.ContactAssembly.log_add_two_le hn2
  have hlogcond : Real.log ((n : ℝ) + 2) ^ 4 ≤ r := by
    have hl0 : 0 ≤ Real.log ((n : ℝ) + 2) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ n + 2 by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)]
    have h1 : Real.log ((n : ℝ) + 2) ^ 4 ≤ (2 * Real.log n) ^ 4 :=
      pow_le_pow_left₀ hl0 hℓ2 4
    have h2 : (2 * Real.log n) ^ 4 = 16 * Real.log n ^ 4 := by ring
    have h3 : Real.log n ^ 4 ≤ Real.log n ^ (d + 5) := pow_le_pow_right₀ hℓ (by omega)
    nlinarith
  refine ⟨hn2, hr1, hlogcond, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hr1 (Real.sqrt_nonneg (d : ℝ))]
  · nlinarith [mul_le_mul_of_nonneg_left hr1 (Real.sqrt_nonneg (d : ℝ)),
      mul_nonneg hC_co hr0.le]

/-! ## The contact passage on one path of the event -/

/-- **The contact passage on a path of the event of Section 5.1.** Let `K` be a compact convex set
with the origin in its interior, `ε > 0` and `E` constants of the event with `C_co, C_loc > 0` and
`C_mart ≥ 0`. There are `C > 0` and a threshold `n₀` such that for every subgradient selection `ξ`
and every legal path `x` which, at a time `n ≥ n₀`, satisfies the bounds of Proposition 4.1
(`CoarseBounds`), the estimates of Lemma 3.1 (`LocalBounds`) and the local martingale bound
(`LocalMartEstimate`), the following hold. There is a contact point `y₀` (a point of the closure of
the complement of `D_n` with `ψ_K(y₀) = b`). At every contact point `y₀` there is a site `z` not
visited before `n` whose cell has `y₀` in its closure, with `|z - y₀| ≤ √d/2` and `ψ_K(z) ≥ b`;
`0 ≤ H ≤ C r_n q_n` for `H = U_{D_n}(y₀)`, with `q_n = √(log n / r_n)` for `d = 2` and
`q_n = log n / r_n` for `d ≥ 3`; and for every nonnegative integrable radial `f` the function
`ζ ↦ f(ζ) U_E(y₀ - ζ)` is integrable, `(f * U_E)(y₀) ≤ ‖f‖₁ H ≤ ‖f‖₁ C r_n q_n`, and `U_E(y₀) = H`,
with `E = D_n ∖ {ψ_K < b}`. The constant and the threshold do not depend on `ξ`, `x`, `n` or `f`. -/
theorem contact_of_estimates7 (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 < ε)
    {E : EventConstants} (hC_co : 0 < E.C_co) (hC_loc : 0 < E.C_loc) (hC_mart : 0 ≤ E.C_mart) :
    ∃ (C : ℝ) (n₀ : ℕ), 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ z : Site d, z ≠ 0 → IsSubgradient (gauge K) (toSpace z) (ξ z)) → ξ 0 = 0 →
      ∀ (x : ℕ → Site d) (n : ℕ), n₀ ≤ n → PathTyping d x →
        CoarseBounds d (gauge K) ε E.c_co E.C_co x n → LocalBounds d (gauge K) ε E.C_loc x n →
        LocalMartEstimate d ε ξ E.C_mart x n →
        (∃ y₀ : EuclideanSpace ℝ (Fin d), gauge K y₀ = normInnerRadius (gauge K) x n ∧
          y₀ ∈ closure (cellSet x n)ᶜ) ∧
        ∀ y₀ : EuclideanSpace ℝ (Fin d), gauge K y₀ = normInnerRadius (gauge K) x n →
          y₀ ∈ closure (cellSet x n)ᶜ →
          (∃ z : Site d, localTime x n z = 0 ∧ y₀ ∈ closure (cell z) ∧
              ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2 ∧
              normInnerRadius (gauge K) x n ≤ gauge K (toSpace z)) ∧
          0 ≤ normPotential d ε (gauge K) (cellSet x n) y₀ ∧
          normPotential d ε (gauge K) (cellSet x n) y₀ ≤
            C * coarseScale (gauge K) ε n *
              GaugeContactShape.Rates.rateQ d (coarseScale (gauge K) ε n) (Real.log n) ∧
          ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
            (∀ u v : EuclideanSpace ℝ (Fin d), ‖u‖ = ‖v‖ → f u = f v) → (∀ u, 0 ≤ f u) →
            Integrable f →
            Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
              f ζ * normPotential d ε (gauge K)
                (cellSet x n \ {v | gauge K v < normInnerRadius (gauge K) x n}) (y₀ - ζ)) ∧
            ∫ ζ : EuclideanSpace ℝ (Fin d),
                f ζ * normPotential d ε (gauge K)
                  (cellSet x n \ {v | gauge K v < normInnerRadius (gauge K) x n}) (y₀ - ζ) ≤
              (∫ ζ : EuclideanSpace ℝ (Fin d), f ζ) *
                normPotential d ε (gauge K) (cellSet x n) y₀ ∧
            ∫ ζ : EuclideanSpace ℝ (Fin d),
                f ζ * normPotential d ε (gauge K)
                  (cellSet x n \ {v | gauge K v < normInnerRadius (gauge K) x n}) (y₀ - ζ) ≤
              (∫ ζ : EuclideanSpace ℝ (Fin d), f ζ) *
                (C * coarseScale (gauge K) ε n *
                  GaugeContactShape.Rates.rateQ d (coarseScale (gauge K) ε n) (Real.log n)) ∧
            normPotential d ε (gauge K)
                (cellSet x n \ {v | gauge K v < normInnerRadius (gauge K) x n}) y₀ =
              normPotential d ε (gauge K) (cellSet x n) y₀ := by
  have hd1 : 1 ≤ d := by omega
  have hΨ : GaugeContactShape.Adm K := ⟨hK, hc, h0⟩
  have hV : 0 < normBallVolume (gauge K) := normBallVolume_gauge_pos hK hc h0
  obtain ⟨C_F, hC_F, hpt⟩ :=
    GaugeSection5Event.exists_pointwise_of_localMart hd hΨ hε hC_mart
  obtain ⟨C_c, hC_c, hcon⟩ := GaugeContactShape.Rates.gauge_contact_rate hd hΨ hε C_F E.C_loc
    E.C_co hC_F hC_loc.le hC_co.le
  obtain ⟨n₀, hn₀⟩ := scale_regime hd1 hε hV hC_co.le
  refine ⟨C_c, n₀, hC_c, ?_⟩
  intro ξ hξ hξ0 x n hn hty hco hloc hlm
  obtain ⟨hn2, hr1, hlog, hlarge2, hlarge3⟩ := hn₀ n hn
  have hr0 : 0 < coarseScale (gauge K) ε n := by linarith
  have hXn : ∀ j : ℕ, euclidNorm (x j) ≤ j := euclidNorm_le_of_steps x hty.1 hty.2
  have hfine := hpt ξ hξ hξ0 x n hty.1 hty.2 (by omega) hlm
  have hcontact := hcon x n (coarseScale (gauge K) ε n) hn2 hty.1 hXn hr0
    (fun _ => ⟨hr1, hlog, hlarge2⟩) (fun _ => hlarge3) hco.2.2.2.2.2 hco.2.2.2.1 hfine hloc.2.2
  refine ⟨GaugeRadialNewtonConvolution.exists_contact_point_gauge hd1 hK hc h0 x n, ?_⟩
  intro y₀ hy₀ hcl
  have hrate := hcontact y₀ hy₀ hcl
  refine ⟨GaugeRadialNewtonConvolution.exists_unvisited_cell_of_contact_point_gauge x n hcl,
    normPotential_cellSet_contact_nonneg hd hK hc h0 hε.le x n hy₀, hrate, ?_⟩
  intro f hrad hf0 hfi
  obtain ⟨hint, hle, hUE⟩ := GaugeRadialNewtonConvolution.gauge_contact_convolution_le_cellSet hd
    hK hc h0 hε.le hrad hf0 hfi x n hy₀
  exact ⟨hint, hle, hle.trans (mul_le_mul_of_nonneg_left hrate (integral_nonneg hf0)), hUE⟩

/-! ## The contact passage with probability `1 - C n^{-p}` -/

/-- **`lem:contact` for the gauge of a convex body, with the contact passage and the convolution
inequality.** Let `K` be a compact convex set with the origin in its interior, `d ≥ 2`, `ε > 0` with
`ε ψ(±e_i) < 1/d`, `r_n = ((d+1) n/(2 d ε |B_ψ|))^{1/(d+1)}` and `q_n = √(log n / r_n)` for `d = 2`,
`q_n = log n / r_n` for `d ≥ 3`. For every `p > 0` there are the constants `E` of the event, a
constant `C` and a threshold `n₀`, chosen before the field of subgradients, the probability space,
the walk, `n` and the weight, such that for every `n ≥ n₀`: the event of Section 5.1 at the
selected nearest-point projection is in `ℱ_n`, is `E7`, and has failure probability at most
`C n^{-p}`; and with probability at least `1 - C n^{-p}`, there is a contact point, and at every
contact point `y₀` there is an unvisited cell with `y₀` in its closure, `0 ≤ H ≤ C r_n q_n`, and for
every nonnegative integrable radial `f` the function `ζ ↦ f(ζ) U_E(y₀ - ζ)` is integrable,
`(f * U_E)(y₀) ≤ ‖f‖₁ H ≤ ‖f‖₁ C r_n q_n` and `U_E(y₀) = H`. -/
theorem gauge_source_contact (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ)) :
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * normBallVolume (gauge K))) ^ ((1 : ℝ) / (d + 1))
    let q : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n
    ∀ p : ℝ, 0 < p → ∃ (E : EventConstants) (C : ℝ) (n₀ : ℕ),
      (0 < E.c_co ∧ 0 < E.C_co ∧ 0 < E.C_loc ∧ 0 < E.C_vec ∧ 0 < E.C_mart ∧ 0 < E.C_quad ∧
        0 < E.C_lin) ∧ 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ z : Site d, z ≠ 0 → IsSubgradient (gauge K) (toSpace z) (ξ z)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X), ∀ n : ℕ, n₀ ≤ n →
        (MeasurableSet[pathFiltration hX.measurable n]
            (EventAtScale hd ⟨hK, hc, h0⟩ hε ξ E X n) ∧
          EventAtScale hd ⟨hK, hc, h0⟩ hε ξ E X n = E7 (gauge K) ε ξ E X n) ∧
        μ (EventAtScale hd ⟨hK, hc, h0⟩ hε ξ E X n)ᶜ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
        μ {ω | ¬ ((∃ y₀ : EuclideanSpace ℝ (Fin d),
            gauge K y₀ = normInnerRadius (gauge K) (X · ω) n ∧
            y₀ ∈ closure (cellSet (X · ω) n)ᶜ) ∧
          ∀ y₀ : EuclideanSpace ℝ (Fin d),
            gauge K y₀ = normInnerRadius (gauge K) (X · ω) n →
            y₀ ∈ closure (cellSet (X · ω) n)ᶜ →
            (∃ z : Site d, localTime (X · ω) n z = 0 ∧ y₀ ∈ closure (cell z) ∧
                ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2 ∧
                normInnerRadius (gauge K) (X · ω) n ≤ gauge K (toSpace z)) ∧
            0 ≤ normPotential d ε (gauge K) (cellSet (X · ω) n) y₀ ∧
            normPotential d ε (gauge K) (cellSet (X · ω) n) y₀ ≤ C * r n * q n ∧
            ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
              (∀ u v : EuclideanSpace ℝ (Fin d), ‖u‖ = ‖v‖ → f u = f v) → (∀ u, 0 ≤ f u) →
              Integrable f →
              Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
                f ζ * normPotential d ε (gauge K)
                  (cellSet (X · ω) n \ {v | gauge K v < normInnerRadius (gauge K) (X · ω) n})
                  (y₀ - ζ)) ∧
              ∫ ζ : EuclideanSpace ℝ (Fin d),
                  f ζ * normPotential d ε (gauge K)
                    (cellSet (X · ω) n \ {v | gauge K v < normInnerRadius (gauge K) (X · ω) n})
                    (y₀ - ζ) ≤
                (∫ ζ : EuclideanSpace ℝ (Fin d), f ζ) *
                  normPotential d ε (gauge K) (cellSet (X · ω) n) y₀ ∧
              ∫ ζ : EuclideanSpace ℝ (Fin d),
                  f ζ * normPotential d ε (gauge K)
                    (cellSet (X · ω) n \ {v | gauge K v < normInnerRadius (gauge K) (X · ω) n})
                    (y₀ - ζ) ≤
                (∫ ζ : EuclideanSpace ℝ (Fin d), f ζ) * (C * r n * q n) ∧
              normPotential d ε (gauge K)
                  (cellSet (X · ω) n \ {v | gauge K v < normInnerRadius (gauge K) (X · ω) n})
                  y₀ =
                normPotential d ε (gauge K) (cellSet (X · ω) n) y₀)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  intro r q p hp
  have hΨ : GaugeContactShape.Adm K := ⟨hK, hc, h0⟩
  have hV : 0 < normBallVolume (gauge K) := normBallVolume_gauge_pos hK hc h0
  obtain ⟨E, C_ev, hpos, hC_ev, hev⟩ :=
    GaugeSection5Event.gauge_section5_event hd hΨ hε hell hp
  obtain ⟨C_c, n₁, hC_c, hdet⟩ := contact_of_estimates7 hd hK hc h0 hε (E := E) hpos.2.1
    hpos.2.2.1 hpos.2.2.2.2.1.le
  refine ⟨E, max C_ev C_c, max n₁ 2, hpos, lt_max_of_lt_left hC_ev, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hn1 : n₁ ≤ n := (le_max_left _ _).trans hn
  obtain ⟨hmeas, hfail⟩ := hev ξ hξ hξ0 μ X hX
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hev_bound : μ (EventAtScale hd hΨ hε ξ E X n)ᶜ ≤
      ENNReal.ofReal (max C_ev C_c * (n : ℝ) ^ (-p)) :=
    (hfail n hn2).2.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hnp))
  have hr0 : ∀ m : ℕ, 0 ≤ r m := fun m => coarseScale_nonneg hε hV m
  have hq0 : ∀ m : ℕ, 0 ≤ q m := fun m => by
    show 0 ≤ (if d = 2 then Real.sqrt (Real.log m / r m) else Real.log m / r m)
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact div_nonneg (Real.log_natCast_nonneg m) (hr0 m)
  refine ⟨hmeas n, hev_bound, ?_⟩
  have hnull : μ (legalSet X)ᶜ = 0 :=
    ae_iff.mp (CERW.Support.Norm.Section5Localization.ae_legal_of_isDriftCERW hX)
  refine le_trans (measure_mono (t := (EventAtScale hd hΨ hε ξ E X n)ᶜ ∪ (legalSet X)ᶜ) ?_) ?_
  · intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hnot
    obtain ⟨hωE, hωL⟩ := hnot
    obtain ⟨hco, hloc, -, hlm, -, -, -⟩ := hωE
    obtain ⟨hex, hall⟩ := hdet ξ hξ hξ0 (fun j => X j ω) n hn1 hωL hco hloc hlm
    refine hω ⟨hex, fun y₀ hy₀ hcl => ?_⟩
    obtain ⟨hgeom, hnn, hrate, hf⟩ := hall y₀ hy₀ hcl
    have hrq : C_c * coarseScale (gauge K) ε n *
        GaugeContactShape.Rates.rateQ d (coarseScale (gauge K) ε n) (Real.log n) ≤
        max C_ev C_c * r n * q n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (hr0 n)) (hq0 n)
    refine ⟨hgeom, hnn, hrate.trans hrq, fun f hrad hf0 hfi => ?_⟩
    obtain ⟨hint, hle, hle2, hUE⟩ := hf f hrad hf0 hfi
    exact ⟨hint, hle, hle2.trans (mul_le_mul_of_nonneg_left hrq (integral_nonneg hf0)), hUE⟩
  · calc μ ((EventAtScale hd hΨ hε ξ E X n)ᶜ ∪ (legalSet X)ᶜ)
        ≤ μ (EventAtScale hd hΨ hε ξ E X n)ᶜ + μ (legalSet X)ᶜ := measure_union_le _ _
      _ = μ (EventAtScale hd hΨ hε ξ E X n)ᶜ := by rw [hnull, add_zero]
      _ ≤ _ := hev_bound

end CERW.Support.Norm.GaugeSourceContactConsequences
