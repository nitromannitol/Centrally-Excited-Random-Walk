import CERW.Support.Norm.GaugePointwise
import CERW.Support.Norm.GaugeProjectionEvents
import CERW.Support.Norm.GaugeCoarseClosed
import CERW.Support.Norm.GaugeContactShape
import CERW.Support.Contact.Quadratic
import CERW.Support.Norm.GaugeLocalTime
import CERW.Support.Norm.GaugeCoarseVolume
import CERW.Support.Main.BorelCantelli

/-!
# The limit shape of the walk driven by the gauge of a convex body

Let `K ⊆ ℝ^d`, `d ≥ 2`, be a compact convex set with the origin in its interior, `ψ = gauge K` its
Minkowski functional, which need not be even, `ε > 0` with `ε ψ(±e_i) < 1/d`, and `ξ(x) ∈ ∂ψ(x)` an
arbitrary selection of subgradients with `ξ(0) = 0`. For the walk with drift opposite to `ξ`
(`IsDriftCERW`) and the scale `r_n = ((d+1) n/(2 d ε |B_ψ|))^{1/(d+1)}`, this module proves

* Proposition `prop:norm-shape` (`gauge_shape_rates`): with probability at least `1 - C n^{-p}`, for
  every `n ≥ 2`, the inner radius, the outer radius and the local times satisfy the rates of the
  source; the constant is chosen before `ξ`, the probability space, the walk and `n`;
* Theorem `thm:norm-shape` (`gauge_shape`): almost surely, for every `η`, the range lies between the
  sublevel sets `{ψ < (1 ∓ η) r_n}` for all large `n`, the local times follow the cone
  `2 d ε (r_n - ψ)_+` up to `η r_n`, and every site is visited infinitely often;
* the one-sided bound on the inner radius (`gauge_inner_upper`) from the quadratic martingale, which
  does not use the contact bound;
* their instances for the cut disc and the triangle with corners.

The high-probability estimates are not assumed: the coarse bounds, the local time potential lemma,
the fine pointwise bound, the compensated path and the projection-direction events are the proved
statements of the modules that this module imports, and they are intersected at one event. On that
event the deterministic rates theorem `GaugeContactShape.Rates.ShapeRatesOfEvents` applies at the
deterministic scale for large `n`; the scale and logarithm regimes, the absorption of small `n`,
the Borel–Cantelli lemma and the passage from the rates to the limit shape are proved here.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.GaugeShapeEvents

open CERW CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel
  CERW.Support.Norm.GaugePotential CERW.Support.Norm.GaugeCoarseVolume

section Scale

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The scale `r_n = A n^{1/(d+1)}` with `A = ((d+1)/(2 d ε |B_ψ|))^{1/(d+1)}`. -/
private theorem coarseScale_eq_mul_rpow (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hV : 0 < normBallVolume Ψ)
    (n : ℕ) :
    coarseScale Ψ ε n =
      (((d : ℝ) + 1) / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1)) *
        (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  unfold coarseScale
  rw [← Real.mul_rpow (by positivity) (Nat.cast_nonneg n)]
  congr 1
  field_simp

/-- The scale tends to infinity. -/
theorem tendsto_coarseScale (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hV : 0 < normBallVolume Ψ) :
    Tendsto (coarseScale Ψ ε) atTop atTop := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hA : 0 < (((d : ℝ) + 1) / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (d + 1))) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  have h2 := h1.const_mul_atTop hA
  refine h2.congr fun n => ?_
  exact (coarseScale_eq_mul_rpow hd hε hV n).symm

/-- Every real power of `log n` is negligible against the scale. -/
theorem tendsto_log_rpow_div_coarseScale (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hV : 0 < normBallVolume Ψ) (K : ℝ) :
    Tendsto (fun n : ℕ => Real.log n ^ K / coarseScale Ψ ε n) atTop (𝓝 0) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  set A : ℝ := (((d : ℝ) + 1) / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1)) with hA
  have hApos : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  have hlo : Tendsto (fun x : ℝ => Real.log x ^ K / x ^ ((1 : ℝ) / (d + 1))) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop K (by positivity)).tendsto_div_nhds_zero
  have h1 := hlo.comp tendsto_natCast_atTop_atTop
  have h2 := h1.div_const A
  rw [zero_div] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp]
  rw [coarseScale_eq_mul_rpow hd hε hV n, ← hA]
  have hp : 0 < (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos hn0 _
  field_simp

/-- Eventually the scale exceeds any given level. -/
theorem eventually_le_coarseScale (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hV : 0 < normBallVolume Ψ)
    (R : ℝ) : ∀ᶠ n : ℕ in atTop, R ≤ coarseScale Ψ ε n :=
  (tendsto_coarseScale hd hε hV).eventually_ge_atTop R

/-- Eventually `1 ≤ log n`. -/
theorem eventually_one_le_log : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n := by
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_three]

end Scale


section Probability

variable {Ω : Type*} [MeasurableSpace Ω]

end Probability

section ShapeOfRates

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- A site whose value is below the inner radius lies in the departure range. -/
private theorem mem_departureRange_of_lt_normInnerRadius (hnn : ∀ y, 0 ≤ Ψ y) (Y : ℕ → Site d)
    (n : ℕ) {x : Site d} (hx : Ψ (toSpace x) < normInnerRadius Ψ Y n) :
    x ∈ departureRange Y n := by
  rw [← CERW.Support.Occupation.toSpace_mem_cellSet_iff]
  by_contra hnot
  have hbdd : BddBelow (Ψ '' (cellSet Y n)ᶜ) := ⟨0, by
    rintro _ ⟨y, -, rfl⟩
    exact hnn y⟩
  exact absurd hx (not_lt.mpr (csInf_le hbdd ⟨toSpace x, hnot, rfl⟩))

/-- A site of the departure range has value at most the outer radius. -/
private theorem le_normMaxRadius_of_mem (Y : ℕ → Site d) (n : ℕ) {x : Site d}
    (hx : x ∈ departureRange Y n) : Ψ (toSpace x) ≤ normMaxRadius Ψ Y n := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.le_sup' (fun j => Ψ (toSpace (Y j)))
    (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hj)))

/-- For `α < 1` and `ℓ ≥ 0`, `r^α ℓ^β / r = (ℓ^{β/(1-α)} / r)^{1-α}`. -/
private lemma rpow_mul_rpow_div_eq {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 ≤ ℓ) {α : ℝ} (hα : α < 1)
    (β : ℝ) : r ^ α * ℓ ^ β / r = (ℓ ^ (β / (1 - α)) / r) ^ (1 - α) := by
  have h1 : 1 - α ≠ 0 := (sub_pos.mpr hα).ne'
  have h2 : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  rw [Real.div_rpow (Real.rpow_nonneg hℓ _) hr.le, ← Real.rpow_mul hℓ, div_mul_cancel₀ _ h1,
    Real.rpow_sub hr, Real.rpow_one]
  field_simp

/-- `r^α (log n)^β` is negligible against `r` for `α < 1`, when every power of `log n` is
negligible against `r`. -/
private lemma tendsto_rpow_mul_rpow_log_div {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (hlog : ∀ K : ℝ, Tendsto (fun n : ℕ => Real.log n ^ K / r n) atTop (𝓝 0)) {α : ℝ}
    (hα : α < 1) (β : ℝ) :
    Tendsto (fun n : ℕ => r n ^ α * Real.log n ^ β / r n) atTop (𝓝 0) := by
  have hpos : 0 < 1 - α := sub_pos.mpr hα
  have hlim := (hlog (β / (1 - α))).rpow_const (Or.inr hpos.le)
  rw [Real.zero_rpow hpos.ne'] at hlim
  refine hlim.congr' ?_
  filter_upwards [hr.eventually_gt_atTop 0] with n hn
  exact (rpow_mul_rpow_div_eq hn (Real.log_natCast_nonneg n) hα β).symm

/-- The three error rates of the shape bounds are negligible against the scale `r`. -/
private theorem error_rates_small (hd : 2 ≤ d) {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (hlog : ∀ K : ℝ, Tendsto (fun n : ℕ => Real.log n ^ K / r n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (if d = 2 then r n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4)
        else (r n * Real.log n) ^ ((1 : ℝ) / 2)) / r n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((7 : ℝ) / 6)
        else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ (((d : ℝ) + 2) / (d + 1))) / r n)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
        else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))) / r n)
      atTop (𝓝 0) := by
  by_cases h2 : d = 2
  · simp only [if_pos h2]
    exact ⟨tendsto_rpow_mul_rpow_log_div hr hlog (by norm_num) _,
      tendsto_rpow_mul_rpow_log_div hr hlog (by norm_num) _,
      tendsto_rpow_mul_rpow_log_div hr hlog (by norm_num) _⟩
  · simp only [if_neg h2]
    have hdpos : (0 : ℝ) < d + 1 := by positivity
    have hα : (d : ℝ) / (d + 1) < 1 := by
      rw [div_lt_one hdpos]
      linarith
    refine ⟨?_, tendsto_rpow_mul_rpow_log_div hr hlog hα _,
      tendsto_rpow_mul_rpow_log_div hr hlog hα _⟩
    refine (tendsto_rpow_mul_rpow_log_div hr hlog (α := 1 / 2) (by norm_num) (1 / 2)).congr' ?_
    filter_upwards [hr.eventually_gt_atTop 0] with n hn
    rw [Real.mul_rpow hn.le (Real.log_natCast_nonneg n)]

/-- Multiplying a negligible error by a constant keeps it negligible. -/
private lemma tendsto_const_mul_div {r e : ℕ → ℝ} (C : ℝ)
    (h : Tendsto (fun n => e n / r n) atTop (𝓝 0)) :
    Tendsto (fun n => C * e n / r n) atTop (𝓝 0) := by
  simpa only [mul_zero, mul_div_assoc] using h.const_mul C

/-- The local times of a site visited only finitely often are bounded. -/
private lemma localTime_le_of_eventually_ne (Y : ℕ → Site d) (x : Site d) (m : ℕ)
    (hm : ∀ j : ℕ, m ≤ j → Y j ≠ x) (n : ℕ) : localTime Y n x ≤ m := by
  rw [localTime]
  calc ((Finset.range n).filter fun j => Y j = x).card
      ≤ (Finset.range m).card := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_filter] at hj
        obtain ⟨hjn, hjx⟩ := hj
        rw [Finset.mem_range] at hjn ⊢
        by_contra hjm
        exact hm j (Nat.le_of_not_lt hjm) hjx
    _ = m := Finset.card_range m

/-- The deterministic core of Theorem 2.1: if the inner radius, the outer radius and the local
times of a path agree with the scale `r` up to errors negligible against `r`, then the range is
asymptotically the `Ψ`-ball of radius `r`, the local times follow the profile, and every site is
visited infinitely often. -/
private theorem shape_of_small_errors (hd : 1 ≤ d) (hnn : ∀ y, 0 ≤ Ψ y) {ε : ℝ} (hε : 0 < ε)
    {r e₁ e₂ e₃ : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (h₁ : Tendsto (fun n => e₁ n / r n) atTop (𝓝 0))
    (h₂ : Tendsto (fun n => e₂ n / r n) atTop (𝓝 0))
    (h₃ : Tendsto (fun n => e₃ n / r n) atTop (𝓝 0)) (Y : ℕ → Site d)
    (hY : ∀ᶠ n : ℕ in atTop, |normInnerRadius Ψ Y n - r n| ≤ e₁ n ∧
        normMaxRadius Ψ Y n - r n ≤ e₂ n ∧
        ∀ x : Site d,
          |(localTime Y n x : ℝ) - 2 * d * ε * max (r n - Ψ (toSpace x)) 0| ≤ e₃ n) :
    (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
      {x : Site d | Ψ (toSpace x) < (1 - η) * r n} ⊆ ↑(departureRange Y n) ∧
      (↑(departureRange Y n) : Set (Site d)) ⊆ {x | Ψ (toSpace x) < (1 + η) * r n}) ∧
    (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
      |(localTime Y n x : ℝ) - 2 * d * ε * max (r n - Ψ (toSpace x)) 0| ≤ η * r n) ∧
    (∀ x : Site d, ∃ᶠ j in atTop, Y j = x) := by
  have hsmall : ∀ {e : ℕ → ℝ}, Tendsto (fun n => e n / r n) atTop (𝓝 0) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, e n < η * r n := by
    intro e he η hη
    filter_upwards [he.eventually (gt_mem_nhds hη), hr.eventually_gt_atTop 0] with n h1 h2
    exact (div_lt_iff₀ h2).mp h1
  have hloc : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
      |(localTime Y n x : ℝ) - 2 * d * ε * max (r n - Ψ (toSpace x)) 0| ≤ η * r n := by
    intro η hη
    filter_upwards [hY, hsmall h₃ η hη] with n hn h3 x
    exact (hn.2.2 x).trans h3.le
  refine ⟨?_, hloc, ?_⟩
  · intro η hη hη1
    filter_upwards [hY, hsmall h₁ η hη, hsmall h₂ η hη] with n hn h1 h2
    obtain ⟨hin, hout, -⟩ := hn
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · refine mem_departureRange_of_lt_normInnerRadius hnn Y n ?_
      have h3 := (abs_le.mp hin).1
      simp only [Set.mem_setOf_eq] at hx
      linarith
    · have h3 := le_normMaxRadius_of_mem (Ψ := Ψ) Y n (Finset.mem_coe.mp hx)
      simp only [Set.mem_setOf_eq]
      linarith
  · intro x
    by_contra hnot
    rw [not_frequently] at hnot
    obtain ⟨m, hm⟩ := eventually_atTop.mp hnot
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hκ : 0 < (d : ℝ) * ε := mul_pos hdpos hε
    obtain ⟨n, hn1, hn2⟩ := ((hloc _ hκ).and
      (hr.eventually_gt_atTop ((m + 2 * ((d : ℝ) * ε) * Ψ (toSpace x)) / ((d : ℝ) * ε)))).exists
    have hle : (localTime Y n x : ℝ) ≤ m := by
      exact_mod_cast localTime_le_of_eventually_ne Y x m hm n
    have h4 := (abs_le.mp (hn1 x)).1
    have h5 : r n - Ψ (toSpace x) ≤ max (r n - Ψ (toSpace x)) 0 := le_max_left _ _
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 2 * d * ε)
    have h7 := (div_lt_iff₀ hκ).mp hn2
    linarith

end ShapeOfRates

section Statements

/-- **Proposition `prop:norm-shape` for the Minkowski functional of a convex body.** For every
`p > 0` there is `C`, chosen before the subgradient selection, the probability space, the walk and
`n`, such that for every `n ≥ 2` the radii and the local times of the walk of drift opposite to
a selection of subgradients of `ψ = gauge K` satisfy simultaneously the three rates, with
probability at least `1 - C n^{-p}`. The scale is `r_n = ((d+1) n/(2 d ε |B_ψ|))^{1/(d+1)}`. -/
def GaugeShapeRates : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}, IsCompact K → Convex ℝ K →
    (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K →
    ∀ ε : ℝ, 0 < ε →
    (∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ)) →
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * normBallVolume (gauge K))) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (|normInnerRadius (gauge K) (X · ω) n - r n|
                    ≤ C * (if d = 2 then r n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4)
                      else (r n * Real.log n) ^ ((1 : ℝ) / 2)) ∧
                  normMaxRadius (gauge K) (X · ω) n - r n
                    ≤ C * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((7 : ℝ) / 6)
                      else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ (((d : ℝ) + 2) / (d + 1))) ∧
                  ∀ x : Site d,
                    |(localTime (X · ω) n x : ℝ)
                        - 2 * d * ε * max (r n - gauge K (toSpace x)) 0|
                      ≤ C * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
                        else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))

/-- **Theorem `thm:norm-shape` for the Minkowski functional of a convex body.** Almost surely, for
every `η ∈ (0,1)` and all large `n`, the range lies between the sublevel sets `{ψ < (1 ∓ η) r_n}`;
the local times follow the cone `2 d ε (r_n - ψ)_+` up to `η r_n`; and every site is visited
infinitely often. -/
def GaugeShape : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}, IsCompact K → Convex ℝ K →
    (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K →
    ∀ {ξ : Site d → EuclideanSpace ℝ (Fin d)},
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
    ∀ {ε : ℝ}, 0 < ε →
    (∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ)) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X →
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * normBallVolume (gauge K))) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
        {x : Site d | gauge K (toSpace x) < (1 - η) * r n} ⊆ ↑(departureRange (X · ω) n) ∧
        (↑(departureRange (X · ω) n) : Set (Site d)) ⊆
          {x | gauge K (toSpace x) < (1 + η) * r n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
        |(localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - gauge K (toSpace x)) 0|
          ≤ η * r n) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x)

/-- **Theorem `thm:norm-shape` from Proposition `prop:norm-shape`** for the gauge of a convex
body: the rates with `p = 2` hold eventually almost surely (Borel–Cantelli), and they are
negligible against the scale `r_n`. No producer is used: this is the deterministic passage from the
rates to the limit shape. -/
theorem gauge_shape_of_rates (hrates : GaugeShapeRates.{u}) : GaugeShape.{u} := by
  intro d hd K hK hc h0 ξ hξ hξ0 ε hε hell Ω _ μ _ X hX r
  have hd1 : 1 ≤ d := by omega
  have hV : 0 < normBallVolume (gauge K) := normBallVolume_gauge_pos hK hc h0
  obtain ⟨C, hC, hCb⟩ := hrates hd hK hc h0 ε hε hell 2 (by norm_num)
  have hr : Tendsto r atTop atTop := tendsto_coarseScale hd1 hε hV
  have hlog : ∀ K : ℝ, Tendsto (fun n : ℕ => Real.log n ^ K / r n) atTop (𝓝 0) :=
    tendsto_log_rpow_div_coarseScale hd1 hε hV
  obtain ⟨t₁, t₂, t₃⟩ := error_rates_small hd hr hlog
  have hev := CERW.Support.Main.ae_eventually_of_le_rpow (p := 2) (n₀ := 2) (by norm_num)
    (fun n hn => hCb ξ hξ hξ0 μ X hX n hn)
  filter_upwards [hev] with ω hω
  exact shape_of_small_errors hd1 (fun y => gauge_nonneg y) hε hr (tendsto_const_mul_div C t₁)
    (tendsto_const_mul_div C t₂) (tendsto_const_mul_div C t₃) (fun j => X j ω) hω

end Statements

section RateForms

variable {d : ℕ}

/-- A power of a square root is a power of the radicand: `(√x)^a = x^(a/2)`. -/
private theorem sqrt_rpow_eq {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    Real.sqrt x ^ a = x ^ (a / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

/-- For positive `r` and `ℓ`, `r * (ℓ / r)^a = r^(1 - a) * ℓ^a`. -/
private theorem mul_div_rpow_eq {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) (a : ℝ) :
    r * (ℓ / r) ^ a = r ^ (1 - a) * ℓ ^ a := by
  rw [Real.div_rpow hℓ.le hr.le, Real.rpow_sub hr, Real.rpow_one]
  ring

/-- The exponent `1 - 1/(d+1)` equals `d/(d+1)`. -/
private theorem one_sub_inv_succ (d : ℕ) :
    (1 : ℝ) - 1 / ((d : ℝ) + 1) = (d : ℝ) / ((d : ℝ) + 1) := by
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The exponent `1/(d+1) + 1` equals `(d+2)/(d+1)`. -/
private theorem inv_succ_add_one (d : ℕ) :
    (1 : ℝ) / ((d : ℝ) + 1) + 1 = ((d : ℝ) + 2) / ((d : ℝ) + 1) := by
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- `r q^{1/2}` is the explicit inner-radius rate of Proposition 5.1. -/
private theorem rate_inner_eq {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) :
    r * GaugeContactShape.Rates.rateQ d r ℓ ^ ((1 : ℝ) / 2) =
      if d = 2 then r ^ ((3 : ℝ) / 4) * ℓ ^ ((1 : ℝ) / 4) else (r * ℓ) ^ ((1 : ℝ) / 2) := by
  have hq : 0 ≤ ℓ / r := div_nonneg hℓ.le hr.le
  by_cases h2 : d = 2
  · simp only [GaugeContactShape.Rates.rateQ, if_pos h2]
    rw [sqrt_rpow_eq hq, mul_div_rpow_eq hr hℓ]
    norm_num
  · simp only [GaugeContactShape.Rates.rateQ, if_neg h2]
    rw [mul_div_rpow_eq hr hℓ, Real.mul_rpow hr.le hℓ.le]
    norm_num

/-- `r q^{1/(d+1)}` is the explicit profile rate of Proposition 5.1. -/
private theorem rate_local_eq {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) :
    r * GaugeContactShape.Rates.rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) =
      if d = 2 then r ^ ((5 : ℝ) / 6) * ℓ ^ ((1 : ℝ) / 6)
      else r ^ ((d : ℝ) / (d + 1)) * ℓ ^ ((1 : ℝ) / (d + 1)) := by
  have hq : 0 ≤ ℓ / r := div_nonneg hℓ.le hr.le
  by_cases h2 : d = 2
  · have hd2 : (d : ℝ) = 2 := by exact_mod_cast h2
    simp only [GaugeContactShape.Rates.rateQ, if_pos h2]
    rw [sqrt_rpow_eq hq, mul_div_rpow_eq hr hℓ, hd2]
    norm_num
  · simp only [GaugeContactShape.Rates.rateQ, if_neg h2]
    rw [mul_div_rpow_eq hr hℓ, one_sub_inv_succ]

/-- `r q^{1/(d+1)} log n` is the explicit outer-radius rate of Proposition 5.1. -/
private theorem rate_outer_eq {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) :
    r * GaugeContactShape.Rates.rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) * ℓ =
      if d = 2 then r ^ ((5 : ℝ) / 6) * ℓ ^ ((7 : ℝ) / 6)
      else r ^ ((d : ℝ) / (d + 1)) * ℓ ^ (((d : ℝ) + 2) / (d + 1)) := by
  rw [rate_local_eq hr hℓ]
  by_cases h2 : d = 2
  · simp only [if_pos h2]
    rw [mul_assoc, ← Real.rpow_add_one hℓ.ne']
    norm_num
  · simp only [if_neg h2]
    rw [mul_assoc, ← Real.rpow_add_one hℓ.ne', inv_succ_add_one]

/-- The three rates of `ShapeRatesOfEvents`, in the form with the rate `q`, are the explicit rates
of Proposition 5.1, at a scale `r > 0` and `ℓ = log n > 0`. -/
private theorem explicit_rates_of_rateQ {K : Set (EuclideanSpace ℝ (Fin d))}
    {Y : ℕ → Site d} {n : ℕ}
    {ε r C : ℝ} (hr : 0 < r) (hℓ : 0 < Real.log n)
    (h : |normInnerRadius (gauge K) Y n - r| ≤
          C * (r * GaugeContactShape.Rates.rateQ d r (Real.log n) ^ ((1 : ℝ) / 2)) ∧
        normMaxRadius (gauge K) Y n - r ≤
          C * (r * GaugeContactShape.Rates.rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)) *
            Real.log n) ∧
        ∀ y : EuclideanSpace ℝ (Fin d),
          |cellLocalTime Y n y - 2 * d * ε * max (r - gauge K y) 0| ≤
            C * (r * GaugeContactShape.Rates.rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)))) :
    |normInnerRadius (gauge K) Y n - r|
        ≤ C * (if d = 2 then r ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4)
          else (r * Real.log n) ^ ((1 : ℝ) / 2)) ∧
      normMaxRadius (gauge K) Y n - r
        ≤ C * (if d = 2 then r ^ ((5 : ℝ) / 6) * Real.log n ^ ((7 : ℝ) / 6)
          else r ^ ((d : ℝ) / (d + 1)) * Real.log n ^ (((d : ℝ) + 2) / (d + 1))) ∧
      ∀ x : Site d,
        |(localTime Y n x : ℝ) - 2 * d * ε * max (r - gauge K (toSpace x)) 0|
          ≤ C * (if d = 2 then r ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
            else r ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← rate_inner_eq hr hℓ]
    exact h₁
  · rw [← rate_outer_eq hr hℓ]
    exact h₂
  · intro x
    have h := h₃ (toSpace x)
    rw [cellLocalTime_of_mem_cell _ _ (toSpace_mem_cell x)] at h
    rw [← rate_local_eq hr hℓ]
    exact h

end RateForms

/-! ## The quadratic martingale of the walk driven by a gauge -/

section Quadratic

open CERW.Support.Drift CERW.Support.Law CERW.Support.Occupation CERW.Support.Contact

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- At a first departure from a nonzero site `x_j`, the squared-norm increment of the next step is
`1 - 2 ε ψ(x_j)`: the central difference of `|·|²` is `2 x` and Euler's relation gives
`ξ(x_j) · x_j = ψ(x_j)`; elsewhere it is `1`. -/
private theorem driftNextMean_sq_sub (hd : 1 ≤ d) (ε : ℝ) {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x))
    (x : ℕ → Site d) (j : ℕ) :
    driftNextMean ε ξ (fun z : Site d => euclidNorm z ^ 2) x j - euclidNorm (x j) ^ 2 =
      1 - (if x j ≠ 0 ∧ x j ∉ (Finset.range j).image x then
        2 * ε * gauge K (toSpace (x j)) else 0) := by
  rw [driftNextMean, sum_driftStepProb_mul ε ξ x j (fun z : Site d => euclidNorm z ^ 2),
    walkOp_sq_euclidNorm hd]
  split_ifs with h
  · rw [centralDiff_sq_euclidNorm, inner_smul_right,
      ((isSubgradient_gauge_iff K).mp (hξ (x j) h.1)).1]
    ring
  · ring

/-- **`eq:quadratic` for the gauge, pathwise.** For a path from the origin and the drift field `ξ`
of a selection of subgradients of `ψ`, `|x_n|² = n - 2 ε Σ_{y ∈ A_n} ψ(y) + 𝒬_n`, where `𝒬` is the
Dynkin martingale of `|·|²` for the drift one-step law. -/
theorem sq_euclidNorm_eq_gauge (hd : 1 ≤ d) (ε : ℝ) {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) (x : ℕ → Site d)
    (h0 : x 0 = 0) (n : ℕ) :
    euclidNorm (x n) ^ 2 =
      n - 2 * ε * ∑ y ∈ departureRange x n, gauge K (toSpace y) +
        dynkinMart (driftStepProb d ε ξ) (fun z : Site d => euclidNorm z ^ 2) x n := by
  have hfresh : ∑ j ∈ Finset.range n,
      (if x j ≠ 0 ∧ x j ∉ (Finset.range j).image x then gauge K (toSpace (x j)) else 0) =
      ∑ y ∈ departureRange x n, gauge K (toSpace y) := by
    rw [sum_fresh_ne_zero_eq_sum_departureRange x n (fun z => gauge K (toSpace z))]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : z = 0
    · subst hz
      have : toSpace (0 : Site d) = 0 := by
        ext i
        simp [toSpace]
      simp [this]
    · simp [hz]
  have hfact : ∑ j ∈ Finset.range n,
      (if x j ≠ 0 ∧ x j ∉ (Finset.range j).image x then
        2 * ε * gauge K (toSpace (x j)) else 0) =
      2 * ε * ∑ j ∈ Finset.range n,
        (if x j ≠ 0 ∧ x j ∉ (Finset.range j).image x then gauge K (toSpace (x j)) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : x j ≠ 0 ∧ x j ∉ (Finset.range j).image x <;> simp [hc]
  have hsum : ∑ j ∈ Finset.range n,
      (driftNextMean ε ξ (fun z : Site d => euclidNorm z ^ 2) x j - euclidNorm (x j) ^ 2) =
        n - 2 * ε * ∑ y ∈ departureRange x n, gauge K (toSpace y) := by
    simp_rw [driftNextMean_sq_sub hd ε hξ x]
    rw [Finset.sum_sub_distrib, hfact, hfresh]
    simp
  have hm : dynkinMart (driftStepProb d ε ξ) (fun z : Site d => euclidNorm z ^ 2) x n =
      euclidNorm (x n) ^ 2 - euclidNorm (x 0) ^ 2 -
        ∑ j ∈ Finset.range n,
          (driftNextMean ε ξ (fun z : Site d => euclidNorm z ^ 2) x j - euclidNorm (x j) ^ 2) := by
    simp only [dynkinMart, stepMean_driftStepProb hd]
  rw [hm, hsum, h0]
  simp

end Quadratic

/-! ## The truncated quadratic martingale and its failure probability -/

section QuadraticEvent

open CERW.Support.Drift CERW.Support.Law CERW.Support.Occupation

variable {d : ℕ}

/-- The squared norm truncated at the level `k`. -/
noncomputable def truncSq (k : ℕ) (z : Site d) : ℝ := (min (euclidNorm z) k) ^ 2

/-- The truncated squared norm agrees with the squared norm below the level `k`. -/
private theorem truncSq_eq (k : ℕ) {z : Site d} (hz : euclidNorm z ≤ k) :
    truncSq k z = euclidNorm z ^ 2 := by
  rw [truncSq, min_eq_left hz]

/-- A unit step changes the truncated squared norm by at most `2k`. -/
private theorem abs_truncSq_sub_le (k : ℕ) (z : Site d) {e : Site d} (he : e ∈ unitSteps d) :
    |truncSq k (z + e) - truncSq k z| ≤ 2 * k := by
  have hnorm : |euclidNorm (z + e) - euclidNorm z| ≤ 1 := by
    have h1 : euclidNorm (z + e) = ‖toSpace (z + e)‖ := (norm_toSpace _).symm
    have h2 : euclidNorm z = ‖toSpace z‖ := (norm_toSpace _).symm
    have h3 : toSpace (z + e) = toSpace z + toSpace e := by
      ext i
      simp [toSpace]
    rw [h1, h2, h3]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [add_sub_cancel_left, norm_toSpace, euclidNorm_of_mem_unitSteps he]
  have hab : |min (euclidNorm (z + e)) (k : ℝ) - min (euclidNorm z) (k : ℝ)| ≤ 1 := by
    have h := abs_min_sub_min_le_max (euclidNorm (z + e)) (k : ℝ) (euclidNorm z) (k : ℝ)
    rw [sub_self, abs_zero] at h
    exact h.trans (max_le hnorm zero_le_one)
  have ha0 : 0 ≤ min (euclidNorm (z + e)) (k : ℝ) :=
    le_min (LatticeProb.euclidNorm_nonneg _) (Nat.cast_nonneg k)
  have hb0 : 0 ≤ min (euclidNorm z) (k : ℝ) := le_min (LatticeProb.euclidNorm_nonneg _)
      (Nat.cast_nonneg k)
  have hak : min (euclidNorm (z + e)) (k : ℝ) ≤ k := min_le_right _ _
  have hbk : min (euclidNorm z) (k : ℝ) ≤ k := min_le_right _ _
  unfold truncSq
  have hfac : min (euclidNorm (z + e)) (k : ℝ) ^ 2 - min (euclidNorm z) (k : ℝ) ^ 2 =
      (min (euclidNorm (z + e)) (k : ℝ) - min (euclidNorm z) (k : ℝ)) *
        (min (euclidNorm (z + e)) (k : ℝ) + min (euclidNorm z) (k : ℝ)) := by ring
  rw [hfac, abs_mul, abs_of_nonneg (add_nonneg ha0 hb0)]
  calc _ ≤ 1 * (2 * (k : ℝ)) := mul_le_mul hab (by linarith) (add_nonneg ha0 hb0) zero_le_one
    _ = 2 * k := one_mul _

/-- The predictable bracket of the rescaling `c M` of a martingale is at most
`c² K ∑_{t<n} g_t` whenever the conditional variances of the increments of `M` are at most
`K g_t`. -/
private lemma predBracket_smul_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (c K : ℝ) (g : ℕ → Ω → ℝ)
    (hvar : ∀ t, μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t] ≤ᵐ[μ] fun ω => K * g t ω) :
    ∀ᵐ ω ∂μ, ∀ n, predBracket μ ℱ (fun t ω => c * M t ω) (fun t ω => c * M t ω) n ω ≤
      c ^ 2 * (K * ∑ t ∈ Finset.range n, g t ω) := by
  have hscale : ∀ t,
      μ[fun ω => (c * M (t + 1) ω - c * M t ω) * (c * M (t + 1) ω - c * M t ω) | ℱ t]
        =ᵐ[μ] fun ω => c ^ 2 * μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t] ω := by
    intro t
    have hfun : (fun ω => (c * M (t + 1) ω - c * M t ω) * (c * M (t + 1) ω - c * M t ω)) =
        (c ^ 2) • fun ω => (M (t + 1) ω - M t ω) ^ 2 := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun]
    exact condExp_smul (c ^ 2) _ (ℱ t)
  filter_upwards [ae_all_iff.mpr hvar, ae_all_iff.mpr hscale] with ω h1 h2 n
  unfold predBracket
  rw [Finset.sum_apply]
  calc ∑ t ∈ Finset.range n,
        μ[fun ω => (c * M (t + 1) ω - c * M t ω) * (c * M (t + 1) ω - c * M t ω) | ℱ t] ω
      ≤ ∑ t ∈ Finset.range n, c ^ 2 * (K * g t ω) := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [h2 t]
        exact mul_le_mul_of_nonneg_left (h1 t) (sq_nonneg c)
    _ = c ^ 2 * (K * ∑ t ∈ Finset.range n, g t ω) := by
        rw [Finset.mul_sum, Finset.mul_sum]

/-- Rescaling: if `|c M_n - c M_0| ≤ C_F (√(b L) + L)` with `c (2 B) = 1`, `M_0 = 0` and
`b ≤ S`, then `|M_n| ≤ 2 B C_F (√(L S) + L)`. -/
private lemma abs_le_of_rescaled {c B C_F L b S M₀ Mₙ : ℝ} (hB : 0 ≤ B) (hc : c * (2 * B) = 1)
    (hC_F : 0 ≤ C_F) (hL : 0 ≤ L) (hbS : b ≤ S) (hM₀ : M₀ = 0)
    (h : |c * Mₙ - c * M₀| ≤ C_F * (Real.sqrt (b * L) + L)) :
    |Mₙ| ≤ 2 * B * C_F * (Real.sqrt (L * S) + L) := by
  have hMn : Mₙ = 2 * B * (c * Mₙ) := by
    calc Mₙ = (c * (2 * B)) * Mₙ := by rw [hc, one_mul]
      _ = 2 * B * (c * Mₙ) := by ring
  rw [hM₀, mul_zero, sub_zero] at h
  have habs : |Mₙ| = 2 * B * |c * Mₙ| := by
    have h2B : (0 : ℝ) ≤ 2 * B := by linarith
    calc |Mₙ| = |2 * B * (c * Mₙ)| := congrArg (fun x => |x|) hMn
      _ = 2 * B * |c * Mₙ| := by rw [abs_mul, abs_of_nonneg h2B]
  have hsqrt : Real.sqrt (b * L) ≤ Real.sqrt (L * S) :=
    Real.sqrt_le_sqrt (by rw [mul_comm L S]; exact mul_le_mul_of_nonneg_right hbS hL)
  calc |Mₙ| = 2 * B * |c * Mₙ| := habs
    _ ≤ 2 * B * (C_F * (Real.sqrt (b * L) + L)) :=
        mul_le_mul_of_nonneg_left h (by linarith)
    _ ≤ 2 * B * (C_F * (Real.sqrt (L * S) + L)) := by
        gcongr
    _ = 2 * B * C_F * (Real.sqrt (L * S) + L) := by ring

/-- For one level `k`, the Dynkin martingale of the truncated squared norm of the drift walk exceeds
`2 (2k + 1) C_F (√(log n · n) + log n)` with probability at most `C_F n^{-p}`, given Freedman's
bound for the natural filtration of the walk. -/
private lemma measure_quad_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    {X : ℕ → Ω → Site d} (hd : 1 ≤ d) (hε : 0 ≤ ε) (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    (hX : IsDriftCERW μ ε ξ X) (k : ℕ) {n : ℕ} {C_F p : ℝ} (hC_F : 0 ≤ C_F)
    (hF : ∀ Z : ℕ → Ω → ℝ, Martingale Z (pathFiltration hX.measurable) μ →
      (∀ᵐ ω ∂μ, ∀ t, |Z (t + 1) ω - Z t ω| ≤ 1) →
      μ {ω | ¬ |Z n ω - Z 0 ω| ≤ C_F * (Real.sqrt (predBracket μ (pathFiltration hX.measurable)
          Z Z n ω * Real.log n) + Real.log n)} ≤ ENNReal.ofReal (C_F * (n : ℝ) ^ (-p))) :
    μ {ω | 2 * (2 * k + 1) * C_F * (Real.sqrt (Real.log n * n) + Real.log n) <
        |dynkinMart (driftStepProb d ε ξ) (truncSq k) (fun j => X j ω) n|} ≤
      ENNReal.ofReal (C_F * (n : ℝ) ^ (-p)) := by
  classical
  set ℱ := pathFiltration hX.measurable with hℱ
  set f : Site d → ℝ := truncSq k with hf
  set c : ℝ := (2 * (2 * (k : ℝ) + 1))⁻¹ with hc
  have hB : 0 < 2 * (2 * (k : ℝ) + 1) := by positivity
  have hc0 : 0 ≤ c := inv_nonneg.mpr hB.le
  have hc1 : c * (2 * (2 * (k : ℝ) + 1)) = 1 := inv_mul_cancel₀ hB.ne'
  have hck : c * (2 * (2 * k)) ≤ 1 := by
    calc c * (2 * (2 * (k : ℝ))) ≤ c * (2 * (2 * (k : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) hc0
      _ = 1 := hc1
  have hck1 : c * (2 * k) ≤ 1 := by
    have h2 : c * (2 * (2 * (k : ℝ))) = 2 * (c * (2 * k)) := by ring
    linarith
  have hM := martingale_driftDynkin hd hε hξ hX f
  have hZ : Martingale (fun t ω => c * driftDynkin ε ξ f X t ω) ℱ μ := hM.smul c
  have hinc : ∀ᵐ ω ∂μ, ∀ t,
      |driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω| ≤ 2 * (2 * k) := by
    filter_upwards [ae_abs_driftDynkin_succ_sub_le hd hε hξ hX f] with ω hω t
    exact hω t (2 * k) fun e he => abs_truncSq_sub_le k (X t ω) he
  have hincZ : ∀ᵐ ω ∂μ, ∀ t,
      |c * driftDynkin ε ξ f X (t + 1) ω - c * driftDynkin ε ξ f X t ω| ≤ 1 := by
    filter_upwards [hinc] with ω hω t
    rw [← mul_sub, abs_mul, abs_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_left (hω t) hc0).trans hck
  have hvar : ∀ t, μ[fun ω => (driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω) ^ 2 |
        ℱ t] ≤ᵐ[μ] fun ω => ((2 * (k : ℝ)) ^ 2) * (fun _ _ => (1 : ℝ)) t ω := by
    intro t
    refine (condExp_sq_driftDynkin_succ_sub_le hd hε hξ hX f t).trans
      (Filter.Eventually.of_forall fun ω => ?_)
    calc ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
          (f (X t ω + e) - f (X t ω)) ^ 2
        ≤ ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e * (2 * (k : ℝ)) ^ 2 := by
          refine Finset.sum_le_sum fun e he => ?_
          refine mul_le_mul_of_nonneg_left ?_ (driftStepProb_nonneg hε hξ _ t e)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_truncSq_sub_le k (X t ω) he) 2
      _ = (2 * (k : ℝ)) ^ 2 * 1 := by
          rw [← Finset.sum_mul, sum_driftStepProb hd ε ξ _ t, one_mul, mul_one]
  have hbr := predBracket_smul_le ℱ (driftDynkin ε ξ f X) c ((2 * (k : ℝ)) ^ 2)
    (fun _ _ => (1 : ℝ)) hvar
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  refine le_trans (measure_mono_ae ?_) (hF _ hZ hincZ)
  filter_upwards [hbr] with ω hω hmem
  intro hle
  have hcΛ2 : c ^ 2 * (2 * (k : ℝ)) ^ 2 ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (mul_nonneg hc0 (by positivity)) hck1
  have hbS : predBracket μ ℱ (fun t ω => c * driftDynkin ε ξ f X t ω)
        (fun t ω => c * driftDynkin ε ξ f X t ω) n ω ≤ (n : ℝ) := by
    calc predBracket μ ℱ (fun t ω => c * driftDynkin ε ξ f X t ω)
          (fun t ω => c * driftDynkin ε ξ f X t ω) n ω
        ≤ c ^ 2 * ((2 * (k : ℝ)) ^ 2 * ∑ t ∈ Finset.range n, (1 : ℝ)) := hω n
      _ = (c ^ 2 * (2 * (k : ℝ)) ^ 2) * n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          ring
      _ ≤ 1 * n := mul_le_mul_of_nonneg_right hcΛ2 (Nat.cast_nonneg n)
      _ = n := one_mul _
  have hmem' : 2 * (2 * (k : ℝ) + 1) * C_F * (Real.sqrt (Real.log n * n) + Real.log n) <
        |driftDynkin ε ξ f X n ω| := by
    rw [← dynkinMart_driftStepProb_eq_driftDynkin hd ε ξ f X n ω]
    exact hmem
  exact absurd hmem' (not_lt.mpr (abs_le_of_rescaled (by positivity) hc1 hC_F hL hbS
    (driftDynkin_zero ε ξ f X ω) hle))

end QuadraticEvent

/-! ## The quadratic martingale event for all levels -/

section QuadraticFailure

open CERW.Support.Drift CERW.Support.Law CERW.Support.Occupation

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- **The quadratic martingale event.** For every `p > 0` there are constants `C_Q, C`, chosen from
the drift strength and the dimension, such that for every selection `ξ` of subgradients, every walk
and every `n ≥ 2`, with probability at least `1 - C n^{-p}` the Dynkin martingale of the squared
norm truncated at the level `k` is at most `C_Q (2k + 1) (√(n log n) + log n)` in modulus at time
`n`, simultaneously for all `k ≤ n + 2` (the union bound over the levels). -/
theorem exists_quadratic_failure_bound (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ C_Q C : ℝ, 0 < C_Q ∧ 0 < C ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ ∀ k : ℕ, k ≤ n + 2 →
            |dynkinMart (driftStepProb d ε ξ) (truncSq k) (fun j => X j ω) n| ≤
              C_Q * (2 * k + 1) * (Real.sqrt (Real.log n * n) + Real.log n)} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C_F, hC_F, hfree⟩ := CERW.Support.Norm.freedman_bound.{u} (p + 1) (by linarith)
  refine ⟨2 * C_F, 4 * C_F, by positivity, by positivity, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hξ' := drift_coord_bound_gauge hε.le hell hξ hξ0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg hnpos.le _
  have hF := fun (Z : ℕ → Ω → ℝ) (hZ : Martingale Z (pathFiltration hX.measurable) μ)
    (hinc : ∀ᵐ ω ∂μ, ∀ t, |Z (t + 1) ω - Z t ω| ≤ 1) =>
    hfree n hn μ (pathFiltration hX.measurable) Z hZ hinc
  set E : ℕ → Set Ω := fun k => {ω | 2 * (2 * k + 1) * C_F *
      (Real.sqrt (Real.log n * n) + Real.log n) <
        |dynkinMart (driftStepProb d ε ξ) (truncSq k) (fun j => X j ω) n|} with hE
  have key : ∀ k : ℕ, μ (E k) ≤ ENNReal.ofReal (C_F * (n : ℝ) ^ (-(p + 1))) := fun k =>
    measure_quad_le hd1 hε.le hξ' hX k hC_F.le hF
  have hsub : {ω | ¬ ∀ k : ℕ, k ≤ n + 2 →
        |dynkinMart (driftStepProb d ε ξ) (truncSq k) (fun j => X j ω) n| ≤
          2 * C_F * (2 * k + 1) * (Real.sqrt (Real.log n * n) + Real.log n)} ⊆
      ⋃ k ∈ Finset.range (n + 3), E k := by
    intro ω hω
    simp only [Set.mem_setOf_eq, not_forall, not_le] at hω
    obtain ⟨k, hk, hlt⟩ := hω
    simp only [Set.mem_iUnion]
    refine ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
    simp only [hE, Set.mem_setOf_eq]
    calc 2 * (2 * (k : ℝ) + 1) * C_F * (Real.sqrt (Real.log n * n) + Real.log n)
        = 2 * C_F * (2 * k + 1) * (Real.sqrt (Real.log n * n) + Real.log n) := by ring
      _ < _ := hlt
  have hpow : (n : ℝ) ^ (-(p + 1)) = (n : ℝ) ^ (-p) * (n : ℝ)⁻¹ := by
    rw [show -(p + 1) = -p + -1 by ring, Real.rpow_add hnpos, Real.rpow_neg_one]
  have hnp1 : (n : ℝ) ^ (-(p + 1)) ≥ 0 := Real.rpow_nonneg hnpos.le _
  have hn3 : ((n : ℝ) + 3) * (n : ℝ)⁻¹ ≤ 4 := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    rw [← div_eq_mul_inv, div_le_iff₀ hnpos]
    linarith
  calc μ {ω | ¬ ∀ k : ℕ, k ≤ n + 2 →
          |dynkinMart (driftStepProb d ε ξ) (truncSq k) (fun j => X j ω) n| ≤
            2 * C_F * (2 * k + 1) * (Real.sqrt (Real.log n * n) + Real.log n)}
      ≤ μ (⋃ k ∈ Finset.range (n + 3), E k) := measure_mono hsub
    _ ≤ ∑ k ∈ Finset.range (n + 3), μ (E k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 3), ENNReal.ofReal (C_F * (n : ℝ) ^ (-(p + 1))) :=
        Finset.sum_le_sum fun k _ => key k
    _ = ENNReal.ofReal (((n + 3 : ℕ) : ℝ) * (C_F * (n : ℝ) ^ (-(p + 1)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (4 * C_F * (n : ℝ) ^ (-p)) := by
        apply ENNReal.ofReal_le_ofReal
        push_cast
        rw [hpow]
        calc ((n : ℝ) + 3) * (C_F * ((n : ℝ) ^ (-p) * (n : ℝ)⁻¹))
            = C_F * (n : ℝ) ^ (-p) * (((n : ℝ) + 3) * (n : ℝ)⁻¹) := by ring
          _ ≤ C_F * (n : ℝ) ^ (-p) * 4 :=
              mul_le_mul_of_nonneg_left hn3 (mul_nonneg hC_F.le hnp)
          _ = 4 * C_F * (n : ℝ) ^ (-p) := by ring

end QuadraticFailure

/-! ## The mass of a sublevel set of the gauge and of the cell set -/

section ConeMass

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- The volume of a sublevel set of the gauge, as a real number: `ρ^d |B_ψ|`. -/
private theorem real_volume_gauge_sublevel (hΨ : GaugeContactShape.Adm K) (hd : 1 ≤ d) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    volume.real {v : EuclideanSpace ℝ (Fin d) | gauge K v < ρ} =
      ρ ^ d * normBallVolume (gauge K) := by
  rw [Measure.real, volume_gauge_sublevel hΨ.compact hΨ.zero_mem hd hρ,
    ENNReal.toReal_ofReal]
  exact mul_nonneg (pow_nonneg hρ _) ENNReal.toReal_nonneg

/-- The integral of the cone function `max (b - ψ) 0` over a ball of radius `S ≥ b / c_ψ` is
`|B_ψ| b^{d+1}/(d+1)`. -/
private theorem integral_cone_gauge (hΨ : GaugeContactShape.Adm K) (hd : 1 ≤ d) {b S : ℝ}
    (hb : 0 ≤ b)
    (hS : b / normMin (gauge K) ≤ S) :
    ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S, max (b - gauge K y) 0 =
      normBallVolume (gauge K) * b ^ (d + 1) / (d + 1) := by
  obtain ⟨hc, hle⟩ := hΨ.normMin_pos_mul_le hd
  have hcont : Continuous (gauge K) := hΨ.continuous
  have hnn : ∀ y, 0 ≤ gauge K y := hΨ.nonneg
  have hfcont : Continuous fun y : EuclideanSpace ℝ (Fin d) => max (b - gauge K y) 0 :=
    (continuous_const.sub hcont).max continuous_const
  have hfzero : ∀ y : EuclideanSpace ℝ (Fin d), S ≤ ‖y‖ → max (b - gauge K y) 0 = 0 := by
    intro y hy
    have hby : b ≤ gauge K y := by
      calc b = (b / normMin (gauge K)) * normMin (gauge K) := (div_mul_cancel₀ b hc.ne').symm
        _ ≤ ‖y‖ * normMin (gauge K) := mul_le_mul_of_nonneg_right (hS.trans hy) hc.le
        _ = normMin (gauge K) * ‖y‖ := mul_comm _ _
        _ ≤ gauge K y := hle y
    exact max_eq_right (by linarith)
  have hint : Integrable fun y : EuclideanSpace ℝ (Fin d) => max (b - gauge K y) 0 := by
    refine hfcont.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S) ?_)
    intro y hy
    refine hfzero y ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    exact hy.le
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => hfzero y (by
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hy
    exact hy)),
    hint.integral_eq_integral_meas_lt (Filter.Eventually.of_forall fun y => le_max_right _ _)]
  have hlayer : ∀ t ∈ Set.Ioi (0 : ℝ),
      volume.real {a : EuclideanSpace ℝ (Fin d) | t < max (b - gauge K a) 0} =
        (max (b - t) 0) ^ d * normBallVolume (gauge K) := by
    intro t ht
    have ht0 : 0 < t := ht
    rcases lt_or_ge t b with htb | htb
    · have hset : {a : EuclideanSpace ℝ (Fin d) | t < max (b - gauge K a) 0} =
          {a | gauge K a < b - t} := by
        ext a
        simp only [Set.mem_setOf_eq, lt_max_iff]
        constructor
        · rintro (h | h)
          · linarith
          · linarith
        · intro h
          exact Or.inl (by linarith)
      rw [hset, real_volume_gauge_sublevel hΨ hd (by linarith),
        max_eq_left (by linarith : 0 ≤ b - t)]
    · have hset : {a : EuclideanSpace ℝ (Fin d) | t < max (b - gauge K a) 0} = ∅ := by
        ext a
        simp only [Set.mem_setOf_eq, lt_max_iff, Set.mem_empty_iff_false, iff_false, not_or,
          not_lt]
        exact ⟨by linarith [hnn a], ht0.le⟩
      rw [hset, max_eq_right (by linarith : b - t ≤ 0), zero_pow (by omega)]
      simp
  have hsd : ∫ t in Set.Ioi (0 : ℝ), (max (b - t) 0) ^ d * normBallVolume (gauge K) =
      ∫ t in Set.Ioc (0 : ℝ) b, (max (b - t) 0) ^ d * normBallVolume (gauge K) := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
      Set.Ioc_subset_Ioi_self (Filter.Eventually.of_forall fun t ht => ?_)
    have hbt : b < t := by
      by_contra h
      exact ht.2 ⟨ht.1, not_lt.mp h⟩
    rw [max_eq_right (by linarith : b - t ≤ 0), zero_pow (by omega), zero_mul]
  have hcongr : ∫ t in (0 : ℝ)..b, (max (b - t) 0) ^ d * normBallVolume (gauge K) =
      ∫ t in (0 : ℝ)..b, (b - t) ^ d * normBallVolume (gauge K) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hb] at ht
    rw [max_eq_left (by linarith [ht.2])]
  rw [setIntegral_congr_fun measurableSet_Ioi hlayer, hsd, ← intervalIntegral.integral_of_le hb,
    hcongr, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ d) b, sub_self, sub_zero,
    integral_pow, zero_pow (Nat.succ_ne_zero d), sub_zero]
  ring

/-- The mass of a sublevel set of the gauge: `∫_{ψ < b} ψ = d |B_ψ| b^{d+1}/(d+1)`, from the mass
identity with `ε = 1` and the explicit potential of the sublevel set. -/
theorem integral_gauge_sublevel_self (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) {b : ℝ}
    (hb : 0 < b) :
    ∫ v in {v : EuclideanSpace ℝ (Fin d) | gauge K v < b}, gauge K v =
      d * normBallVolume (gauge K) * b ^ (d + 1) / (d + 1) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hc, hle⟩ := hΨ.normMin_pos_mul_le hd1
  have hmeas : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | gauge K v < b} :=
    measurableSet_lt hΨ.continuous.measurable measurable_const
  have hsub : {v : EuclideanSpace ℝ (Fin d) | gauge K v < b} ⊆
      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (b / normMin (gauge K)) := by
    intro v hv
    rw [Metric.mem_ball, dist_zero_right]
    have h1 := hle v
    have h2 : normMin (gauge K) * ‖v‖ < normMin (gauge K) * (b / normMin (gauge K)) := by
      rw [mul_div_cancel₀ _ hc.ne']
      exact lt_of_le_of_lt h1 hv
    exact lt_of_mul_lt_mul_left h2 hc.le
  have hmass := GaugeContactShape.Rates.integral_ball_normPotential hd hΨ one_pos hmeas hsub
  have hcone := integral_cone_gauge hΨ hd1 hb.le (le_refl (b / normMin (gauge K)))
  have hpot : ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (b / normMin (gauge K)),
      normPotential d 1 (gauge K) {v | gauge K v < b} y =
      2 * d * ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (b / normMin (gauge K)),
        max (b - gauge K y) 0 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball fun y _ => ?_
    rw [gauge_ball_potential hd hΨ.compact hΨ.convex hΨ.zero_mem 1 hb y]
    ring
  rw [hpot, hcone] at hmass
  have hd0 : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp at hmass ⊢
  linarith

end ConeMass

/-! ## The integral of the gauge over the cell set -/

section CellIntegral

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- On the cell `C_y`, `ψ` exceeds `ψ(y)` by at most `Λ_ψ √d / 2`. -/
private theorem gauge_le_of_mem_cell (hΨ : GaugeContactShape.Adm K) {y : Site d}
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ∈ cell y) :
    gauge K v ≤ gauge K (toSpace y) + normMax (gauge K) * (Real.sqrt d / 2) := by
  have h1 := hΨ.add_le (toSpace y) (v - toSpace y)
  rw [add_sub_cancel] at h1
  have h2 := hΨ.le_normMax_mul (v - toSpace y)
  have h3 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hv
  have hΛ := hΨ.normMax_nonneg
  have h4 : normMax (gauge K) * ‖v - toSpace y‖ ≤ normMax (gauge K) * (Real.sqrt d / 2) :=
    mul_le_mul_of_nonneg_left h3 hΛ
  linarith

/-- The integral of `ψ` over the cell set is at most the sum of `ψ` over the departure range plus
`Λ_ψ (√d / 2)` times the number of cells: on each cell of volume one, `ψ ≤ ψ(y) + Λ_ψ √d/2`. -/
theorem integral_cellSet_gauge_le (hΨ : GaugeContactShape.Adm K) (x : ℕ → Site d) (n : ℕ) :
    ∫ v in cellSet x n, gauge K v ≤
      ∑ y ∈ departureRange x n, gauge K (toSpace y) +
        normMax (gauge K) * (Real.sqrt d / 2) * (departureRange x n).card := by
  have hint : ∀ y ∈ departureRange x n, IntegrableOn (gauge K) (cell y) := by
    intro y _
    refine Measure.integrableOn_of_bounded (M := gauge K (toSpace y) +
        normMax (gauge K) * (Real.sqrt d / 2)) (by rw [CERW.Support.Occupation.volume_cell]; simp)
      hΨ.continuous.aestronglyMeasurable ?_
    refine (ae_restrict_iff' (CERW.Support.Occupation.measurableSet_cell y)).mpr
      (Filter.Eventually.of_forall fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hΨ.nonneg v)]
    exact gauge_le_of_mem_cell hΨ hv
  rw [cellSet, integral_biUnion_finset (departureRange x n)
    (fun y _ => CERW.Support.Occupation.measurableSet_cell y)
    (fun y _ z _ hyz => cell_disjoint hyz) hint]
  calc ∑ y ∈ departureRange x n, ∫ v in cell y, gauge K v
      ≤ ∑ y ∈ departureRange x n,
          (gauge K (toSpace y) + normMax (gauge K) * (Real.sqrt d / 2)) := by
        refine Finset.sum_le_sum fun y hy => ?_
        calc ∫ v in cell y, gauge K v
            ≤ ∫ v in cell y, (gauge K (toSpace y) + normMax (gauge K) * (Real.sqrt d / 2)) :=
              setIntegral_mono_on (hint y hy)
                (integrableOn_const (by rw [CERW.Support.Occupation.volume_cell]; simp))
                (CERW.Support.Occupation.measurableSet_cell y)
                fun v hv => gauge_le_of_mem_cell hΨ hv
          _ = gauge K (toSpace y) + normMax (gauge K) * (Real.sqrt d / 2) := by
              rw [setIntegral_const]
              simp [measureReal_def, CERW.Support.Occupation.volume_cell]
    _ = ∑ y ∈ departureRange x n, gauge K (toSpace y) +
        normMax (gauge K) * (Real.sqrt d / 2) * (departureRange x n).card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        ring

end CellIntegral

/-! ## The arithmetic of the one-sided inner radius bound -/

section InnerArith

/-- The real arithmetic of the one-sided bound on the inner radius. If
`a b^{d+1} ≤ a r^{d+1} + Q + ε Λ √d A` for `n = a r^{d+1}` with `a = 2 ε d V/(d+1)`, the coarse
bounds `A ≤ C_A r^d`, `R ≤ C_R r`, the martingale bound `Q ≤ C_Q (2R + 5)(√(L n) + L)` and
`L ≤ r`, then `b - r ≤ C (r^{(3-d)/2} L^{1/2} + 1)`. -/
private theorem inner_upper_arith {d : ℕ} (hd : 2 ≤ d) {ε V Λ CA CR CQ : ℝ} (hε : 0 < ε)
    (hV : 0 < V)
    (hΛ : 0 ≤ Λ) (hCA : 0 ≤ CA) (hCR : 0 ≤ CR) (hCQ : 0 ≤ CQ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r b A L n Q R : ℝ}, 1 ≤ r → 0 ≤ b → 1 ≤ L → L ≤ r → 0 ≤ A → 0 ≤ Q →
      0 ≤ R → n = 2 * ε * d * V * r ^ (d + 1) / (d + 1) → A ≤ CA * r ^ d → R ≤ CR * r →
      Q ≤ CQ * (2 * R + 5) * (Real.sqrt (L * n) + L) →
      2 * ε * (d * V * b ^ (d + 1) / (d + 1)) ≤ n + Q + ε * Λ * Real.sqrt d * A →
      b - r ≤ C * (r ^ (((3 : ℝ) - d) / 2) * L ^ ((1 : ℝ) / 2) + 1) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  set a : ℝ := 2 * ε * d * V / (d + 1) with ha
  have ha0 : 0 < a := by positivity
  set C₀ : ℝ := (CQ * (2 * CR + 5) * (Real.sqrt a + 1) + ε * Λ * Real.sqrt d * CA) /
    ((d + 1) * a) with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  refine ⟨C₀ + 1, by linarith, ?_⟩
  intro r b A L n Q R hr hb hL1 hLr hA0 hQ0 hR0 hn hA hR hQ hmass
  have hr0 : 0 < r := by linarith
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < r ^ (((3 : ℝ) - d) / 2) := Real.rpow_pos_of_pos hr0 _
  have hs0 : 0 ≤ L ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hL0.le _
  have hrhs0 : 0 ≤ (C₀ + 1) * (r ^ (((3 : ℝ) - d) / 2) * L ^ ((1 : ℝ) / 2) + 1) := by positivity
  rcases le_or_gt b r with hbr | hbr
  · linarith
  -- the case `b > r`
  have hn' : n = a * r ^ (d + 1) := by rw [hn, ha]; ring
  have hmass' : a * b ^ (d + 1) ≤ a * r ^ (d + 1) + Q + ε * Λ * Real.sqrt d * A := by
    have h : 2 * ε * (d * V * b ^ (d + 1) / (d + 1)) = a * b ^ (d + 1) := by rw [ha]; ring
    rw [h, hn'] at hmass
    exact hmass
  -- Bernoulli
  have hbern : (d + 1 : ℝ) * r ^ d * (b - r) ≤ b ^ (d + 1) - r ^ (d + 1) := by
    set t : ℝ := b / r with ht
    have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hr0]; linarith
    have hb' : b = t * r := by rw [ht]; field_simp
    have h1 := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ t - 1) (d + 1)
    have h2 : (1 + (t - 1)) ^ (d + 1) = t ^ (d + 1) := by ring
    rw [h2] at h1
    have h3 : r ^ (d + 1) * (1 + ((d + 1 : ℕ) : ℝ) * (t - 1)) ≤ r ^ (d + 1) * t ^ (d + 1) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e1 : ((d : ℝ) + 1) * r ^ d * (b - r) = r ^ (d + 1) * (((d : ℝ) + 1) * (t - 1)) := by
      rw [hb', pow_succ]
      ring
    have e2 : b ^ (d + 1) = r ^ (d + 1) * t ^ (d + 1) := by
      rw [hb', mul_pow]
      ring
    rw [e1, e2]
    push_cast at h3
    linarith [h3]
  have hkey : a * ((d + 1 : ℝ) * r ^ d * (b - r)) ≤ Q + ε * Λ * Real.sqrt d * A := by
    have h := mul_le_mul_of_nonneg_left hbern ha0.le
    linarith [h, hmass']
  -- the bound on `Q`
  set t : ℝ := r ^ (((d : ℝ) + 1) / 2) with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos hr0 _
  have ht2 : t ^ 2 = r ^ (d + 1) := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    norm_num
    rw [← Real.rpow_natCast]
    norm_num
  have hsq : Real.sqrt (L * n) = Real.sqrt (a * L) * t := by
    rw [hn', show L * (a * r ^ (d + 1)) = (a * L) * t ^ 2 by rw [ht2]; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq ht0.le]
  have hrt : r ^ d * r ^ (((3 : ℝ) - d) / 2) = r * t := by
    calc r ^ d * r ^ (((3 : ℝ) - d) / 2) = r ^ ((d : ℝ) + ((3 : ℝ) - d) / 2) := by
          rw [← Real.rpow_natCast, Real.rpow_add hr0]
      _ = r ^ (1 + ((d : ℝ) + 1) / 2) := by congr 1; ring
      _ = r * t := by rw [Real.rpow_add hr0, Real.rpow_one]
  have hsqrtL : L ^ ((1 : ℝ) / 2) = Real.sqrt L := (Real.sqrt_eq_rpow L).symm
  have hsqrt_aL : Real.sqrt (a * L) = Real.sqrt a * Real.sqrt L := Real.sqrt_mul ha0.le L
  have hrL : r * L ≤ r ^ d := by
    calc r * L ≤ r * r := mul_le_mul_of_nonneg_left hLr hr0.le
      _ = r ^ 2 := (sq r).symm
      _ ≤ r ^ d := pow_le_pow_right₀ hr hd
  set u : ℝ := r ^ (((3 : ℝ) - d) / 2) with hudef
  have hsa0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hsL0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hQ' : Q ≤ CQ * (2 * CR + 5) * r ^ d * (Real.sqrt a * (u * Real.sqrt L) + 1) := by
    have hR5 : 2 * R + 5 ≤ (2 * CR + 5) * r := by
      have h1 : 2 * R + 5 ≤ 2 * (CR * r) + 5 := by linarith
      have h2 : (2 * CR + 5) * r = 2 * (CR * r) + 5 * r := by ring
      linarith
    calc Q ≤ CQ * (2 * R + 5) * (Real.sqrt (L * n) + L) := hQ
      _ ≤ CQ * ((2 * CR + 5) * r) * (Real.sqrt (L * n) + L) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR5 hCQ) ?_
          positivity
      _ = CQ * (2 * CR + 5) * (Real.sqrt a * Real.sqrt L * (r * t) + r * L) := by
          rw [hsq, hsqrt_aL]
          ring
      _ = CQ * (2 * CR + 5) * (Real.sqrt a * Real.sqrt L * (r ^ d * u) + r * L) := by
          rw [hrt]
      _ ≤ CQ * (2 * CR + 5) * (Real.sqrt a * Real.sqrt L * (r ^ d * u) + r ^ d) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = CQ * (2 * CR + 5) * r ^ d * (Real.sqrt a * (u * Real.sqrt L) + 1) := by ring
  have hA' : ε * Λ * Real.sqrt d * A ≤ ε * Λ * Real.sqrt d * CA * r ^ d := by
    calc ε * Λ * Real.sqrt d * A ≤ ε * Λ * Real.sqrt d * (CA * r ^ d) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = ε * Λ * Real.sqrt d * CA * r ^ d := by ring
  have hrd : 0 < r ^ d := pow_pos hr0 d
  have huL : 0 ≤ u * Real.sqrt L := mul_nonneg hu0.le hsL0
  have hfinal : a * (d + 1) * (b - r) ≤
      (CQ * (2 * CR + 5) * (Real.sqrt a * (u * Real.sqrt L) + 1) +
        ε * Λ * Real.sqrt d * CA) := by
    have h1 : a * ((d + 1 : ℝ) * r ^ d * (b - r)) ≤
        r ^ d * (CQ * (2 * CR + 5) * (Real.sqrt a * (u * Real.sqrt L) + 1) +
          ε * Λ * Real.sqrt d * CA) := by
      calc a * ((d + 1 : ℝ) * r ^ d * (b - r)) ≤ Q + ε * Λ * Real.sqrt d * A := hkey
        _ ≤ CQ * (2 * CR + 5) * r ^ d * (Real.sqrt a * (u * Real.sqrt L) + 1) +
            ε * Λ * Real.sqrt d * CA * r ^ d := add_le_add hQ' hA'
        _ = r ^ d * (CQ * (2 * CR + 5) * (Real.sqrt a * (u * Real.sqrt L) + 1) +
            ε * Λ * Real.sqrt d * CA) := by ring
    have h2 : r ^ d * (a * (d + 1) * (b - r)) ≤ r ^ d * (CQ * (2 * CR + 5) *
        (Real.sqrt a * (u * Real.sqrt L) + 1) + ε * Λ * Real.sqrt d * CA) := by
      calc r ^ d * (a * (d + 1) * (b - r)) = a * ((d + 1 : ℝ) * r ^ d * (b - r)) := by ring
        _ ≤ _ := h1
    exact le_of_mul_le_mul_left h2 hrd
  have hden : 0 < a * (d + 1) := mul_pos ha0 hd1
  have hb1 : b - r ≤ (CQ * (2 * CR + 5) * (Real.sqrt a * (u * Real.sqrt L) + 1) +
      ε * Λ * Real.sqrt d * CA) / (a * (d + 1)) := by
    rw [le_div_iff₀ hden]
    linarith
  have hb2 : (CQ * (2 * CR + 5) * (Real.sqrt a * (u * Real.sqrt L) + 1) +
      ε * Λ * Real.sqrt d * CA) / (a * (d + 1)) ≤ C₀ * (u * Real.sqrt L + 1) := by
    have hq0 : 0 ≤ CQ * (2 * CR + 5) := by positivity
    have hε0 : 0 ≤ ε * Λ * Real.sqrt d * CA := by positivity
    have hnum : CQ * (2 * CR + 5) * (Real.sqrt a * (u * Real.sqrt L) + 1) +
        ε * Λ * Real.sqrt d * CA ≤
        (CQ * (2 * CR + 5) * (Real.sqrt a + 1) + ε * Λ * Real.sqrt d * CA) *
          (u * Real.sqrt L + 1) := by
      have h := add_nonneg (mul_nonneg hq0 (add_nonneg hsa0 huL)) (mul_nonneg hε0 huL)
      linarith [h]
    calc (CQ * (2 * CR + 5) * (Real.sqrt a * (u * Real.sqrt L) + 1) +
        ε * Λ * Real.sqrt d * CA) / (a * (d + 1))
        ≤ ((CQ * (2 * CR + 5) * (Real.sqrt a + 1) + ε * Λ * Real.sqrt d * CA) *
          (u * Real.sqrt L + 1)) / (a * (d + 1)) := div_le_div_of_nonneg_right hnum hden.le
      _ = C₀ * (u * Real.sqrt L + 1) := by
          rw [hC₀]
          ring
  rw [hsqrtL]
  calc b - r ≤ C₀ * (u * Real.sqrt L + 1) := hb1.trans hb2
    _ ≤ (C₀ + 1) * (u * Real.sqrt L + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end InnerArith

/-! ## The one-sided bound on the inner radius from the quadratic martingale -/

section KeyInequality

open CERW.Support.Drift CERW.Support.Law CERW.Support.Occupation

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- A unit step changes the Euclidean norm by at most one. -/
private theorem euclidNorm_add_le (z : Site d) {e : Site d} (he : e ∈ unitSteps d) :
    euclidNorm (z + e) ≤ euclidNorm z + 1 := by
  have h1 : euclidNorm (z + e) = ‖toSpace (z + e)‖ := (norm_toSpace _).symm
  have h2 : euclidNorm z = ‖toSpace z‖ := (norm_toSpace _).symm
  have h3 : toSpace (z + e) = toSpace z + toSpace e := by
    ext i
    simp [toSpace]
  rw [h1, h2, h3]
  refine (norm_add_le _ _).trans ?_
  rw [norm_toSpace e, euclidNorm_of_mem_unitSteps he]

/-- Above the radius of the path, the truncated squared norm has the same Dynkin martingale as the
squared norm. -/
private theorem dynkinMart_truncSq_eq (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (x : ℕ → Site d)
    (n k : ℕ) (hk : maxRadius x n + 1 ≤ k) :
    dynkinMart (driftStepProb d ε ξ) (truncSq k) x n =
      dynkinMart (driftStepProb d ε ξ) (fun z : Site d => euclidNorm z ^ 2) x n := by
  have hx : ∀ j, j ≤ n → euclidNorm (x j) ≤ k := fun j hj =>
    ((euclidNorm_le_maxRadius x hj).trans (by linarith))
  have hxe : ∀ j, j ≤ n → ∀ e ∈ unitSteps d, euclidNorm (x j + e) ≤ k := fun j hj e he =>
    (euclidNorm_add_le (x j) he).trans (by linarith [euclidNorm_le_maxRadius x hj])
  unfold dynkinMart
  rw [truncSq_eq k (hx n le_rfl), truncSq_eq k (hx 0 (Nat.zero_le n))]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := (Finset.mem_range.mp hj).le
  unfold stepMean
  refine Finset.sum_congr rfl fun e he => ?_
  rw [truncSq_eq k (hxe j hjn e he), truncSq_eq k (hx j hjn)]

/-- The gauge is integrable on the cell set. -/
private theorem integrableOn_cellSet_gauge (hΨ : GaugeContactShape.Adm K) (x : ℕ → Site d) (n : ℕ) :
    IntegrableOn (gauge K) (cellSet x n) := by
  have hint : ∀ y ∈ departureRange x n, IntegrableOn (gauge K) (cell y) := by
    intro y _
    refine Measure.integrableOn_of_bounded (M := gauge K (toSpace y) +
        normMax (gauge K) * (Real.sqrt d / 2)) (by rw [CERW.Support.Occupation.volume_cell]; simp)
      hΨ.continuous.aestronglyMeasurable ?_
    refine (ae_restrict_iff' (CERW.Support.Occupation.measurableSet_cell y)).mpr
      (Filter.Eventually.of_forall fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hΨ.nonneg v)]
    exact gauge_le_of_mem_cell hΨ hv
  rw [cellSet]
  exact (integrableOn_finset_iUnion (μ := volume)).mpr hint

/-- **The inequality behind the one-sided inner bound.** For a path from the origin and a level
`k ≥ H_n + 1`, the inner radius `b` of the cell set satisfies
`2 ε d |B_ψ| b^{d+1}/(d+1) ≤ n + |𝒬^{(k)}_n| + ε Λ_ψ √d |A_n|`: the sublevel set `{ψ < b}` lies in
the cell set, `∫_{ψ<b} ψ = d |B_ψ| b^{d+1}/(d+1)`, the integral of `ψ` over the cell set is at most
`Σ_{A_n} ψ + Λ_ψ (√d/2) |A_n|`, and `|x_n|² ≥ 0` in `eq:quadratic`. -/
theorem key_inequality (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) {ε : ℝ} (hε : 0 < ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) (x : ℕ → Site d)
    (h0 : x 0 = 0) (n k : ℕ) (hk : maxRadius x n + 1 ≤ k)
    (hb : 0 < normInnerRadius (gauge K) x n) :
    2 * ε * (d * normBallVolume (gauge K) * normInnerRadius (gauge K) x n ^ (d + 1) / (d + 1)) ≤
      n + |dynkinMart (driftStepProb d ε ξ) (truncSq k) x n| +
        ε * normMax (gauge K) * Real.sqrt d * (departureRange x n).card := by
  have hd1 : 1 ≤ d := by omega
  set b := normInnerRadius (gauge K) x n with hbdef
  have hid := sq_euclidNorm_eq_gauge hd1 ε hξ x h0 n
  rw [← dynkinMart_truncSq_eq ε ξ x n k hk] at hid
  have hQ : dynkinMart (driftStepProb d ε ξ) (truncSq k) x n ≤
      |dynkinMart (driftStepProb d ε ξ) (truncSq k) x n| := le_abs_self _
  have hsq0 : 0 ≤ euclidNorm (x n) ^ 2 := sq_nonneg _
  have hSum : 2 * ε * ∑ y ∈ departureRange x n, gauge K (toSpace y) ≤
      n + |dynkinMart (driftStepProb d ε ξ) (truncSq k) x n| := by linarith
  have hsub := sublevel_subset_cellSet_gauge K x n
  have hmono : ∫ v in {v : EuclideanSpace ℝ (Fin d) | gauge K v < b}, gauge K v ≤
      ∫ v in cellSet x n, gauge K v :=
    setIntegral_mono_set (integrableOn_cellSet_gauge hΨ x n)
      (Filter.Eventually.of_forall fun v => hΨ.nonneg v) (Filter.Eventually.of_forall hsub)
  have hcell := integral_cellSet_gauge_le hΨ x n
  rw [integral_gauge_sublevel_self hd hΨ hb] at hmono
  have hΛ := hΨ.normMax_nonneg
  have hmul : 2 * ε * (d * normBallVolume (gauge K) * b ^ (d + 1) / (d + 1)) ≤
      2 * ε * (∑ y ∈ departureRange x n, gauge K (toSpace y) +
        normMax (gauge K) * (Real.sqrt d / 2) * (departureRange x n).card) :=
    mul_le_mul_of_nonneg_left (hmono.trans hcell) (by positivity)
  nlinarith [hmul, hSum]

end KeyInequality

/-! ## The one-sided bound on the inner radius with high probability -/

section InnerUpper

/-- A set outside two events of small probability and a null event has small probability. -/
private theorem measure_le_of_subset_union_two_null {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S E₁ E₂ N : Set Ω} {a₁ a₂ C : ℝ}
    (hS : ∀ ω, ω ∉ E₁ → ω ∉ E₂ → ω ∉ N → ω ∉ S)
    (h₁ : μ E₁ ≤ ENNReal.ofReal a₁) (h₂ : μ E₂ ≤ ENNReal.ofReal a₂) (hN : μ N = 0)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hC : a₁ + a₂ ≤ C) : μ S ≤ ENNReal.ofReal C := by
  have hsub : S ⊆ E₁ ∪ E₂ ∪ N := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    exact hS ω hnot.1.1 hnot.1.2 hnot.2 hω
  calc μ S ≤ μ (E₁ ∪ E₂ ∪ N) := measure_mono hsub
    _ ≤ μ (E₁ ∪ E₂) + μ N := measure_union_le _ _
    _ = μ (E₁ ∪ E₂) := by rw [hN, add_zero]
    _ ≤ μ E₁ + μ E₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal a₁ + ENNReal.ofReal a₂ := add_le_add h₁ h₂
    _ = ENNReal.ofReal (a₁ + a₂) := (ENNReal.ofReal_add ha₁ ha₂).symm
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC

/-- **The one-sided bound on the inner radius (the stronger inner rate of the source).** With the
scale `r_n`, for every `p > 0` there is `C`, chosen before the subgradient selection, the
probability space, the walk and `n`, such that for every `n ≥ 2`, with probability at least
`1 - C n^{-p}`, `inf_{y ∉ D_n} ψ(y) - r_n ≤ C (r_n^{(3-d)/2} (log n)^{1/2} + 1)`. It uses the
coarse bounds and the quadratic martingale, but neither the contact bound nor the local time
estimates. -/
def GaugeInnerUpper : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}, IsCompact K → Convex ℝ K →
    (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K →
    ∀ ε : ℝ, 0 < ε →
    (∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ)) →
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * normBallVolume (gauge K))) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (normInnerRadius (gauge K) (X · ω) n - r n ≤
            C * (r n ^ (((3 : ℝ) - d) / 2) * Real.log n ^ ((1 : ℝ) / 2) + 1))} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p))

/-- **The one-sided bound on the inner radius**, from the coarse bounds and the quadratic
martingale event, by the key inequality and the arithmetic of the scale. -/
theorem gauge_inner_upper : GaugeInnerUpper.{u} := by
  intro d hd K hK hc h0 ε hε hell r p hp
  have hd1 : 1 ≤ d := by omega
  have hΨ : GaugeContactShape.Adm K := ⟨hK, hc, h0⟩
  have hV : 0 < normBallVolume (gauge K) := normBallVolume_gauge_pos hK hc h0
  obtain ⟨c_co, C_co, hc_co, hC_co, hco⟩ :=
    GaugeCoarseClosed.gauge_coarse_bounds hd hK hc h0 ε hε hell p hp
  obtain ⟨C_Q, C_P, hC_Q, hC_P, hquad⟩ := exists_quadratic_failure_bound (K := K) hd hε hell hp
  obtain ⟨C₀, hC₀, harith⟩ := inner_upper_arith hd (V := normBallVolume (gauge K))
    (Λ := normMax (gauge K)) (CA := C_co) (CR := C_co) (CQ := C_Q) hε hV hΨ.normMax_nonneg
    hC_co.le hC_co.le hC_Q.le
  have hreg : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ coarseScale (gauge K) ε n ∧ 1 ≤ Real.log n ∧
      Real.log n ≤ coarseScale (gauge K) ε n := by
    filter_upwards [eventually_ge_atTop 2, eventually_le_coarseScale hd1 hε hV 1,
      eventually_one_le_log, eventually_mul_log_pow_le_coarseScale hd1 hε hV one_pos 1]
      with n a b c e
    exact ⟨a, b, c, by simpa using e⟩
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hreg
  set Cp : ℝ := C_co + C_P with hCp
  have hCp0 : 0 < Cp := by positivity
  have hNp : 0 ≤ (N₁ : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg N₁) _
  refine ⟨max (max C₀ Cp) ((N₁ : ℝ) ^ p), lt_max_of_lt_left (lt_max_of_lt_left hC₀), ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg hnpos.le _
  have hCC₀ : C₀ ≤ max (max C₀ Cp) ((N₁ : ℝ) ^ p) := (le_max_left _ _).trans (le_max_left _ _)
  have hCCp : Cp ≤ max (max C₀ Cp) ((N₁ : ℝ) ^ p) := (le_max_right _ _).trans (le_max_left _ _)
  by_cases hnN : N₁ ≤ n
  · obtain ⟨hn2, hr1, hℓ1, hℓr⟩ := hN₁ n hnN
    have hξ' := drift_coord_bound_gauge hε.le hell hξ hξ0
    have hnull : μ {ω | ¬ (X 0 ω = 0 ∧ ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d)} = 0 := by
      have hpath : ∀ᵐ ω ∂μ, X 0 ω = 0 ∧ ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d := by
        have h0' : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
          rw [ae_iff]
          exact hX.start
        filter_upwards [h0', ae_all_iff.mpr
          (CERW.Support.Drift.ae_sub_mem_unitSteps_drift hd1 hε.le hξ' hX)] with ω h0 hs
        exact ⟨h0, hs⟩
      exact ae_iff.mp hpath
    refine le_trans (measure_le_of_subset_union_two_null (a₁ := C_co * (n : ℝ) ^ (-p))
      (a₂ := C_P * (n : ℝ) ^ (-p)) (C := Cp * (n : ℝ) ^ (-p)) ?_ (hco ξ hξ hξ0 μ X hX n hn)
      (hquad ξ hξ hξ0 μ X hX n hn) hnull (mul_nonneg hC_co.le hnp) (mul_nonneg hC_P.le hnp)
      (le_of_eq (by rw [hCp]; ring)))
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCCp hnp))
    · intro ω h1 h2 h3
      have hco' := not_not.mp h1
      have hq' := not_not.mp h2
      have hpath : X 0 ω = 0 ∧ ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d := by
        by_contra hc'
        exact h3 hc'
      obtain ⟨-, hcard, -, -, -, hRad⟩ := hco'
      set x : ℕ → Site d := fun j => X j ω with hxdef
      have hXn : ∀ j, euclidNorm (x j) ≤ j :=
        CERW.Support.Occupation.euclidNorm_le_of_steps x hpath.1 hpath.2
      set R : ℝ := maxRadius x n with hRdef
      have hR0 : 0 ≤ R := (LatticeProb.euclidNorm_nonneg (x 0)).trans
        (euclidNorm_le_maxRadius x (Nat.zero_le n))
      have hRn : R ≤ n := GaugeContactShape.maxRadius_le_nat x n hXn
      set k : ℕ := ⌈R⌉₊ + 1 with hkdef
      have hkR : R + 1 ≤ k := by
        rw [hkdef]
        push_cast
        linarith [Nat.le_ceil R]
      have hkn : k ≤ n + 2 := by
        have : ⌈R⌉₊ ≤ n := Nat.ceil_le.mpr hRn
        omega
      have hk2 : (2 * (k : ℝ) + 1) ≤ 2 * R + 5 := by
        have := Nat.ceil_lt_add_one hR0
        rw [hkdef]
        push_cast
        linarith
      have hQ := hq' k hkn
      have hQ' : |dynkinMart (driftStepProb d ε ξ) (truncSq k) x n| ≤
          C_Q * (2 * R + 5) * (Real.sqrt (Real.log n * n) + Real.log n) :=
        hQ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk2 hC_Q.le)
          (add_nonneg (Real.sqrt_nonneg _) (Real.log_natCast_nonneg n)))
      have hb0 := normInnerRadius_gauge_nonneg K x n
      have hℓ0 : 0 < Real.log n := by linarith
      have hr0 : 0 < coarseScale (gauge K) ε n := by linarith
      intro hbad
      refine hbad ?_
      have hrhs0 : 0 ≤ (coarseScale (gauge K) ε n) ^ (((3 : ℝ) - d) / 2) *
          Real.log n ^ ((1 : ℝ) / 2) + 1 := by positivity
      rcases hb0.eq_or_lt with hz | hb
      · rw [← hz]
        have hr0' : 0 < r n := hr0
        have hrhs0' : 0 ≤ r n ^ (((3 : ℝ) - d) / 2) * Real.log n ^ ((1 : ℝ) / 2) + 1 := hrhs0
        have : 0 ≤ max (max C₀ Cp) ((N₁ : ℝ) ^ p) *
            (r n ^ (((3 : ℝ) - d) / 2) * Real.log n ^ ((1 : ℝ) / 2) + 1) :=
          mul_nonneg (le_trans hCp0.le hCCp) hrhs0'
        linarith
      · have hmass := key_inequality hd hΨ hε hξ x hpath.1 n k (by linarith) hb
        have hnr : (n : ℝ) = 2 * ε * d * normBallVolume (gauge K) *
            coarseScale (gauge K) ε n ^ (d + 1) / (d + 1) := by
          rw [nat_eq_coarseScale_pow hd1 hε hV n]
          ring
        have hmain := harith (r := coarseScale (gauge K) ε n) (b := normInnerRadius (gauge K) x n)
          (A := ((departureRange x n).card : ℝ)) (L := Real.log n) (n := (n : ℝ))
          (Q := |dynkinMart (driftStepProb d ε ξ) (truncSq k) x n|) (R := R) hr1 hb0 hℓ1 hℓr
          (Nat.cast_nonneg _) (abs_nonneg _) hR0 hnr hcard hRad hQ' hmass
        exact hmain.trans (mul_le_mul_of_nonneg_right hCC₀ hrhs0)
  · rw [not_le] at hnN
    refine le_trans prob_le_one ?_
    rw [ENNReal.one_le_ofReal]
    have h1 : (n : ℝ) ^ p ≤ (N₁ : ℝ) ^ p :=
      Real.rpow_le_rpow hnpos.le (by exact_mod_cast hnN.le) hp.le
    have h2 : (1 : ℝ) ≤ (N₁ : ℝ) ^ p * (n : ℝ) ^ (-p) := by
      rw [Real.rpow_neg hnpos.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hnpos p)]
      exact h1
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hnp)

end InnerUpper

section Assembly

/-- A set whose complement meets four events of small probability only outside it has small
probability. -/
private theorem measure_le_of_subset_union_four {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S E₁ E₂ E₃ E₄ : Set Ω} {a₁ a₂ a₃ a₄ C : ℝ}
    (hS : ∀ ω, ω ∉ E₁ → ω ∉ E₂ → ω ∉ E₃ → ω ∉ E₄ → ω ∉ S)
    (h₁ : μ E₁ ≤ ENNReal.ofReal a₁) (h₂ : μ E₂ ≤ ENNReal.ofReal a₂)
    (h₃ : μ E₃ ≤ ENNReal.ofReal a₃) (h₄ : μ E₄ ≤ ENNReal.ofReal a₄) (ha₁ : 0 ≤ a₁)
    (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha₄ : 0 ≤ a₄) (hC : a₁ + a₂ + a₃ + a₄ ≤ C) :
    μ S ≤ ENNReal.ofReal C := by
  have hsub : S ⊆ E₁ ∪ E₂ ∪ E₃ ∪ E₄ := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    exact hS ω hnot.1.1.1 hnot.1.1.2 hnot.1.2 hnot.2 hω
  calc μ S ≤ μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄) := measure_mono hsub
    _ ≤ μ (E₁ ∪ E₂ ∪ E₃) + μ E₄ := measure_union_le _ _
    _ ≤ (μ (E₁ ∪ E₂) + μ E₃) + μ E₄ := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ((μ E₁ + μ E₂) + μ E₃) + μ E₄ :=
        add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
    _ ≤ ((ENNReal.ofReal a₁ + ENNReal.ofReal a₂) + ENNReal.ofReal a₃) + ENNReal.ofReal a₄ := by
        gcongr
    _ = ENNReal.ofReal (a₁ + a₂ + a₃ + a₄) := by
        rw [ENNReal.ofReal_add (by positivity) ha₄, ENNReal.ofReal_add (add_nonneg ha₁ ha₂) ha₃,
          ENNReal.ofReal_add ha₁ ha₂]
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC

/-- **Proposition `prop:norm-shape` for the Minkowski functional of a convex body, from the
producers.** The coarse bounds, the local time potential lemma, the fine pointwise bound, and the
compensated-path and projection-direction events of the walk hold simultaneously with probability
at least `1 - C n^{-p}`; on their intersection, for large `n`, the deterministic rates theorem
`ShapeRatesOfEvents` applies at the deterministic scale `r_n` with a nearest-point map onto
`{ψ ≤ r_n}`, and gives the radii and the profile; for small `n` the bound is absorbed into the
constant. No hypothesis on the walk beyond `IsDriftCERW` is used. -/
theorem gauge_shape_rates : GaugeShapeRates.{u} := by
  intro d hd K hK hc h0 ε hε hell r p hp
  have hd1 : 1 ≤ d := by omega
  have hΨ : GaugeContactShape.Adm K := ⟨hK, hc, h0⟩
  have hV : 0 < normBallVolume (gauge K) := normBallVolume_gauge_pos hK hc h0
  obtain ⟨c_co, C_co, hc_co, hC_co, hco⟩ :=
    GaugeCoarseClosed.gauge_coarse_bounds hd hK hc h0 ε hε hell p hp
  obtain ⟨C_loc, hC_loc, hloc⟩ :=
    GaugeLocalTime.gauge_local_time_potential hd hK hc h0 ε hε hell p hp
  obtain ⟨C_F, hC_F, hfine⟩ :=
    GaugePointwise.gauge_pointwise_local_time hd hK hc h0 ε hε hell p hp
  obtain ⟨C₁, C_P, hC₁, hC_P, hproj⟩ :=
    GaugeProjectionEvents.exists_projectionEvent_failure_bound (K := K) hd hε hell hp
  obtain ⟨C₀, r₀, M, hC₀, hM, hdet⟩ :=
    GaugeContactShape.Rates.gauge_shape_rates_of_events hd hΨ hε hell hC_co hC_F.le hC_loc hC₁
  have hreg : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ r₀ ≤ coarseScale (gauge K) ε n ∧
      M * Real.log n ^ (d + 5) ≤ coarseScale (gauge K) ε n ∧ 1 ≤ Real.log n := by
    filter_upwards [eventually_ge_atTop 2, eventually_le_coarseScale hd1 hε hV r₀,
      eventually_mul_log_pow_le_coarseScale hd1 hε hV hM (d + 5), eventually_one_le_log]
      with n a b c e
    exact ⟨a, b, c, e⟩
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hreg
  set Cp : ℝ := C_co + C_loc + C_F + C_P with hCp
  have hCp0 : 0 < Cp := by positivity
  have hNp : 0 ≤ (N₁ : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg N₁) _
  refine ⟨max (max C₀ Cp) ((N₁ : ℝ) ^ p), lt_max_of_lt_left (lt_max_of_lt_left hC₀), ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg hnpos.le _
  have hCC₀ : C₀ ≤ max (max C₀ Cp) ((N₁ : ℝ) ^ p) := (le_max_left _ _).trans (le_max_left _ _)
  have hCCp : Cp ≤ max (max C₀ Cp) ((N₁ : ℝ) ^ p) := (le_max_right _ _).trans (le_max_left _ _)
  by_cases hnN : N₁ ≤ n
  · obtain ⟨hn2, hr₀, hMlog, hℓ⟩ := hN₁ n hnN
    obtain ⟨hr0, hnr, P, ⟨hP1, hP2⟩, -⟩ :=
      GaugeProjectionEvents.existsUnique_nearestPoint_at_scale hd hΨ hε (by omega : 1 ≤ n)
    have hℓ0 : 0 < Real.log n := by linarith
    refine le_trans (measure_le_of_subset_union_four (a₁ := C_co * (n : ℝ) ^ (-p))
      (a₂ := C_loc * (n : ℝ) ^ (-p)) (a₃ := C_F * (n : ℝ) ^ (-p))
      (a₄ := C_P * (n : ℝ) ^ (-p)) (C := Cp * (n : ℝ) ^ (-p)) ?_ (hco ξ hξ hξ0 μ X hX n hn)
      (hloc ξ hξ hξ0 μ X hX n hn) (hfine ξ hξ hξ0 μ X hX n hn)
      (hproj ξ hξ hξ0 μ X hX n hn P) (mul_nonneg hC_co.le hnp) (mul_nonneg hC_loc.le hnp)
      (mul_nonneg hC_F.le hnp) (mul_nonneg hC_P.le hnp) (le_of_eq ?_))
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCCp hnp))
    · intro ω h1 h2 h3 h4
      have hco' := not_not.mp h1
      have hlo' := not_not.mp h2
      have hfi' := not_not.mp h3
      have hpr' := not_not.mp h4
      obtain ⟨-, -, -, hLT, -, hRad⟩ := hco'
      obtain ⟨hx0, hstep, -, -⟩ := id hpr'
      have hdetω := hdet ξ hξ hξ0 (fun j => X j ω) n (coarseScale (gauge K) ε n) hx0 hstep hr₀
        hℓ hMlog hnr hRad hLT hfi' hlo'.2.2 P hP1 hP2
        (GaugeProjectionEvents.ProjectionEvent.compensated hpr')
        (fun j hj hrj k hk => GaugeProjectionEvents.ProjectionEvent.martingale hpr' hj hk)
      obtain ⟨e1, e2, e3⟩ := explicit_rates_of_rateQ (ε := ε) hr0 hℓ0 hdetω
      have hA1 : 0 ≤ (if d = 2 then coarseScale (gauge K) ε n ^ ((3 : ℝ) / 4) *
            Real.log n ^ ((1 : ℝ) / 4) else (coarseScale (gauge K) ε n * Real.log n) ^
              ((1 : ℝ) / 2)) := by
        split_ifs <;> positivity
      have hA2 : 0 ≤ (if d = 2 then coarseScale (gauge K) ε n ^ ((5 : ℝ) / 6) *
            Real.log n ^ ((7 : ℝ) / 6) else coarseScale (gauge K) ε n ^ ((d : ℝ) / (d + 1)) *
              Real.log n ^ (((d : ℝ) + 2) / (d + 1))) := by
        split_ifs <;> positivity
      have hA3 : 0 ≤ (if d = 2 then coarseScale (gauge K) ε n ^ ((5 : ℝ) / 6) *
            Real.log n ^ ((1 : ℝ) / 6) else coarseScale (gauge K) ε n ^ ((d : ℝ) / (d + 1)) *
              Real.log n ^ ((1 : ℝ) / (d + 1))) := by
        split_ifs <;> positivity
      intro hbad
      exact hbad ⟨e1.trans (mul_le_mul_of_nonneg_right hCC₀ hA1),
        e2.trans (mul_le_mul_of_nonneg_right hCC₀ hA2),
        fun x => (e3 x).trans (mul_le_mul_of_nonneg_right hCC₀ hA3)⟩
    · rw [hCp]
      ring
  · rw [not_le] at hnN
    refine le_trans prob_le_one ?_
    rw [ENNReal.one_le_ofReal]
    have h1 : (n : ℝ) ^ p ≤ (N₁ : ℝ) ^ p :=
      Real.rpow_le_rpow hnpos.le (by exact_mod_cast hnN.le) hp.le
    have h2 : (1 : ℝ) ≤ (N₁ : ℝ) ^ p * (n : ℝ) ^ (-p) := by
      rw [Real.rpow_neg hnpos.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hnpos p)]
      exact h1
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hnp)

end Assembly

section Final

/-- **Theorem `thm:norm-shape` for the Minkowski functional of a convex body.** The almost-sure
shape, profile and recurrence of the centrally excited random walk with drift opposite to a
selection of subgradients of `ψ = gauge K`, from the rates of Proposition 5.1. -/
theorem gauge_shape : GaugeShape.{u} := gauge_shape_of_rates gauge_shape_rates

end Final

section Consumption

open CERW.Support.Norm.GaugePotential (cornerTriangle isCompact_cornerTriangle
  convex_cornerTriangle zero_mem_interior_cornerTriangle)

/-- **Proposition `prop:norm-shape` at the cut disc, `ε = 1/4`.** A subgradient selection and an
actual walk exist, and for every walk of this law, for every `p > 0` there is `C` such that for
every `n ≥ 2`, with probability at least `1 - C n^{-p}`, the radii and the local times of the walk
satisfy the rates of Proposition 5.1 for the gauge `cutDisc`. -/
theorem cutDisc_shape_rates {p : ℝ} (hp : 0 < p) :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 → IsSubgradient (gauge cutDisc) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X) ∧
      let r : ℕ → ℝ := fun n =>
        ((((2 : ℕ) : ℝ) + 1) * n /
          (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * normBallVolume (gauge cutDisc))) ^
            ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
      ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ (|normInnerRadius (gauge cutDisc) (X · ω) n - r n|
                      ≤ C * (if (2 : ℕ) = 2 then r n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4)
                        else (r n * Real.log n) ^ ((1 : ℝ) / 2)) ∧
                    normMaxRadius (gauge cutDisc) (X · ω) n - r n
                      ≤ C * (if (2 : ℕ) = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((7 : ℝ) / 6)
                        else r n ^ (((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) + 1)) *
                          Real.log n ^ ((((2 : ℕ) : ℝ) + 2) / (((2 : ℕ) : ℝ) + 1))) ∧
                    ∀ x : Site 2,
                      |(localTime (X · ω) n x : ℝ) - 2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) *
                          max (r n - gauge cutDisc (toSpace x)) 0|
                        ≤ C * (if (2 : ℕ) = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
                          else r n ^ (((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) + 1)) *
                            Real.log n ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))))}
            ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨ξ, hξ, hξ0, hwalk⟩ := exists_isDriftCERW_gauge (d := 2) (by norm_num)
    convex_cutDisc zero_mem_interior_cutDisc (by norm_num) cutDisc_ellipticity
  obtain ⟨C, hC, hb⟩ := gauge_shape_rates (le_refl 2) isCompact_cutDisc convex_cutDisc
      zero_mem_interior_cutDisc (1 / 4 : ℝ)
    (by norm_num) cutDisc_ellipticity p hp
  exact ⟨ξ, hξ, hξ0, hwalk, C, hC, fun μ _ X hX n hn => hb ξ hξ hξ0 μ X hX n hn⟩

/-- **Theorem `thm:norm-shape` at the cut disc, `ε = 1/4`.** A subgradient selection and an actual
walk exist, and for every walk of this law, almost surely the range lies between the sublevel sets
`{{ψ < (1 ∓ η) r_n}}` of the gauge `cutDisc`, the local times follow the cone `2 d ε (r_n - ψ)_+` up
to `η r_n`, and every site is visited infinitely often. -/
theorem cutDisc_shape :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 → IsSubgradient (gauge cutDisc) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X →
      let r : ℕ → ℝ := fun n =>
        ((((2 : ℕ) : ℝ) + 1) * n /
          (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * normBallVolume (gauge cutDisc))) ^
            ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
      ∀ᵐ ω ∂μ,
        (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
          {x : Site 2 | gauge cutDisc (toSpace x) < (1 - η) * r n} ⊆
              ↑(departureRange (X · ω) n) ∧
            (↑(departureRange (X · ω) n) : Set (Site 2)) ⊆
              {x | gauge cutDisc (toSpace x) < (1 + η) * r n}) ∧
        (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site 2,
          |(localTime (X · ω) n x : ℝ) - 2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) *
              max (r n - gauge cutDisc (toSpace x)) 0| ≤ η * r n) ∧
        (∀ x : Site 2, ∃ᶠ j in atTop, X j ω = x) := by
  obtain ⟨ξ, hξ, hξ0, hwalk⟩ := exists_isDriftCERW_gauge (d := 2) (by norm_num)
    convex_cutDisc zero_mem_interior_cutDisc (by norm_num) cutDisc_ellipticity
  exact ⟨ξ, hξ, hξ0, hwalk, fun μ _ X hX =>
    gauge_shape (le_refl 2) isCompact_cutDisc convex_cutDisc zero_mem_interior_cutDisc hξ hξ0
        (by norm_num) cutDisc_ellipticity μ X hX⟩

/-- **Proposition `prop:norm-shape` at the triangle with corners, `ε = 1/4`.** A subgradient
selection and an actual walk exist, and for every walk of this law, for every `p > 0` there is `C`
such that for every `n ≥ 2`, with probability at least `1 - C n^{-p}`, the radii and the local times
of the walk satisfy the rates of Proposition 5.1 for the gauge `cornerTriangle`. -/
theorem cornerTriangle_shape_rates {p : ℝ} (hp : 0 < p) :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 → IsSubgradient (gauge cornerTriangle) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X) ∧
      let r : ℕ → ℝ := fun n =>
        ((((2 : ℕ) : ℝ) + 1) * n /
          (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * normBallVolume (gauge cornerTriangle))) ^
            ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
      ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ (|normInnerRadius (gauge cornerTriangle) (X · ω) n - r n|
                      ≤ C * (if (2 : ℕ) = 2 then r n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4)
                        else (r n * Real.log n) ^ ((1 : ℝ) / 2)) ∧
                    normMaxRadius (gauge cornerTriangle) (X · ω) n - r n
                      ≤ C * (if (2 : ℕ) = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((7 : ℝ) / 6)
                        else r n ^ (((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) + 1)) *
                          Real.log n ^ ((((2 : ℕ) : ℝ) + 2) / (((2 : ℕ) : ℝ) + 1))) ∧
                    ∀ x : Site 2,
                      |(localTime (X · ω) n x : ℝ) - 2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) *
                          max (r n - gauge cornerTriangle (toSpace x)) 0|
                        ≤ C * (if (2 : ℕ) = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
                          else r n ^ (((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) + 1)) *
                            Real.log n ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))))}
            ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨ξ, hξ, hξ0, hwalk⟩ := exists_isDriftCERW_gauge (d := 2) (by norm_num)
    convex_cornerTriangle zero_mem_interior_cornerTriangle (by norm_num)
        GaugeContactShape.Rates.cornerTriangle_ellipticity
  obtain ⟨C, hC, hb⟩ := gauge_shape_rates (le_refl 2) isCompact_cornerTriangle convex_cornerTriangle
      zero_mem_interior_cornerTriangle (1 / 4 : ℝ)
    (by norm_num) GaugeContactShape.Rates.cornerTriangle_ellipticity p hp
  exact ⟨ξ, hξ, hξ0, hwalk, C, hC, fun μ _ X hX n hn => hb ξ hξ hξ0 μ X hX n hn⟩

/-- **Theorem `thm:norm-shape` at the triangle with corners, `ε = 1/4`.** A subgradient selection
and an actual walk exist, and for every walk of this law, almost surely the range lies between the
sublevel sets `{{ψ < (1 ∓ η) r_n}}` of the gauge `cornerTriangle`, the local times follow the cone
`2 d ε (r_n - ψ)_+` up to `η r_n`, and every site is visited infinitely often. -/
theorem cornerTriangle_shape :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 → IsSubgradient (gauge cornerTriangle) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X →
      let r : ℕ → ℝ := fun n =>
        ((((2 : ℕ) : ℝ) + 1) * n /
          (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * normBallVolume (gauge cornerTriangle))) ^
            ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
      ∀ᵐ ω ∂μ,
        (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
          {x : Site 2 | gauge cornerTriangle (toSpace x) < (1 - η) * r n} ⊆
              ↑(departureRange (X · ω) n) ∧
            (↑(departureRange (X · ω) n) : Set (Site 2)) ⊆
              {x | gauge cornerTriangle (toSpace x) < (1 + η) * r n}) ∧
        (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site 2,
          |(localTime (X · ω) n x : ℝ) - 2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) *
              max (r n - gauge cornerTriangle (toSpace x)) 0| ≤ η * r n) ∧
        (∀ x : Site 2, ∃ᶠ j in atTop, X j ω = x) := by
  obtain ⟨ξ, hξ, hξ0, hwalk⟩ := exists_isDriftCERW_gauge (d := 2) (by norm_num)
    convex_cornerTriangle zero_mem_interior_cornerTriangle (by norm_num)
        GaugeContactShape.Rates.cornerTriangle_ellipticity
  exact ⟨ξ, hξ, hξ0, hwalk, fun μ _ X hX =>
    gauge_shape (le_refl 2) isCompact_cornerTriangle convex_cornerTriangle
        zero_mem_interior_cornerTriangle hξ hξ0 (by norm_num)
        GaugeContactShape.Rates.cornerTriangle_ellipticity μ X hX⟩

/-- **The one-sided inner bound at the cut disc, `ε = 1/4`.** A subgradient selection and an actual
walk exist, and for every walk of this law, for every `p > 0` there is `C` such that for every
`n ≥ 2`, with probability at least `1 - C n^{-p}`, `inf_{y ∉ D_n} ψ(y) - r_n` is at most
`C (r_n^{(3-d)/2} (log n)^{1/2} + 1)`, for the gauge `cutDisc`. -/
theorem cutDisc_inner_upper {p : ℝ} (hp : 0 < p) :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 → IsSubgradient (gauge cutDisc) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X) ∧
      let r : ℕ → ℝ := fun n =>
        ((((2 : ℕ) : ℝ) + 1) * n /
          (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * normBallVolume (gauge cutDisc))) ^
            ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
      ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ (normInnerRadius (gauge cutDisc) (X · ω) n - r n ≤
              C * (r n ^ ((3 - ((2 : ℕ) : ℝ)) / 2) * Real.log n ^ ((1 : ℝ) / 2) + 1))} ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨ξ, hξ, hξ0, hwalk⟩ := exists_isDriftCERW_gauge (d := 2) (by norm_num)
    convex_cutDisc zero_mem_interior_cutDisc (by norm_num) cutDisc_ellipticity
  obtain ⟨C, hC, hb⟩ := gauge_inner_upper (le_refl 2) isCompact_cutDisc convex_cutDisc
      zero_mem_interior_cutDisc (1 / 4 : ℝ)
    (by norm_num) cutDisc_ellipticity p hp
  exact ⟨ξ, hξ, hξ0, hwalk, C, hC, fun μ _ X hX n hn => hb ξ hξ hξ0 μ X hX n hn⟩

/-- **The one-sided inner bound at the triangle with corners, `ε = 1/4`.** A subgradient selection
and an actual walk exist, and for every walk of this law, for every `p > 0` there is `C` such that
for every `n ≥ 2`, with probability at least `1 - C n^{-p}`, `inf_{y ∉ D_n} ψ(y) - r_n` is at most
`C (r_n^{(3-d)/2} (log n)^{1/2} + 1)`, for the gauge `cornerTriangle`. -/
theorem cornerTriangle_inner_upper {p : ℝ} (hp : 0 < p) :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 → IsSubgradient (gauge cornerTriangle) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X) ∧
      let r : ℕ → ℝ := fun n =>
        ((((2 : ℕ) : ℝ) + 1) * n /
          (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * normBallVolume (gauge cornerTriangle))) ^
            ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
      ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4 : ℝ) ξ X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ (normInnerRadius (gauge cornerTriangle) (X · ω) n - r n ≤
              C * (r n ^ ((3 - ((2 : ℕ) : ℝ)) / 2) * Real.log n ^ ((1 : ℝ) / 2) + 1))} ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨ξ, hξ, hξ0, hwalk⟩ := exists_isDriftCERW_gauge (d := 2) (by norm_num)
    convex_cornerTriangle zero_mem_interior_cornerTriangle (by norm_num)
        GaugeContactShape.Rates.cornerTriangle_ellipticity
  obtain ⟨C, hC, hb⟩ := gauge_inner_upper (le_refl 2) isCompact_cornerTriangle convex_cornerTriangle
      zero_mem_interior_cornerTriangle (1 / 4 : ℝ)
    (by norm_num) GaugeContactShape.Rates.cornerTriangle_ellipticity p hp
  exact ⟨ξ, hξ, hξ0, hwalk, C, hC, fun μ _ X hX n hn => hb ξ hξ hξ0 μ X hX n hn⟩

end Consumption

end CERW.Support.Norm.GaugeShapeEvents
