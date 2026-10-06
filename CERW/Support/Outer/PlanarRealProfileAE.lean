import CERW.Support.Outer.PlanarRealProfile
import CERW.Frozen.FluctuationRates
import CERW.Support.Main.BorelCantelli

/-!
# The almost-sure real-point displays of the plane

`CERW.Support.Outer.PlanarRealProfile` proves, with probability at least `1 - C n^{-p}`, the
displays of the last subsection of the outer-radius section at every real point `y`: the bound
`U_E(y) ≤ C √r_n (log n)^{3/2}` of the excess potential for `|y| ≤ b + w`, the two-region
estimates of `ℓ~_n(y) - 2dε (r_n - |y|)_+` and the uniform bound, with the exact support-zero case
beyond `b + w`. The existing `CERW.Frozen.fluctuation_rates` proves the lattice, radius and volume
statement of the theorem on the fluctuations together with its almost-sure clause. This module
assembles the almost-sure statement at the original walk for all real points.

* `PlanarRealDisplays` is the bundle: the profile with the constant `C`, the bound
  `|R_in(n) - r_n| ≤ C √(r_n log n)` of the inner radius, and the two-region estimates with
  `|R_in(n) - r_n|` absorbed into the error `C √r_n (log n)^{3/2}` (`n ≥ 3`);
  `planarRealDisplays_of_profile` is the deterministic absorption.
* `planar_real_displays_ae` is the almost-sure statement: for centrally excited random walk with
  `d = 2` and `0 < ε < 1/2`, there is a constant `C`, chosen before the probability space, the walk,
  the sample point and the time, such that almost surely the bundle holds for all large `n`. The
  producers are `planar_real_profile_prob` (Borel-Cantelli with `p = 2`) and the almost-sure clause
  of `CERW.Frozen.fluctuation_rates`.
* `planar_real_displays_ae_on_E7` adds, on the same full-measure event, that the sample point is
  eventually in the literal event `E7` of Section 5.1 and that the path is legal almost surely;
  legality is not a field of `E7` and no equality of `E7` with its legal part is claimed.
* `exists_realization_planar_real_ae` consumes the statement at an actual planar centrally excited
  random walk with `ε = 1/4`: a sample point in the full-measure event and a time `n ≥ 3` at which
  the bundle holds, a real interior point and a real exterior point, neither a lattice site, the
  actual excess set `D_n ∖ B(0, R_in(n))` measurable, bounded and of positive area, and the
  supremum of its absolute potential finite.

No display, event or tail estimate is a premise.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.PlanarRealAE

open CERW CERW.Support.Outer.PlanarReal CERW.Support.Outer.SourceDisplays
  CERW.Support.Norm.ContactEvent CERW.Support.Norm.Section5Localization
open private radius_pos innerRadius_le from CERW.Support.Outer.OuterRadius
open private toSpace_ne_of_not_int quarter_ne_int norm_smul_single
  from CERW.Support.Outer.PlanarRealProfile

variable {d : ℕ}

/-- `sourceRadius` is the radius `r_n = ((d + 1) n / (2 d ε ω_d))^{1/(d+1)}` of the source, with
`ω_d` the volume of the unit ball, written out. -/
theorem sourceRadius_eq_source (d : ℕ) (ε : ℝ) (n : ℕ) :
    sourceRadius d ε n = ((d + 1) * n / (2 * d * ε *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^ ((1 : ℝ) / (d + 1)) :=
  rfl

/-- The width `w = R_out(n) - R_in(n) + 2 √d` of the source is nonnegative. -/
theorem width_nonneg (hd1 : 1 ≤ d) (Y : ℕ → Site d) (n : ℕ) :
    0 ≤ maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d := by
  have h := innerRadius_le hd1 Y n
  have hs := Real.sqrt_nonneg (d : ℝ)
  linarith

/-! ## The bundle of the real-point displays -/

/-- **The real-point displays with the inner radius absorbed.** For a path `Y`, a time `n` and a
constant `C`, with `b = R_in(n)`, `r = r_n` and `Z = √r (log n)^{3/2}`:

* `PlanarRealProfile`: the excess potential bound for `|y| ≤ b + w`, the two-region estimates, the
  support-zero case and the uniform bound, at every real `y`;
* the inner radius bound `|b - r| ≤ C √(r log n)` of `prop:inner`;
* the first estimate with `|b - r_n|` absorbed: `|ℓ~_n(y) - 2dε (r - |y|)_+| ≤ C Z` for
  `|y| ≤ b`;
* the bound `2dε (r - |y|)_+ ≤ C Z` for `|y| ≥ b`. -/
def PlanarRealDisplays (d : ℕ) (ε C : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  PlanarRealProfile d ε C Y n ∧
  |innerRadius Y n - sourceRadius d ε n| ≤
    C * Real.sqrt (sourceRadius d ε n * Real.log n) ∧
  (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ innerRadius Y n →
    |cellLocalTime Y n y - 2 * d * ε * max (sourceRadius d ε n - ‖y‖) 0| ≤
      C * (Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2))) ∧
  (∀ y : EuclideanSpace ℝ (Fin d), innerRadius Y n ≤ ‖y‖ →
    2 * d * ε * max (sourceRadius d ε n - ‖y‖) 0 ≤
      C * (Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2)))

/-- The profile is monotone in the constant (for `n ≥ 1`, where `log n ≥ 0`). -/
private lemma planarRealProfile_mono {ε C C' : ℝ} {Y : ℕ → Site d} {n : ℕ} (hn : 1 ≤ n)
    (hC : C ≤ C') (h : PlanarRealProfile d ε C Y n) : PlanarRealProfile d ε C' Y n := by
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hZ : 0 ≤ Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlog _)
  have hW : 0 ≤ Real.sqrt (sourceRadius d ε n) * Real.log n :=
    mul_nonneg (Real.sqrt_nonneg _) hlog
  have hβ : 0 ≤ |innerRadius Y n - sourceRadius d ε n| := abs_nonneg _
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun y hy => (h1 y hy).trans (mul_le_mul_of_nonneg_right hC hZ),
    fun y hy => (h2 y hy).trans (mul_le_mul_of_nonneg_right hC (add_nonneg hZ hβ)),
    fun y hy => ?_, fun y => (h4 y).trans (mul_le_mul_of_nonneg_right hC hZ)⟩
  obtain ⟨a, b, c, e⟩ := h3 y hy
  exact ⟨a, b, fun hyw => (c hyw).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hC hW)),
    e⟩

/-- **Absorption of `|b - r_n|`.** If the profile holds with the constant `C₁` and the inner radius
bound `|b - r_n| ≤ C₂ √(r_n log n)` holds, then for `n ≥ 3` the bundle holds with every constant
`C` with `C₁ (1 + C₂) ≤ C`, `2dε C₂ ≤ C` and `C₂ ≤ C`: `√(r_n log n) ≤ √r_n (log n)^{3/2}`
because `log n ≥ 1`. -/
theorem planarRealDisplays_of_profile (hd1 : 1 ≤ d) {ε C₁ C₂ C : ℝ} (hε : 0 < ε)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCa : C₁ * (1 + C₂) ≤ C) (hCb : 2 * d * ε * C₂ ≤ C)
    (hCc : C₂ ≤ C) {Y : ℕ → Site d} {n : ℕ} (hn : 3 ≤ n)
    (hprof : PlanarRealProfile d ε C₁ Y n)
    (hin : |innerRadius Y n - sourceRadius d ε n| ≤
      C₂ * Real.sqrt (sourceRadius d ε n * Real.log n)) :
    PlanarRealDisplays d ε C Y n := by
  have hr : 0 < sourceRadius d ε n := radius_pos hd1 hε (by omega : 1 ≤ n)
  have hL1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < n))]
    have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    exact this.le.trans (by exact_mod_cast hn)
  have hlog0 : 0 ≤ Real.log n := by linarith
  have hZ0 : 0 ≤ Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlog0 _)
  have hW0 : 0 ≤ Real.sqrt (sourceRadius d ε n * Real.log n) := Real.sqrt_nonneg _
  have hWZ : Real.sqrt (sourceRadius d ε n * Real.log n) ≤
      Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_mul hr.le, Real.sqrt_eq_rpow (Real.log n)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)) (Real.sqrt_nonneg _)
  have hβ : |innerRadius Y n - sourceRadius d ε n| ≤
      C₂ * (Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2)) :=
    hin.trans (mul_le_mul_of_nonneg_left hWZ hC₂)
  have hCe : C₁ ≤ C :=
    calc C₁ = C₁ * 1 := (mul_one _).symm
      _ ≤ C₁ * (1 + C₂) := mul_le_mul_of_nonneg_left (by linarith) hC₁
      _ ≤ C := hCa
  refine ⟨planarRealProfile_mono (by omega) hCe hprof,
    hin.trans (mul_le_mul_of_nonneg_right hCc hW0), fun y hy => ?_, fun y hy => ?_⟩
  · calc |cellLocalTime Y n y - 2 * d * ε * max (sourceRadius d ε n - ‖y‖) 0|
        ≤ C₁ * (Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2) +
          |innerRadius Y n - sourceRadius d ε n|) := hprof.2.1 y hy
      _ ≤ C₁ * (Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2) +
          C₂ * (Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hβ) hC₁
      _ = C₁ * (1 + C₂) * (Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2)) := by
        ring
      _ ≤ C * (Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hCa hZ0
  · calc 2 * d * ε * max (sourceRadius d ε n - ‖y‖) 0
        ≤ 2 * d * ε * |innerRadius Y n - sourceRadius d ε n| := (hprof.2.2.1 y hy).2.1
      _ ≤ 2 * d * ε * (C₂ * (Real.sqrt (sourceRadius d ε n) *
          Real.log n ^ ((3 : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left hβ (by positivity)
      _ = 2 * d * ε * C₂ * (Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2)) := by
        ring
      _ ≤ C * (Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hCb hZ0

/-! ## The almost-sure statement -/

/-- **The almost-sure real-point displays of the plane.** Let `0 < ε < 1/2`. There is a constant
`C`, chosen before the probability space, the walk, the sample point and the time, such that for
every centrally excited random walk `X` in the plane, almost surely, for all large `n`, the
bundle `PlanarRealDisplays` holds: at every real `y` the excess potential bound
`U_E(y) ≤ C √r_n (log n)^{3/2}` for `|y| ≤ b + w`, the two-region estimates (also with
`|b - r_n|` absorbed), the support-zero case `ℓ~_n(y) = 0` for `|y| > b + w`, the inner radius
bound and the uniform bound `|ℓ~_n(y) - 2dε (r_n - |y|)_+| ≤ C √r_n (log n)^{3/2}`. The
probability producer is `planar_real_profile_prob` with `p = 2` and the lattice and radius
producer is the almost-sure clause of `CERW.Frozen.fluctuation_rates`. -/
theorem planar_real_displays_ae {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), IsCERW μ ε X →
        ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, PlanarRealDisplays 2 ε C (fun j => X j ω) n := by
  obtain ⟨C₁, Cp, hC₁, hCp, hprob⟩ := planar_real_profile_prob.{u} (d := 2) rfl hε hεd
    (p := 2) (by norm_num)
  obtain ⟨C₂, hC₂, -, hfl⟩ := CERW.Frozen.fluctuation_rates.{u} (d := 2) le_rfl ε hε hεd 2
    (by norm_num)
  refine ⟨max (max (C₁ * (1 + C₂)) (2 * ((2 : ℕ) : ℝ) * ε * C₂)) C₂, ?_, ?_⟩
  · exact lt_max_of_lt_left (lt_max_of_lt_left (by positivity))
  intro Ω _ μ _ X hX
  have h1 := CERW.Support.Main.ae_eventually_of_le_rpow (μ := μ)
    (P := fun n ω => PlanarRealProfile 2 ε C₁ (fun j => X j ω) n) (C := Cp) (p := 2)
    (by norm_num) (n₀ := 2) (fun n hn => hprob μ X hX n hn)
  filter_upwards [h1, hfl μ X hX] with ω hω1 hω2
  filter_upwards [hω1, hω2, eventually_ge_atTop 3] with n hn1 hn2 hn3
  obtain ⟨hI, -, -⟩ := hn2
  rw [if_pos rfl] at hI
  obtain ⟨hin, -⟩ := hI
  exact planarRealDisplays_of_profile (by omega) hε hC₁.le hC₂.le
    ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _) hn3 hn1 hin

/-- **The same almost-sure event inside the literal event of Section 5.1.** For `0 < ε < 1/2`
there are constants `K` of the event `E7` and `C`, chosen before the probability space, the walk,
the sample point and the time, such that for every centrally excited random walk `X` in the
plane: the illegal sample points are null, and almost surely, for all large `n`, the sample point
belongs to `E7 K X n` and the bundle `PlanarRealDisplays` holds. Legality is not a field of `E7`
and `E7` is not claimed to equal its legal part. -/
theorem planar_real_displays_ae_on_E7 {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ)) :
    ∃ (K : EventConstants) (C : ℝ), 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), IsCERW μ ε X →
        (∀ᵐ ω ∂μ, ω ∈ legalSet X) ∧
        ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε (fun z => unitDir (toSpace z)) K X n ∧
          PlanarRealDisplays 2 ε C (fun j => X j ω) n := by
  obtain ⟨K, _, _, _, Cp, n₀, -, -, -, -, hE⟩ :=
    planar_displays_on_E7_of_isCERW.{u} hε hεd (p := 2) (by norm_num)
  obtain ⟨C, hC, hAE⟩ := planar_real_displays_ae.{u} hε hεd
  refine ⟨K, C, hC, fun μ _ X hX => ⟨?_, ?_⟩⟩
  · exact MeasureTheory.ae_iff.mpr (hE μ X hX n₀ le_rfl).1.2.1
  · have h1 := CERW.Support.Main.ae_eventually_of_le_rpow (μ := μ)
      (P := fun n ω => ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε
        (fun z => unitDir (toSpace z)) K X n) (C := Cp) (p := 2) (by norm_num) (n₀ := n₀)
      (fun n hn => (hE μ X hX n hn).1.1)
    filter_upwards [h1, hAE μ X hX] with ω hω1 hω2
    filter_upwards [hω1, hω2] with n hn1 hn2
    exact ⟨hn1, hn2⟩

/-- **The profile on the legal carrier, almost surely.** For `0 < ε < 1/2` there are constants `K`
and `Cr`, chosen before the probability space, the walk, the sample point and the time, such that
for every centrally excited random walk `X` in the plane, almost surely, for all large `n`, the
sample point belongs to the event `E7` of the legal carrier of `X` (a walk with the same drift
field that is legal at every sample point and coincides with `X` almost surely) and the carrier has
`PlanarRealProfile` with the constant `Cr`. No equality of the carrier with `X` at any sample point
is asserted. -/
theorem planar_real_profile_ae_on_carrier {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / ((2 : ℕ) : ℝ)) :
    ∃ (K : EventConstants) (Cr : ℝ), 0 < Cr ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), IsCERW μ ε X →
        ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε (fun z => unitDir (toSpace z)) K
              (legalCarrier (by norm_num : 1 ≤ 2) X) n ∧
            PlanarRealProfile 2 ε Cr (fun j => legalCarrier (by norm_num : 1 ≤ 2) X j ω) n := by
  obtain ⟨K, _, _, Cr, Cp, n₀, -, -, hCr, -, hE⟩ :=
    planar_displays_on_E7_of_isCERW.{u} hε hεd (p := 2) (by norm_num)
  refine ⟨K, Cr, hCr, fun μ _ X hX => ?_⟩
  refine CERW.Support.Main.ae_eventually_of_le_rpow (μ := μ)
    (P := fun n ω => ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε
        (fun z => unitDir (toSpace z)) K (legalCarrier (by norm_num : 1 ≤ 2) X) n ∧
      PlanarRealProfile 2 ε Cr (fun j => legalCarrier (by norm_num : 1 ≤ 2) X j ω) n)
    (C := Cp) (p := 2) (by norm_num) (n₀ := n₀) (fun n hn => ?_)
  refine le_trans (measure_mono ?_) (hE μ X hX n hn).2.1
  intro ω hω hmem
  exact hω ⟨hmem, ((hE μ X hX n hn).2.2 ω hmem).2.2⟩

/-! ## Consumption at an actual planar walk -/

/-- **Consumer of the almost-sure displays.** There are a probability space carrying centrally
excited random walk in the plane with `ε = 1/4`, constants `K` and `C`, the full-measure
statements of `planar_real_displays_ae_on_E7` and `planar_real_profile_ae_on_carrier`, and a
sample point `ω` of the full-measure event with a time `n ≥ 3` at which the sample point is legal,
starts at the origin, lies in the literal
event `E7`, and the bundle holds. At it, `1/2 ≤ R_in(n)`; the excess set
`D_n ∖ B(0, R_in(n))` is measurable, bounded and of positive area and the supremum of its
absolute potential is finite and its integrand is integrable at every real point; the real point
`y₁ = e₁/4`, which is not a lattice site, lies in `B(0, R_in(n))` with the excess potential bound
and both forms of the inner estimate; and the real point `y₂ = (b + w + 1/3) e₁ + e₂/4`, which is
not a lattice site, lies beyond the support, where
`ℓ~_n(y₂) = 0` and the cone and the uniform bound hold. -/
theorem exists_realization_planar_real_ae :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), IsCERW μ (1 / 4 : ℝ) X ∧
      ∃ (K : EventConstants) (C : ℝ), 0 < C ∧
        (∀ᵐ ω ∂μ, ω ∈ legalSet X) ∧
        (∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (1 / 4 : ℝ)
            (fun z => unitDir (toSpace z)) K X n ∧
          PlanarRealDisplays 2 (1 / 4 : ℝ) C (fun j => X j ω) n) ∧
        (∃ (K' : EventConstants) (Cr : ℝ), 0 < Cr ∧
          ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
            ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (1 / 4 : ℝ)
                (fun z => unitDir (toSpace z)) K' (legalCarrier (by norm_num : 1 ≤ 2) X) n ∧
              PlanarRealProfile 2 (1 / 4 : ℝ) Cr
                (fun j => legalCarrier (by norm_num : 1 ≤ 2) X j ω) n) ∧
        ∃ (ω : Ω) (n : ℕ), 3 ≤ n ∧ ω ∈ legalSet X ∧ X 0 ω = 0 ∧
          ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (1 / 4 : ℝ)
            (fun z => unitDir (toSpace z)) K X n ∧
          PlanarRealDisplays 2 (1 / 4 : ℝ) C (fun j => X j ω) n ∧
          1 / 2 ≤ innerRadius (fun j => X j ω) n ∧
          MeasurableSet (cellSet (fun j => X j ω) n \
            Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (innerRadius (fun j => X j ω) n)) ∧
          Bornology.IsBounded (cellSet (fun j => X j ω) n \
            Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (innerRadius (fun j => X j ω) n)) ∧
          0 < volume (cellSet (fun j => X j ω) n \
            Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (innerRadius (fun j => X j ω) n)) ∧
          BddAbove (Set.range fun z : EuclideanSpace ℝ (Fin 2) =>
            |potential 2 (1 / 4 : ℝ) (cellSet (fun j => X j ω) n \
              Metric.ball 0 (innerRadius (fun j => X j ω) n)) z|) ∧
          (∀ y : EuclideanSpace ℝ (Fin 2), IntegrableOn
            (fun v : EuclideanSpace ℝ (Fin 2) => inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ 2)
            (cellSet (fun j => X j ω) n \
              Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (innerRadius (fun j => X j ω) n))) ∧
          (∃ y₁ : EuclideanSpace ℝ (Fin 2), ‖y₁‖ < innerRadius (fun j => X j ω) n ∧
            (∀ x : Site 2, toSpace x ≠ y₁) ∧
            potential 2 (1 / 4 : ℝ) (cellSet (fun j => X j ω) n \
              Metric.ball 0 (innerRadius (fun j => X j ω) n)) y₁ ≤
              C * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) *
                Real.log n ^ ((3 : ℝ) / 2)) ∧
            |cellLocalTime (fun j => X j ω) n y₁ -
                2 * (2 : ℕ) * (1 / 4 : ℝ) * max (sourceRadius 2 (1 / 4 : ℝ) n - ‖y₁‖) 0| ≤
              C * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n ^ ((3 : ℝ) / 2)) ∧
            |cellLocalTime (fun j => X j ω) n y₁ -
                2 * (2 : ℕ) * (1 / 4 : ℝ) * max (sourceRadius 2 (1 / 4 : ℝ) n - ‖y₁‖) 0| ≤
              C * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n ^ ((3 : ℝ) / 2) +
                |innerRadius (fun j => X j ω) n - sourceRadius 2 (1 / 4 : ℝ) n|)) ∧
          (∃ y₂ : EuclideanSpace ℝ (Fin 2),
            innerRadius (fun j => X j ω) n + (maxRadius (fun j => X j ω) n -
              innerRadius (fun j => X j ω) n + 2 * Real.sqrt (2 : ℕ)) < ‖y₂‖ ∧
            (∀ x : Site 2, toSpace x ≠ y₂) ∧
            cellLocalTime (fun j => X j ω) n y₂ = 0 ∧
            2 * (2 : ℕ) * (1 / 4 : ℝ) * max (sourceRadius 2 (1 / 4 : ℝ) n - ‖y₂‖) 0 ≤
              C * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n ^ ((3 : ℝ) / 2)) ∧
            |cellLocalTime (fun j => X j ω) n y₂ -
                2 * (2 : ℕ) * (1 / 4 : ℝ) * max (sourceRadius 2 (1 / 4 : ℝ) n - ‖y₂‖) 0| ≤
              C * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n ^ ((3 : ℝ) / 2))) := by
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hεd : (1 / 4 : ℝ) < 1 / ((2 : ℕ) : ℝ) := by norm_num
  obtain ⟨Ω, hΩ, μ, hμ, X, hX⟩ := CERW.Support.Law.exists_isCERW (d := 2) (by omega) hε.le hεd
  obtain ⟨K, C, hC, hall⟩ := planar_real_displays_ae_on_E7.{0} hε hεd
  obtain ⟨hleg, hae⟩ := hall μ X hX
  obtain ⟨K', Cr, hCr, hcar⟩ := planar_real_profile_ae_on_carrier.{0} hε hεd
  refine ⟨Ω, hΩ, μ, hμ, X, hX, K, C, hC, hleg, hae, ⟨K', Cr, hCr, hcar μ X hX⟩, ?_⟩
  haveI : (ae μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
  obtain ⟨ω, hωL, hω⟩ := (hleg.and hae).exists
  obtain ⟨n, ⟨hE, hD⟩, hn3⟩ := (hω.and (eventually_ge_atTop 3)).exists
  have h0 : X 0 ω = 0 := hωL.1
  have hb := half_le_innerRadius (by omega : 1 ≤ 2) (fun j => X j ω) n (by omega) h0
  have hw := width_nonneg (d := 2) (by omega) (fun j => X j ω) n
  have hEm : MeasurableSet (cellSet (fun j => X j ω) n \
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (innerRadius (fun j => X j ω) n)) :=
    (CERW.Support.Occupation.measurableSet_cellSet (fun j => X j ω) n).diff
      measurableSet_ball
  have hEb : Bornology.IsBounded (cellSet (fun j => X j ω) n \
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (innerRadius (fun j => X j ω) n)) :=
    (Metric.isBounded_ball.subset (CERW.Support.Occupation.cellSet_subset_ball (by omega : 1 ≤ 2)
      (fun j => X j ω) n)).subset Set.sdiff_subset
  have hvol := volume_cellSet_diff_ball_innerRadius_pos (d := 2) le_rfl (fun j => X j ω) n
    (by omega) h0
  have hbdd := bddAbove_abs_potential (d := 2) (by omega) (by norm_num : (0 : ℝ) ≤ 1 / 4) hEm hEb
  refine ⟨ω, n, hn3, hωL, h0, hE, hD, hb, hEm, hEb, hvol, hbdd,
    fun y => CERW.Support.Geometry.integrableOn_potentialIntegrand (by omega) hEm
      hEb.measure_lt_top.ne y, ?_, ?_⟩
  · refine ⟨(1 / 4 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ), ?_, ?_, ?_⟩
    · rw [norm_smul_single, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      linarith
    · intro x
      refine toSpace_ne_of_not_int (0 : Fin 2) fun m => ?_
      have h10 : ((1 / 4 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 0 = 1 / 4 := by
        simp
      rw [h10]
      exact quarter_ne_int m
    · have hy1b : ‖(1 / 4 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ ≤
          innerRadius (fun j => X j ω) n := by
        rw [norm_smul_single, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
        linarith
      exact ⟨hD.1.1 _ (hy1b.trans (le_add_of_nonneg_right hw)), hD.2.2.1 _ hy1b,
        hD.1.2.1 _ hy1b⟩
  · obtain ⟨y₂, hy20, hy21⟩ : ∃ y : EuclideanSpace ℝ (Fin 2),
        y 0 = innerRadius (fun j => X j ω) n + (maxRadius (fun j => X j ω) n -
          innerRadius (fun j => X j ω) n + 2 * Real.sqrt (2 : ℕ)) + 1 / 3 ∧ y 1 = 1 / 4 :=
      ⟨(innerRadius (fun j => X j ω) n + (maxRadius (fun j => X j ω) n -
          innerRadius (fun j => X j ω) n + 2 * Real.sqrt (2 : ℕ)) + 1 / 3) •
          EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (1 / 4 : ℝ) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ), by simp, by simp⟩
    have hy2 : y₂ 0 ≤ ‖y₂‖ := (Real.le_norm_self (y₂ 0)).trans (PiLp.norm_apply_le y₂ 0)
    rw [hy20] at hy2
    have hfar : innerRadius (fun j => X j ω) n + (maxRadius (fun j => X j ω) n -
        innerRadius (fun j => X j ω) n + 2 * Real.sqrt (2 : ℕ)) < ‖y₂‖ :=
      lt_of_lt_of_le (lt_add_of_pos_right _ (by norm_num)) hy2
    have hbn : innerRadius (fun j => X j ω) n ≤ ‖y₂‖ :=
      le_trans (le_add_of_nonneg_right hw) hfar.le
    exact ⟨y₂, hfar, fun x => toSpace_ne_of_not_int (1 : Fin 2) fun m => by
        rw [hy21]; exact quarter_ne_int m,
      (hD.1.2.2.1 y₂ hbn).2.2.2 hfar, hD.2.2.2 y₂ hbn, hD.1.2.2.2 y₂⟩

end CERW.Support.Outer.PlanarRealAE
