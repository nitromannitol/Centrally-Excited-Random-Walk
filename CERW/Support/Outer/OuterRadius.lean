import CERW.Support.Statements
import CERW.Support.Main.EventProb
import CERW.Support.Main.BorelCantelli
import CERW.Support.Main.LimitShape
import CERW.Support.Main.ScaleLimits
import CERW.Support.Drift.Bridge
import CERW.Support.Norm.BallLayer
import CERW.Support.Contact.ContactCell
import CERW.Support.Inner.InnerRadius
import CERW.Support.Contact.ContactLower
import CERW.Support.Contact.Kernel
import CERW.Support.Geometry.Assembly
import CERW.Support.LocalTime.KernelAsymptotics
import CERW.Support.LocalTime.LocalMart
import CERW.Support.Drift.Dynkin

/-!
# The outer radius and the fluctuation rates of the Euclidean walk

`outer_radius_of` is Proposition 7.1 (the bound `R_out(n) ≤ r_n + C (log n)^{d+1}`, respectively
`r_n + C √r_n (log n)^{5/2}` in the plane) and `fluctuation_rates_of` is Theorem 1.2, both for
the Euclidean centrally excited random walk. The inputs are Proposition 6.1 (`inner_radius`), the
near-far lemma (Lemma 7.2, `near_far`), the outer crossing lemma (Lemma 4.3, `outer_crossing`) and,
for Theorem 1.2, Proposition 7.1 itself (`outer_radius`).

The proof is deterministic on the intersection of three good events: the events of
Sections 3 and 4 (`PathFacts`), the conclusions of Proposition 6.1 (`InnerOK`), and the martingale
bounds of the ramp functions `(u_s · x - k)₊` (`LinOK`), which with `outer_crossing` give the
crossing bound (`CrossOK`). For `d ≥ 3` the bracket of the local martingales beyond the inner ball
is bounded by the positive part of the potential of `E = D_n ∖ B(0, R_in)` (Newton's theorem for a
radial weight and a lattice absorption argument); probes beyond the outer radius bound the
volume of the caps of `E`, the near-far lemma bounds `U_E^+` on the annulus, and a Young
inequality closes the estimate for the width `w = R_out - R_in + 2√d`. In the plane the bracket
is bounded directly and the maximum principle for the harmonic function `U_E` inside the inner
ball gives the uniform bound on the local times.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- The radius `r_n = ((d+1) n / (2 d ε ω_d))^{1/(d+1)}` of `eq:radius`. -/
private noncomputable def radius (d : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  ((d + 1) * n / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))

/-- The rate `q_n` of `eq:qn`. -/
private noncomputable def qrate (d : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  if d = 2 then Real.sqrt (Real.log n / radius d ε n) else Real.log n / radius d ε n

/-- The bracket sum `W_x = Σ_{j<n} (1 + |Y_j - x|)^{2-2d}` of the local martingale at `x`. -/
private noncomputable def braSum (Y : ℕ → Site d) (n : ℕ) (x : Site d) : ℝ :=
  ∑ j ∈ Finset.range n, (1 + euclidNorm (Y j - x)) ^ (2 - 2 * (d : ℝ))

/-- The compensated position `Z_t = X_t + ε Σ_{j<t} I_j u_{X_j}` of a path. -/
private noncomputable def compPath (d : ℕ) (ε : ℝ) (Y : ℕ → Site d) (t : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  toSpace (Y t) + ε • ∑ j ∈ Finset.range t,
    if Y j ∉ departureRange Y j then unitDir (toSpace (Y j)) else 0

/-- The linear martingale event of `eq:linear-mart` for the Euclidean walk, for every direction
`u_s` with `|s| ≤ n` and every level `k`. -/
private def LinOK (d : ℕ) (ε C₁ : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  ∀ s : Site d, euclidNorm s ≤ n → ∀ k : ℕ, k ≤ n →
    |dynkinMart (driftStepProb d ε (fun z => unitDir (toSpace z)))
        (fun z => max (inner ℝ (unitDir (toSpace s)) (toSpace z) - k) 0) Y n|
      ≤ C₁ * (Real.sqrt (Real.log n *
            ∑ z ∈ (departureRange Y n).filter
              (fun z => (k : ℝ) - 1 < inner ℝ (unitDir (toSpace s)) (toSpace z)),
            (localTime Y n z : ℝ)) + Real.log n)

/-- The deterministic consequences of the good events of Sections 4 and 5. -/
private structure PathFacts (d : ℕ) (ε C₀ C₁ : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop where
  start : Y 0 = 0
  step : ∀ j, Y (j + 1) - Y j ∈ unitSteps d
  maxLoc : (maxLocalTime Y n : ℝ) ≤ C₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1))
  maxRad : maxRadius Y n ≤ C₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1))
  glob : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
    |cellLocalTime Y n y - potential d ε (cellSet Y n) y| ≤ C₁ *
      (if d = 2 then Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2) + Real.log ((n : ℝ) + 2)
        else Real.sqrt (maxLocalTime Y n * Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2))
  point : ∀ x : Site d, euclidNorm x ≤ 3 * n →
    |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
      C₁ * (Real.sqrt (braSum Y n x * Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2))
  vec : ∀ s t : ℕ, s < t → t ≤ n →
    ‖compPath d ε Y t - compPath d ε Y s‖ ≤ C₁ * Real.sqrt (((t : ℝ) - s) * Real.log ((n : ℝ) + 2))

/-- The clauses of Proposition 6.1 for a path. -/
private def InnerOK (d : ℕ) (ε C : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  |innerRadius Y n - radius d ε n| ≤ C * radius d ε n * qrate d ε n ∧
  volume (((radius d ε n)⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
      ≤ ENNReal.ofReal (C * qrate d ε n) ∧
  ∀ y : EuclideanSpace ℝ (Fin d),
    |cellLocalTime Y n y - 2 * d * ε * max (radius d ε n - ‖y‖) 0|
      ≤ C * radius d ε n * qrate d ε n ^ ((1 : ℝ) / d)

/-- The maximal local time over the visited sites of norm at least `b`. -/
private noncomputable def outerMax (Y : ℕ → Site d) (n : ℕ) (b : ℝ) : ℕ :=
  ((departureRange Y n).filter (fun z => b ≤ euclidNorm z)).sup (localTime Y n)

/-- The mass bound of `eq:mass` for the part of `D_n` outside the inner ball. -/
private def MassOK (d : ℕ) (ε Cm : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  (volume (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (innerRadius Y n))).toReal
    ≤ Cm * radius d ε n ^ d * qrate d ε n

/-- The crossing bound `eq:euclid-crossing`. -/
private def CrossOK (d : ℕ) (Ccr : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  ∀ b : ℝ, 0 ≤ b → maxRadius Y n ≤ b + Ccr * (1 + (outerMax Y n b : ℝ)) * Real.log n

/-! ### Monotonicity in the constants -/

/-- The logarithm `log (n + 2)` is nonnegative. -/
private lemma mono_log_nonneg (n : ℕ) : 0 ≤ Real.log ((n : ℝ) + 2) :=
  Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

/-- `PathFacts` is monotone in its constant `C₁`. -/
private theorem PathFacts.mono {ε C₀ C₁ C₁' : ℝ} (h : C₁ ≤ C₁') {Y : ℕ → Site d} {n : ℕ}
    (hY : PathFacts d ε C₀ C₁ Y n) : PathFacts d ε C₀ C₁' Y n := by
  have hL := mono_log_nonneg n
  refine ⟨hY.start, hY.step, hY.maxLoc, hY.maxRad, fun y hy => ?_, fun x hx => ?_,
    fun s t hst htn => ?_⟩
  · refine (hY.glob y hy).trans (mul_le_mul_of_nonneg_right h ?_)
    split_ifs
    · exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) hL
    · exact add_nonneg (Real.sqrt_nonneg _) hL
  · exact (hY.point x hx).trans (mul_le_mul_of_nonneg_right h
      (add_nonneg (Real.sqrt_nonneg _) hL))
  · exact (hY.vec s t hst htn).trans (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _))

/-- `LinOK` is monotone in its constant. -/
private theorem LinOK.mono {ε C₁ C₁' : ℝ} (h : C₁ ≤ C₁') {Y : ℕ → Site d} {n : ℕ}
    (hY : LinOK d ε C₁ Y n) : LinOK d ε C₁' Y n := by
  intro s hs k hk
  refine (hY s hs k hk).trans (mul_le_mul_of_nonneg_right h ?_)
  exact add_nonneg (Real.sqrt_nonneg _) (Real.log_natCast_nonneg n)
/-- `eq:newton-convolution` and `eq:radial-convolution`: for `d ≥ 3` and the kernel
`χ(ζ) = (1 + |ζ|)^{2-2d}`, `(χ * U_D)(y) ≤ ‖χ‖₁ U_D^+(y)`. -/
private def NewtonConv (d : ℕ) : Prop :=
  ∀ {ε : ℝ}, 0 ≤ ε → ∀ {D : Set (EuclideanSpace ℝ (Fin d))}, MeasurableSet D →
    Bornology.IsBounded D → ∀ y : EuclideanSpace ℝ (Fin d),
    ∫ ζ : EuclideanSpace ℝ (Fin d), (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) * potential d ε D (y - ζ)
      ≤ (∫ ζ : EuclideanSpace ℝ (Fin d), (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ))) *
        positivePotential d ε D y

/-! ### The geometry of `D_n` and its pieces -/

/-- The ball of radius `R_in(n)` lies in `D_n`. -/
private theorem ball_innerRadius_subset (hd : 1 ≤ d) (Y : ℕ → Site d) (n : ℕ) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (innerRadius Y n) ⊆ cellSet Y n :=
  (CERW.Support.Contact.exists_contact_cell hd Y n).1

/-- The inner radius is nonnegative. -/
private theorem innerRadius_nonneg (Y : ℕ → Site d) (n : ℕ) : 0 ≤ innerRadius Y n :=
  Real.sInf_nonneg (by rintro _ ⟨y, _, rfl⟩; exact norm_nonneg y)

/-- The outer radius is nonnegative. -/
private lemma gd_maxRadius_nonneg (Y : ℕ → Site d) (n : ℕ) : 0 ≤ maxRadius Y n :=
  (LatticeProb.euclidNorm_nonneg (Y 0)).trans (euclidNorm_le_maxRadius Y (Nat.zero_le n))

/-- The inner radius is at most `R_out(n) + √d/2`. -/
private theorem innerRadius_le (hd : 1 ≤ d) (Y : ℕ → Site d) (n : ℕ) :
    innerRadius Y n ≤ maxRadius Y n + Real.sqrt d / 2 := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hR := gd_maxRadius_nonneg Y n
  have hsq : 0 ≤ Real.sqrt d / 2 := by positivity
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨v, hv⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin d))
    (show 0 ≤ maxRadius Y n + Real.sqrt d / 2 + η / 2 by linarith)
  have hvD : v ∉ cellSet Y n := fun hvD => by
    have := CERW.Support.Occupation.norm_le_of_mem_cellSet Y n hvD
    linarith
  calc innerRadius Y n ≤ ‖v‖ := csInf_le ⟨0, by rintro _ ⟨y, _, rfl⟩; exact norm_nonneg y⟩
        ⟨v, hvD, rfl⟩
    _ ≤ maxRadius Y n + Real.sqrt d / 2 + η := by linarith

/-- `E = D_n ∖ B(0,b)` lies in the annulus `{b ≤ |v| ≤ b + w}` with `w = R_out - b + 2√d`. -/
private theorem sdiff_subset_annulus (hd : 1 ≤ d) (Y : ℕ → Site d) (n : ℕ) :
    cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (innerRadius Y n) ⊆
      {v | innerRadius Y n ≤ ‖v‖ ∧
        ‖v‖ ≤ innerRadius Y n + (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d)} := by
  rintro v ⟨hvD, hvb⟩
  have hsq : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · rwa [Metric.mem_ball, dist_zero_right, not_lt] at hvb
  · have := CERW.Support.Occupation.cellSet_subset_ball hd Y n hvD
    rw [mem_ball_zero_iff] at this
    linarith

/-- The Euclidean norm is a norm in the sense of `CERW.IsNorm`. -/
private lemma gd_isNorm : CERW.IsNorm (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) :=
  ⟨norm_add_le, fun t x => by simp only [norm_smul, Real.norm_eq_abs],
    fun x hx => norm_eq_zero.mp hx⟩

/-- `lem:layer` for the Euclidean norm: a set in an annulus of width `a` has potential at most
`2dεa` in absolute value. -/
private theorem annulus_potential_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (ha : 0 < a)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hsub : D ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + a}) (y : EuclideanSpace ℝ (Fin d)) :
    |potential d ε D y| ≤ 2 * d * ε * a := by
  have hsub' : D ⊆ {v | max b 0 ≤ ‖v‖ ∧ ‖v‖ ≤ max b 0 + a} := by
    intro v hv
    obtain ⟨h1, h2⟩ := hsub hv
    have h3 := norm_nonneg v
    refine ⟨max_le h1 h3, ?_⟩
    rcases le_total b 0 with hb | hb
    · rw [max_eq_right hb]
      linarith
    · rw [max_eq_left hb]
      exact h2
  have h := CERW.Support.Norm.layer_potential hd gd_isNorm hε (le_max_right b 0) ha hD hsub' y
  rwa [CERW.Support.Inner.normPotential_norm_eq (by omega)] at h

/-- Splitting the potential over a measurable subset of finite volume. -/
private lemma gd_potential_sdiff_eq (hd : 1 ≤ d) {ε : ℝ}
    {A D : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (hAD : A ⊆ D) (y : EuclideanSpace ℝ (Fin d)) :
    potential d ε D y = potential d ε A y + potential d ε (D \ A) y := by
  have hF : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) D :=
    CERW.Support.Geometry.integrableOn_potentialIntegrand hd hD hDfin y
  have hFA : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) A := hF.mono_set hAD
  have hFE : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) (D \ A) := hF.mono_set Set.sdiff_subset
  have hunion : A ∪ (D \ A) = D := Set.union_sdiff_cancel hAD
  have hsplit : ∫ v in D, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d =
      (∫ v in A, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) +
      (∫ v in D \ A, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) := by
    conv_lhs => rw [← hunion]
    exact setIntegral_union Set.disjoint_sdiff_right (hD.diff hA) hFA hFE
  unfold potential
  rw [hsplit]
  ring

/-- `eq:ballpotential-euclid` and the decomposition `U_{D_n} = U_{B(0,b)} + U_E`. -/
private theorem potential_split (hd : 2 ≤ d) (ε : ℝ) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDb : Bornology.IsBounded D) {b : ℝ} (hb : 0 < b)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ D) (y : EuclideanSpace ℝ (Fin d)) :
    potential d ε D y =
      2 * d * ε * max (b - ‖y‖) 0 + potential d ε (D \ Metric.ball 0 b) y := by
  rw [gd_potential_sdiff_eq (by omega) measurableSet_ball hD hDb.measure_lt_top.ne hball y,
    CERW.Support.Geometry.potential_ball hd ε hb y]
/-- Rescaling by `r`: `|D ∖ B(0,r)| ≤ r^d |r⁻¹ D ∆ B(0,1)|`. -/
private lemma gd_volume_sdiff_ball_le {r : ℝ} (hr : 0 < r)
    (D : Set (EuclideanSpace ℝ (Fin d))) :
    volume (D \ Metric.ball 0 r) ≤ ENNReal.ofReal (r ^ d) *
      volume ((r⁻¹ • D) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  have hpre : D \ Metric.ball 0 r =
      (fun x : EuclideanSpace ℝ (Fin d) => r⁻¹ • x) ⁻¹'
        ((r⁻¹ • D) \ Metric.ball 0 1) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_preimage, Set.smul_mem_smul_set_iff₀ (inv_ne_zero hr.ne'),
      mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr,
      inv_mul_lt_iff₀ hr, mul_one]
  rw [hpre, Measure.addHaar_preimage_smul volume (inv_ne_zero hr.ne'),
    finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_pos (pow_pos hr d)]
  exact mul_le_mul_right (measure_mono fun x hx => Or.inl hx) _

/-- The shell `B(0,r) ∖ B(0,b)` has volume at most `ω_d d r^d t` when `1 - b/r ≤ t`. -/
private lemma gd_volume_shell_le (hd : 1 ≤ d) {r b : ℝ} (hr : 0 < r) (hb : 0 ≤ b) {t : ℝ}
    (ht : 1 - b / r ≤ t) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r \ Metric.ball 0 b) ≤
      ENNReal.ofReal (unitBallVolume d * d * r ^ d * t) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  rcases le_or_gt r b with hrb | hbr
  · rw [Set.sdiff_eq_empty.mpr (Metric.ball_subset_ball hrb), measure_empty]
    exact zero_le
  have hω := unitBallVolume_pos d
  have hrd : 0 < r ^ d := pow_pos hr d
  have hbd : 0 ≤ b ^ d := pow_nonneg hb d
  have hV : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) =
      ENNReal.ofReal (unitBallVolume d) :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  rw [measure_sdiff (Metric.ball_subset_ball hbr.le) measurableSet_ball.nullMeasurableSet
      measure_ball_lt_top.ne, Measure.addHaar_ball _ _ hr.le, Measure.addHaar_ball _ _ hb,
    finrank_euclideanSpace_fin, hV, ← ENNReal.ofReal_mul hrd.le, ← ENNReal.ofReal_mul hbd,
    ← ENNReal.ofReal_sub _ (mul_nonneg hbd hω.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hbern : 1 + (d : ℝ) * (b / r - 1) ≤ (1 + (b / r - 1)) ^ d :=
    one_add_mul_le_pow (by have : 0 ≤ b / r := div_nonneg hb hr.le; linarith) d
  rw [show 1 + (b / r - 1) = b / r by ring] at hbern
  have hbpow : b ^ d = r ^ d * (b / r) ^ d := by rw [div_pow]; field_simp
  have hkey : r ^ d - b ^ d ≤ (d : ℝ) * r ^ d * t := by
    rw [hbpow]
    calc r ^ d - r ^ d * (b / r) ^ d ≤ r ^ d - r ^ d * (1 + d * (b / r - 1)) := by
          have := mul_le_mul_of_nonneg_left hbern hrd.le
          linarith
      _ = r ^ d * ((d : ℝ) * (1 - b / r)) := by ring
      _ ≤ r ^ d * ((d : ℝ) * t) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg d)) hrd.le
      _ = (d : ℝ) * r ^ d * t := by ring
  calc r ^ d * unitBallVolume d - b ^ d * unitBallVolume d
      = (r ^ d - b ^ d) * unitBallVolume d := by ring
    _ ≤ ((d : ℝ) * r ^ d * t) * unitBallVolume d := mul_le_mul_of_nonneg_right hkey hω.le
    _ = unitBallVolume d * d * r ^ d * t := by ring

/-- `eq:mass`: the volume outside the inner ball, from the volume clause and the inner radius
clause of Proposition 6.1. -/
private theorem mass_of_inner (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {Cin : ℝ} (hCin : 0 ≤ Cin)
    (Y : ℕ → Site d) {n : ℕ} (hn : 1 ≤ n) (h : InnerOK d ε Cin Y n) :
    MassOK d ε (Cin * (1 + d * unitBallVolume d)) Y n := by
  obtain ⟨hin, hvol, -⟩ := h
  have hω := unitBallVolume_pos d
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hr : 0 < radius d ε n := by
    unfold radius
    refine Real.rpow_pos_of_pos ?_ _
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hb0 := innerRadius_nonneg Y n
  set r := radius d ε n with hrdef
  set q := qrate d ε n with hqdef
  set b := innerRadius Y n with hbdef
  have hrd : 0 < r ^ d := pow_pos hr d
  have hq : 0 ≤ q := by
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    rw [hqdef]
    unfold qrate
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact div_nonneg hlog hr.le
  have ht : 0 ≤ Cin * q := mul_nonneg hCin hq
  have hbr : 1 - b / r ≤ Cin * q := by
    rw [show 1 - b / r = (r - b) / r by field_simp, div_le_iff₀ hr]
    have h1 : r - b ≤ |b - r| := by rw [abs_sub_comm]; exact le_abs_self _
    have h2 : Cin * q * r = Cin * r * q := by ring
    linarith
  have hsub : cellSet Y n \ Metric.ball 0 b ⊆
      (cellSet Y n \ Metric.ball 0 r) ∪ (Metric.ball 0 r \ Metric.ball 0 b) := by
    rintro v ⟨hvD, hvb⟩
    by_cases hvr : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r
    · exact Or.inr ⟨hvr, hvb⟩
    · exact Or.inl ⟨hvD, hvr⟩
  have h1 : volume (cellSet Y n \ Metric.ball 0 r) ≤ ENNReal.ofReal (r ^ d * (Cin * q)) := by
    rw [ENNReal.ofReal_mul hrd.le]
    exact (gd_volume_sdiff_ball_le hr _).trans (mul_le_mul_right hvol _)
  have h2 := gd_volume_shell_le (d := d) (by omega) hr hb0 hbr
  have h3 : volume (cellSet Y n \ Metric.ball 0 b) ≤
      ENNReal.ofReal (r ^ d * (Cin * q) + unitBallVolume d * d * r ^ d * (Cin * q)) := by
    rw [ENNReal.ofReal_add (mul_nonneg hrd.le ht)
      (mul_nonneg (mul_nonneg (mul_nonneg hω.le hdpos.le) hrd.le) ht)]
    exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add h1 h2))
  have h4 := ENNReal.toReal_le_of_le_ofReal
    (add_nonneg (mul_nonneg hrd.le ht)
      (mul_nonneg (mul_nonneg (mul_nonneg hω.le hdpos.le) hrd.le) ht)) h3
  unfold MassOK
  calc (volume (cellSet Y n \ Metric.ball 0 b)).toReal
      ≤ r ^ d * (Cin * q) + unitBallVolume d * d * r ^ d * (Cin * q) := h4
    _ = Cin * (1 + d * unitBallVolume d) * r ^ d * q := by ring
/-! ### Newton's theorem for the radial convolution -/

section

open CERW.Generic.Kernel CERW.Generic.Newton

/-- A linear isometry of `ℝ^d` acts on the Euclidean unit sphere. -/
private noncomputable def nw_sphereMap
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
  ⟨A θ, by simp⟩

/-- The action of a linear isometry on the unit sphere is measurable. -/
private lemma nw_measurable_sphereMap
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Measurable (nw_sphereMap A) :=
  ((A.continuous.comp continuous_subtype_val).subtype_mk _).measurable

/-- Surface measure on the unit sphere is invariant under linear isometries. -/
private lemma nw_map_sphereMap_toSphere
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Measure.map (nw_sphereMap A) (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  ext S hS
  rw [Measure.map_apply (nw_measurable_sphereMap A) hS,
    Measure.toSphere_apply' _ ((nw_measurable_sphereMap A) hS), Measure.toSphere_apply' _ hS]
  congr 1
  have hset : Set.Ioo (0 : ℝ) 1 •
      ((↑) '' (nw_sphereMap A ⁻¹' S) : Set (EuclideanSpace ℝ (Fin d))) =
      A ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' S)) := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨t, ht, _, ⟨θ, hθ, rfl⟩, rfl⟩
      refine ⟨t, ht, _, ⟨nw_sphereMap A θ, hθ, rfl⟩, ?_⟩
      simp [nw_sphereMap]
    · rintro ⟨t, ht, _, ⟨θ, hθ, rfl⟩, h⟩
      refine ⟨t, ht, _, ⟨⟨A.symm θ, by simp⟩, ?_, rfl⟩, ?_⟩
      · simpa [nw_sphereMap] using hθ
      · have h' : t • (θ : EuclideanSpace ℝ (Fin d)) = A x := h
        show t • A.symm (θ : EuclideanSpace ℝ (Fin d)) = x
        rw [← A.symm.map_smul, h', A.symm_apply_apply]
  rw [hset]
  exact (LinearIsometryEquiv.measurePreserving A).measure_preimage_equiv
    (f := A.toMeasurableEquiv) _

/-- Integrals over the unit sphere are invariant under linear isometries. -/
private lemma nw_integral_sphereMap
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    {f : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ} (hf : Measurable f) :
    ∫ θ, f (nw_sphereMap A θ) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      ∫ θ, f θ ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  have h := integral_map (nw_measurable_sphereMap A).aemeasurable
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) (f := f)
    (by rw [nw_map_sphereMap_toSphere]; exact hf.aestronglyMeasurable)
  rw [nw_map_sphereMap_toSphere] at h
  exact h.symm

/-- The Newtonian field commutes with linear isometries. -/
private lemma nw_newtonField_map
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : newtonField (A x) = A (newtonField x) := by
  simp only [newtonField, A.norm_map, LinearIsometryEquiv.map_smul]

/-- The sphere integrand `θ ↦ ⟨ξ, K(v - sθ)⟩` is measurable. -/
private lemma nw_measurable_inner_newtonField (ξ v : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    Measurable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))) :=
  measurable_const.inner (measurable_newtonField.comp
    (measurable_const.sub (measurable_subtype_coe.const_smul s)))

/-- The component of the spherical average of the Newtonian field orthogonal to `v` vanishes:
a reflection fixing `v` and reversing `w ⟂ v` preserves surface measure. -/
private lemma nw_integral_sphere_inner_newtonField_perp {v w : EuclideanSpace ℝ (Fin d)}
    (hvw : inner ℝ w v = 0) (s : ℝ) :
    ∫ θ, inner ℝ w (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere = 0 := by
  set R := Submodule.reflection (ℝ ∙ w)ᗮ with hR
  have hRv : R v = v :=
    Submodule.reflection_mem_subspace_eq_self
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hvw)
  have hRw : R w = -w := Submodule.reflection_orthogonalComplement_singleton_eq_neg w
  have h := nw_integral_sphereMap R (nw_measurable_inner_newtonField w v s)
  have hpt : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ w (newtonField (v - s • (nw_sphereMap R θ : EuclideanSpace ℝ (Fin d)))) =
        -inner ℝ w (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) := by
    intro θ
    have h1 : v - s • (nw_sphereMap R θ : EuclideanSpace ℝ (Fin d)) =
        R (v - s • (θ : EuclideanSpace ℝ (Fin d))) := by
      rw [R.map_sub, R.map_smul, hRv]
      rfl
    rw [h1, nw_newtonField_map, ← R.inner_map_map w, hRw, hR, Submodule.reflection_reflection,
      inner_neg_left]
  simp_rw [hpt, integral_neg] at h
  linarith

/-- The Newtonian field is continuous away from the origin. -/
private lemma nw_continuousAt_newtonField_of_ne {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    ContinuousAt (newtonField : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) x :=
  ((continuous_norm.pow d).continuousAt.inv₀
    (pow_ne_zero d (norm_ne_zero_iff.mpr hx))).smul continuousAt_id

/-- For `|v| ≠ s` the sphere integrand `θ ↦ ⟨ξ, K(v - sθ)⟩` is integrable, being continuous on a
compact space. -/
private lemma nw_integrable_inner_newtonField (ξ : EuclideanSpace ℝ (Fin d))
    {v : EuclideanSpace ℝ (Fin d)} {s : ℝ} (hs : 0 < s) (hvs : ‖v‖ ≠ s) :
    Integrable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))))
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  haveI : CompactSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hcont : Continuous (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hθ : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
      simp
    have hne : v - s • (θ : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
      intro h
      have hv : v = s • (θ : EuclideanSpace ℝ (Fin d)) := sub_eq_zero.mp h
      apply hvs
      rw [hv, norm_smul, hθ, Real.norm_eq_abs, abs_of_pos hs, mul_one]
    have hc : ContinuousAt (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        v - s • (θ : EuclideanSpace ℝ (Fin d))) θ :=
      continuousAt_const.sub (continuousAt_subtype_val.const_smul s)
    exact ContinuousAt.comp_of_eq (g := newtonField)
      (f := fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        v - s • (θ : EuclideanSpace ℝ (Fin d))) (nw_continuousAt_newtonField_of_ne hne) hc rfl
  exact Continuous.integrable_of_hasCompactSupport (continuous_const.inner hcont)
    (HasCompactSupport.of_compactSpace _)

/-- The kernel average `eq:kernel-average` against an arbitrary vector `ξ`: for `v ≠ 0`, `s > 0`
and `|v| ≠ s`, `∫_S ξ · K(v - sθ) dσ(θ) = σ_d |v|^{-d} (ξ · v) 1{s < |v|}`. -/
private lemma nw_integral_sphere_inner_newtonField_vec (hd : 2 ≤ d)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) {s : ℝ} (hs : 0 < s) (hvs : ‖v‖ ≠ s)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    ∫ θ, inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      if s < ‖v‖ then d * unitBallVolume d * (inner ℝ ξ v / ‖v‖ ^ d) else 0 := by
  have hrpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hvv : inner ℝ v v = ‖v‖ * ‖v‖ := real_inner_self_eq_norm_mul_norm v
  set a : ℝ := inner ℝ ξ (unitDir v) with ha_def
  have ha : a = ‖v‖⁻¹ * inner ℝ ξ v := by
    rw [ha_def, unitDir, real_inner_smul_right]
  set w : EuclideanSpace ℝ (Fin d) := ξ - a • unitDir v with hw_def
  have hperp : inner ℝ w v = 0 := by
    rw [hw_def, inner_sub_left, real_inner_smul_left, unitDir, real_inner_smul_left, hvv, ha]
    field_simp
    ring
  have hdecomp : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) =
        a * inner ℝ (unitDir v) (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) +
          inner ℝ w (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) := by
    intro θ
    rw [hw_def, inner_sub_left, real_inner_smul_left]
    ring
  simp_rw [hdecomp]
  rw [integral_add ((nw_integrable_inner_newtonField (unitDir v) hs hvs).const_mul a)
    (nw_integrable_inner_newtonField w hs hvs), integral_const_mul,
    CERW.Support.Geometry.integral_sphere_inner_newtonField hd hv hs hvs,
    nw_integral_sphere_inner_newtonField_perp hperp, add_zero]
  split_ifs
  · rw [ha, ← CERW.Support.Geometry.div_pow_eq_rpow_sub hrpos d]
    field_simp
  · simp

/-- The weight `χ(|ζ|)` times the kernel `|a - ζ|^{1-d}` is integrable, with integral at most
`M d ω_d + ∫ χ(|ζ|) dζ`: inside the unit ball around `a` the weight is at most `M` and the kernel
has integral `d ω_d`, outside the kernel is at most one. -/
private lemma nw_integrable_weight_mul_kernel (hd : 1 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    (a : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))) ∧
      ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤
        M * (d * unitBallVolume d) + ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ := by
  obtain ⟨hint, hval⟩ := integrableOn_ball_and_integral_eq hd a one_pos
  have hind := hint.integrable_indicator (Metric.isOpen_ball.measurableSet)
  have hGi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      M * (Metric.ball a 1).indicator (fun v => ‖v - a‖ ^ (1 - (d : ℝ))) ζ + χ ‖ζ‖) :=
    (hind.const_mul M).add hχi
  have hmeas : Measurable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))) :=
    (hχm.comp measurable_norm).mul ((measurable_const.sub measurable_id).norm.pow_const _)
  have hle : ∀ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤
      M * (Metric.ball a 1).indicator (fun v => ‖v - a‖ ^ (1 - (d : ℝ))) ζ + χ ‖ζ‖ := by
    intro ζ
    have hk : 0 ≤ ‖a - ζ‖ ^ (1 - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have hsw : ‖a - ζ‖ = ‖ζ - a‖ := norm_sub_rev a ζ
    by_cases hζ : ζ ∈ Metric.ball a 1
    · rw [Set.indicator_of_mem hζ, ← hsw]
      have h1 : χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤ M * ‖a - ζ‖ ^ (1 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_right (hM _) hk
      linarith [hχ0 ‖ζ‖]
    · rw [Set.indicator_of_notMem hζ]
      have hge : 1 ≤ ‖a - ζ‖ := by
        rw [hsw]
        simpa [Metric.mem_ball, dist_eq_norm] using hζ
      have hk1 : ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hge (by
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd
          linarith)
      have h1 : χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤ χ ‖ζ‖ * 1 :=
        mul_le_mul_of_nonneg_left hk1 (hχ0 _)
      linarith
  have hfi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))) := by
    refine hGi.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hχ0 _) (Real.rpow_nonneg (norm_nonneg _) _))]
    exact hle ζ
  refine ⟨hfi, ?_⟩
  calc ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))
      ≤ ∫ ζ : EuclideanSpace ℝ (Fin d),
          (M * (Metric.ball a 1).indicator (fun v => ‖v - a‖ ^ (1 - (d : ℝ))) ζ + χ ‖ζ‖) :=
        integral_mono hfi hGi hle
    _ = M * (d * unitBallVolume d) + ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ := by
        rw [integral_add (hind.const_mul M) hχi, integral_const_mul,
          integral_indicator Metric.isOpen_ball.measurableSet, hval, mul_one]

/-- Pointwise bound of the radial weight times the field `⟨ξ, K(w - ζ)⟩` by `|ξ|` times the
weighted kernel `χ(|ζ|) |w - ζ|^{1-d}`. -/
private lemma nw_norm_weight_inner_le (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ0 : ∀ s, 0 ≤ χ s)
    (w ξ ζ : EuclideanSpace ℝ (Fin d)) :
    ‖χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ))‖ ≤
      ‖ξ‖ * (χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ0 _), Real.norm_eq_abs]
  have h1 : |inner ℝ ξ (newtonField (w - ζ))| ≤ ‖ξ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ)) := by
    rw [← norm_newtonField hd]
    exact abs_real_inner_le_norm _ _
  calc χ ‖ζ‖ * |inner ℝ ξ (newtonField (w - ζ))|
      ≤ χ ‖ζ‖ * (‖ξ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := mul_le_mul_of_nonneg_left h1 (hχ0 _)
    _ = ‖ξ‖ * (χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := by ring

/-- The radial weight times the field `⟨ξ, K(w - ζ)⟩` is integrable. -/
private lemma nw_integrable_weight_inner_newtonField (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    (w ξ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ))) := by
  have hk := (nw_integrable_weight_mul_kernel (by omega) hχm hχ0 hM hχi w).1
  have hmeas : Measurable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ))) :=
    (hχm.comp measurable_norm).mul
      (measurable_const.inner (measurable_newtonField.comp (measurable_const.sub measurable_id)))
  exact (hk.const_mul ‖ξ‖).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ζ => nw_norm_weight_inner_le hd hχ0 w ξ ζ)

/-- The mass of a radial weight in a centred ball, in polar coordinates:
`∫_{B(0,s)} χ(|ζ|) dζ = d ω_d ∫_0^s r^{d-1} χ(r) dr`. -/
private lemma nw_integral_ball_weight (hd : 1 ≤ d) (χ : ℝ → ℝ) (s : ℝ) :
    ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ =
      d * unitBallVolume d *
        ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * (Set.Iio s).indicator χ r := by
  haveI : NeZero d := ⟨by omega⟩
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hind : (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s).indicator (fun ζ => χ ‖ζ‖) =
      fun ζ => (Set.Iio s).indicator χ ‖ζ‖ := by
    funext ζ
    by_cases hζ : ‖ζ‖ < s <;> simp [Set.indicator, hζ]
  rw [← integral_indicator Metric.isOpen_ball.measurableSet, hind,
    integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d))), hfin]
  simp only [unitBallVolume, Measure.real, nsmul_eq_mul, smul_eq_mul]
  ring

/-- Newton's theorem for a radial weight: for `w ≠ 0` and any vector `ξ`,
`∫ χ(|ζ|) ⟨ξ, K(w - ζ)⟩ dζ = (∫_{B(0,|w|)} χ(|ζ|) dζ) ⟨ξ, w⟩ / |w|^d`. -/
private lemma nw_integral_weight_inner_newtonField (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {w : EuclideanSpace ℝ (Fin d)} (hw : w ≠ 0) (ξ : EuclideanSpace ℝ (Fin d)) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ)) =
      (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖w‖, χ ‖ζ‖) *
        (inner ℝ ξ w / ‖w‖ ^ d) := by
  have hint := nw_integrable_weight_inner_newtonField hd hχm hχ0 hM hχi w ξ
  rw [integral_eq_integral_Ioi_sphere (by omega) hint, nw_integral_ball_weight (by omega)]
  have hae : ∀ᵐ r : ℝ ∂(volume : Measure ℝ), r ≠ ‖w‖ := by
    rw [ae_iff]
    simp
  have hpt : ∀ᵐ r : ℝ ∂(volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)),
      r ^ (d - 1) * ∫ θ, χ ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ *
          inner ℝ ξ (newtonField (w - r • (θ : EuclideanSpace ℝ (Fin d))))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
        d * unitBallVolume d * (inner ℝ ξ w / ‖w‖ ^ d) *
          (r ^ (d - 1) * (Set.Iio ‖w‖).indicator χ r) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hae] with r hr hr0
    have hr0' : 0 < r := hr0
    have hθ : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ = r := fun θ => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0', mem_sphere_zero_iff_norm.mp θ.2, mul_one]
    simp_rw [hθ]
    rw [integral_const_mul, nw_integral_sphere_inner_newtonField_vec hd hw hr0' hr.symm ξ]
    by_cases hlt : r < ‖w‖
    · simp only [hlt, if_true, Set.indicator_of_mem (Set.mem_Iio.mpr hlt)]
      ring
    · simp only [hlt, if_false, Set.indicator_of_notMem (mt Set.mem_Iio.mp hlt)]
      ring
  rw [integral_congr_ae hpt, integral_const_mul]
  ring

/-- For each position `v`, the radial weight times the field `⟨g(v), K(v - y₀ - ζ)⟩` is integrable
in `ζ`, uniformly in `v`, and jointly integrable in `(v, ζ)` over `F × ℝ^d` for a set `F` of finite
volume. -/
private lemma nw_integrable_weight_fieldPair (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {F : Set (EuclideanSpace ℝ (Fin d))} (hFfin : volume F ≠ ⊤)
    (y₀ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      χ ‖p.2‖ * inner ℝ (g p.1) (newtonField (p.1 - y₀ - p.2)))
      (((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict F).prod volume) := by
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hmeas : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      χ ‖p.2‖ * inner ℝ (g p.1) (newtonField (p.1 - y₀ - p.2))) :=
    (hχm.comp measurable_snd.norm).mul ((hg.comp measurable_fst).inner
      (measurable_newtonField.comp ((measurable_fst.sub_const y₀).sub measurable_snd)))
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun v =>
    nw_integrable_weight_inner_newtonField hd hχm hχ0 hM hχi (v - y₀) (g v), ?_⟩
  refine Integrable.mono' (integrableOn_const hFfin (C := Λ * (M * (d * unitBallVolume d) +
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖)))
    hmeas.norm.aestronglyMeasurable.integral_prod_right' (Filter.Eventually.of_forall fun v => ?_)
  obtain ⟨hki, hkle⟩ := nw_integrable_weight_mul_kernel (by omega) hχm hχ0 hM hχi (v - y₀)
  have hfi := nw_integrable_weight_inner_newtonField hd hχm hχ0 hM hχi (v - y₀) (g v)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ζ => norm_nonneg _)]
  calc ∫ ζ : EuclideanSpace ℝ (Fin d), ‖χ ‖ζ‖ * inner ℝ (g v) (newtonField (v - y₀ - ζ))‖
      ≤ ∫ ζ : EuclideanSpace ℝ (Fin d), Λ * (χ ‖ζ‖ * ‖v - y₀ - ζ‖ ^ (1 - (d : ℝ))) := by
        refine integral_mono hfi.norm (hki.const_mul Λ) fun ζ => ?_
        exact (nw_norm_weight_inner_le hd hχ0 (v - y₀) (g v) ζ).trans
          (mul_le_mul_of_nonneg_right (hΛ v) (mul_nonneg (hχ0 _) (Real.rpow_nonneg
            (norm_nonneg _) _)))
    _ = Λ * ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖v - y₀ - ζ‖ ^ (1 - (d : ℝ)) :=
        integral_const_mul _ _
    _ ≤ Λ * (M * (d * unitBallVolume d) + ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) :=
        mul_le_mul_of_nonneg_left hkle hΛ0

/-- The mass of a radial weight in a centred ball lies between `0` and the total mass. -/
private lemma nw_ball_weight_bounds {χ : ℝ → ℝ} (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖)) (s : ℝ) :
    0 ≤ ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ ∧
      ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ ≤
        ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ :=
  ⟨integral_nonneg fun _ => hχ0 _,
    setIntegral_le_integral hχi (Filter.Eventually.of_forall fun _ => hχ0 _)⟩

/-- Fubini and Newton's theorem for the radial weight, without a sign condition: the weighted
field potential of `F` for the field `u_v` has integral at most the total weight times the integral
over `F` of the positive part of `u_v · (v - y₀) |v - y₀|^{-d}`. -/
private lemma nw_weighted_fieldPotential_le (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {F : Set (EuclideanSpace ℝ (Fin d))} (hF : MeasurableSet F)
    (hFfin : volume F ≠ ⊤) (y₀ : EuclideanSpace ℝ (Fin d)) :
    ∫ ζ : EuclideanSpace ℝ (Fin d),
        χ ‖ζ‖ * ∫ v in F, inner ℝ (unitDir v) (newtonField (v - y₀ - ζ)) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
        ∫ v in F, max (inner ℝ (unitDir v) (v - y₀) / ‖v - y₀‖ ^ d) 0 := by
  haveI : NeZero d := ⟨by omega⟩
  have hg : Measurable (unitDir : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
    measurable_norm.inv.smul measurable_id
  have hI := nw_integrable_weight_fieldPair hd hχm hχ0 hM hχi hg norm_unitDir_le hFfin y₀
  have hcm : ∀ ζ : EuclideanSpace ℝ (Fin d),
      χ ‖ζ‖ * ∫ v in F, inner ℝ (unitDir v) (newtonField (v - y₀ - ζ)) =
        ∫ v in F, χ ‖ζ‖ * inner ℝ (unitDir v) (newtonField (v - y₀ - ζ)) := fun ζ =>
    (integral_const_mul _ _).symm
  simp_rw [hcm]
  rw [← integral_integral_swap (f := fun (v ζ : EuclideanSpace ℝ (Fin d)) =>
    χ ‖ζ‖ * inner ℝ (unitDir v) (newtonField (v - y₀ - ζ))) hI]
  have hgi : Integrable (fun v : EuclideanSpace ℝ (Fin d) =>
      (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
        max (inner ℝ (unitDir v) (v - y₀) / ‖v - y₀‖ ^ d) 0)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict F) :=
    ((CERW.Support.Geometry.integrableOn_potentialIntegrand (by omega) hF hFfin
      y₀).pos_part).const_mul _
  rw [← integral_const_mul]
  refine integral_mono_ae hI.integral_prod_left hgi ?_
  have hne : ∀ᵐ v : EuclideanSpace ℝ (Fin d), v ≠ y₀ := by
    rw [ae_iff]
    simp
  rw [Filter.EventuallyLE, ae_restrict_iff' hF]
  filter_upwards [hne] with v hv _
  rw [nw_integral_weight_inner_newtonField hd hχm hχ0 hM hχi (sub_ne_zero.mpr hv) (unitDir v)]
  obtain ⟨hm0, hm1⟩ := nw_ball_weight_bounds hχ0 hχi ‖v - y₀‖
  exact (mul_le_mul_of_nonneg_left (le_max_left _ _) hm0).trans
    (mul_le_mul_of_nonneg_right hm1 (le_max_right _ _))

/-- `eq:newton-convolution` for a bounded integrable radial weight `χ ≥ 0`: the weighted potential
`∫ χ(|ζ|) U_D(y - ζ) dζ` is at most `(∫ χ(|ζ|) dζ) U_D^+(y)`. -/
private lemma nw_weighted_potential_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * potential d ε D (y - ζ) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) * positivePotential d ε D y := by
  have hle := nw_weighted_fieldPotential_le hd hχm hχ0 hM hχi hD hDfin y
  have hc : 0 ≤ 2 * ε / unitBallVolume d :=
    div_nonneg (mul_nonneg zero_le_two hε) (unitBallVolume_pos d).le
  set h : EuclideanSpace ℝ (Fin d) → ℝ := fun t =>
    χ ‖t‖ * ∫ v in D, inner ℝ (unitDir v) (newtonField (v - y - t)) with hh
  have hfun : (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * potential d ε D (y - ζ)) =
      fun ζ => (2 * ε / unitBallVolume d) * h (-ζ) := by
    funext ζ
    have hv : ∀ v : EuclideanSpace ℝ (Fin d), v - y - -ζ = v - (y - ζ) := fun v => by abel
    simp only [hh, potential, norm_neg, hv, inner_newtonField]
    ring
  rw [hfun, integral_const_mul, integral_neg_eq_self h volume]
  calc (2 * ε / unitBallVolume d) * ∫ t : EuclideanSpace ℝ (Fin d), h t
      ≤ (2 * ε / unitBallVolume d) * ((∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
          ∫ v in D, max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0) :=
        mul_le_mul_of_nonneg_left hle hc
    _ = (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) * positivePotential d ε D y := by
        rw [positivePotential]
        ring

/-- Newton's theorem for the radial convolution: `(χ * U_D)(y) ≤ ‖χ‖₁ U_D^+(y)`. -/
private theorem newton_conv (hd : 3 ≤ d) : NewtonConv d := by
  intro ε hε D hD hDb y
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hexp : 2 - 2 * (d : ℝ) ≤ 0 := by linarith
  have hχm : Measurable (fun s : ℝ => (1 + |s|) ^ (2 - 2 * (d : ℝ))) := by fun_prop
  have hχ0 : ∀ s : ℝ, 0 ≤ (1 + |s|) ^ (2 - 2 * (d : ℝ)) := fun s =>
    Real.rpow_nonneg (add_nonneg zero_le_one (abs_nonneg s)) _
  have hχ1 : ∀ s : ℝ, (1 + |s|) ^ (2 - 2 * (d : ℝ)) ≤ 1 := fun s =>
    Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (abs_nonneg s)) hexp
  have hr : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < 2 * d - 2 := by
    rw [finrank_euclideanSpace_fin]
    linarith
  have he : (2 : ℝ) - 2 * d = -(2 * d - 2) := by ring
  have hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      (1 + |‖ζ‖|) ^ (2 - 2 * (d : ℝ))) := by
    simp only [abs_norm, he]
    exact integrable_one_add_norm hr
  have h := nw_weighted_potential_le (by omega) hε hχm hχ0 hχ1 hχi hD hDb.measure_lt_top.ne y
  simpa only [abs_norm] using h

end
/-! ### The envelope of the local times, `d ≥ 3` -/

/-- Young's inequality for a square root: `A √(B L) ≤ λ B + A² L / (4 λ)`. -/
private lemma ev_mul_sqrt_le_add (B L A lam : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hlam : 0 < lam) :
    A * Real.sqrt (B * L) ≤ lam * B + A ^ 2 * L / (4 * lam) := by
  set u : ℝ := lam * B with hu
  set v : ℝ := A ^ 2 * L / (4 * lam) with hv
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hsq : (A * Real.sqrt (B * L) / 2) ^ 2 = u * v := by
    rw [hu, hv]
    rw [div_pow, mul_pow, Real.sq_sqrt (mul_nonneg hB hL)]
    field_simp
    ring
  have hroot : Real.sqrt (u * v) = A * Real.sqrt (B * L) / 2 := by
    rw [← hsq, Real.sqrt_sq]
    positivity
  have hamgm : 2 * Real.sqrt (u * v) ≤ u + v := by
    have h := two_mul_le_add_sq (Real.sqrt u) (Real.sqrt v)
    rw [Real.sq_sqrt hu0, Real.sq_sqrt hv0] at h
    rw [mul_assoc, ← Real.sqrt_mul hu0 v] at h
    linarith
  rw [hroot] at hamgm
  have : 2 * (A * Real.sqrt (B * L) / 2) = A * Real.sqrt (B * L) := by ring
  rw [this] at hamgm
  rw [hu, hv] at hamgm
  exact hamgm

/-- The lattice weight `k(w) = (1 + |w|)^{2-2d}`. -/
private noncomputable def ev_kern (d : ℕ) (w : Site d) : ℝ :=
  (1 + euclidNorm w) ^ (2 - 2 * (d : ℝ))

/-- The lattice weight is nonnegative. -/
private lemma ev_kern_nonneg (w : Site d) : 0 ≤ ev_kern d w :=
  Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg w]) _

/-- The lattice weight is symmetric: `k(x - y) = k(y - x)`. -/
private lemma ev_kern_sub_comm (x y : Site d) : ev_kern d (x - y) = ev_kern d (y - x) := by
  unfold ev_kern
  rw [← neg_sub y x, CERW.Generic.Lattice.euclidNorm_neg]

/-- Comparison of powers with a nonpositive exponent: if `1 + f ≤ c (1 + e)` then
`(1 + e)^q ≤ c^{-q} (1 + f)^q`. -/
private lemma ev_rpow_le_mul_rpow_of_le {e f c q : ℝ} (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < c)
    (hq : q ≤ 0) (h : 1 + f ≤ c * (1 + e)) :
    (1 + e) ^ q ≤ c ^ (-q) * (1 + f) ^ q := by
  have h1 : (c * (1 + e)) ^ q ≤ (1 + f) ^ q :=
    Real.rpow_le_rpow_of_nonpos (by linarith) h hq
  rw [Real.mul_rpow hc.le (by linarith)] at h1
  have h2 : c ^ (-q) * c ^ q = 1 := by
    rw [← Real.rpow_add hc, neg_add_cancel, Real.rpow_zero]
  calc (1 + e) ^ q = c ^ (-q) * (c ^ q * (1 + e) ^ q) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ c ^ (-q) * (1 + f) ^ q :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hc.le _)

/-- The triangle inequality for the lattice kernel: `|z - x| ≤ |z - y| + |y - x|`. -/
private lemma ev_euclidNorm_sub_le_add (z y x : Site d) :
    euclidNorm (z - x) ≤ euclidNorm (z - y) + euclidNorm (y - x) := by
  have h := CERW.Support.Occupation.euclidNorm_add_le (z - y) (y - x)
  rwa [sub_add_sub_cancel] at h

/-- If `e ≥ ρ / 2` then the weight at `e` is at most `2^{2d-2}` times the weight at `ρ`. -/
private lemma ev_rpow_le_two_rpow_mul {e ρ q : ℝ} (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hq : q ≤ 0)
    (h : ρ / 2 ≤ e) : (1 + e) ^ q ≤ (2 : ℝ) ^ (-q) * (1 + ρ) ^ q :=
  ev_rpow_le_mul_rpow_of_le he hρ (by norm_num) hq (by linarith)

/-- Each term of the lattice convolution of two weights is at most `2^{2d-2} k(z - x)` times
the sum of the two weights. -/
private lemma ev_kern_mul_le (hd : 1 ≤ d) (z y x : Site d) :
    ev_kern d (z - y) * ev_kern d (y - x) ≤
      (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) *
        (ev_kern d (z - y) + ev_kern d (y - x)) := by
  have hq : 2 - 2 * (d : ℝ) ≤ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hk1 := ev_kern_nonneg (z - y)
  have hk2 := ev_kern_nonneg (y - x)
  have hk3 := ev_kern_nonneg (z - x)
  have hc : 0 ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have htri := ev_euclidNorm_sub_le_add z y x
  have hn1 := LatticeProb.euclidNorm_nonneg (z - y)
  have hn2 := LatticeProb.euclidNorm_nonneg (y - x)
  have hn3 := LatticeProb.euclidNorm_nonneg (z - x)
  by_cases hcase : euclidNorm (z - x) / 2 ≤ euclidNorm (y - x)
  · have hb : ev_kern d (y - x) ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) :=
      ev_rpow_le_two_rpow_mul hn2 hn3 hq hcase
    calc ev_kern d (z - y) * ev_kern d (y - x)
        ≤ ev_kern d (z - y) * ((2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x)) :=
          mul_le_mul_of_nonneg_left hb hk1
      _ = (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) * ev_kern d (z - y) := by ring
      _ ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) *
            (ev_kern d (z - y) + ev_kern d (y - x)) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc hk3)
  · have hcase' : euclidNorm (z - x) / 2 ≤ euclidNorm (z - y) := by
      rw [not_le] at hcase
      linarith
    have ha : ev_kern d (z - y) ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) :=
      ev_rpow_le_two_rpow_mul hn1 hn3 hq hcase'
    calc ev_kern d (z - y) * ev_kern d (y - x)
        ≤ ((2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x)) * ev_kern d (y - x) :=
          mul_le_mul_of_nonneg_right ha hk2
      _ ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) *
            (ev_kern d (z - y) + ev_kern d (y - x)) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc hk3)

/-- The lattice convolution of the weight with itself, over any finite set, is bounded by a
constant multiple of the weight. -/
private lemma ev_sum_kern_mul_kern_le (hd : 1 ≤ d) {K₀ : ℝ}
    (hK₀ : ∀ (F : Finset (Site d)) (u : Site d), ∑ y ∈ F, ev_kern d (y - u) ≤ K₀)
    (F : Finset (Site d)) (z x : Site d) :
    ∑ y ∈ F, ev_kern d (z - y) * ev_kern d (y - x) ≤
      (2 * (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * K₀) * ev_kern d (z - x) := by
  have hk3 := ev_kern_nonneg (z - x)
  have hc : 0 ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hsum1 : ∑ y ∈ F, ev_kern d (z - y) ≤ K₀ := by
    have := hK₀ F z
    simpa only [ev_kern_sub_comm z] using this
  have hsum2 := hK₀ F x
  calc ∑ y ∈ F, ev_kern d (z - y) * ev_kern d (y - x)
      ≤ ∑ y ∈ F, (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) *
          (ev_kern d (z - y) + ev_kern d (y - x)) :=
        Finset.sum_le_sum fun y _ => ev_kern_mul_le hd z y x
    _ = (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) *
          (∑ y ∈ F, ev_kern d (z - y) + ∑ y ∈ F, ev_kern d (y - x)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - x) * (K₀ + K₀) :=
        mul_le_mul_of_nonneg_left (add_le_add hsum1 hsum2) (mul_nonneg hc hk3)
    _ = (2 * (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * K₀) * ev_kern d (z - x) := by ring

/-- The lattice absorption estimate: if the local time satisfies the pointwise bound on `S`
with a square root of the kernel sum, and `a` is comparable to the kernel at `z`, then the
`a`-weighted local time sum is bounded by twice the `a`-weighted potential sum, up to a
multiple of `L`. -/
private lemma ev_absorb_sum {ℓ U a : Site d → ℝ} {S : Finset (Site d)} {z : Site d}
    {c₀ c₁ K₀ A₀ C₁ L γ : ℝ}
    (hK₀ : ∀ (F : Finset (Site d)) (u : Site d), ∑ y ∈ F, ev_kern d (y - u) ≤ K₀)
    (hconv : ∀ (F : Finset (Site d)) (x : Site d),
      ∑ y ∈ F, ev_kern d (z - y) * ev_kern d (y - x) ≤ A₀ * ev_kern d (z - x))
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hA₀ : 0 ≤ A₀)
    (ha : ∀ y, c₀ * ev_kern d (z - y) ≤ a y ∧ a y ≤ c₁ * ev_kern d (z - y))
    (hℓ0 : ∀ y, 0 ≤ ℓ y) (hC₁ : 0 ≤ C₁) (hL : 0 ≤ L) (hγ : 0 < γ)
    (hγ' : γ * (c₁ * A₀) ≤ c₀ / 2)
    (hfine : ∀ y ∈ S,
      ℓ y ≤ U y + C₁ * (Real.sqrt ((∑ x ∈ S, ℓ x * ev_kern d (x - y)) * L) + L)) :
    ∑ y ∈ S, a y * ℓ y ≤
      2 * ∑ y ∈ S, a y * U y + 2 * ((C₁ + C₁ ^ 2 / (4 * γ)) * L) * (c₁ * K₀) := by
  have ha0 : ∀ y, 0 ≤ a y := fun y => (mul_nonneg hc₀.le (ev_kern_nonneg _)).trans (ha y).1
  set W : Site d → ℝ := fun y => ∑ x ∈ S, ℓ x * ev_kern d (x - y) with hW
  have hW0 : ∀ y, 0 ≤ W y := fun y =>
    Finset.sum_nonneg fun x _ => mul_nonneg (hℓ0 x) (ev_kern_nonneg _)
  set Cg : ℝ := C₁ + C₁ ^ 2 / (4 * γ) with hCg
  have hCg0 : 0 ≤ Cg := by rw [hCg]; positivity
  have h1 : ∀ y ∈ S, ℓ y ≤ U y + Cg * L + γ * W y := by
    intro y hy
    have h := hfine y hy
    have hyoung := ev_mul_sqrt_le_add (W y) L C₁ γ (hW0 y) hL hC₁ hγ
    calc ℓ y ≤ U y + C₁ * (Real.sqrt (W y * L) + L) := h
      _ = U y + (C₁ * Real.sqrt (W y * L) + C₁ * L) := by ring
      _ ≤ U y + (γ * W y + C₁ ^ 2 * L / (4 * γ) + C₁ * L) := by linarith
      _ = U y + Cg * L + γ * W y := by rw [hCg]; ring
  have h2 : ∑ y ∈ S, a y * ℓ y ≤
      ∑ y ∈ S, (a y * U y + (Cg * L) * a y + γ * (a y * W y)) := by
    refine Finset.sum_le_sum fun y hy => ?_
    calc a y * ℓ y ≤ a y * (U y + Cg * L + γ * W y) :=
          mul_le_mul_of_nonneg_left (h1 y hy) (ha0 y)
      _ = a y * U y + (Cg * L) * a y + γ * (a y * W y) := by ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h2
  have hsumA : ∑ y ∈ S, a y ≤ c₁ * K₀ := by
    calc ∑ y ∈ S, a y ≤ ∑ y ∈ S, c₁ * ev_kern d (y - z) :=
          Finset.sum_le_sum fun y _ => by rw [← ev_kern_sub_comm z y]; exact (ha y).2
      _ = c₁ * ∑ y ∈ S, ev_kern d (y - z) := by rw [Finset.mul_sum]
      _ ≤ c₁ * K₀ := mul_le_mul_of_nonneg_left (hK₀ S z) hc₁.le
  have hswap : ∑ y ∈ S, a y * W y = ∑ x ∈ S, ℓ x * ∑ y ∈ S, a y * ev_kern d (x - y) := by
    simp only [hW, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have hinner : ∀ x, ∑ y ∈ S, a y * ev_kern d (x - y) ≤ c₁ * A₀ * ev_kern d (z - x) := by
    intro x
    calc ∑ y ∈ S, a y * ev_kern d (x - y)
        ≤ ∑ y ∈ S, c₁ * (ev_kern d (z - y) * ev_kern d (y - x)) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [ev_kern_sub_comm x y]
          calc a y * ev_kern d (y - x) ≤ (c₁ * ev_kern d (z - y)) * ev_kern d (y - x) :=
                mul_le_mul_of_nonneg_right (ha y).2 (ev_kern_nonneg _)
            _ = c₁ * (ev_kern d (z - y) * ev_kern d (y - x)) := by ring
      _ = c₁ * ∑ y ∈ S, ev_kern d (z - y) * ev_kern d (y - x) := by rw [Finset.mul_sum]
      _ ≤ c₁ * (A₀ * ev_kern d (z - x)) := mul_le_mul_of_nonneg_left (hconv S x) hc₁.le
      _ = c₁ * A₀ * ev_kern d (z - x) := by ring
  have hAW : c₀ * ∑ y ∈ S, a y * W y ≤ c₁ * A₀ * ∑ x ∈ S, a x * ℓ x := by
    rw [hswap, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have hnn : 0 ≤ c₁ * A₀ * ℓ x := mul_nonneg (mul_nonneg hc₁.le hA₀) (hℓ0 x)
    calc c₀ * (ℓ x * ∑ y ∈ S, a y * ev_kern d (x - y))
        ≤ c₀ * (ℓ x * (c₁ * A₀ * ev_kern d (z - x))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hinner x) (hℓ0 x)) hc₀.le
      _ = c₁ * A₀ * ℓ x * (c₀ * ev_kern d (z - x)) := by ring
      _ ≤ c₁ * A₀ * ℓ x * a x := mul_le_mul_of_nonneg_left (ha x).1 hnn
      _ = c₁ * A₀ * (a x * ℓ x) := by ring
  have hΛ0 : 0 ≤ ∑ x ∈ S, a x * ℓ x :=
    Finset.sum_nonneg fun x _ => mul_nonneg (ha0 x) (hℓ0 x)
  have hγAW : γ * ∑ y ∈ S, a y * W y ≤ (∑ x ∈ S, a x * ℓ x) / 2 := by
    have h3 : γ * (c₁ * A₀) * ∑ x ∈ S, a x * ℓ x ≤ c₀ / 2 * ∑ x ∈ S, a x * ℓ x :=
      mul_le_mul_of_nonneg_right hγ' hΛ0
    have h4 : c₀ * (γ * ∑ y ∈ S, a y * W y) ≤ c₀ * ((∑ x ∈ S, a x * ℓ x) / 2) := by
      calc c₀ * (γ * ∑ y ∈ S, a y * W y) = γ * (c₀ * ∑ y ∈ S, a y * W y) := by ring
        _ ≤ γ * (c₁ * A₀ * ∑ x ∈ S, a x * ℓ x) := mul_le_mul_of_nonneg_left hAW hγ.le
        _ = γ * (c₁ * A₀) * ∑ x ∈ S, a x * ℓ x := by ring
        _ ≤ c₀ / 2 * ∑ x ∈ S, a x * ℓ x := h3
        _ = c₀ * ((∑ x ∈ S, a x * ℓ x) / 2) := by ring
    exact le_of_mul_le_mul_left h4 hc₀
  have hCL : Cg * L * ∑ y ∈ S, a y ≤ Cg * L * (c₁ * K₀) :=
    mul_le_mul_of_nonneg_left hsumA (mul_nonneg hCg0 hL)
  linarith

/-- The radial weight `χ(s) = (1 + |s|)^{2-2d}`. -/
private noncomputable def ev_chi (d : ℕ) (s : ℝ) : ℝ := (1 + |s|) ^ (2 - 2 * (d : ℝ))

/-- The radial weight is nonnegative. -/
private lemma ev_chi_nonneg (s : ℝ) : 0 ≤ ev_chi d s :=
  Real.rpow_nonneg (by linarith [abs_nonneg s]) _

/-- The radial weight is measurable. -/
private lemma ev_measurable_chi : Measurable (ev_chi d) := by
  unfold ev_chi
  fun_prop

/-- The weight of a norm is `(1 + ‖ζ‖)^{2-2d}`. -/
private lemma ev_chi_norm (ζ : EuclideanSpace ℝ (Fin d)) :
    ev_chi d ‖ζ‖ = (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) := by
  rw [ev_chi, abs_norm]

/-- For `d ≥ 3` the radial weight is integrable on `ℝ^d`. -/
private lemma ev_integrable_chi_norm (hd : 3 ≤ d) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => ev_chi d ‖ζ‖) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h := integrable_one_add_norm (E := EuclideanSpace ℝ (Fin d)) (μ := volume)
    (r := 2 * (d : ℝ) - 2) (by rw [finrank_euclideanSpace_fin]; linarith)
  refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
  show (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) = ev_chi d ‖ζ‖
  rw [ev_chi_norm, show -(2 * (d : ℝ) - 2) = 2 - 2 * (d : ℝ) by ring]

/-- The cell weight `a(y) = ∫_{C_y} χ(|y₀ - ζ|) dζ`. -/
private noncomputable def ev_cellWeight (d : ℕ) (y₀ : EuclideanSpace ℝ (Fin d)) (y : Site d) :
    ℝ :=
  ∫ ζ in cell y, ev_chi d ‖y₀ - ζ‖

/-- Two-sided bounds for the integral over a unit cell of a function bounded on the cell. -/
private lemma ev_setIntegral_cell_mem_Icc {G : EuclideanSpace ℝ (Fin d) → ℝ} (y : Site d)
    (hG : IntegrableOn G (cell y)) {lo hi : ℝ}
    (h : ∀ ζ ∈ cell y, lo ≤ G ζ ∧ G ζ ≤ hi) :
    lo ≤ ∫ ζ in cell y, G ζ ∧ ∫ ζ in cell y, G ζ ≤ hi := by
  have hvol : volume (cell y) ≠ ⊤ := by
    rw [CERW.Support.Occupation.volume_cell]
    exact ENNReal.one_ne_top
  have hmeas := CERW.Support.Occupation.measurableSet_cell (d := d) y
  have hreal : volume.real (cell y) = 1 := by
    rw [Measure.real, CERW.Support.Occupation.volume_cell]
    simp
  have hc : ∀ c : ℝ, IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) => c) (cell y) :=
    fun c => integrableOn_const hvol
  constructor
  · have := setIntegral_mono_on (hc lo) hG hmeas fun ζ hζ => (h ζ hζ).1
    rwa [setIntegral_const, hreal, one_smul] at this
  · have := setIntegral_mono_on hG (hc hi) hmeas fun ζ hζ => (h ζ hζ).2
    rwa [setIntegral_const, hreal, one_smul] at this

/-- For a point `ζ` of the cell of `y`, and a site `z` whose cell is near `y₀`, the distance
`|y₀ - ζ|` differs from `|z - y|` by at most `√d`. -/
private lemma ev_abs_norm_sub_sub_euclidNorm_le {y₀ ζ : EuclideanSpace ℝ (Fin d)}
    {y z : Site d} (hζ : ζ ∈ cell y) (hz : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2) :
    |‖y₀ - ζ‖ - euclidNorm (z - y)| ≤ Real.sqrt d := by
  have h1 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hζ
  have hw : euclidNorm (z - y) = ‖toSpace z - toSpace y‖ := by
    rw [← norm_toSpace, CERW.Support.Occupation.toSpace_sub]
  set w : EuclideanSpace ℝ (Fin d) := toSpace z - toSpace y with hwdef
  set r : EuclideanSpace ℝ (Fin d) := (y₀ - toSpace z) + (toSpace y - ζ) with hr
  have hsplit : y₀ - ζ = w + r := by rw [hwdef, hr]; abel
  have hrn : ‖r‖ ≤ Real.sqrt d := by
    calc ‖r‖ ≤ ‖y₀ - toSpace z‖ + ‖toSpace y - ζ‖ := norm_add_le _ _
      _ ≤ Real.sqrt d / 2 + Real.sqrt d / 2 := by
          rw [norm_sub_rev y₀, norm_sub_rev (toSpace y)]
          exact add_le_add hz h1
      _ = Real.sqrt d := by ring
  have h3 := abs_norm_sub_norm_le (w + r) w
  rw [add_sub_cancel_left] at h3
  rw [hw, hsplit]
  exact h3.trans hrn

/-- The comparison of the cell weight with the lattice kernel, pointwise on the cell. -/
private lemma ev_chi_cell_bounds (hd : 1 ≤ d) {y₀ ζ : EuclideanSpace ℝ (Fin d)} {y z : Site d}
    (hζ : ζ ∈ cell y) (hz : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2) :
    ((1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))))⁻¹ * ev_kern d (z - y) ≤ ev_chi d ‖y₀ - ζ‖ ∧
      ev_chi d ‖y₀ - ζ‖ ≤ (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - y) := by
  have hq : 2 - 2 * (d : ℝ) ≤ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have habs := ev_abs_norm_sub_sub_euclidNorm_le (y₀ := y₀) hζ hz
  have hr0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hs0 : 0 ≤ ‖y₀ - ζ‖ := norm_nonneg _
  have ht0 := LatticeProb.euclidNorm_nonneg (z - y)
  have hc : 0 < 1 + Real.sqrt d := by linarith
  have hcpos : 0 < (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) := Real.rpow_pos_of_pos hc _
  obtain ⟨habs1, habs2⟩ := abs_le.mp habs
  have hup := ev_rpow_le_mul_rpow_of_le hs0 ht0 hc hq
    (show 1 + euclidNorm (z - y) ≤ (1 + Real.sqrt d) * (1 + ‖y₀ - ζ‖) by
      linarith [mul_nonneg hr0 hs0])
  have hlow := ev_rpow_le_mul_rpow_of_le ht0 hs0 hc hq
    (show 1 + ‖y₀ - ζ‖ ≤ (1 + Real.sqrt d) * (1 + euclidNorm (z - y)) by
      linarith [mul_nonneg hr0 ht0])
  rw [ev_chi_norm]
  constructor
  · rw [inv_mul_le_iff₀ hcpos]
    exact hlow
  · exact hup

/-- Two-sided bounds for the cell weight by the lattice kernel. -/
private lemma ev_cellWeight_bounds (hd : 3 ≤ d) {y₀ : EuclideanSpace ℝ (Fin d)} {z : Site d}
    (hz : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2) (y : Site d) :
    ((1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))))⁻¹ * ev_kern d (z - y) ≤ ev_cellWeight d y₀ y ∧
      ev_cellWeight d y₀ y ≤ (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) * ev_kern d (z - y) := by
  have hint : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => ev_chi d ‖y₀ - ζ‖) :=
    (ev_integrable_chi_norm hd).comp_sub_left y₀
  exact ev_setIntegral_cell_mem_Icc y hint.integrableOn fun ζ hζ =>
    ev_chi_cell_bounds (by omega) hζ hz

/-- Summing over the cells of a finite set of sites: if `Uf` varies by at most `M` across each
cell and is at least `-Cf` off the union of the cells, then the cell-weighted sum of the values
of `Uf` at the sites is at most the integral of `G Uf` plus `(M + Cf) ∫ G`. -/
private lemma ev_sum_setIntegral_mul_le {G Uf : EuclideanSpace ℝ (Fin d) → ℝ}
    {S : Finset (Site d)} {M Cf : ℝ} (hG0 : ∀ ζ, 0 ≤ G ζ) (hG : Integrable G)
    (hGU : Integrable (fun ζ => G ζ * Uf ζ)) (hM : 0 ≤ M) (hCf : 0 ≤ Cf)
    (hmod : ∀ y ∈ S, ∀ ζ ∈ cell y, Uf (toSpace y) ≤ Uf ζ + M)
    (hfar : ∀ ζ ∉ ⋃ y ∈ S, cell y, -Cf ≤ Uf ζ) :
    ∑ y ∈ S, (∫ ζ in cell y, G ζ) * Uf (toSpace y) ≤
      (∫ ζ, G ζ * Uf ζ) + (M + Cf) * ∫ ζ, G ζ := by
  set F : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => G ζ * (Uf ζ + M + Cf) with hF
  have hFeq : F = fun ζ => G ζ * Uf ζ + (M + Cf) * G ζ := by
    funext ζ
    rw [hF]
    ring
  have hFint : Integrable F := by
    rw [hFeq]
    exact hGU.add (hG.const_mul _)
  have hVmeas : MeasurableSet (⋃ y ∈ S, cell y) :=
    Finset.measurableSet_biUnion S fun y _ => CERW.Support.Occupation.measurableSet_cell y
  have hterm : ∀ y ∈ S, (∫ ζ in cell y, G ζ) * Uf (toSpace y) ≤ ∫ ζ in cell y, F ζ := by
    intro y hy
    rw [← integral_mul_const]
    refine setIntegral_mono_on (hG.integrableOn.mul_const _) hFint.integrableOn
      (CERW.Support.Occupation.measurableSet_cell y) fun ζ hζ => ?_
    have h1 := mul_le_mul_of_nonneg_left (hmod y hy ζ hζ) (hG0 ζ)
    have h2 : G ζ * (Uf ζ + M) ≤ G ζ * (Uf ζ + M + Cf) :=
      mul_le_mul_of_nonneg_left (by linarith) (hG0 ζ)
    exact h1.trans h2
  have hsum : ∑ y ∈ S, ∫ ζ in cell y, F ζ = ∫ ζ in ⋃ y ∈ S, cell y, F ζ := by
    rw [integral_biUnion_finset S (fun y _ => CERW.Support.Occupation.measurableSet_cell y)
      (fun x _ y _ hxy => cell_disjoint hxy) (fun y _ => hFint.integrableOn)]
  have hcompl : 0 ≤ ∫ ζ in (⋃ y ∈ S, cell y)ᶜ, F ζ := by
    refine setIntegral_nonneg hVmeas.compl fun ζ hζ => ?_
    have := hfar ζ hζ
    exact mul_nonneg (hG0 ζ) (by linarith)
  have htot := integral_add_compl hVmeas hFint
  have hFval : ∫ ζ, F ζ = (∫ ζ, G ζ * Uf ζ) + (M + Cf) * ∫ ζ, G ζ := by
    rw [hFeq, integral_add hGU (hG.const_mul _), integral_const_mul]
  calc ∑ y ∈ S, (∫ ζ in cell y, G ζ) * Uf (toSpace y)
      ≤ ∑ y ∈ S, ∫ ζ in cell y, F ζ := Finset.sum_le_sum hterm
    _ = ∫ ζ in ⋃ y ∈ S, cell y, F ζ := hsum
    _ ≤ ∫ ζ, F ζ := by linarith
    _ = (∫ ζ, G ζ * Uf ζ) + (M + Cf) * ∫ ζ, G ζ := hFval

/-- The potential of a finite-volume set `D` at a point at distance at least `R ≥ 1` from every
point of `D` is at most `(2ε/ω_d) |D| / R` in absolute value. -/
private lemma ev_abs_potential_le_of_far (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hDfin : volume D ≠ ⊤) {R : ℝ} (hR : 1 ≤ R)
    {ζ : EuclideanSpace ℝ (Fin d)} (hfar : ∀ v ∈ D, R ≤ ‖v - ζ‖) :
    |potential d ε D ζ| ≤ 2 * ε / unitBallVolume d * ((volume D).toReal / R) := by
  have hω := unitBallVolume_pos d
  have hbd : ∀ v ∈ D, ‖inner ℝ (unitDir v) (v - ζ) / ‖v - ζ‖ ^ d‖ ≤ 1 / R := by
    intro v hv
    have hw := hfar v hv
    have hw1 : 1 ≤ ‖v - ζ‖ := hR.trans hw
    have hwpos : 0 < ‖v - ζ‖ := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hwpos d)]
    have h1 : |inner ℝ (unitDir v) (v - ζ)| ≤ ‖v - ζ‖ :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) (norm_unitDir_le v))
    have h2 : ‖v - ζ‖ ^ 2 ≤ ‖v - ζ‖ ^ d := pow_le_pow_right₀ hw1 hd
    rw [div_le_div_iff₀ (pow_pos hwpos d) (by linarith)]
    calc |inner ℝ (unitDir v) (v - ζ)| * R ≤ ‖v - ζ‖ * ‖v - ζ‖ :=
          mul_le_mul h1 hw (by linarith) hwpos.le
      _ = ‖v - ζ‖ ^ 2 := by ring
      _ ≤ ‖v - ζ‖ ^ d := h2
      _ = 1 * ‖v - ζ‖ ^ d := (one_mul _).symm
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume) hDfin.lt_top hbd
  have hreal : volume.real D = (volume D).toReal := rfl
  rw [hreal] at hint
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  unfold potential
  rw [abs_mul, abs_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [← Real.norm_eq_abs]
  calc ‖∫ v in D, inner ℝ (unitDir v) (v - ζ) / ‖v - ζ‖ ^ d‖
      ≤ 1 / R * (volume D).toReal := hint
    _ = (volume D).toReal / R := by ring

/-- Near the origin the integrand of the radial estimate is at most `(1 + |ζ|)^{-d}`. -/
private lemma ev_chi_mul_min_le_near (hd : 3 ≤ d) (b : ℝ) (ζ : EuclideanSpace ℝ (Fin d)) :
    ev_chi d ‖ζ‖ * min b ‖ζ‖ ≤ (1 + ‖ζ‖) ^ (-(d : ℝ)) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hx : 1 ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
  have hx0 : 0 < 1 + ‖ζ‖ := by linarith
  calc ev_chi d ‖ζ‖ * min b ‖ζ‖ ≤ ev_chi d ‖ζ‖ * ‖ζ‖ :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (ev_chi_nonneg _)
    _ = (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) * ‖ζ‖ := by rw [ev_chi_norm]
    _ ≤ (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) * (1 + ‖ζ‖) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hx0.le _)
    _ = (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ) + 1) := (Real.rpow_add_one hx0.ne' _).symm
    _ ≤ (1 + ‖ζ‖) ^ (-(d : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)

/-- Far from the origin the integrand of the radial estimate is at most `b |ζ|^{2-2d}`. -/
private lemma ev_chi_mul_min_le_far (hd : 1 ≤ d) {b : ℝ} (hb : 0 ≤ b)
    {ζ : EuclideanSpace ℝ (Fin d)} (hζ : 0 < ‖ζ‖) :
    ev_chi d ‖ζ‖ * min b ‖ζ‖ ≤ b * ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) ≤ ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) :=
    Real.rpow_le_rpow_of_nonpos hζ (by linarith) (by linarith)
  rw [ev_chi_norm, show 2 - 2 * (d : ℝ) = -(2 * (d : ℝ) - 2) by ring]
  calc (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) * min b ‖ζ‖
      ≤ (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) * b :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.rpow_nonneg (by linarith [hζ]) _)
    _ ≤ ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) * b := mul_le_mul_of_nonneg_right h1 hb
    _ = b * ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) := by ring

/-- The radial estimate `∫ χ(|ζ|) min(b, |ζ|) dζ ≤ σ_d (log(1 + T) + 1)` with `T = max 1 b` and
`σ_d = d ω_d`. -/
private lemma ev_integral_chi_mul_min_le (hd : 3 ≤ d) {b : ℝ} (hb : 0 ≤ b) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖ ≤
      d * unitBallVolume d * (Real.log (1 + max 1 b) + 1) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set T : ℝ := max 1 b with hT
  have hT1 : 1 ≤ T := le_max_left _ _
  have hTb : b ≤ T := le_max_right _ _
  have hTpos : 0 < T := by linarith
  have hω := unitBallVolume_pos d
  set f : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => ev_chi d ‖ζ‖ * min b ‖ζ‖ with hf
  have hfm : Measurable f :=
    (ev_measurable_chi.comp measurable_norm).mul (measurable_const.min measurable_norm)
  have hf0 : ∀ ζ, 0 ≤ f ζ := fun ζ => mul_nonneg (ev_chi_nonneg _) (le_min hb (norm_nonneg ζ))
  obtain ⟨hI1, hJ1⟩ :=
    CERW.Generic.Kernel.integrableOn_ball_one_add_norm_rpow_and_integral_le (d := d)
      (by omega) hTpos
  obtain ⟨hI2, hJ2⟩ :=
    CERW.Generic.Kernel.integrableOn_compl_ball_rpow_neg_and_integral_eq (d := d)
      (s := 2 * (d : ℝ) - 2) (ρ := T) (by omega) (by linarith) hTpos
  have hfb : IntegrableOn f (Metric.ball 0 T) :=
    hI1.mono' hfm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_ball fun ζ _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ζ)]
        exact ev_chi_mul_min_le_near hd b ζ)
  have hfc : IntegrableOn f (Metric.ball 0 T)ᶜ :=
    (hI2.const_mul b).mono' hfm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_ball.compl fun ζ hζ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ζ)]
        have hζT : T ≤ ‖ζ‖ := by
          rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hζ
          exact hζ
        exact ev_chi_mul_min_le_far (by omega) hb (by linarith))
  have hfint : Integrable f := by
    have := hfb.union hfc
    rwa [Set.union_compl_self, integrableOn_univ] at this
  have hA : ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T, f ζ ≤
      d * unitBallVolume d * Real.log (1 + T) :=
    (setIntegral_mono_on hfb hI1 measurableSet_ball fun ζ _ =>
      ev_chi_mul_min_le_near hd b ζ).trans hJ1
  have hexp : (d : ℝ) - (2 * (d : ℝ) - 2) ≤ -1 := by linarith
  have hbT : b * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) ≤ 1 := by
    have h1 : T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) ≤ T ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hT1 hexp
    rw [Real.rpow_neg_one] at h1
    calc b * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) ≤ T * T⁻¹ :=
          mul_le_mul hTb h1 (Real.rpow_nonneg hTpos.le _) hTpos.le
      _ = 1 := mul_inv_cancel₀ hTpos.ne'
  have hB : ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ, f ζ ≤
      d * unitBallVolume d := by
    have hdiv : (1 : ℝ) ≤ 2 * (d : ℝ) - 2 - d := by linarith
    calc ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ, f ζ
        ≤ ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ,
            b * ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) :=
          setIntegral_mono_on hfc (hI2.const_mul b) measurableSet_ball.compl fun ζ hζ => by
            have hζT : T ≤ ‖ζ‖ := by
              rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hζ
              exact hζ
            exact ev_chi_mul_min_le_far (by omega) hb (by linarith)
      _ = b * (d * unitBallVolume d * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) /
            (2 * (d : ℝ) - 2 - d)) := by rw [integral_const_mul, hJ2]
      _ = d * unitBallVolume d * (b * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2))) /
            (2 * (d : ℝ) - 2 - d) := by ring
      _ ≤ d * unitBallVolume d * 1 / (2 * (d : ℝ) - 2 - d) := by
          gcongr
      _ ≤ d * unitBallVolume d := by
          rw [mul_one, div_le_iff₀ (by linarith)]
          have : 0 ≤ (d : ℝ) * unitBallVolume d := by positivity
          calc (d : ℝ) * unitBallVolume d = d * unitBallVolume d * 1 := (mul_one _).symm
            _ ≤ d * unitBallVolume d * (2 * (d : ℝ) - 2 - d) :=
                mul_le_mul_of_nonneg_left hdiv this
  rw [← integral_add_compl measurableSet_ball hfint]
  calc (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T, f ζ) +
        ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ, f ζ
      ≤ d * unitBallVolume d * Real.log (1 + T) + d * unitBallVolume d := add_le_add hA hB
    _ = d * unitBallVolume d * (Real.log (1 + T) + 1) := by ring

/-- The bracket sum equals the local-time weighted kernel sum over any finite set of sites
containing the departure range. -/
private lemma ev_braSum_eq (X : ℕ → Site d) (n : ℕ) {S : Finset (Site d)}
    (hS : departureRange X n ⊆ S) (y : Site d) :
    braSum X n y = ∑ x ∈ S, (localTime X n x : ℝ) * ev_kern d (x - y) := by
  show ∑ j ∈ Finset.range n, ev_kern d (X j - y) = _
  rw [CERW.Support.LocalTime.sum_range_eq_sum_localTime X n (fun w => ev_kern d (w - y))]
  refine Finset.sum_subset hS fun x _ hx => ?_
  rw [mem_departureRange_iff, not_lt, Nat.le_zero] at hx
  rw [hx, Nat.cast_zero, zero_mul]

/-- A path with `|X_j| ≤ j` has `H_n ≤ n`. -/
private lemma ev_maxRadius_le_nat (X : ℕ → Site d) (n : ℕ) (hXn : ∀ j, euclidNorm (X j) ≤ j) :
    maxRadius X n ≤ n := by
  unfold maxRadius
  refine Finset.sup'_le _ _ fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact (hXn j).trans (by exact_mod_cast hjn)

/-- The lattice departure range lies in the lattice ball of radius `2n`. -/
private lemma ev_departureRange_subset_ballFinset_two_mul {X : ℕ → Site d} {n : ℕ}
    (hXn : ∀ j, euclidNorm (X j) ≤ j) :
    departureRange X n ⊆ LatticeProb.ballFinset d (2 * n) := by
  intro x hx
  have h1 := CERW.Support.Occupation.departureRange_subset_ballFinset X n hx
  rw [LatticeProb.mem_ballFinset_iff] at h1 ⊢
  have h2 := ev_maxRadius_le_nat X n hXn
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The lattice step: there are constants `c₀, α₁` depending only on `d` and `C₁` such that the
bracket at a site `z` whose cell is near `y₀` satisfies
`c₀ W_z ≤ 2 Σ_{y} a(y) U(y) + α₁ L`. -/
private lemma ev_kernel_sum_le (hd : 3 ≤ d) {C₁ : ℝ} (hC₁ : 0 ≤ C₁) :
    ∃ c₀ α₁ : ℝ, 0 < c₀ ∧ 0 ≤ α₁ ∧ ∀ (X : ℕ → Site d) (n : ℕ) (U : Site d → ℝ),
      (∀ j, euclidNorm (X j) ≤ j) →
      (∀ y : Site d, euclidNorm y ≤ 3 * n →
        |(localTime X n y : ℝ) - U y| ≤
          C₁ * (Real.sqrt (braSum X n y * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2))) →
      ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (z : Site d), ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2 →
        c₀ * braSum X n z ≤
          2 * ∑ y ∈ LatticeProb.ballFinset d (2 * n), ev_cellWeight d y₀ y * U y +
            α₁ * Real.log ((n : ℝ) + 2) := by
  obtain ⟨K₀, hK₀pos, hK⟩ := CERW.Generic.Lattice.sum_finset_rpow_two_sub_two_mul_le hd
  have hK₀ : ∀ (F : Finset (Site d)) (u : Site d), ∑ y ∈ F, ev_kern d (y - u) ≤ K₀ :=
    fun F u => hK F u
  have hd1 : 1 ≤ d := by omega
  set A₀ : ℝ := 2 * (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * K₀ with hA₀
  have hA₀pos : 0 < A₀ := by
    rw [hA₀]
    exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)) hK₀pos
  have hsq : 0 < 1 + Real.sqrt d := by linarith [Real.sqrt_nonneg (d : ℝ)]
  set c₁ : ℝ := (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) with hc₁
  have hc₁pos : 0 < c₁ := Real.rpow_pos_of_pos hsq _
  set c₀ : ℝ := c₁⁻¹ with hc₀
  have hc₀pos : 0 < c₀ := inv_pos.mpr hc₁pos
  set γ : ℝ := c₀ / (2 * (c₁ * A₀)) with hγ
  have hγpos : 0 < γ := by rw [hγ]; positivity
  have hγ' : γ * (c₁ * A₀) ≤ c₀ / 2 := by
    rw [hγ]
    have : 0 < c₁ * A₀ := mul_pos hc₁pos hA₀pos
    field_simp
    exact le_refl _
  refine ⟨c₀, 2 * (C₁ + C₁ ^ 2 / (4 * γ)) * (c₁ * K₀), hc₀pos, by positivity, ?_⟩
  intro X n U hXn hfine y₀ z hz
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  set S : Finset (Site d) := LatticeProb.ballFinset d (2 * n) with hS
  have hAS : departureRange X n ⊆ S := ev_departureRange_subset_ballFinset_two_mul hXn
  have hℓ0 : ∀ y : Site d, 0 ≤ (localTime X n y : ℝ) := fun y => Nat.cast_nonneg _
  have hw := fun y => ev_cellWeight_bounds hd hz y
  have hfine' : ∀ y ∈ S, (localTime X n y : ℝ) ≤ U y +
      C₁ * (Real.sqrt ((∑ x ∈ S, (localTime X n x : ℝ) * ev_kern d (x - y)) * L) + L) := by
    intro y hy
    rw [hS, LatticeProb.mem_ballFinset_iff] at hy
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h := hfine y (by linarith)
    rw [ev_braSum_eq X n hAS y] at h
    have := (abs_le.mp h).2
    linarith
  have habs := ev_absorb_sum (S := S) (z := z) (c₀ := c₀) (c₁ := c₁) (K₀ := K₀) (A₀ := A₀)
    (C₁ := C₁) (L := L) (γ := γ) (ℓ := fun y => (localTime X n y : ℝ)) (U := U)
    (a := ev_cellWeight d y₀) hK₀ (fun F x => ev_sum_kern_mul_kern_le hd1 hK₀ F z x) hc₀pos
    hc₁pos hA₀pos.le (fun y => by
      have := hw y
      rw [hc₀]
      exact this) hℓ0 hC₁ hL0 hγpos hγ' hfine'
  have hlow : c₀ * braSum X n z ≤
      ∑ y ∈ S, ev_cellWeight d y₀ y * (localTime X n y : ℝ) := by
    rw [ev_braSum_eq X n hAS z, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    calc c₀ * ((localTime X n x : ℝ) * ev_kern d (x - z))
        = (localTime X n x : ℝ) * (c₀ * ev_kern d (z - x)) := by
          rw [ev_kern_sub_comm x z]; ring
      _ ≤ (localTime X n x : ℝ) * ev_cellWeight d y₀ x :=
          mul_le_mul_of_nonneg_left (hw x).1 (hℓ0 x)
      _ = ev_cellWeight d y₀ x * (localTime X n x : ℝ) := by ring
  calc c₀ * braSum X n z
      ≤ ∑ y ∈ S, ev_cellWeight d y₀ y * (localTime X n y : ℝ) := hlow
    _ ≤ 2 * ∑ y ∈ S, ev_cellWeight d y₀ y * U y +
          2 * ((C₁ + C₁ ^ 2 / (4 * γ)) * L) * (c₁ * K₀) := habs
    _ = 2 * ∑ y ∈ S, ev_cellWeight d y₀ y * U y +
          2 * (C₁ + C₁ ^ 2 / (4 * γ)) * (c₁ * K₀) * L := by ring

/-- The logarithm of `1 + max 1 b` is at most a constant multiple of `log (n + 2)` when
`b ≤ 2 Λ n`. -/
private lemma ev_log_one_add_max_le {Λ b : ℝ} {n : ℕ} (hn : 2 ≤ n) (hb : b ≤ Λ * (2 * n)) :
    Real.log (1 + max 1 b) ≤
      (1 + Real.log (1 + max 1 (2 * Λ))) * Real.log ((n : ℝ) + 2) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set Λ' : ℝ := max 1 (2 * Λ) with hΛ'
  have hΛ'1 : 1 ≤ Λ' := le_max_left _ _
  have hΛ'2 : 2 * Λ ≤ Λ' := le_max_right _ _
  have hn2 : 1 ≤ (n : ℝ) + 2 := by linarith
  have hT : max 1 b ≤ Λ' * ((n : ℝ) + 2) := by
    refine max_le ?_ ?_
    · exact one_le_mul_of_one_le_of_one_le hΛ'1 hn2
    · calc b ≤ Λ * (2 * n) := hb
        _ = (2 * Λ) * n := by ring
        _ ≤ Λ' * n := mul_le_mul_of_nonneg_right hΛ'2 hn0
        _ ≤ Λ' * ((n : ℝ) + 2) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h1 : 1 + max 1 b ≤ (1 + Λ') * ((n : ℝ) + 2) := by
    calc 1 + max 1 b ≤ 1 + Λ' * ((n : ℝ) + 2) := by linarith
      _ ≤ (1 + Λ') * ((n : ℝ) + 2) := by linarith
  have hpos1 : 0 < 1 + max 1 b := by linarith [le_max_left (1 : ℝ) b]
  have hpos2 : 0 < 1 + Λ' := by linarith
  have hpos3 : 0 < (n : ℝ) + 2 := by linarith
  have hL : 1 ≤ Real.log ((n : ℝ) + 2) := CERW.Support.Law.one_le_log_add_two hn
  have hlog0 : 0 ≤ Real.log (1 + Λ') := Real.log_nonneg (by linarith)
  calc Real.log (1 + max 1 b) ≤ Real.log ((1 + Λ') * ((n : ℝ) + 2)) :=
        Real.log_le_log hpos1 h1
    _ = Real.log (1 + Λ') + Real.log ((n : ℝ) + 2) := Real.log_mul hpos2.ne' hpos3.ne'
    _ ≤ (1 + Real.log (1 + Λ')) * Real.log ((n : ℝ) + 2) := by
        linarith [mul_nonneg hlog0 (sub_nonneg.mpr hL)]

/-- The far-field bound: at a point of the complement of the cells of the ball of radius `2n`,
the potential of `D_n` is at least `-4ε/ω_d`. -/
private lemma ev_neg_le_potential_of_not_mem (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {X : ℕ → Site d} {n : ℕ} (hn : 2 ≤ n) (hn4 : 4 * Real.sqrt d ≤ n)
    (hXn : ∀ j, euclidNorm (X j) ≤ j) {ζ : EuclideanSpace ℝ (Fin d)}
    (hζ : ζ ∉ ⋃ y ∈ LatticeProb.ballFinset d (2 * n), cell y) :
    -(2 * ε / unitBallVolume d * 2) ≤ potential d ε (cellSet X n) ζ := by
  have hω := unitBallVolume_pos d
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmax : maxRadius X n ≤ n := ev_maxRadius_le_nat X n hXn
  have hc : cellCenter ζ ∉ LatticeProb.ballFinset d (2 * n) := fun hcS =>
    hζ (Set.mem_iUnion₂.mpr ⟨cellCenter ζ, hcS, mem_cell_cellCenter ζ⟩)
  rw [LatticeProb.mem_ballFinset_iff, not_le] at hc
  have h1 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter ζ)
  have hζn : 2 * (n : ℝ) - Real.sqrt d / 2 < ‖ζ‖ := by
    have h2 : ‖toSpace (cellCenter ζ)‖ ≤ ‖ζ‖ + ‖ζ - toSpace (cellCenter ζ)‖ := by
      calc ‖toSpace (cellCenter ζ)‖ = ‖ζ - (ζ - toSpace (cellCenter ζ))‖ := by
            rw [sub_sub_cancel]
        _ ≤ ‖ζ‖ + ‖ζ - toSpace (cellCenter ζ)‖ := norm_sub_le _ _
    rw [norm_toSpace] at h2
    linarith
  have hfar : ∀ v ∈ cellSet X n, (n : ℝ) / 2 ≤ ‖v - ζ‖ := by
    intro v hv
    have hvn := CERW.Support.Occupation.norm_le_of_mem_cellSet X n hv
    have h3 : ‖ζ‖ - ‖v‖ ≤ ‖ζ - v‖ := norm_sub_norm_le ζ v
    rw [norm_sub_rev] at h3
    linarith [Real.sqrt_nonneg (d : ℝ)]
  have hDfin : volume (cellSet X n) ≠ ⊤ := by
    rw [CERW.Support.Occupation.volume_cellSet]
    exact ENNReal.natCast_ne_top _
  have hvol : (volume (cellSet X n)).toReal ≤ n := by
    rw [CERW.Support.Occupation.volume_cellSet, ENNReal.toReal_natCast]
    exact_mod_cast CERW.Support.Occupation.card_departureRange_le X n
  have hpot := ev_abs_potential_le_of_far hd hε hDfin (R := (n : ℝ) / 2) (by linarith) hfar
  have hratio : (volume (cellSet X n)).toReal / ((n : ℝ) / 2) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hc0 : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hbound := hpot.trans (mul_le_mul_of_nonneg_left hratio hc0)
  exact (neg_le_neg_iff.mpr hbound).trans (neg_abs_le _)

/-- The potential of a measurable set of finite volume is continuous. -/
private lemma ev_continuous_potential (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) :
    Continuous (potential d ε E) := by
  obtain ⟨C, hC0, hC⟩ := CERW.Support.Geometry.exists_potential_holder hd
  exact CERW.Support.Geometry.continuous_of_holder_half (by positivity)
    fun y z => hC ε hε E hE hEfin y z

/-- For `d ≥ 3` and a measurable set `E` of finite volume, `ζ ↦ χ(|ζ|) U_E(y - ζ)` is
integrable. -/
private lemma ev_integrable_chi_mul_potential (hd : 3 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => ev_chi d ‖ζ‖ * potential d ε E (y - ζ)) := by
  have hcont := ev_continuous_potential (by omega) hε hE hEfin
  have hbd := fun ζ : EuclideanSpace ℝ (Fin d) =>
    CERW.Support.Geometry.abs_potential_le (by omega) hε hE hEfin (y - ζ)
  exact (ev_integrable_chi_norm hd).mul_bdd
    (hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ζ => (Real.norm_eq_abs _).trans_le (hbd ζ))

/-- The potential is at most its positive part `U_E^+`. -/
private lemma ev_potential_le_positivePotential (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) : potential d ε E y ≤ positivePotential d ε E y := by
  have hint := CERW.Support.Geometry.integrableOn_potentialIntegrand hd hE hEfin y
  have hω := unitBallVolume_pos d
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  unfold potential positivePotential
  exact mul_le_mul_of_nonneg_left
    (integral_mono hint hint.pos_part fun v => le_max_left _ _) hc

/-- The positive part `U_E^+` of the potential is nonnegative. -/
private lemma ev_positivePotential_nonneg {ε : ℝ} (hε : 0 ≤ ε)
    (E : Set (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d)) :
    0 ≤ positivePotential d ε E y := by
  have hω := unitBallVolume_pos d
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  exact mul_nonneg hc (integral_nonneg fun v => le_max_right _ _)

/-- The decomposition `U_D = 2dε (b - |·|)_+ + U_{D ∖ B(0,b)}`, including the degenerate radius
`b = 0`. -/
private lemma ev_potential_split (hd : 2 ≤ d) (ε : ℝ) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDb : Bornology.IsBounded D) {b : ℝ} (hb : 0 ≤ b)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ D) (y : EuclideanSpace ℝ (Fin d)) :
    potential d ε D y =
      2 * d * ε * max (b - ‖y‖) 0 + potential d ε (D \ Metric.ball 0 b) y := by
  rcases hb.lt_or_eq with hb | hb
  · exact potential_split hd ε hD hDb hb hball y
  · subst hb
    rw [Metric.ball_zero, Set.sdiff_empty,
      max_eq_right (by linarith [norm_nonneg y] : (0 : ℝ) - ‖y‖ ≤ 0), mul_zero, zero_add]

/-- `eq:potential-convolution` beyond the inner ball: for `|y| ≥ b` and `B(0,b) ⊆ D`,
`∫ χ(|ζ|) U_D(y - ζ) dζ ≤ 2dε ∫ χ(|ζ|) min(b, |ζ|) dζ + ‖χ‖₁ U_E^+(y)` with `E = D ∖ B(0,b)`. -/
private lemma ev_integral_chi_mul_potential_le (hd : 3 ≤ d) (hN : NewtonConv d) {ε : ℝ}
    (hε : 0 < ε) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) {b : ℝ} (hb : 0 ≤ b)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ D) {y : EuclideanSpace ℝ (Fin d)}
    (hy : b ≤ ‖y‖) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * potential d ε D (y - ζ) ≤
      2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖) +
        (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖) *
          positivePotential d ε (D \ Metric.ball 0 b) y := by
  have hE : MeasurableSet (D \ Metric.ball 0 b) := hD.diff measurableSet_ball
  have hEb : Bornology.IsBounded (D \ Metric.ball 0 b) := hDb.subset Set.sdiff_subset
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hEfin : volume (D \ Metric.ball 0 b) ≠ ⊤ := hEb.measure_lt_top.ne
  have hχ := ev_integrable_chi_norm hd
  have hint0 := ev_integrable_chi_mul_potential hd hε.le hD hDfin y
  have hint2 := ev_integrable_chi_mul_potential hd hε.le hE hEfin y
  have hint1 : Integrable
      (fun ζ : EuclideanSpace ℝ (Fin d) => ev_chi d ‖ζ‖ * min b ‖ζ‖) := by
    refine hχ.mul_bdd (c := b) (continuous_const.min continuous_norm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hb (norm_nonneg ζ))]
    exact min_le_left _ _
  have hP : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  have hpt : ∀ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * potential d ε D (y - ζ) ≤
      2 * d * ε * (ev_chi d ‖ζ‖ * min b ‖ζ‖) +
        ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ) := by
    intro ζ
    have hcone : max (b - ‖y - ζ‖) 0 ≤ min b ‖ζ‖ := by
      refine max_le (le_min (by linarith [norm_nonneg (y - ζ)]) ?_) (le_min hb (norm_nonneg ζ))
      have h1 : ‖y‖ ≤ ‖y - ζ‖ + ‖ζ‖ := by
        calc ‖y‖ = ‖(y - ζ) + ζ‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - ζ‖ + ‖ζ‖ := norm_add_le _ _
      linarith
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcone hP)
      (ev_chi_nonneg (d := d) ‖ζ‖)
    rw [ev_potential_split (by omega) ε hD hDb hb hball (y - ζ)]
    calc ev_chi d ‖ζ‖ * (2 * d * ε * max (b - ‖y - ζ‖) 0 +
          potential d ε (D \ Metric.ball 0 b) (y - ζ))
        = ev_chi d ‖ζ‖ * (2 * d * ε * max (b - ‖y - ζ‖) 0) +
            ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ) := by ring
      _ ≤ ev_chi d ‖ζ‖ * (2 * d * ε * min b ‖ζ‖) +
            ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ) := by linarith
      _ = 2 * d * ε * (ev_chi d ‖ζ‖ * min b ‖ζ‖) +
            ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ) := by ring
  have hNE := hN hε.le hE hEb y
  simp only [← ev_chi_norm] at hNE
  calc ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * potential d ε D (y - ζ)
      ≤ ∫ ζ : EuclideanSpace ℝ (Fin d), (2 * d * ε * (ev_chi d ‖ζ‖ * min b ‖ζ‖) +
          ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ)) :=
        integral_mono hint0 ((hint1.const_mul _).add hint2) hpt
    _ = 2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖) +
          ∫ ζ : EuclideanSpace ℝ (Fin d),
            ev_chi d ‖ζ‖ * potential d ε (D \ Metric.ball 0 b) (y - ζ) := by
        rw [integral_add (hint1.const_mul _) hint2, integral_const_mul]
    _ ≤ 2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖) +
          (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖) *
            positivePotential d ε (D \ Metric.ball 0 b) y := by linarith

/-- The potential step: the `a`-weighted sum of the potential over the lattice ball of radius
`2n` is at most `β L + m U_E^+(y₀)`, where `m = ∫ χ(|ζ|) dζ`, `E = D_n ∖ B(0,b)`, `|y₀| ≥ b`,
and `β` depends only on `d, ε, C₃`. -/
private lemma ev_sum_cellWeight_mul_potential_le (hd : 3 ≤ d) (hN : NewtonConv d) {ε : ℝ}
    (hε : 0 < ε) {C₃ : ℝ} (hC₃ : 0 ≤ C₃) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ (X : ℕ → Site d) (n : ℕ), 2 ≤ n → 4 * Real.sqrt d ≤ n →
      (∀ j, euclidNorm (X j) ≤ j) →
      (∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * ((n : ℝ) + Real.sqrt d) →
        ‖y - z‖ ≤ Real.sqrt d →
        |potential d ε (cellSet X n) y - potential d ε (cellSet X n) z| ≤
          C₃ * Real.log ((n : ℝ) + 2)) →
      ∀ (b : ℝ) (y₀ : EuclideanSpace ℝ (Fin d)), 0 ≤ b →
        Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ cellSet X n →
        b ≤ ‖y₀‖ → ‖y₀‖ ≤ 2 * n →
        ∑ y ∈ LatticeProb.ballFinset d (2 * n),
            ev_cellWeight d y₀ y * potential d ε (cellSet X n) (toSpace y) ≤
          β * Real.log ((n : ℝ) + 2) +
            (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖) *
              positivePotential d ε (cellSet X n \ Metric.ball 0 b) y₀ := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hω := unitBallVolume_pos d
  set m : ℝ := ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun ζ => ev_chi_nonneg _
  set Cf : ℝ := 2 * ε / unitBallVolume d * 2 with hCf
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  set CT : ℝ := 1 + Real.log (1 + max 1 (2 * 1)) with hCT
  have hCT0 : 0 ≤ CT := by
    rw [hCT]
    have : 0 ≤ Real.log (1 + max 1 (2 * 1 : ℝ)) :=
      Real.log_nonneg (by linarith [le_max_left (1 : ℝ) (2 * 1)])
    linarith
  refine ⟨2 * d * ε * (d * unitBallVolume d * (CT + 1)) + (C₃ + Cf) * m, by positivity, ?_⟩
  intro X n hn hn4 hXn hmod b y₀ hb hball hby hyn
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hL1 : 1 ≤ L := CERW.Support.Law.one_le_log_add_two hn
  have hsd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hDmeas : MeasurableSet (cellSet X n) := CERW.Support.Occupation.measurableSet_cellSet X n
  have hDbdd : Bornology.IsBounded (cellSet X n) :=
    (Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin d)))
      (r := maxRadius X n + Real.sqrt d)).subset
      (CERW.Support.Occupation.cellSet_subset_ball hd1 X n)
  have hDfin : volume (cellSet X n) ≠ ⊤ := hDbdd.measure_lt_top.ne
  set G : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => ev_chi d ‖y₀ - ζ‖ with hG
  set Uf : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => potential d ε (cellSet X n) ζ with hUf
  have hG0 : ∀ ζ, 0 ≤ G ζ := fun ζ => ev_chi_nonneg _
  have hGint : Integrable G := (ev_integrable_chi_norm hd).comp_sub_left y₀
  have hGU : Integrable (fun ζ => G ζ * Uf ζ) := by
    have := (ev_integrable_chi_mul_potential hd hε.le hDmeas hDfin y₀).comp_sub_left y₀
    simpa only [sub_sub_cancel] using this
  have hGUint : ∫ ζ, G ζ * Uf ζ =
      ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * potential d ε (cellSet X n) (y₀ - ζ) := by
    have := integral_sub_left_eq_self
      (fun ζ : EuclideanSpace ℝ (Fin d) =>
        ev_chi d ‖ζ‖ * potential d ε (cellSet X n) (y₀ - ζ)) volume y₀
    simpa only [sub_sub_cancel] using this
  have hGm : ∫ ζ, G ζ = m :=
    integral_sub_left_eq_self (fun ζ : EuclideanSpace ℝ (Fin d) => ev_chi d ‖ζ‖) volume y₀
  have hmod' : ∀ y ∈ LatticeProb.ballFinset d (2 * n), ∀ ζ ∈ cell y,
      Uf (toSpace y) ≤ Uf ζ + C₃ * L := by
    intro y hy ζ hζ
    rw [LatticeProb.mem_ballFinset_iff] at hy
    have h1 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hζ
    have h2 := hmod (toSpace y) ζ (by rw [norm_toSpace]; linarith) (by
      rw [norm_sub_rev]; linarith)
    have := (abs_le.mp h2).2
    simp only [hUf]
    linarith
  have hfar : ∀ ζ ∉ ⋃ y ∈ LatticeProb.ballFinset d (2 * n), cell y, -Cf ≤ Uf ζ := fun ζ hζ =>
    ev_neg_le_potential_of_not_mem hd2 hε.le hn hn4 hXn hζ
  have hsum := ev_sum_setIntegral_mul_le (S := LatticeProb.ballFinset d (2 * n)) (M := C₃ * L)
    (Cf := Cf) hG0 hGint hGU (mul_nonneg hC₃ (by linarith)) hCf0 hmod' hfar
  have hb2 : b ≤ 1 * (2 * n) := by linarith
  have hlog := ev_log_one_add_max_le hn hb2
  have hIB := ev_integral_chi_mul_min_le hd hb
  have hIB' : ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖ ≤
      d * unitBallVolume d * ((CT + 1) * L) := by
    refine hIB.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    linarith
  have hconv := ev_integral_chi_mul_potential_le hd hN hε hDmeas hDbdd hb hball hby
  have hP : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  have hstep : 2 * (d : ℝ) * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖) ≤
      2 * d * ε * (d * unitBallVolume d * (CT + 1)) * L := by
    calc 2 * (d : ℝ) * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖)
        ≤ 2 * d * ε * (d * unitBallVolume d * ((CT + 1) * L)) :=
          mul_le_mul_of_nonneg_left hIB' hP
      _ = 2 * d * ε * (d * unitBallVolume d * (CT + 1)) * L := by ring
  have hCfm : Cf * m ≤ Cf * m * L := by
    have := mul_nonneg (mul_nonneg hCf0 hm0) (sub_nonneg.mpr hL1)
    linarith
  calc ∑ y ∈ LatticeProb.ballFinset d (2 * n),
          ev_cellWeight d y₀ y * potential d ε (cellSet X n) (toSpace y)
      ≤ (∫ ζ, G ζ * Uf ζ) + (C₃ * L + Cf) * ∫ ζ, G ζ := hsum
    _ ≤ (2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖) +
          m * positivePotential d ε (cellSet X n \ Metric.ball 0 b) y₀) +
          (C₃ * L + Cf) * m := by
        rw [hGm, hGUint]
        linarith
    _ ≤ (2 * d * ε * (d * unitBallVolume d * (CT + 1)) + (C₃ + Cf) * m) * L +
          m * positivePotential d ε (cellSet X n \ Metric.ball 0 b) y₀ := by linarith

/-- `eq:convolution-bound`, `eq:potential-convolution` and `eq:envelopehigh` (`d ≥ 3`): beyond the
inner ball the bracket `W_x` and the local time at the site `x` of a point `y` are bounded by
`log n` plus the positive potential of `E = D_n ∖ B(0,b)` at `y`. -/
private theorem envelope_high (hd : 3 ≤ d) (hN : NewtonConv d) {ε : ℝ} (hε : 0 < ε) (c₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      (∀ j, euclidNorm (Y j) ≤ j) →
      (∀ x : Site d, euclidNorm x ≤ 3 * n →
        |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
          c₁ * (Real.sqrt (braSum Y n x * Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2))) →
      ∀ b : ℝ, 0 ≤ b → Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ cellSet Y n →
      ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ 2 * n →
        braSum Y n (cellCenter y) ≤ C * (Real.log ((n : ℝ) + 2) +
          positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y) ∧
        (localTime Y n (cellCenter y) : ℝ) ≤ C * (Real.log ((n : ℝ) + 2) +
          positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  set C₁ : ℝ := max c₁ 0 with hC₁def
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  obtain ⟨CM, hCM0, hCM⟩ := CERW.Support.Geometry.exists_potential_cell_modulus hd2
  set C₃ : ℝ := 2 * CM * ε with hC₃def
  have hC₃ : 0 ≤ C₃ := by positivity
  obtain ⟨c₀, α₁, hc₀, hα₁, hlat⟩ := ev_kernel_sum_le hd hC₁
  obtain ⟨β, hβ, hpot⟩ := ev_sum_cellWeight_mul_potential_le hd hN hε hC₃
  set m : ℝ := ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun ζ => ev_chi_nonneg _
  set K : ℝ := (2 * β + α₁ + 2 * m) / c₀ with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨1 + C₃ + C₁ * K + 2 * C₁ + K, by positivity, max 2 ⌈4 * Real.sqrt d⌉₊, ?_⟩
  intro Y n hn hYn hfine b hb hball y hby hyn
  have hn2 : 2 ≤ n := le_of_max_le_left hn
  have hn4 : 4 * Real.sqrt d ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hn)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hsd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hL1 : 1 ≤ L := CERW.Support.Law.one_le_log_add_two hn2
  have hmax : maxRadius Y n ≤ n := ev_maxRadius_le_nat Y n hYn
  have hDmeas : MeasurableSet (cellSet Y n) := CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDsub : cellSet Y n ⊆ Metric.ball 0 ((n : ℝ) + Real.sqrt d) :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n).trans
      (Metric.ball_subset_ball (by linarith))
  have hDbdd : Bornology.IsBounded (cellSet Y n) := Metric.isBounded_ball.subset hDsub
  have hEmeas : MeasurableSet (cellSet Y n \ Metric.ball 0 b) := hDmeas.diff measurableSet_ball
  have hEfin : volume (cellSet Y n \ Metric.ball 0 b) ≠ ⊤ :=
    (hDbdd.subset Set.sdiff_subset).measure_lt_top.ne
  have hfine₁ : ∀ x : Site d, euclidNorm x ≤ 3 * n →
      |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
        C₁ * (Real.sqrt (braSum Y n x * L) + L) := by
    intro x hx
    exact (hfine x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (add_nonneg (Real.sqrt_nonneg _) (by linarith)))
  have hmod : ∀ u v : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ 2 * ((n : ℝ) + Real.sqrt d) →
      ‖u - v‖ ≤ Real.sqrt d →
      |potential d ε (cellSet Y n) u - potential d ε (cellSet Y n) v| ≤ C₃ * L := by
    intro u v hu huv
    have h := hCM ε hε.le ((n : ℝ) + Real.sqrt d) (by linarith) (cellSet Y n) hDmeas hDsub
      u v hu huv
    have hsq : (n : ℝ) + Real.sqrt d + 2 ≤ ((n : ℝ) + 2) ^ 2 := by
      have e : ((n : ℝ) + 2) ^ 2 = (n : ℝ) * n + 3 * n + 2 + ((n : ℝ) + 2) := by ring
      have := mul_nonneg hn0 hn0
      linarith
    have hlog : Real.log ((n : ℝ) + Real.sqrt d + 2) ≤ 2 * L := by
      have h3 : Real.log (((n : ℝ) + 2) ^ 2) = 2 * L := by
        rw [Real.log_pow, hL]
        norm_num
      rw [← h3]
      exact Real.log_le_log (by linarith) hsq
    calc |potential d ε (cellSet Y n) u - potential d ε (cellSet Y n) v|
        ≤ CM * ε * Real.log ((n : ℝ) + Real.sqrt d + 2) := h
      _ ≤ CM * ε * (2 * L) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = C₃ * L := by rw [hC₃def]; ring
  have hzy : ‖toSpace (cellCenter y) - y‖ ≤ Real.sqrt d / 2 := by
    rw [norm_sub_rev]
    exact CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter y)
  set P : ℝ := positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y with hPdef
  have hP0 : 0 ≤ P := ev_positivePotential_nonneg hε.le _ _
  set W : ℝ := braSum Y n (cellCenter y) with hWdef
  have hb1 : c₀ * W ≤ 2 * ∑ x ∈ LatticeProb.ballFinset d (2 * n),
      ev_cellWeight d y x * potential d ε (cellSet Y n) (toSpace x) + α₁ * L :=
    hlat Y n (fun x => potential d ε (cellSet Y n) (toSpace x)) hYn hfine₁ y (cellCenter y) hzy
  have hb2 : ∑ x ∈ LatticeProb.ballFinset d (2 * n),
      ev_cellWeight d y x * potential d ε (cellSet Y n) (toSpace x) ≤ β * L + m * P :=
    hpot Y n hn2 hn4 hYn hmod b y hb hball hby hyn
  have hW0 : 0 ≤ W := by
    rw [hWdef]
    unfold braSum
    exact Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg (Y j - cellCenter y)]) _
  have hW : W ≤ K * (L + P) := by
    refine le_of_mul_le_mul_left ?_ hc₀
    have h1 : c₀ * W ≤ (2 * β + α₁) * L + 2 * m * P := by
      linarith
    have h2 : c₀ * (K * (L + P)) = (2 * β + α₁ + 2 * m) * (L + P) := by
      rw [hK]
      field_simp
    rw [h2]
    have h3 : 0 ≤ (2 * β + α₁) * P := mul_nonneg (by linarith) hP0
    have h4 : 0 ≤ 2 * m * L := mul_nonneg (by linarith) (by linarith)
    linarith
  have hLP : 0 ≤ L + P := by linarith
  have hKC : K ≤ 1 + C₃ + C₁ * K + 2 * C₁ + K := by
    have := mul_nonneg hC₁ hK0
    linarith
  refine ⟨hW.trans (mul_le_mul_of_nonneg_right hKC hLP), ?_⟩
  have hzn : euclidNorm (cellCenter y) ≤ 3 * n := by
    have h1 : ‖toSpace (cellCenter y)‖ - ‖y‖ ≤ ‖toSpace (cellCenter y) - y‖ :=
      norm_sub_norm_le _ _
    rw [norm_toSpace] at h1
    linarith
  have hℓ : (localTime Y n (cellCenter y) : ℝ) -
      potential d ε (cellSet Y n) (toSpace (cellCenter y)) ≤ C₁ * (Real.sqrt (W * L) + L) :=
    (abs_le.mp (hfine₁ (cellCenter y) hzn)).2
  have hUz : potential d ε (cellSet Y n) (toSpace (cellCenter y)) ≤
      potential d ε (cellSet Y n) y + C₃ * L := by
    have h := hmod y (toSpace (cellCenter y)) (by linarith)
      (by rw [norm_sub_rev]; linarith)
    have := (abs_le.mp h).1
    linarith
  have hUy : potential d ε (cellSet Y n) y ≤ P := by
    rw [ev_potential_split hd2 ε hDmeas hDbdd hb hball y,
      max_eq_right (by linarith : b - ‖y‖ ≤ 0), mul_zero, zero_add]
    exact ev_potential_le_positivePotential hd1 hε.le hEmeas hEfin y
  have hsqrt : Real.sqrt (W * L) ≤ W + L := by
    have h1 : W * L ≤ (W + L) ^ 2 := by
      have e : (W + L) ^ 2 = W * L + (W * W + W * L + L * L) := by ring
      have := mul_nonneg hW0 hW0
      have := mul_nonneg hW0 (by linarith : (0 : ℝ) ≤ L)
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ L) (by linarith : (0 : ℝ) ≤ L)
      linarith
    calc Real.sqrt (W * L) ≤ Real.sqrt ((W + L) ^ 2) := Real.sqrt_le_sqrt h1
      _ = W + L := Real.sqrt_sq (by linarith)
  have hC₁sq : C₁ * Real.sqrt (W * L) ≤ C₁ * (K * (L + P) + L) :=
    mul_le_mul_of_nonneg_left (hsqrt.trans (by linarith)) hC₁
  have e : (1 + C₃ + C₁ * K + 2 * C₁ + K) * (L + P) =
      (P + C₃ * L + C₁ * (K * (L + P) + L) + C₁ * L) +
        (L + C₃ * P + 2 * C₁ * P + K * (L + P)) := by ring
  have h5 : 0 ≤ C₃ * P := mul_nonneg hC₃ hP0
  have h6 : 0 ≤ 2 * C₁ * P := mul_nonneg (by linarith) hP0
  have h7 : 0 ≤ K * (L + P) := mul_nonneg hK0 hLP
  have h8 : (localTime Y n (cellCenter y) : ℝ) ≤
      P + C₃ * L + C₁ * (K * (L + P) + L) + C₁ * L := by
    have e2 : C₁ * (Real.sqrt (W * L) + L) = C₁ * Real.sqrt (W * L) + C₁ * L := by ring
    linarith
  linarith
/-! ### The geometry of a set in an annulus -/

section GeomA

open CERW.Generic.Kernel CERW.Support.Geometry

/-- On a bounded set the function `|v - y|^{2-d}` is integrable for `d ≥ 2`. -/
private lemma gma_integrableOn_rpow (hd : 2 ≤ d) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hEb : Bornology.IsBounded E) (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => ‖v - y‖ ^ (2 - (d : ℝ))) E := by
  obtain ⟨ρ, hρ⟩ := hEb.subset_ball y
  have hρ1 : 0 < max ρ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsub : E ⊆ Metric.ball y (max ρ 1) :=
    hρ.trans (Metric.ball_subset_ball (le_max_left _ _))
  have hd2 : (d : ℝ) - 2 < d := by linarith
  have h0 := (integrableOn_ball_rpow_neg_and_integral_eq (d := d) (by omega) hd2 hρ1).1
  simp only [neg_sub] at h0
  have hmp := measurePreserving_sub_right (volume : Measure (EuclideanSpace ℝ (Fin d))) y
  have hemb := measurableEmbedding_subRight y
  have h1 : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v - y‖ ^ (2 - (d : ℝ)))
      (Metric.ball y (max ρ 1)) := by
    rw [ball_eq_preimage_sub]
    exact (hmp.integrableOn_comp_preimage hemb (f := fun v => ‖v‖ ^ (2 - (d : ℝ)))).mpr h0
  exact h1.mono_set hsub

/-- The positive potential at a point beyond the support: `u_v·(v-y) ≤ |v-y|²/(2|v|)`. -/
private theorem positivePotential_le_of_outside (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    {b R : ℝ} (hb : 0 < b) (hsub : E ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ R})
    {y : EuclideanSpace ℝ (Fin d)} (hy : R ≤ ‖y‖) :
    positivePotential d ε E y ≤
      ε / (unitBallVolume d * b) * ∫ v in E, ‖v - y‖ ^ (2 - (d : ℝ)) := by
  have hω := unitBallVolume_pos d
  have hint := gma_integrableOn_rpow hd hEb y
  have hpt : ∀ v ∈ E, max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0 ≤
      (2 * b)⁻¹ * ‖v - y‖ ^ (2 - (d : ℝ)) := by
    intro v hv
    obtain ⟨hbv, hvR⟩ := hsub hv
    have hv0 : v ≠ 0 := by
      intro h
      rw [h, norm_zero] at hbv
      linarith
    have hvy : ‖v‖ ≤ ‖y‖ := hvR.trans hy
    have hnn : 0 ≤ (2 * b)⁻¹ * ‖v - y‖ ^ (2 - (d : ℝ)) :=
      mul_nonneg (inv_nonneg.mpr (by linarith)) (Real.rpow_nonneg (norm_nonneg _) _)
    refine max_le ?_ hnn
    by_cases hne : v = y
    · have h0 : inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d = 0 := by
        rw [hne]
        simp
      rw [h0]
      exact hnn
    · have hs : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have h1 := inner_unitDir_sub_le_sq_div hv0 hvy
      have hs2 : ‖v - y‖ ^ (2 - (d : ℝ)) = ‖v - y‖ ^ 2 / ‖v - y‖ ^ d := by
        rw [Real.rpow_sub hs, Real.rpow_two, Real.rpow_natCast]
      calc inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d
          ≤ (‖v - y‖ ^ 2 / (2 * ‖v‖)) / ‖v - y‖ ^ d :=
            div_le_div_of_nonneg_right h1 (pow_pos hs d).le
        _ ≤ (‖v - y‖ ^ 2 / (2 * b)) / ‖v - y‖ ^ d := by
            refine div_le_div_of_nonneg_right ?_ (pow_pos hs d).le
            exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
        _ = (2 * b)⁻¹ * ‖v - y‖ ^ (2 - (d : ℝ)) := by
            rw [hs2]
            field_simp
  have hmono : ∫ v in E, max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0 ≤
      ∫ v in E, (2 * b)⁻¹ * ‖v - y‖ ^ (2 - (d : ℝ)) := by
    refine integral_mono_of_nonneg ?_ (hint.const_mul _) ?_
    · exact Filter.Eventually.of_forall fun v => le_max_right _ _
    · exact (ae_restrict_iff' hE).mpr (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hmono
  unfold positivePotential
  calc 2 * ε / unitBallVolume d *
        ∫ v in E, max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0
      ≤ 2 * ε / unitBallVolume d * ((2 * b)⁻¹ * ∫ v in E, ‖v - y‖ ^ (2 - (d : ℝ))) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ε / (unitBallVolume d * b) * ∫ v in E, ‖v - y‖ ^ (2 - (d : ℝ)) := by ring

/-- For a point `v` of the cap of the ball of radius `t` about `c u`, the probe `(c + 4t) u`
satisfies `u_v · (v - (c + 4t) u) ≤ -t` and `|v - (c + 4t) u| ≤ 5t`. -/
private lemma gma_probe_bounds {c t : ℝ} (ht : 0 < t) (htc : 2 * t ≤ c)
    {u v : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1) (hv0 : v ≠ 0) (hvc : ‖v‖ ≤ c)
    (hvB : ‖v - c • u‖ < t) :
    inner ℝ (unitDir v) (v - (c + 4 * t) • u) ≤ -t ∧ ‖v - (c + 4 * t) • u‖ ≤ 5 * t := by
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hIu : c - t ≤ inner ℝ v u := by
    have h1 : inner ℝ v u = inner ℝ (v - c • u) u + c := by
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
      ring
    have h2 : |inner ℝ (v - c • u) u| ≤ ‖v - c • u‖ * ‖u‖ := abs_real_inner_le_norm _ _
    rw [hu, mul_one] at h2
    have h3 := neg_abs_le (inner ℝ (v - c • u) u)
    linarith
  have hinner : inner ℝ (unitDir v) (v - (c + 4 * t) • u) =
      ‖v‖ - (c + 4 * t) * inner ℝ v u / ‖v‖ := by
    rw [unitDir, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_smul_right]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hinner]
    have h1 : (‖v‖ + t) * ‖v‖ ≤ (c + t) * c :=
      mul_le_mul (add_le_add_left hvc t) hvc hr.le (by linarith)
    have h2 : (c + t) * c ≤ (c + 4 * t) * (c - t) := by
      nlinarith [mul_nonneg ht.le (sub_nonneg.mpr htc)]
    have h3 : (c + 4 * t) * (c - t) ≤ (c + 4 * t) * inner ℝ v u :=
      mul_le_mul_of_nonneg_left hIu (by linarith)
    have h4 : ‖v‖ + t ≤ (c + 4 * t) * inner ℝ v u / ‖v‖ := by
      rw [le_div_iff₀ hr]
      linarith
    linarith
  · have h1 : v - (c + 4 * t) • u = (v - c • u) - (4 * t) • u := by
      rw [add_smul, sub_sub]
    rw [h1]
    calc ‖(v - c • u) - (4 * t) • u‖ ≤ ‖v - c • u‖ + ‖(4 * t) • u‖ := norm_sub_le _ _
      _ ≤ t + 4 * t := by
        rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      _ = 5 * t := by ring

/-- Step 2 of the higher-dimensional proof: a probe potential bound bounds the volume of a cap. -/
private theorem cap_mass_of_probe (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    {b w t lo hi : ℝ} (hsub : E ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w}) (hb : 0 < b)
    (ht : 0 < t) (htb : 2 * t ≤ b + w) {u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1)
    (hlow : -lo ≤ potential d ε E (((b + w + 4 * t) : ℝ) • u))
    (hhi : positivePotential d ε E (((b + w + 4 * t) : ℝ) • u) ≤ hi) :
    (volume (E ∩ Metric.ball (((b + w) : ℝ) • u) t)).toReal ≤
      unitBallVolume d / (2 * ε) * 5 ^ d * (lo + hi) * t ^ (d - 1) := by
  have hω := unitBallVolume_pos d
  have hEfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
  set y : EuclideanSpace ℝ (Fin d) := ((b + w + 4 * t : ℝ)) • u with hy
  have hint := integrableOn_potentialIntegrand (d := d) (by omega) hE hEfin y
  set B : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball (((b + w) : ℝ) • u) t with hB
  have hBm : MeasurableSet B := Metric.isOpen_ball.measurableSet
  set κ : ℝ := t / (5 * t) ^ d with hκ
  have hκpos : 0 < κ := by positivity
  have hpt : ∀ v ∈ E, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d ≤
      max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0 - B.indicator (fun _ => κ) v := by
    intro v hv
    by_cases hvB : v ∈ B
    · rw [Set.indicator_of_mem hvB]
      obtain ⟨hb1, hb2⟩ := hsub hv
      have hv0 : v ≠ 0 := by
        intro h
        rw [h, norm_zero] at hb1
        linarith
      obtain ⟨h1, h2⟩ := gma_probe_bounds (c := b + w) ht htb hu hv0 hb2
        (by rwa [hB, Metric.mem_ball, dist_eq_norm] at hvB)
      have h1' : inner ℝ (unitDir v) (v - y) ≤ -t := h1
      have hs : 0 < ‖v - y‖ := by
        rw [norm_pos_iff, sub_ne_zero]
        intro h
        rw [h] at h1'
        simp only [sub_self, inner_zero_right] at h1'
        linarith
      have hf : inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d ≤ -κ := by
        calc inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d ≤ (-t) / ‖v - y‖ ^ d :=
              div_le_div_of_nonneg_right h1' (pow_pos hs d).le
          _ = -(t / ‖v - y‖ ^ d) := neg_div _ _
          _ ≤ -κ := by
              refine neg_le_neg ?_
              exact div_le_div_of_nonneg_left ht.le (pow_pos hs d)
                (pow_le_pow_left₀ hs.le h2 d)
      have := le_max_right (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0
      linarith
    · rw [Set.indicator_of_notMem hvB, sub_zero]
      exact le_max_left _ _
  have hposint : IntegrableOn (fun v => max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0) E :=
    hint.pos_part
  have hindint : IntegrableOn (fun v => B.indicator (fun _ => κ) v) E :=
    (integrableOn_const hEfin).indicator hBm
  have hmono : ∫ v in E, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d ≤
      ∫ v in E, (max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0 -
        B.indicator (fun _ => κ) v) :=
    setIntegral_mono_on hint (hposint.sub hindint) hE hpt
  rw [integral_sub hposint hindint, setIntegral_indicator hBm, setIntegral_const] at hmono
  have hK0 : 0 < 2 * ε / unitBallVolume d := by positivity
  have hmono' := mul_le_mul_of_nonneg_left hmono hK0.le
  have hpot : potential d ε E y = 2 * ε / unitBallVolume d *
      ∫ v in E, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d := rfl
  have hpos : positivePotential d ε E y = 2 * ε / unitBallVolume d *
      ∫ v in E, max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0 := rfl
  rw [measureReal_def, smul_eq_mul, mul_sub] at hmono'
  have hV : (volume (E ∩ B)).toReal * (2 * ε / unitBallVolume d * κ) ≤ lo + hi := by
    rw [← hpot] at hmono'
    rw [← hpos] at hmono'
    nlinarith
  have hfinal : (lo + hi) / (2 * ε / unitBallVolume d * κ) =
      unitBallVolume d / (2 * ε) * 5 ^ d * (lo + hi) * t ^ (d - 1) := by
    have htd : t ^ d = t ^ (d - 1) * t := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hκ, mul_pow, htd]
    field_simp
  rw [← hfinal]
  exact (le_div_iff₀ (by positivity)).mpr hV

/-- A ball of radius `t ≥ w` meets `E` in at most `3^{d-1}` times the cap bound. -/
private theorem local_mass_of_cap (hd : 1 ≤ d) {E : Set (EuclideanSpace ℝ (Fin d))}
    {b w lam : ℝ} (hsub : E ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w}) (hlam : 0 ≤ lam)
    (hcap : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t →
      volume (E ∩ Metric.ball (((b + w) : ℝ) • u) t) ≤ ENNReal.ofReal (lam * t ^ (d - 1)))
    (y : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : w ≤ t) (ht0 : 0 < t) :
    (volume (E ∩ Metric.ball y t)).toReal ≤ lam * 3 ^ (d - 1) * t ^ (d - 1) := by
  by_cases hne : (E ∩ Metric.ball y t).Nonempty
  · obtain ⟨v, hvE, hvB⟩ := hne
    obtain ⟨hb1, hb2⟩ := hsub hvE
    obtain ⟨u, hu, huv⟩ : ∃ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 ∧ ‖v - (b + w) • u‖ ≤ w := by
      by_cases hv0 : v = 0
      · haveI : NeZero d := ⟨by omega⟩
        obtain ⟨u, hu⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin d)) zero_le_one
        refine ⟨u, hu, ?_⟩
        rw [hv0, norm_zero] at hb1
        rw [hv0, zero_sub, norm_neg, norm_smul, hu, mul_one, Real.norm_eq_abs,
          abs_of_nonneg (by rw [hv0, norm_zero] at hb2; exact hb2)]
        linarith
      · have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv0
        refine ⟨unitDir v, ?_, ?_⟩
        · rw [unitDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
        · have h1 : v = ‖v‖ • unitDir v := by
            rw [unitDir, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
          have h2 : ‖unitDir v‖ = 1 := by
            rw [unitDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
          have h3 : v - (b + w) • unitDir v = (‖v‖ - (b + w)) • unitDir v := by
            rw [sub_smul, ← h1]
          rw [h3, norm_smul, h2, mul_one, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
          linarith
    have hball : Metric.ball y t ⊆ Metric.ball (((b + w) : ℝ) • u) (3 * t) := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      rw [Metric.mem_ball, dist_eq_norm] at hvB
      calc ‖z - (b + w) • u‖ = ‖(z - y) + (y - v) + (v - (b + w) • u)‖ := by
            congr 1
            abel
        _ ≤ ‖(z - y) + (y - v)‖ + ‖v - (b + w) • u‖ := norm_add_le _ _
        _ ≤ ‖z - y‖ + ‖y - v‖ + ‖v - (b + w) • u‖ := by
            gcongr
            exact norm_add_le _ _
        _ < 3 * t := by
            rw [norm_sub_rev y v]
            linarith
    have hvol : volume (E ∩ Metric.ball y t) ≤ ENNReal.ofReal (lam * (3 * t) ^ (d - 1)) :=
      (measure_mono (Set.inter_subset_inter_right E hball)).trans
        (hcap u hu (3 * t) (by linarith))
    calc (volume (E ∩ Metric.ball y t)).toReal
        ≤ (ENNReal.ofReal (lam * (3 * t) ^ (d - 1))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
      _ = lam * (3 * t) ^ (d - 1) := ENNReal.toReal_ofReal (by positivity)
      _ = lam * 3 ^ (d - 1) * t ^ (d - 1) := by rw [mul_pow]; ring
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty, ENNReal.toReal_zero]
    positivity

end GeomA

/-- The volume of a ball of radius `t ≥ 0` is `ω_d t^d`. -/
private lemma gmb_volume_ball (hd : 1 ≤ d) (y : EuclideanSpace ℝ (Fin d)) {t : ℝ}
    (ht : 0 ≤ t) :
    volume (Metric.ball y t) = ENNReal.ofReal (unitBallVolume d * t ^ d) := by
  haveI : NeZero d := ⟨by omega⟩
  rw [Measure.addHaar_ball volume y ht, finrank_euclideanSpace_fin, unitBallVolume,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal measure_ball_lt_top.ne,
    mul_comm]

/-- The tail integral `(d-2) ∫_r^∞ t^{1-d} dt = r^{2-d}`. -/
private lemma gmb_lintegral_tail (hd : 3 ≤ d) {r : ℝ} (hr : 0 < r) :
    ∫⁻ t in Set.Ioi r, ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ))) =
      ENNReal.ofReal (r ^ (2 - (d : ℝ))) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : (1 - (d : ℝ)) < -1 := by linarith
  have hint : IntegrableOn (fun t : ℝ => t ^ (1 - (d : ℝ))) (Set.Ioi r) :=
    integrableOn_Ioi_rpow_of_lt ha hr
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)]
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt ha hr]
    congr 1
    have h1 : (1 - (d : ℝ)) + 1 = 2 - d := by ring
    rw [h1]
    have h2 : (2 - (d : ℝ)) ≠ 0 := by linarith
    field_simp
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (hr.le.trans ht.le) _)

/-- Layer-cake formula (as an inequality): `∫_E |v-y|^{2-d} ≤ (d-2) ∫_0^∞ |E ∩ B(y,t)| t^{1-d} dt`,
in `[0, ∞]`-valued integrals. -/
private lemma gmb_layer_cake (hd : 3 ≤ d) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hE : MeasurableSet E) (y : EuclideanSpace ℝ (Fin d)) :
    ∫⁻ v in E, ENNReal.ofReal (‖v - y‖ ^ (2 - (d : ℝ))) ≤
      ∫⁻ t, ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ))) *
        volume (E ∩ Metric.ball y t) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set f : ℝ → ENNReal := fun t => ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ))) with hf
  have hfm : Measurable f := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact measurable_const.mul (measurable_id.pow_const _)
  set G : EuclideanSpace ℝ (Fin d) → ℝ → ENNReal :=
    fun v t => if ‖v - y‖ < t then f t else 0 with hG
  have hGm : Measurable (Function.uncurry G) := by
    have hS : MeasurableSet {q : EuclideanSpace ℝ (Fin d) × ℝ | ‖q.1 - y‖ < q.2} :=
      measurableSet_lt ((measurable_fst.sub_const y).norm) measurable_snd
    exact Measurable.ite hS (hfm.comp measurable_snd) measurable_const
  have h1 : ∀ v, ENNReal.ofReal (‖v - y‖ ^ (2 - (d : ℝ))) ≤ ∫⁻ t, G v t := by
    intro v
    by_cases hv : v = y
    · subst hv
      have h2 : (2 - (d : ℝ)) ≠ 0 := by linarith
      simp [Real.zero_rpow h2]
    · have hr : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
      have hvt : (fun t => G v t) = (Set.Ioi ‖v - y‖).indicator f := by
        funext t
        simp [hG, Set.indicator]
      rw [hvt, lintegral_indicator measurableSet_Ioi, hf, gmb_lintegral_tail hd hr]
  calc ∫⁻ v in E, ENNReal.ofReal (‖v - y‖ ^ (2 - (d : ℝ)))
      ≤ ∫⁻ v in E, ∫⁻ t, G v t := lintegral_mono h1
    _ = ∫⁻ t, ∫⁻ v in E, G v t := lintegral_lintegral_swap hGm.aemeasurable
    _ = ∫⁻ t, f t * volume (E ∩ Metric.ball y t) := by
        congr 1
        funext t
        have hvt : (fun v => G v t) = (Metric.ball y t).indicator (fun _ => f t) := by
          funext v
          simp [hG, Set.indicator, dist_eq_norm]
        rw [hvt, lintegral_indicator_const Metric.isOpen_ball.measurableSet,
          Measure.restrict_apply' hE, Set.inter_comm]

/-- For `t > 0`, `t^{1-d} t^d = t`. -/
private lemma gmb_rpow_mul_pow (d : ℕ) {t : ℝ} (ht : 0 < t) :
    t ^ (1 - (d : ℝ)) * t ^ d = t := by
  rw [← Real.rpow_natCast t d, ← Real.rpow_add ht]
  simp

/-- For `t > 0` and `d ≥ 1`, `t^{1-d} t^{d-1} = 1`. -/
private lemma gmb_rpow_mul_pow_pred (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    t ^ (1 - (d : ℝ)) * t ^ (d - 1) = 1 := by
  rw [← Real.rpow_natCast t (d - 1), ← Real.rpow_add ht, Nat.cast_sub hd]
  simp

/-- The layer-cake bound with a cut scale `s ≥ w`:
`∫_E |v-y|^{2-d} ≤ (d-2) ω_d w²/2 + (d-2) lam (s-w) + m s^{2-d}`, in `[0, ∞]`-valued form. -/
private lemma gmb_lintegral_bound (hd : 3 ≤ d) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) {w lam m s : ℝ} (hw : 0 < w)
    (hlam : 0 < lam) (hm : 0 < m) (hws : w ≤ s)
    (hloc : ∀ (y : EuclideanSpace ℝ (Fin d)) (t : ℝ), w ≤ t →
      (volume (E ∩ Metric.ball y t)).toReal ≤ lam * t ^ (d - 1))
    (hmass : (volume E).toReal ≤ m) (y : EuclideanSpace ℝ (Fin d)) :
    ∫⁻ v in E, ENNReal.ofReal (‖v - y‖ ^ (2 - (d : ℝ))) ≤
      ENNReal.ofReal (((d : ℝ) - 2) * unitBallVolume d * w ^ 2 / 2 +
        ((d : ℝ) - 2) * lam * (s - w) + m * s ^ (2 - (d : ℝ))) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 < (d : ℝ) - 2 := by linarith
  have hs : 0 < s := hw.trans_le hws
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  set f : ℝ → ENNReal := fun t => ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ))) with hf
  have hfm : Measurable f := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact measurable_const.mul (measurable_id.pow_const _)
  set B1 : ℝ → ENNReal := (Set.Ioc 0 w).indicator
    (fun t => ENNReal.ofReal (((d : ℝ) - 2) * unitBallVolume d * t)) with hB1
  set B2 : ℝ → ENNReal := (Set.Ioc w s).indicator
    (fun _ => ENNReal.ofReal (((d : ℝ) - 2) * lam)) with hB2
  set B3 : ℝ → ENNReal := (Set.Ioi s).indicator (fun t => ENNReal.ofReal m * f t) with hB3
  have hB1m : Measurable B1 := by
    refine Measurable.indicator ?_ measurableSet_Ioc
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id)
  have hB2m : Measurable B2 := measurable_const.indicator measurableSet_Ioc
  have hB3m : Measurable B3 := (measurable_const.mul hfm).indicator measurableSet_Ioi
  have hfin : ∀ t, volume (E ∩ Metric.ball y t) ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top hEfin (measure_mono Set.inter_subset_left)
  have hpt : ∀ t, f t * volume (E ∩ Metric.ball y t) ≤ B1 t + B2 t + B3 t := by
    intro t
    by_cases ht0 : t ≤ 0
    · have : Metric.ball y t = ∅ := Metric.ball_eq_empty.mpr ht0
      simp [this]
    have ht0 := not_le.mp ht0
    by_cases htw : t ≤ w
    · have hB2z : B2 t = 0 :=
        Set.indicator_of_notMem (fun h : t ∈ Set.Ioc w s => (not_le.mpr h.1) htw) _
      have hB3z : B3 t = 0 :=
        Set.indicator_of_notMem
          (fun h : t ∈ Set.Ioi s => (not_le.mpr h) (htw.trans hws)) _
      have hB1e : B1 t = ENNReal.ofReal (((d : ℝ) - 2) * unitBallVolume d * t) :=
        Set.indicator_of_mem (show t ∈ Set.Ioc 0 w from ⟨ht0, htw⟩) _
      rw [hB2z, hB3z, hB1e, add_zero, add_zero]
      have hid := gmb_rpow_mul_pow d ht0
      calc f t * volume (E ∩ Metric.ball y t) ≤ f t * volume (Metric.ball y t) := by
            gcongr
            exact Set.inter_subset_right
        _ = ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ)) * (unitBallVolume d * t ^ d)) := by
            rw [gmb_volume_ball (by omega) y ht0.le, hf]
            exact (ENNReal.ofReal_mul (mul_nonneg hp.le (Real.rpow_nonneg ht0.le _))).symm
        _ = ENNReal.ofReal (((d : ℝ) - 2) * unitBallVolume d * t) := by
            congr 1
            calc ((d : ℝ) - 2) * t ^ (1 - (d : ℝ)) * (unitBallVolume d * t ^ d)
                = ((d : ℝ) - 2) * unitBallVolume d * (t ^ (1 - (d : ℝ)) * t ^ d) := by ring
              _ = ((d : ℝ) - 2) * unitBallVolume d * t := by rw [hid]
    by_cases hts : t ≤ s
    · have hB1z : B1 t = 0 :=
        Set.indicator_of_notMem (fun h : t ∈ Set.Ioc 0 w => htw h.2) _
      have hB3z : B3 t = 0 :=
        Set.indicator_of_notMem (fun h : t ∈ Set.Ioi s => (not_le.mpr h) hts) _
      have hB2e : B2 t = ENNReal.ofReal (((d : ℝ) - 2) * lam) :=
        Set.indicator_of_mem (show t ∈ Set.Ioc w s from ⟨not_le.mp htw, hts⟩) _
      rw [hB1z, hB3z, hB2e, zero_add, add_zero]
      have hid := gmb_rpow_mul_pow_pred (d := d) (by omega) ht0
      have hvol : volume (E ∩ Metric.ball y t) ≤ ENNReal.ofReal (lam * t ^ (d - 1)) :=
        (ENNReal.le_ofReal_iff_toReal_le (hfin t) (by positivity)).mpr
          (hloc y t (not_le.mp htw).le)
      calc f t * volume (E ∩ Metric.ball y t)
          ≤ f t * ENNReal.ofReal (lam * t ^ (d - 1)) := by gcongr
        _ = ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ)) * (lam * t ^ (d - 1))) :=
            (ENNReal.ofReal_mul (mul_nonneg hp.le (Real.rpow_nonneg ht0.le _))).symm
        _ = ENNReal.ofReal (((d : ℝ) - 2) * lam) := by
            congr 1
            calc ((d : ℝ) - 2) * t ^ (1 - (d : ℝ)) * (lam * t ^ (d - 1))
                = ((d : ℝ) - 2) * lam * (t ^ (1 - (d : ℝ)) * t ^ (d - 1)) := by ring
              _ = ((d : ℝ) - 2) * lam := by rw [hid, mul_one]
    · have hB1z : B1 t = 0 :=
        Set.indicator_of_notMem (fun h : t ∈ Set.Ioc 0 w => hts (h.2.trans hws)) _
      have hB2z : B2 t = 0 :=
        Set.indicator_of_notMem (fun h : t ∈ Set.Ioc w s => hts h.2) _
      have hB3e : B3 t = ENNReal.ofReal m * f t :=
        Set.indicator_of_mem (show t ∈ Set.Ioi s from not_le.mp hts) _
      rw [hB1z, hB2z, hB3e, zero_add, zero_add, mul_comm]
      have hvol : volume (E ∩ Metric.ball y t) ≤ ENNReal.ofReal m :=
        (ENNReal.le_ofReal_iff_toReal_le (hfin t) hm.le).mpr
          ((ENNReal.toReal_mono hEfin (measure_mono Set.inter_subset_left)).trans hmass)
      gcongr
  have hA : 0 ≤ ((d : ℝ) - 2) * unitBallVolume d * w ^ 2 / 2 := by positivity
  have hB : 0 ≤ ((d : ℝ) - 2) * lam * (s - w) :=
    mul_nonneg (mul_nonneg hp.le hlam.le) (sub_nonneg.mpr hws)
  have hC : 0 ≤ m * s ^ (2 - (d : ℝ)) := mul_nonneg hm.le (Real.rpow_nonneg hs.le _)
  have hI1 : (∫⁻ t, B1 t) = ENNReal.ofReal (((d : ℝ) - 2) * unitBallVolume d * w ^ 2 / 2) := by
    have hint : IntegrableOn (fun t : ℝ => ((d : ℝ) - 2) * unitBallVolume d * t)
        (Set.Ioc 0 w) := (continuous_const.mul continuous_id).integrableOn_Ioc
    rw [hB1, lintegral_indicator measurableSet_Ioc,
      ← ofReal_integral_eq_lintegral_ofReal hint]
    · congr 1
      rw [← intervalIntegral.integral_of_le hw.le, intervalIntegral.integral_const_mul,
        integral_id]
      ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (mul_nonneg hp.le hω.le) ht.1.le
  have hI2 : (∫⁻ t, B2 t) = ENNReal.ofReal (((d : ℝ) - 2) * lam * (s - w)) := by
    rw [hB2, lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc,
      ← ENNReal.ofReal_mul (mul_nonneg hp.le hlam.le)]
  have hI3 : (∫⁻ t, B3 t) = ENNReal.ofReal (m * s ^ (2 - (d : ℝ))) := by
    rw [hB3, lintegral_indicator measurableSet_Ioi, lintegral_const_mul _ hfm, hf,
      gmb_lintegral_tail hd hs, ← ENNReal.ofReal_mul hm.le]
  calc ∫⁻ v in E, ENNReal.ofReal (‖v - y‖ ^ (2 - (d : ℝ)))
      ≤ ∫⁻ t, f t * volume (E ∩ Metric.ball y t) := gmb_layer_cake hd hE y
    _ ≤ ∫⁻ t, (B1 t + B2 t + B3 t) := lintegral_mono hpt
    _ = (∫⁻ t, B1 t) + (∫⁻ t, B2 t) + ∫⁻ t, B3 t := by
        rw [lintegral_add_left (f := fun t => B1 t + B2 t) (hB1m.add hB2m),
          lintegral_add_left (f := B1) hB1m]
    _ = ENNReal.ofReal (((d : ℝ) - 2) * unitBallVolume d * w ^ 2 / 2 +
        ((d : ℝ) - 2) * lam * (s - w) + m * s ^ (2 - (d : ℝ))) := by
        rw [hI1, hI2, hI3, ← ENNReal.ofReal_add hA hB, ← ENNReal.ofReal_add (add_nonneg hA hB) hC]

/-- The optimal cut scale of the layer-cake bound: there is `s ≥ w` with
`(d-2) lam (s-w) + m s^{2-d} ≤ (d-1) lam^{(d-2)/(d-1)} m^{1/(d-1)}`. -/
private lemma gmb_choose_scale (hd : 3 ≤ d) {w lam m : ℝ} (hw : 0 < w) (hlam : 0 < lam)
    (hm : 0 < m) :
    ∃ s : ℝ, w ≤ s ∧ ((d : ℝ) - 2) * lam * (s - w) + m * s ^ (2 - (d : ℝ)) ≤
      ((d : ℝ) - 1) * lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
        m ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : (d : ℝ) - 1 ≠ 0 := by linarith
  obtain ⟨s0, hs0def⟩ : ∃ s0 : ℝ, s0 = (m / lam) ^ ((1 : ℝ) / ((d : ℝ) - 1)) := ⟨_, rfl⟩
  have hmlam : 0 < m / lam := div_pos hm hlam
  have hs0 : 0 < s0 := hs0def ▸ Real.rpow_pos_of_pos hmlam _
  have hs0q : s0 ^ ((d : ℝ) - 1) = m / lam := by
    rw [hs0def, ← Real.rpow_mul hmlam.le, one_div, inv_mul_cancel₀ hq, Real.rpow_one]
  have hm_eq : m = lam * s0 ^ ((d : ℝ) - 1) := by
    rw [hs0q]
    field_simp
  have hms : m * s0 ^ (2 - (d : ℝ)) = lam * s0 := by
    rw [hm_eq, mul_assoc, ← Real.rpow_add hs0]
    have : ((d : ℝ) - 1) + (2 - (d : ℝ)) = 1 := by ring
    rw [this, Real.rpow_one]
  have hlams0 : lam * s0 =
      lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) * m ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
    have hsum : ((d : ℝ) - 2) / ((d : ℝ) - 1) + (1 : ℝ) / ((d : ℝ) - 1) = 1 := by
      field_simp
      ring
    have hl : lam = lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
        lam ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
      rw [← Real.rpow_add hlam, hsum, Real.rpow_one]
    have hl1 : 0 < lam ^ ((1 : ℝ) / ((d : ℝ) - 1)) := Real.rpow_pos_of_pos hlam _
    rw [hs0def, Real.div_rpow hm.le hlam.le]
    calc lam * (m ^ ((1 : ℝ) / ((d : ℝ) - 1)) / lam ^ ((1 : ℝ) / ((d : ℝ) - 1)))
        = (lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) * lam ^ ((1 : ℝ) / ((d : ℝ) - 1))) *
          (m ^ ((1 : ℝ) / ((d : ℝ) - 1)) / lam ^ ((1 : ℝ) / ((d : ℝ) - 1))) := by
          rw [← hl]
      _ = lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) * m ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
          field_simp
  have hK : ((d : ℝ) - 1) * lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
      m ^ ((1 : ℝ) / ((d : ℝ) - 1)) = ((d : ℝ) - 1) * (lam * s0) := by
    rw [hlams0]
    ring
  have hlm : 0 < lam * s0 := mul_pos hlam hs0
  by_cases hcase : w ≤ s0
  · refine ⟨s0, hcase, ?_⟩
    rw [hK, hms]
    have h1 : 0 ≤ ((d : ℝ) - 2) * (lam * w) :=
      mul_nonneg (by linarith) (mul_nonneg hlam.le hw.le)
    linarith
  · have hlt : s0 < w := not_le.mp hcase
    refine ⟨w, le_rfl, ?_⟩
    rw [sub_self, mul_zero, zero_add, hK]
    have h1 : w ^ (2 - (d : ℝ)) ≤ s0 ^ (2 - (d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hs0 hlt.le (by linarith)
    calc m * w ^ (2 - (d : ℝ)) ≤ m * s0 ^ (2 - (d : ℝ)) := by gcongr
      _ = lam * s0 := hms
      _ ≤ ((d : ℝ) - 1) * (lam * s0) := le_mul_of_one_le_left hlm.le (by linarith)

/-- Step 4 of the higher-dimensional proof: the layer-cake bound for `∫_E |v-y|^{2-d}` from the
local mass bound at scales `t ≥ w` and the total mass. -/
private theorem integral_rpow_le_of_local_mass (hd : 3 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    {w lam m : ℝ} (hw : 0 < w) (hlam : 0 < lam) (hm : 0 < m)
    (hloc : ∀ (y : EuclideanSpace ℝ (Fin d)) (t : ℝ), w ≤ t →
      (volume (E ∩ Metric.ball y t)).toReal ≤ lam * t ^ (d - 1))
    (hmass : (volume E).toReal ≤ m) (y : EuclideanSpace ℝ (Fin d)) :
    ∫ v in E, ‖v - y‖ ^ (2 - (d : ℝ)) ≤
      ((d : ℝ) - 2) * unitBallVolume d * w ^ 2 / 2 +
        ((d : ℝ) - 1) * lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) * m ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
  have hEfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
  obtain ⟨s, hws, hs⟩ := gmb_choose_scale hd hw hlam hm
  have hlint := gmb_lintegral_bound hd hE hEfin hw hlam hm hws hloc hmass y
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hR : 0 ≤ ((d : ℝ) - 2) * unitBallVolume d * w ^ 2 / 2 +
      ((d : ℝ) - 1) * lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
        m ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
    have h1 : 0 ≤ ((d : ℝ) - 2) * unitBallVolume d * w ^ 2 / 2 := by
      have : 0 ≤ (d : ℝ) - 2 := by linarith
      positivity
    have h2 : 0 ≤ ((d : ℝ) - 1) * lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
        m ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
      have : 0 ≤ (d : ℝ) - 1 := by linarith
      positivity
    exact add_nonneg h1 h2
  have hmeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) => ‖v - y‖ ^ (2 - (d : ℝ))) :=
    (measurable_id.sub_const y).norm.pow_const _
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun v => Real.rpow_nonneg (norm_nonneg _) _)
    hmeas.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hR (hlint.trans (ENNReal.ofReal_le_ofReal ?_))
  linarith

/-- The integrals `∫_E |v-y|^{2-d}` are bounded uniformly in `y` for a bounded set `E`. -/
private theorem integral_rpow_bddAbove (hd : 3 ≤ d) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) :
    BddAbove (Set.range fun y : EuclideanSpace ℝ (Fin d) => ∫ v in E, ‖v - y‖ ^ (2 - (d : ℝ))) := by
  have hm : 0 < (volume E).toReal + 1 := by positivity
  refine ⟨((d : ℝ) - 2) * unitBallVolume d * 1 ^ 2 / 2 +
    ((d : ℝ) - 1) * ((volume E).toReal + 1) ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
      ((volume E).toReal + 1) ^ ((1 : ℝ) / ((d : ℝ) - 1)), ?_⟩
  rintro _ ⟨y, rfl⟩
  refine integral_rpow_le_of_local_mass hd hE hEb (w := 1) (lam := (volume E).toReal + 1)
    one_pos hm hm ?_ (by linarith) y
  intro y' t ht
  calc (volume (E ∩ Metric.ball y' t)).toReal ≤ (volume E).toReal :=
        ENNReal.toReal_mono hEb.measure_lt_top.ne (measure_mono Set.inter_subset_left)
    _ ≤ (volume E).toReal + 1 := by linarith
    _ ≤ ((volume E).toReal + 1) * t ^ (d - 1) :=
        le_mul_of_one_le_right hm.le (one_le_pow₀ ht)

/-! ### The exterior analysis for `d ≥ 3` -/

/-- For large `n`, the radius `r_n` is positive, `K log n ≤ r_n` and `4 r_n ≤ n`. -/
private lemma hx_scales (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      0 < radius d ε n ∧ K * Real.log n ≤ radius d ε n ∧ 4 * radius d ε n ≤ n := by
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc : 0 < ((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d) := by positivity
  have he : (0 : ℝ) < 1 / ((d : ℝ) + 1) := by positivity
  set a : ℝ := (((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))
    with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hc _
  have hrad : ∀ n : ℕ, radius d ε n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    intro n
    rw [radius, ha_def, ← Real.mul_rpow hc.le (Nat.cast_nonneg n)]
    congr 1
    ring
  have hK1 : 0 < |K| + 1 := by positivity
  have h1 : ∀ᶠ n : ℕ in atTop, 4 * a ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) :=
    ((tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (4 * a)
  have h2 : ∀ᶠ n : ℕ in atTop,
      Real.log (n + 2) ^ (1 : ℝ) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)) < a / (|K| + 1) :=
    (CERW.Support.Main.tendsto_log_rpow_div_rpow 1 he).eventually_lt_const (div_pos ha hK1)
  have h3 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hA, hB, h1n⟩ := hn₀ n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1n
  set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1)) with hN_def
  have hNpos : 0 < N := Real.rpow_pos_of_pos (by linarith) _
  rw [hrad n]
  refine ⟨mul_pos ha hNpos, ?_, ?_⟩
  · rw [Real.rpow_one, div_lt_iff₀ hNpos] at hB
    have hlog : Real.log n ≤ Real.log (n + 2) := Real.log_le_log (by linarith) (by linarith)
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    calc K * Real.log n ≤ |K| * Real.log (n + 2) :=
          (mul_le_mul_of_nonneg_right (le_abs_self K) hlog0).trans
            (mul_le_mul_of_nonneg_left hlog (abs_nonneg K))
      _ ≤ (|K| + 1) * Real.log (n + 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (hlog0.trans hlog)
      _ ≤ (|K| + 1) * (a / (|K| + 1) * N) := mul_le_mul_of_nonneg_left hB.le hK1.le
      _ = a * N := by field_simp
  · have hN2 : N * N ≤ n := by
      rw [hN_def, ← Real.rpow_add (by linarith)]
      calc (n : ℝ) ^ ((1 : ℝ) / (d + 1) + 1 / (d + 1)) ≤ (n : ℝ) ^ (1 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le hn1
            have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
            rw [← add_div, div_le_one (by positivity)]
            linarith
        _ = n := Real.rpow_one _
    calc 4 * (a * N) = (4 * a) * N := by ring
      _ ≤ N * N := mul_le_mul_of_nonneg_right hA hNpos.le
      _ ≤ n := hN2

/-- For `n ≥ 3`: `1 ≤ log n` and `log (n + 2) ≤ 2 log n`. -/
private lemma hx_log_facts {n : ℕ} (hn : 3 ≤ n) :
    1 ≤ Real.log n ∧ Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨?_, ?_⟩
  · rw [Real.le_log_iff_exp_le (by linarith)]
    have h := Real.exp_one_lt_d9
    norm_num at h
    linarith
  · have h9 : (3 : ℝ) * n ≤ (n : ℝ) ^ 2 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hn3 (by linarith)
    calc Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
          Real.log_le_log (by linarith) (by linarith)
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num

/-- `log (n + √d + 2) ≤ (1 + log (1 + √d)) log (n + 2)` once `log (n + 2) ≥ 1`. -/
private lemma hx_log_shift (d n : ℕ) (hL : 1 ≤ Real.log ((n : ℝ) + 2)) :
    Real.log ((n : ℝ) + Real.sqrt d + 2) ≤
      (1 + Real.log (1 + Real.sqrt d)) * Real.log ((n : ℝ) + 2) := by
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog1 : 0 ≤ Real.log (1 + Real.sqrt d) := Real.log_nonneg (by linarith)
  have hprod : (n : ℝ) + Real.sqrt d + 2 ≤ ((n : ℝ) + 2) * (1 + Real.sqrt d) := by
    have : 0 ≤ ((n : ℝ) + 1) * Real.sqrt d := mul_nonneg (by linarith) hs
    linarith
  have hmul : Real.log (1 + Real.sqrt d) * 1 ≤
      Real.log (1 + Real.sqrt d) * Real.log ((n : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left hL hlog1
  calc Real.log ((n : ℝ) + Real.sqrt d + 2) ≤ Real.log (((n : ℝ) + 2) * (1 + Real.sqrt d)) :=
        Real.log_le_log (by linarith) hprod
    _ = Real.log ((n : ℝ) + 2) + Real.log (1 + Real.sqrt d) :=
        Real.log_mul (by linarith) (by linarith)
    _ ≤ (1 + Real.log (1 + Real.sqrt d)) * Real.log ((n : ℝ) + 2) := by linarith

/-- The arithmetic of Step 1: the point bound at an unvisited site, the bracket bound and the
cell modulus give `|U_E(y)| ≤ C_p Θ`. -/
private lemma hx_probe_arith {C₁ Cenv γ μ κ Θ L Λ W h P U : ℝ} (hCenv : 0 ≤ Cenv)
    (hγ : 0 ≤ γ) (hμ : 0 ≤ μ) (hκ : 0 ≤ κ) (hL0 : 0 ≤ L) (hL : L ≤ 2 * Θ)
    (hpt : |0 - P| ≤ C₁ * (Real.sqrt (W * L) + L)) (hW : W ≤ Cenv * (L + h))
    (hh : h ≤ γ * Θ) (hmod : |U - P| ≤ μ * Λ) (hΛ : Λ ≤ κ * L) :
    |U| ≤ (max C₁ 0 * (Real.sqrt (2 * Cenv * (2 + γ)) + 2) + 2 * μ * κ) * Θ := by
  have hΘ : 0 ≤ Θ := by linarith
  have hA : 0 ≤ Cenv * (2 + γ) := mul_nonneg hCenv (by linarith)
  have hW' : W ≤ Cenv * (2 + γ) * Θ := by
    calc W ≤ Cenv * (L + h) := hW
      _ ≤ Cenv * (2 * Θ + γ * Θ) := mul_le_mul_of_nonneg_left (by linarith) hCenv
      _ = Cenv * (2 + γ) * Θ := by ring
  have hWL : W * L ≤ 2 * Cenv * (2 + γ) * Θ ^ 2 := by
    calc W * L ≤ Cenv * (2 + γ) * Θ * L := mul_le_mul_of_nonneg_right hW' hL0
      _ ≤ Cenv * (2 + γ) * Θ * (2 * Θ) := mul_le_mul_of_nonneg_left hL (mul_nonneg hA hΘ)
      _ = 2 * Cenv * (2 + γ) * Θ ^ 2 := by ring
  have hsq : Real.sqrt (W * L) ≤ Real.sqrt (2 * Cenv * (2 + γ)) * Θ := by
    calc Real.sqrt (W * L) ≤ Real.sqrt (2 * Cenv * (2 + γ) * Θ ^ 2) := Real.sqrt_le_sqrt hWL
      _ = Real.sqrt (2 * Cenv * (2 + γ)) * Θ := by
          rw [Real.sqrt_mul (by linarith) (Θ ^ 2), Real.sqrt_sq hΘ]
  have hC : 0 ≤ max C₁ 0 := le_max_right _ _
  have hs0 : 0 ≤ Real.sqrt (W * L) + L := add_nonneg (Real.sqrt_nonneg _) hL0
  have hP : |P| ≤ max C₁ 0 * (Real.sqrt (2 * Cenv * (2 + γ)) * Θ + 2 * Θ) := by
    calc |P| = |0 - P| := by rw [zero_sub, abs_neg]
      _ ≤ C₁ * (Real.sqrt (W * L) + L) := hpt
      _ ≤ max C₁ 0 * (Real.sqrt (W * L) + L) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hs0
      _ ≤ max C₁ 0 * (Real.sqrt (2 * Cenv * (2 + γ)) * Θ + 2 * Θ) :=
          mul_le_mul_of_nonneg_left (by linarith) hC
  have hμΛ : μ * Λ ≤ μ * (κ * (2 * Θ)) :=
    mul_le_mul_of_nonneg_left (hΛ.trans (mul_le_mul_of_nonneg_left hL hκ)) hμ
  have hU : |U| - |P| ≤ |U - P| := abs_sub_abs_le_abs_sub U P
  linarith

/-- `ε/(ω b) I ≤ (2ε/ω) Θ` when `I ≤ r Θ` and `r ≤ 2b`. -/
private lemma hx_outside_arith {ε ω b r I Θ : ℝ} (hε : 0 ≤ ε) (hω : 0 < ω) (hb : 0 < b)
    (hΘ : 0 ≤ Θ) (hI : I ≤ r * Θ) (hrb : r ≤ 2 * b) :
    ε / (ω * b) * I ≤ 2 * ε / ω * Θ := by
  have hc : 0 ≤ ε / (ω * b) := div_nonneg hε (mul_pos hω hb).le
  have hω' := hω.ne'
  have hb' := hb.ne'
  calc ε / (ω * b) * I ≤ ε / (ω * b) * (2 * b * Θ) :=
        mul_le_mul_of_nonneg_left (hI.trans (mul_le_mul_of_nonneg_right hrb hΘ)) hc
    _ = 2 * ε / ω * Θ := by field_simp

/-- `((X^{(d-2)/(d-1)} Y^{1/(d-1)})^{d-1} = X^{d-2} Y` for `X, Y ≥ 0`. -/
private lemma hx_rpow_pow (hd : 3 ≤ d) {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (X ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) * Y ^ ((1 : ℝ) / ((d : ℝ) - 1))) ^ (d - 1) =
      X ^ (d - 2) * Y := by
  have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hd2 : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hpos : (d : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [mul_pow, ← Real.rpow_natCast (X ^ _), ← Real.rpow_natCast (Y ^ _), ← Real.rpow_mul hX,
    ← Real.rpow_mul hY, hd1, div_mul_cancel₀ _ hpos, div_mul_cancel₀ _ hpos, Real.rpow_one,
    ← hd2, Real.rpow_natCast]

/-- Step 4 of Section 7.2 (Young's inequality): if `Θ ≥ lg > 0` satisfies
`Θ ≤ lg + (c₁ w² + (d-1) (aΘ)^{(d-2)/(d-1)} (c r^{d-1} lg)^{1/(d-1)}) / r`, then
`Θ ≤ K (w²/r + lg)`. -/
private lemma hx_theta_arith (hd : 3 ≤ d) {a c c₁ : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hc₁ : 0 ≤ c₁) :
    ∃ K : ℝ, 0 < K ∧ ∀ Θ lg r w : ℝ, 0 < lg → lg ≤ Θ → 0 < r →
      Θ ≤ lg + (c₁ * w ^ 2 + ((d : ℝ) - 1) * ((a * Θ) ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
        (c * r ^ (d - 1) * lg) ^ ((1 : ℝ) / ((d : ℝ) - 1)))) / r →
      Θ ≤ K * (w ^ 2 / r + lg) := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1ne : (d : ℝ) - 1 ≠ 0 := by linarith
  set k : ℝ := 2 * ((d : ℝ) - 1) with hk_def
  have hk : 0 < k := by linarith
  set M : ℝ := k ^ (d - 1) * a ^ (d - 2) * c with hM_def
  have hM : 0 < M := by positivity
  refine ⟨M + 2 + 2 * c₁, by linarith, ?_⟩
  intro Θ lg r w hlg hlgΘ hr h
  have hΘ : 0 < Θ := lt_of_lt_of_le hlg hlgΘ
  set F : ℝ := (a * Θ) ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
    (c * r ^ (d - 1) * lg) ^ ((1 : ℝ) / ((d : ℝ) - 1)) with hF_def
  have hF0 : 0 ≤ F := by positivity
  have hw2 : 0 ≤ w ^ 2 / r := div_nonneg (sq_nonneg w) hr.le
  have h1 : 0 ≤ M * (w ^ 2 / r) := mul_nonneg hM.le hw2
  have h2 : 0 ≤ c₁ * lg := mul_nonneg hc₁ hlg.le
  have h3 : 0 ≤ M * lg := mul_nonneg hM.le hlg.le
  have h4 : 0 ≤ c₁ * (w ^ 2 / r) := mul_nonneg hc₁ hw2
  rcases le_or_gt F (r * Θ / k) with hA | hB
  · have hdF : ((d : ℝ) - 1) * F ≤ r * Θ / 2 := by
      calc ((d : ℝ) - 1) * F ≤ ((d : ℝ) - 1) * (r * Θ / k) :=
            mul_le_mul_of_nonneg_left hA (by linarith)
        _ = r * Θ / 2 := by rw [hk_def]; field_simp
    have hdiv : (c₁ * w ^ 2 + ((d : ℝ) - 1) * F) / r ≤ c₁ * (w ^ 2 / r) + Θ / 2 := by
      rw [div_le_iff₀ hr]
      have e : (c₁ * (w ^ 2 / r) + Θ / 2) * r = c₁ * w ^ 2 + r * Θ / 2 := by
        field_simp
      rw [e]
      linarith
    linarith
  · have hpow : (r * Θ / k) ^ (d - 1) < F ^ (d - 1) :=
      pow_lt_pow_left₀ hB (by positivity) (by omega)
    have hFpow : F ^ (d - 1) = (a * Θ) ^ (d - 2) * (c * r ^ (d - 1) * lg) :=
      hx_rpow_pow hd (by positivity) (by positivity)
    have hΘpow : Θ ^ (d - 1) = Θ ^ (d - 2) * Θ := by
      rw [← pow_succ]
      congr 1
      omega
    have e1 : (r * Θ / k) ^ (d - 1) = r ^ (d - 1) * Θ ^ (d - 2) * Θ / k ^ (d - 1) := by
      rw [div_pow, mul_pow, hΘpow, mul_assoc]
    have e2 : (a * Θ) ^ (d - 2) * (c * r ^ (d - 1) * lg) =
        r ^ (d - 1) * Θ ^ (d - 2) * (a ^ (d - 2) * c * lg) := by
      rw [mul_pow]
      ring
    rw [hFpow, e1, e2, div_lt_iff₀ (pow_pos hk _), mul_assoc (r ^ (d - 1) * Θ ^ (d - 2))] at hpow
    have hP : 0 < r ^ (d - 1) * Θ ^ (d - 2) := by positivity
    have hlt : Θ < a ^ (d - 2) * c * lg * k ^ (d - 1) := lt_of_mul_lt_mul_left hpow hP.le
    have hΘM : Θ ≤ M * lg := by
      rw [hM_def]
      linarith
    linarith

/-- Step 1 of Section 7.2: at a probe point `y` beyond the outer radius, whose cell is unvisited,
the potential of `E = D_n ∖ B(0,b)` is at most `C_p Θ` in absolute value. -/
private lemma hx_probe_potential (hd : 2 ≤ d) {ε C₁ Cenv Ccm γ Θ : ℝ} (hε : 0 ≤ ε)
    (hCenv : 0 ≤ Cenv) (hCcm : 0 ≤ Ccm) (hγ : 0 ≤ γ)
    (hcm : ∀ ε : ℝ, 0 ≤ ε → ∀ R : ℝ, 1 ≤ R →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → D ⊆ Metric.ball 0 R →
      ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R → ‖y - z‖ ≤ Real.sqrt d →
        |potential d ε D y - potential d ε D z| ≤ Ccm * ε * Real.log (R + 2))
    {Y : ℕ → Site d} {n : ℕ} {b : ℝ} (hb : 0 < b) (hdn : (d : ℝ) ≤ n)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ cellSet Y n)
    (hL1 : 1 ≤ Real.log ((n : ℝ) + 2)) (hLΘ : Real.log ((n : ℝ) + 2) ≤ 2 * Θ)
    (hpoint : ∀ x : Site d, euclidNorm x ≤ 3 * n →
      |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
        C₁ * (Real.sqrt (braSum Y n x * Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2)))
    (hbra : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ 2 * n →
      braSum Y n (cellCenter y) ≤ Cenv * (Real.log ((n : ℝ) + 2) +
        positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y))
    {y : EuclideanSpace ℝ (Fin d)} (hyR : maxRadius Y n + Real.sqrt d / 2 < ‖y‖)
    (hyb : b ≤ ‖y‖) (hyn : ‖y‖ ≤ n)
    (hUp : positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y ≤ γ * Θ) :
    |potential d ε (cellSet Y n \ Metric.ball 0 b) y| ≤
      (max C₁ 0 * (Real.sqrt (2 * Cenv * (2 + γ)) + 2) +
        2 * (Ccm * ε) * (1 + Real.log (1 + Real.sqrt d))) * Θ := by
  have hd1 : 1 ≤ d := by omega
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hs0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hsd : Real.sqrt d ≤ d := by
    rw [Real.sqrt_le_left (by linarith), sq]
    calc (d : ℝ) = d * 1 := (mul_one _).symm
      _ ≤ d * d := mul_le_mul_of_nonneg_left hd' (by linarith)
  have hDm : MeasurableSet (cellSet Y n) := CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDsub : cellSet Y n ⊆ Metric.ball 0 ((n : ℝ) + Real.sqrt d) :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n).trans
      (Metric.ball_subset_ball (by linarith))
  have hDb : Bornology.IsBounded (cellSet Y n) := Metric.isBounded_ball.subset hDsub
  have hyz : ‖y - toSpace (cellCenter y)‖ ≤ Real.sqrt d / 2 :=
    CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter y)
  have hz1 : ‖y‖ ≤ ‖toSpace (cellCenter y)‖ + ‖y - toSpace (cellCenter y)‖ :=
    norm_le_norm_add_norm_sub' y (toSpace (cellCenter y))
  have hz2 : ‖toSpace (cellCenter y)‖ ≤ ‖y‖ + ‖y - toSpace (cellCenter y)‖ :=
    norm_le_norm_add_norm_sub y (toSpace (cellCenter y))
  rw [norm_toSpace] at hz1 hz2
  have hz0 : localTime Y n (cellCenter y) = 0 := by
    by_contra hne
    have hmem : cellCenter y ∈ departureRange Y n :=
      mem_departureRange_iff.mpr (Nat.pos_of_ne_zero hne)
    obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp hmem
    have hle := euclidNorm_le_maxRadius Y (Nat.le_of_lt (Finset.mem_range.mp hj))
    rw [hjz] at hle
    linarith
  have hpt := hpoint (cellCenter y) (by linarith)
  rw [hz0, Nat.cast_zero] at hpt
  have hW := hbra y hyb (by linarith)
  have hmod := hcm ε hε ((n : ℝ) + Real.sqrt d) (by linarith) (cellSet Y n) hDm hDsub y
    (toSpace (cellCenter y)) (by linarith) (by linarith)
  have hsplit := potential_split hd ε hDm hDb hb hball y
  rw [max_eq_right (by linarith), mul_zero, zero_add] at hsplit
  rw [hsplit] at hmod
  have hκ : 0 ≤ 1 + Real.log (1 + Real.sqrt d) := by
    have : 0 ≤ Real.log (1 + Real.sqrt d) := Real.log_nonneg (by linarith)
    linarith
  exact hx_probe_arith hCenv hγ (mul_nonneg hCcm hε) hκ (by linarith) hLΘ hpt hW hUp hmod
    (hx_log_shift d n hL1)

/-- Step 2 of Section 7.2: the probe bounds give the cap bound `|E ∩ B((b+w)u,t)| ≤ K₃ Θ t^{d-1}`
for every unit vector `u` and every `t ≥ w`; for `t > r/4` it follows from the mass bound. -/
private lemma hx_cap (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) {b w r Θ lg Cp Cm' K₃ : ℝ}
    (hsub : E ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w}) (hw1 : 1 ≤ w) (hr : 0 < r) (hbr : r / 2 ≤ b)
    (hlg : 0 ≤ lg) (hlgΘ : lg ≤ Θ) (hCm' : 0 ≤ Cm')
    (hmass : (volume E).toReal ≤ Cm' * r ^ (d - 1) * lg)
    (hK₃s : unitBallVolume d / (2 * ε) * 5 ^ d * (Cp + 2 * ε / unitBallVolume d) ≤ K₃)
    (hK₃m : Cm' * 4 ^ (d - 1) ≤ K₃)
    (hprobe : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t → t ≤ r / 4 →
      -(Cp * Θ) ≤ potential d ε E ((b + w + 4 * t) • u) ∧
      positivePotential d ε E ((b + w + 4 * t) • u) ≤ 2 * ε / unitBallVolume d * Θ) :
    ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t →
      volume (E ∩ Metric.ball ((b + w) • u) t) ≤ ENNReal.ofReal (K₃ * Θ * t ^ (d - 1)) := by
  intro u hu t ht
  have hΘ : 0 ≤ Θ := hlg.trans hlgΘ
  have ht0 : 0 < t := by linarith
  have htd : 0 ≤ t ^ (d - 1) := pow_nonneg ht0.le _
  have hK₃ : 0 ≤ K₃ := (mul_nonneg hCm' (pow_nonneg (by norm_num) _)).trans hK₃m
  have hfin : volume (E ∩ Metric.ball ((b + w) • u) t) ≠ ⊤ :=
    ((hEb.subset Set.inter_subset_left).measure_lt_top).ne
  rw [ENNReal.le_ofReal_iff_toReal_le hfin (mul_nonneg (mul_nonneg hK₃ hΘ) htd)]
  rcases le_or_gt t (r / 4) with htr | htr
  · obtain ⟨hlo, hhi⟩ := hprobe u hu t ht htr
    have h := cap_mass_of_probe hd hε hE hEb hsub (by linarith) ht0 (by linarith) hu hlo hhi
    calc (volume (E ∩ Metric.ball ((b + w) • u) t)).toReal
        ≤ unitBallVolume d / (2 * ε) * 5 ^ d * (Cp * Θ + 2 * ε / unitBallVolume d * Θ) *
            t ^ (d - 1) := h
      _ = unitBallVolume d / (2 * ε) * 5 ^ d * (Cp + 2 * ε / unitBallVolume d) *
            (Θ * t ^ (d - 1)) := by ring
      _ ≤ K₃ * (Θ * t ^ (d - 1)) := mul_le_mul_of_nonneg_right hK₃s (mul_nonneg hΘ htd)
      _ = K₃ * Θ * t ^ (d - 1) := by ring
  · have hEfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
    have hmono : (volume (E ∩ Metric.ball ((b + w) • u) t)).toReal ≤ (volume E).toReal :=
      ENNReal.toReal_mono hEfin (measure_mono Set.inter_subset_left)
    have hr0 : 0 ≤ r := hr.le
    have hr4 : r ^ (d - 1) ≤ 4 ^ (d - 1) * t ^ (d - 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hr0 (by linarith) _
    calc (volume (E ∩ Metric.ball ((b + w) • u) t)).toReal ≤ Cm' * r ^ (d - 1) * lg :=
          hmono.trans hmass
      _ ≤ Cm' * (4 ^ (d - 1) * t ^ (d - 1)) * Θ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hr4 hCm') hlgΘ hlg
            (mul_nonneg hCm' (mul_nonneg (pow_nonneg (by norm_num) _) htd))
      _ = Cm' * 4 ^ (d - 1) * (Θ * t ^ (d - 1)) := by ring
      _ ≤ K₃ * (Θ * t ^ (d - 1)) := mul_le_mul_of_nonneg_right hK₃m (mul_nonneg hΘ htd)
      _ = K₃ * Θ * t ^ (d - 1) := by ring

/-- Step 3 of Section 7.2: the envelope bound and the bound on `U_E^+` in the annulus bound the
largest local time beyond the inner radius by `C_env (2 + C_nf K₃) ((Θ w^{d-1})^{1/d} + Θ)`. -/
private lemma hx_outer_bound (hd : 1 ≤ d) {ε : ℝ} {Y : ℕ → Site d} {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin d))} {b w Θ K₃ Cenv Cnf : ℝ}
    (hRbw : maxRadius Y n ≤ b + w) (hRn : maxRadius Y n ≤ n)
    (hL : Real.log ((n : ℝ) + 2) ≤ 2 * Θ) (hΘ : 0 ≤ Θ) (hw : 0 ≤ w) (hK₃ : 1 ≤ K₃)
    (hCenv : 0 ≤ Cenv) (hCnf : 0 ≤ Cnf)
    (henv : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ 2 * n →
      (localTime Y n (cellCenter y) : ℝ) ≤ Cenv * (Real.log ((n : ℝ) + 2) +
        positivePotential d ε E y))
    (hnf : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ b + w →
      positivePotential d ε E y ≤
        Cnf * (K₃ * Θ * w ^ (d - 1)) ^ ((1 : ℝ) / d) + Cnf * (K₃ * Θ)) :
    (outerMax Y n b : ℝ) ≤ Cenv * (2 + Cnf * K₃) * ((Θ * w ^ (d - 1)) ^ ((1 : ℝ) / d) + Θ) := by
  have hΘw : 0 ≤ Θ * w ^ (d - 1) := mul_nonneg hΘ (pow_nonneg hw _)
  set X : ℝ := (Θ * w ^ (d - 1)) ^ ((1 : ℝ) / d) with hX_def
  have hX : 0 ≤ X := Real.rpow_nonneg hΘw _
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hK₃X : (K₃ * Θ * w ^ (d - 1)) ^ ((1 : ℝ) / d) ≤ K₃ * X := by
    rw [mul_assoc, Real.mul_rpow (by linarith) hΘw]
    apply mul_le_mul_of_nonneg_right _ hX
    calc K₃ ^ ((1 : ℝ) / d) ≤ K₃ ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hK₃
          rw [div_le_one hdpos]
          exact_mod_cast hd
      _ = K₃ := Real.rpow_one K₃
  have hRHS : 0 ≤ Cenv * (2 + Cnf * K₃) * (X + Θ) :=
    mul_nonneg (mul_nonneg hCenv (add_nonneg (by norm_num) (mul_nonneg hCnf (by linarith))))
      (by linarith)
  unfold outerMax
  rcases Finset.eq_empty_or_nonempty
      ((departureRange Y n).filter (fun z => b ≤ euclidNorm z)) with hs | hs
  · rw [hs, Finset.sup_empty, Nat.bot_eq_zero, Nat.cast_zero]
    exact hRHS
  · obtain ⟨z, hz, hsup⟩ := Finset.exists_mem_eq_sup _ hs (localTime Y n)
    rw [hsup]
    obtain ⟨hzA, hzb⟩ := Finset.mem_filter.mp hz
    have hzR : euclidNorm z ≤ maxRadius Y n := by
      obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp hzA
      rw [← hjz]
      exact euclidNorm_le_maxRadius Y (Nat.le_of_lt (Finset.mem_range.mp hj))
    have hnz : ‖toSpace z‖ = euclidNorm z := norm_toSpace z
    have hcc : cellCenter (toSpace z) = z :=
      (eq_cellCenter_of_mem_cell (toSpace_mem_cell z)).symm
    have h1 := henv (toSpace z) (by rw [hnz]; exact hzb) (by rw [hnz]; linarith)
    have h2 := hnf (toSpace z) (by rw [hnz]; exact hzb) (by rw [hnz]; linarith)
    rw [hcc] at h1
    have h4 := mul_le_mul_of_nonneg_left hK₃X hCnf
    have h3 : Real.log ((n : ℝ) + 2) + positivePotential d ε E (toSpace z) ≤
        (2 + Cnf * K₃) * (X + Θ) := by
      linarith
    calc (localTime Y n z : ℝ)
        ≤ Cenv * (Real.log ((n : ℝ) + 2) + positivePotential d ε E (toSpace z)) := h1
      _ ≤ Cenv * ((2 + Cnf * K₃) * (X + Θ)) := mul_le_mul_of_nonneg_left h3 hCenv
      _ = Cenv * (2 + Cnf * K₃) * (X + Θ) := by ring

/-- Steps 1 to 4 of Section 7.2 for a fixed path at a fixed large time `n`: the curvature size
`Θ = log n + r⁻¹ sup_y ∫_E |v-y|^{2-d}` satisfies `log n ≤ Θ ≤ K_θ (w²/r + log n)` and bounds the
largest local time beyond the inner radius. -/
private lemma hx_path (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) {C₁ Cm' Cenv Cnf Ccm Kθ K₃ : ℝ}
    (hCm' : 0 < Cm') (hCenv : 0 < Cenv) (hCnf : 0 < Cnf) (hCcm : 0 ≤ Ccm)
    (hK₃s : unitBallVolume d / (2 * ε) * 5 ^ d *
      ((max C₁ 0 * (Real.sqrt (2 * Cenv * (2 + 2 * ε / unitBallVolume d)) + 2) +
        2 * (Ccm * ε) * (1 + Real.log (1 + Real.sqrt d))) + 2 * ε / unitBallVolume d) ≤ K₃)
    (hK₃m : Cm' * 4 ^ (d - 1) ≤ K₃) (hK₃2 : 2 ≤ K₃)
    (hKθ : ∀ Θ lg r w : ℝ, 0 < lg → lg ≤ Θ → 0 < r →
      Θ ≤ lg + (((d : ℝ) - 2) * unitBallVolume d / 2 * w ^ 2 + ((d : ℝ) - 1) *
        ((K₃ * 3 ^ (d - 1) * Θ) ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
          (Cm' * r ^ (d - 1) * lg) ^ ((1 : ℝ) / ((d : ℝ) - 1)))) / r →
      Θ ≤ Kθ * (w ^ 2 / r + lg))
    (hnf : ∀ w b lam : ℝ, 1 ≤ w → w ≤ b → 1 ≤ lam →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D →
        D ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w} →
        (∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t →
          volume (D ∩ Metric.ball ((b + w) • u) t) ≤ ENNReal.ofReal (lam * t ^ (d - 1))) →
        (∀ y : EuclideanSpace ℝ (Fin d), ∫ v in D, ‖v - y‖ ^ (2 - (d : ℝ)) ≤ lam * b) →
        ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ b + w →
          positivePotential d ε D y ≤ Cnf * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) + Cnf * lam)
    (hcm : ∀ ε : ℝ, 0 ≤ ε → ∀ R : ℝ, 1 ≤ R →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → D ⊆ Metric.ball 0 R →
      ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R → ‖y - z‖ ≤ Real.sqrt d →
        |potential d ε D y - potential d ε D z| ≤ Ccm * ε * Real.log (R + 2))
    {Y : ℕ → Site d} {n : ℕ} (hj : ∀ j, euclidNorm (Y j) ≤ j)
    (hpoint : ∀ x : Site d, euclidNorm x ≤ 3 * n →
      |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
        C₁ * (Real.sqrt (braSum Y n x * Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2)))
    (henv : ∀ y : EuclideanSpace ℝ (Fin d), innerRadius Y n ≤ ‖y‖ → ‖y‖ ≤ 2 * n →
      braSum Y n (cellCenter y) ≤ Cenv * (Real.log ((n : ℝ) + 2) +
        positivePotential d ε (cellSet Y n \ Metric.ball 0 (innerRadius Y n)) y) ∧
      (localTime Y n (cellCenter y) : ℝ) ≤ Cenv * (Real.log ((n : ℝ) + 2) +
        positivePotential d ε (cellSet Y n \ Metric.ball 0 (innerRadius Y n)) y))
    (hr : 0 < radius d ε n) (hbr1 : radius d ε n / 2 ≤ innerRadius Y n)
    (hbr2 : innerRadius Y n ≤ 2 * radius d ε n) (h4r : 4 * radius d ε n ≤ n)
    (hdn : (d : ℝ) ≤ n) (hlg1 : 1 ≤ Real.log n)
    (hLlg : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n)
    (hmass : (volume (cellSet Y n \ Metric.ball 0 (innerRadius Y n))).toReal ≤
      Cm' * radius d ε n ^ (d - 1) * Real.log n)
    (hw : maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d ≤ radius d ε n / 8) :
    ∃ Θ : ℝ, Real.log n ≤ Θ ∧
      Θ ≤ Kθ * ((maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) ^ 2 / radius d ε n +
        Real.log n) ∧
      (outerMax Y n (innerRadius Y n) : ℝ) ≤ Cenv * (2 + Cnf * K₃) *
        ((Θ * (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) ^ (d - 1)) ^ ((1 : ℝ) / d) +
          Θ) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hs1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd1)
  have hRn : maxRadius Y n ≤ n := Finset.sup'_le _ _ fun j hj' =>
    (hj j).trans (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj'))
  have hbR : innerRadius Y n ≤ maxRadius Y n + Real.sqrt d / 2 := innerRadius_le hd1 Y n
  have hball := ball_innerRadius_subset hd1 Y n
  have hsub := sdiff_subset_annulus hd1 Y n
  set b := innerRadius Y n with hb_def
  set R := maxRadius Y n with hR_def
  set r := radius d ε n with hr_def
  set lg := Real.log n with hlg_def
  set L := Real.log ((n : ℝ) + 2) with hL_def
  set w := R - b + 2 * Real.sqrt d with hw_def
  set E := cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b with hE_def
  have hb0 : 0 < b := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hwb : w ≤ b := by linarith
  have hEm : MeasurableSet E :=
    (CERW.Support.Occupation.measurableSet_cellSet Y n).diff Metric.isOpen_ball.measurableSet
  have hEb : Bornology.IsBounded E :=
    (Metric.isBounded_ball.subset (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n)).subset
      Set.sdiff_subset
  have hn0 : (0 : ℝ) < n := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hL1 : 1 ≤ L := hlg1.trans (Real.log_le_log hn0 (by linarith))
  -- the curvature size `Θ`
  set I : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ∫ v in E, ‖v - y‖ ^ (2 - (d : ℝ))
    with hI_def
  have hbdd : BddAbove (Set.range I) := integral_rpow_bddAbove hd hEm hEb
  have hI0 : ∀ y, 0 ≤ I y := fun y =>
    setIntegral_nonneg hEm fun v _ => Real.rpow_nonneg (norm_nonneg _) _
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = sSup (Set.range I) := ⟨_, rfl⟩
  have hIS : ∀ y, I y ≤ S := fun y => hS ▸ le_csSup hbdd (Set.mem_range_self y)
  have hS0 : 0 ≤ S := (hI0 0).trans (hIS 0)
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : ℝ, Θ = lg + S / r := ⟨_, rfl⟩
  have hlgΘ : lg ≤ Θ := by
    rw [hΘ]
    linarith [div_nonneg hS0 hr.le]
  have hΘ0 : 0 ≤ Θ := by linarith
  have hIΘ : ∀ y, I y ≤ r * Θ := by
    intro y
    have e : r * Θ = r * lg + S := by
      rw [hΘ, mul_add, mul_div_cancel₀ S hr.ne']
    have : 0 ≤ r * lg := mul_nonneg hr.le (by linarith)
    linarith [hIS y]
  have hLΘ : L ≤ 2 * Θ := by linarith
  -- Steps 1 and 2: the probes and the cap bound
  have hprobe : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t → t ≤ r / 4 →
      -((max C₁ 0 * (Real.sqrt (2 * Cenv * (2 + 2 * ε / unitBallVolume d)) + 2) +
        2 * (Ccm * ε) * (1 + Real.log (1 + Real.sqrt d))) * Θ) ≤
        potential d ε E ((b + w + 4 * t) • u) ∧
      positivePotential d ε E ((b + w + 4 * t) • u) ≤ 2 * ε / unitBallVolume d * Θ := by
    intro u hu t ht htr
    have hnorm : ‖(b + w + 4 * t) • u‖ = b + w + 4 * t := by
      rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hUp : positivePotential d ε E ((b + w + 4 * t) • u) ≤ 2 * ε / unitBallVolume d * Θ :=
      (positivePotential_le_of_outside hd2 hε.le hEm hEb hb0 hsub
        (by rw [hnorm]; linarith)).trans
        (hx_outside_arith hε.le hω hb0 hΘ0 (hIΘ _) (by linarith))
    refine ⟨?_, hUp⟩
    have h := hx_probe_potential hd2 hε.le hCenv.le hCcm (by positivity) hcm hb0 hdn hball hL1
      hLΘ hpoint (fun y hy1 hy2 => (henv y hy1 hy2).1) (y := (b + w + 4 * t) • u)
      (by rw [hnorm]; linarith) (by rw [hnorm]; linarith) (by rw [hnorm]; linarith) hUp
    exact neg_le_of_abs_le h
  have hcap := hx_cap hd2 hε hEm hEb hsub hw1 hr hbr1 (by linarith) hlgΘ hCm'.le hmass hK₃s
    hK₃m hprobe
  -- Step 3: `lem:near-far` and the envelope
  have hlam1 : 1 ≤ K₃ * Θ := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hintb : ∀ y, I y ≤ K₃ * Θ * b := by
    intro y
    have h2 : 2 * (Θ * b) ≤ K₃ * (Θ * b) := mul_le_mul_of_nonneg_right hK₃2 (mul_nonneg hΘ0 hb0.le)
    have h3 : r * Θ ≤ 2 * b * Θ := mul_le_mul_of_nonneg_right (by linarith) hΘ0
    calc I y ≤ r * Θ := hIΘ y
      _ ≤ K₃ * Θ * b := by linarith
  have hU := hnf w b (K₃ * Θ) hw1 hwb hlam1 E hEm hsub hcap hintb
  have hmain := hx_outer_bound hd1 (by linarith) hRn hLΘ hΘ0 (by linarith) (by linarith)
    hCenv.le hCnf.le (fun y hy1 hy2 => (henv y hy1 hy2).2) hU
  -- Step 4: the bound on `Θ`
  have hloc : ∀ (y : EuclideanSpace ℝ (Fin d)) (t : ℝ), w ≤ t →
      (volume (E ∩ Metric.ball y t)).toReal ≤ K₃ * Θ * 3 ^ (d - 1) * t ^ (d - 1) :=
    fun y t ht => local_mass_of_cap hd1 hsub (by linarith) hcap y ht (by linarith)
  have hm : 0 < Cm' * r ^ (d - 1) * lg := mul_pos (mul_pos hCm' (pow_pos hr _)) (by linarith)
  have hlam : 0 < K₃ * Θ * 3 ^ (d - 1) := mul_pos (by linarith) (pow_pos (by norm_num) _)
  have hSle : S ≤ ((d : ℝ) - 2) * unitBallVolume d / 2 * w ^ 2 + ((d : ℝ) - 1) *
      ((K₃ * 3 ^ (d - 1) * Θ) ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
        (Cm' * r ^ (d - 1) * lg) ^ ((1 : ℝ) / ((d : ℝ) - 1))) := by
    rw [hS]
    refine csSup_le (Set.range_nonempty _) (Set.forall_mem_range.2 fun y => ?_)
    have h := integral_rpow_le_of_local_mass hd hEm hEb (by linarith) hlam hm hloc hmass y
    rw [show K₃ * Θ * 3 ^ (d - 1) = K₃ * 3 ^ (d - 1) * Θ by ring] at h
    calc I y ≤ _ := h
      _ = _ := by ring
  refine ⟨Θ, hlgΘ, hKθ Θ lg r w (by linarith) hlgΘ hr ?_, hmain⟩
  calc Θ = lg + S / r := hΘ
    _ ≤ _ := by gcongr

/-- Steps 1 to 4 of Section 7.2: with `w = R_out - b + 2√d` at most `r/8`, there is a
curvature size `Θ ≥ log n` with `Θ ≤ C (w²/r + log n)` such that the largest local time outside
the inner ball is at most `C ((Θ w^{d-1})^{1/d} + Θ)`. -/
private theorem high_exterior (hd : 3 ≤ d) (hN : NewtonConv d) (hnear : near_far) {ε : ℝ}
    (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) (C₀ C₁ Cin Cm : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      PathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n → MassOK d ε Cm Y n →
      maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d ≤ radius d ε n / 8 →
      ∃ Θ : ℝ, Real.log n ≤ Θ ∧
        Θ ≤ K * ((maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) ^ 2 / radius d ε n +
          Real.log n) ∧
        (outerMax Y n (innerRadius Y n) : ℝ) ≤ K * ((Θ * (maxRadius Y n - innerRadius Y n +
          2 * Real.sqrt d) ^ (d - 1)) ^ ((1 : ℝ) / d) + Θ) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨Cenv, hCenv, nenv, henv⟩ := envelope_high hd hN hε C₁
  obtain ⟨Cnf, hCnf, hnf⟩ := hnear hd2 ε hε hεd
  obtain ⟨Ccm, hCcm, hcm⟩ := CERW.Support.Geometry.exists_potential_cell_modulus hd2
  set Cm' : ℝ := max Cm 1 with hCm'_def
  have hCm' : 0 < Cm' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set Cp : ℝ := max C₁ 0 * (Real.sqrt (2 * Cenv * (2 + 2 * ε / unitBallVolume d)) + 2) +
    2 * (Ccm * ε) * (1 + Real.log (1 + Real.sqrt d)) with hCp_def
  have hCp : 0 ≤ Cp := by
    have h1 : 0 ≤ max C₁ 0 := le_max_right _ _
    have h2 : 0 ≤ Real.log (1 + Real.sqrt d) :=
      Real.log_nonneg (by linarith [Real.sqrt_nonneg (d : ℝ)])
    rw [hCp_def]
    positivity
  set Ks : ℝ := unitBallVolume d / (2 * ε) * 5 ^ d * (Cp + 2 * ε / unitBallVolume d)
    with hKs_def
  have hKs : 0 ≤ Ks := by
    rw [hKs_def]
    positivity
  have hCm4 : 0 ≤ Cm' * 4 ^ (d - 1) := by positivity
  set K₃ : ℝ := Ks + Cm' * 4 ^ (d - 1) + 2 with hK₃_def
  have hK₃s : Ks ≤ K₃ := by linarith
  have hK₃m : Cm' * 4 ^ (d - 1) ≤ K₃ := by linarith
  have hK₃2 : 2 ≤ K₃ := by linarith
  obtain ⟨Kθ, hKθpos, hKθ⟩ := hx_theta_arith hd (a := K₃ * 3 ^ (d - 1)) (c := Cm')
    (c₁ := ((d : ℝ) - 2) * unitBallVolume d / 2) (mul_pos (by linarith) (pow_pos (by norm_num) _))
    hCm'
    (div_nonneg (mul_nonneg (by linarith) hω.le) (by norm_num))
  obtain ⟨n₁, hn₁⟩ := hx_scales hd1 hε (2 * max Cin 0)
  have hKb : 0 ≤ Cenv * (2 + Cnf * K₃) := by positivity
  refine ⟨Kθ + Cenv * (2 + Cnf * K₃), by linarith, max n₁ (max nenv d), ?_⟩
  intro Y n hn hP hI hM hw
  have hn₁' : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnenv : nenv ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hdn : d ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨hr, hKr, h4r⟩ := hn₁ n hn₁'
  obtain ⟨hlg1, hLlg⟩ := hx_log_facts (n := n) (by omega)
  have hlg0 : 0 ≤ Real.log n := by linarith
  have hj := CERW.Support.Occupation.euclidNorm_le_of_steps Y hP.start hP.step
  have hq : qrate d ε n = Real.log n / radius d ε n := by
    rw [qrate, if_neg (by omega)]
  have hrq : radius d ε n * qrate d ε n = Real.log n := by
    rw [hq]
    field_simp
  have hin : |innerRadius Y n - radius d ε n| ≤ max Cin 0 * Real.log n := by
    have h := hI.1
    rw [mul_assoc, hrq] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlg0)
  obtain ⟨hin1, hin2⟩ := abs_le.mp hin
  have hmass : (volume (cellSet Y n \ Metric.ball 0 (innerRadius Y n))).toReal ≤
      Cm' * radius d ε n ^ (d - 1) * Real.log n := by
    have h : (volume (cellSet Y n \ Metric.ball 0 (innerRadius Y n))).toReal ≤
        Cm * radius d ε n ^ d * qrate d ε n := hM
    have hpow : radius d ε n ^ d = radius d ε n ^ (d - 1) * radius d ε n := by
      rw [← pow_succ]
      congr 1
      omega
    have e : Cm * radius d ε n ^ d * qrate d ε n = Cm * (radius d ε n ^ (d - 1) * Real.log n) := by
      rw [hpow, hq]
      field_simp
    have hnn : 0 ≤ radius d ε n ^ (d - 1) * Real.log n := mul_nonneg (pow_nonneg hr.le _) hlg0
    calc _ ≤ Cm * radius d ε n ^ d * qrate d ε n := h
      _ = Cm * (radius d ε n ^ (d - 1) * Real.log n) := e
      _ ≤ Cm' * (radius d ε n ^ (d - 1) * Real.log n) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
      _ = Cm' * radius d ε n ^ (d - 1) * Real.log n := by ring
  have henv' := henv Y n hnenv hj hP.point (innerRadius Y n) (innerRadius_nonneg Y n)
    (ball_innerRadius_subset hd1 Y n)
  obtain ⟨Θ, h1, h2, h3⟩ := hx_path hd hε hCm' hCenv hCnf hCcm hK₃s hK₃m hK₃2 hKθ
    hnf hcm hj hP.point henv' hr (by linarith) (by linarith) h4r
    (by exact_mod_cast hdn) hlg1 hLlg hmass hw
  have hwr : 0 ≤ (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) ^ 2 / radius d ε n +
      Real.log n := add_nonneg (div_nonneg (sq_nonneg _) hr.le) hlg0
  have hX : 0 ≤ (Θ * (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) ^ (d - 1)) ^
      ((1 : ℝ) / d) + Θ := by
    have hw0 : 0 ≤ maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d := by
      have := innerRadius_le hd1 Y n
      have : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
      linarith
    have hΘ0 : 0 ≤ Θ := hlg0.trans h1
    exact add_nonneg (Real.rpow_nonneg (mul_nonneg hΘ0 (pow_nonneg hw0 _)) _) hΘ0
  refine ⟨Θ, h1, ?_, ?_⟩
  · exact h2.trans (mul_le_mul_of_nonneg_right (by linarith) hwr)
  · exact h3.trans (mul_le_mul_of_nonneg_right (by linarith) hX)

/-- Weighted Young inequality in the form used in Step 5: if `a ^ (m + 1) = Θ w ^ m`, then
`lg * a ≤ δ * w + lg ^ (m + 1) * Θ / δ ^ m` for every `δ > 0`. -/
private lemma ar_young (m : ℕ) {a w lg Θ δ : ℝ} (hlg : 0 < lg) (hΘ : 0 ≤ Θ) (hw : 0 ≤ w)
    (ha0 : 0 ≤ a) (hδ : 0 < δ) (ha : a ^ (m + 1) = Θ * w ^ m) :
    lg * a ≤ δ * w + lg ^ (m + 1) * Θ / δ ^ m := by
  by_contra h
  rw [not_le] at h
  have hδw : 0 ≤ δ * w := mul_nonneg hδ.le hw
  have hT : 0 ≤ lg ^ (m + 1) * Θ / δ ^ m := by positivity
  have hlt : δ * w < lg * a := by linarith
  have hapos : 0 < a := by
    rcases ha0.lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, mul_zero] at hlt
      exact absurd hlt (not_lt.2 hδw)
  have hwle : w ≤ lg * a / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  have hpow : w ^ m ≤ (lg * a / δ) ^ m := pow_le_pow_left₀ hw hwle m
  have hmul : a ^ m * a ≤ a ^ m * (Θ * lg ^ m / δ ^ m) := by
    calc a ^ m * a = Θ * w ^ m := by rw [← pow_succ, ha]
      _ ≤ Θ * (lg * a / δ) ^ m := mul_le_mul_of_nonneg_left hpow hΘ
      _ = a ^ m * (Θ * lg ^ m / δ ^ m) := by rw [div_pow, mul_pow]; ring
  have hale : a ≤ Θ * lg ^ m / δ ^ m :=
    le_of_mul_le_mul_left hmul (pow_pos hapos m)
  have hfin : lg * a ≤ lg ^ (m + 1) * Θ / δ ^ m := by
    calc lg * a ≤ lg * (Θ * lg ^ m / δ ^ m) := mul_le_mul_of_nonneg_left hale hlg.le
      _ = lg ^ (m + 1) * Θ / δ ^ m := by ring
  linarith

/-- The final arithmetic of Step 5 of Section 7.2. -/
private theorem arith_high (hd : 3 ≤ d) (K₁ K₂ K₃ : ℝ) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hK₃ : 0 < K₃) :
    ∃ K : ℝ, 0 < K ∧ ∀ (lg r w L Θ : ℝ), 1 ≤ lg → 0 < r → 0 ≤ w → 0 ≤ L →
      w ≤ K₁ * lg * (1 + L) →
      L ≤ K₂ * ((Θ * w ^ (d - 1)) ^ ((1 : ℝ) / d) + Θ) →
      lg ≤ Θ → Θ ≤ K₃ * (w ^ 2 / r + lg) →
      K * lg ^ d * w ≤ r → w ≤ K * lg ^ (d + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hc : 0 < K₁ * K₂ := mul_pos hK₁ hK₂
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = K₁ + K₁ * K₂ * (2 * (K₁ * K₂)) ^ m + K₁ * K₂ := ⟨_, rfl⟩
  have hA : 0 < A := by rw [hAdef]; positivity
  refine ⟨4 * A * K₃, by positivity, ?_⟩
  intro lg r w L Θ hlg hr hw hL h1 h2 h3 h4 h5
  have hlg0 : 0 < lg := by linarith
  have hΘ1 : 1 ≤ Θ := hlg.trans h3
  have hΘ0 : 0 ≤ Θ := by linarith
  have ha0 : 0 ≤ (Θ * w ^ (m + 1 - 1)) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  generalize hadef : (Θ * w ^ (m + 1 - 1)) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) = a at ha0 h2
  have ha : a ^ (m + 1) = Θ * w ^ m := by
    rw [← hadef, one_div, Real.rpow_inv_natCast_pow (by positivity) (Nat.succ_ne_zero m)]
    simp
  have hc2 : 0 < 2 * (K₁ * K₂) := by positivity
  have hy := ar_young m hlg0 hΘ0 hw ha0 (inv_pos.2 hc2) ha
  have hy2 : K₁ * K₂ * (lg * a) ≤ w / 2 + K₁ * K₂ * (2 * (K₁ * K₂)) ^ m * (lg ^ (m + 1) * Θ) := by
    calc K₁ * K₂ * (lg * a)
        ≤ K₁ * K₂ * ((2 * (K₁ * K₂))⁻¹ * w + lg ^ (m + 1) * Θ / ((2 * (K₁ * K₂))⁻¹) ^ m) :=
          mul_le_mul_of_nonneg_left hy hc.le
      _ = w / 2 + K₁ * K₂ * (2 * (K₁ * K₂)) ^ m * (lg ^ (m + 1) * Θ) := by
          rw [inv_pow, div_inv_eq_mul]
          field_simp
  have hL2 : K₁ * lg * L ≤ K₁ * K₂ * (lg * a) + K₁ * K₂ * (lg * Θ) := by
    calc K₁ * lg * L ≤ K₁ * lg * (K₂ * (a + Θ)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = K₁ * K₂ * (lg * a) + K₁ * K₂ * (lg * Θ) := by ring
  have hlgm : 1 ≤ lg ^ m := one_le_pow₀ hlg
  have hlgle : lg ≤ lg ^ (m + 1) := by
    calc lg = lg * 1 := (mul_one lg).symm
      _ ≤ lg * lg ^ m := mul_le_mul_of_nonneg_left hlgm hlg0.le
      _ = lg ^ (m + 1) := (pow_succ' lg m).symm
  have hP1 : lg ≤ lg ^ (m + 1) * Θ := by
    calc lg ≤ lg ^ (m + 1) := hlgle
      _ = lg ^ (m + 1) * 1 := (mul_one _).symm
      _ ≤ lg ^ (m + 1) * Θ := mul_le_mul_of_nonneg_left hΘ1 (by positivity)
  have hP2 : lg * Θ ≤ lg ^ (m + 1) * Θ := mul_le_mul_of_nonneg_right hlgle hΘ0
  have hw3 : w ≤ 2 * A * (lg ^ (m + 1) * Θ) := by
    have e1 : K₁ * lg ≤ K₁ * (lg ^ (m + 1) * Θ) := mul_le_mul_of_nonneg_left hP1 hK₁.le
    have e2 : K₁ * K₂ * (lg * Θ) ≤ K₁ * K₂ * (lg ^ (m + 1) * Θ) :=
      mul_le_mul_of_nonneg_left hP2 hc.le
    have e3 : K₁ * lg * (1 + L) = K₁ * lg + K₁ * lg * L := by ring
    have e4 : A * (lg ^ (m + 1) * Θ) = K₁ * (lg ^ (m + 1) * Θ)
        + K₁ * K₂ * (2 * (K₁ * K₂)) ^ m * (lg ^ (m + 1) * Θ)
        + K₁ * K₂ * (lg ^ (m + 1) * Θ) := by rw [hAdef]; ring
    linarith
  have hQ : lg ^ (m + 1) * (w ^ 2 / r) * (4 * A * K₃) ≤ w := by
    have e : lg ^ (m + 1) * (w ^ 2 / r) * (4 * A * K₃)
        = w * (4 * A * K₃ * lg ^ (m + 1) * w) / r := by
      field_simp
    rw [e, div_le_iff₀ hr]
    exact mul_le_mul_of_nonneg_left h5 hw
  have hw4 : w ≤ 2 * A * (lg ^ (m + 1) * (K₃ * (w ^ 2 / r + lg))) :=
    calc w ≤ 2 * A * (lg ^ (m + 1) * Θ) := hw3
      _ ≤ 2 * A * (lg ^ (m + 1) * (K₃ * (w ^ 2 / r + lg))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (by positivity))
            (by positivity)
  have e5 : 2 * A * (lg ^ (m + 1) * (K₃ * (w ^ 2 / r + lg)))
      = lg ^ (m + 1) * (w ^ 2 / r) * (4 * A * K₃) / 2 + 2 * A * K₃ * (lg ^ (m + 1) * lg) := by
    ring
  have e6 : 4 * A * K₃ * lg ^ (m + 1 + 1) = 2 * (2 * A * K₃ * (lg ^ (m + 1) * lg)) := by
    rw [pow_succ _ (m + 1)]
    ring
  rw [e5] at hw4
  rw [e6]
  linarith
/-! ### The planar exterior analysis -/

section

open Filter LatticeProb

/-- `r_n³ = 3 n / (4 ε ω₂)` in the plane. -/
private lemma pl_radius_cube {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    radius 2 ε n ^ 3 = 3 / (4 * ε * unitBallVolume 2) * n := by
  have hω := unitBallVolume_pos 2
  have hx : 0 ≤ (((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε * unitBallVolume 2) := by
    positivity
  rw [radius, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num
  ring

/-- For large `n`: `16 ≤ n`, `4 ≤ log n`, `(log n)^5 ≤ η r_n` and `r_n ≤ n/8`. -/
private lemma pl_eventually {ε : ℝ} (hε : 0 < ε) {η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 16 ≤ (n : ℝ) ∧ 4 ≤ Real.log n ∧
      Real.log n ^ 5 ≤ η * radius 2 ε n ∧ radius 2 ε n ≤ n / 8 := by
  have hω := unitBallVolume_pos 2
  set c : ℝ := 3 / (4 * ε * unitBallVolume 2) with hc_def
  have hc : 0 < c := by positivity
  have h1 : ∀ᶠ n : ℕ in atTop, (16 + 512 * c : ℝ) ≤ n :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have h2 : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  have h3 : ∀ᶠ n : ℕ in atTop, Real.log n ^ 15 / (1 * (n : ℝ) + 0) < η ^ 3 * c :=
    ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 15 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).eventually_lt_const (by positivity)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hn1, hn2, hn3⟩ := hn₀ n hn
  have hr3 := pl_radius_cube hε n
  have hr0 : 0 ≤ radius 2 ε n := Real.rpow_nonneg (by positivity) _
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog0 : 0 ≤ Real.log n := by linarith
  refine ⟨by linarith, hn2, ?_, ?_⟩
  · have h15 : Real.log n ^ 15 ≤ η ^ 3 * c * n := by
      rw [one_mul, add_zero, div_lt_iff₀ hnpos] at hn3
      exact hn3.le
    rw [← pow_le_pow_iff_left₀ (pow_nonneg hlog0 5) (by positivity) three_ne_zero]
    calc (Real.log n ^ 5) ^ 3 = Real.log n ^ 15 := by ring
      _ ≤ η ^ 3 * c * n := h15
      _ = (η * radius 2 ε n) ^ 3 := by rw [mul_pow, hr3]; ring
  · rw [← pow_le_pow_iff_left₀ hr0 (by positivity) three_ne_zero, hr3]
    have h512 : 512 * c ≤ (n : ℝ) ^ 2 := by nlinarith
    calc c * n = (512 * c) * n / 512 := by ring
      _ ≤ (n : ℝ) ^ 2 * n / 512 := by gcongr
      _ = ((n : ℝ) / 8) ^ 3 := by ring

/-- `a (1 + a)^{-2} ≤ (1 + a)^{-1}` for `a ≥ 0`. -/
private lemma pl_mul_rpow_neg_two_le {a : ℝ} (ha : 0 ≤ a) :
    a * (1 + a) ^ (-2 : ℝ) ≤ (1 + a) ^ (-1 : ℝ) := by
  have h1 : 0 < 1 + a := by linarith
  have hk : 0 ≤ (1 + a) ^ (-2 : ℝ) := Real.rpow_nonneg h1.le _
  calc a * (1 + a) ^ (-2 : ℝ) ≤ (1 + a) * (1 + a) ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hk
    _ = (1 + a) ^ (1 : ℝ) * (1 + a) ^ (-2 : ℝ) := by rw [Real.rpow_one]
    _ = (1 + a) ^ (-1 : ℝ) := by rw [← Real.rpow_add h1]; norm_num

/-- The bracket sum at `x` from a bound `ℓ_n(z) ≤ c |z - x| + A` on the local times, the
packing bound and the logarithmic lattice sum: `W_x ≤ K (c (2ρ + 1) + A log(R + 2))`. -/
private lemma pl_braSum_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (Y : ℕ → Site 2) (n : ℕ) (x : Site 2) (c A ρ R : ℝ), 0 ≤ c → 0 ≤ A →
      0 ≤ ρ → 1 ≤ R → departureRange Y n ⊆ ballFinset 2 ρ →
      (∀ z ∈ departureRange Y n, euclidNorm (z - x) ≤ R) →
      (∀ z ∈ departureRange Y n, (localTime Y n z : ℝ) ≤ c * euclidNorm (z - x) + A) →
      braSum Y n x ≤ K * (c * (2 * ρ + 1) + A * Real.log (R + 2)) := by
  obtain ⟨Cp, hCp, hpack⟩ :=
    CERW.Generic.Lattice.sum_rpow_one_sub_le_card_rpow (d := 2) (by norm_num)
  obtain ⟨C₂, hC₂, hlog⟩ := CERW.Generic.Lattice.sum_finset_rpow_neg_le_log (d := 2) (by norm_num)
  refine ⟨Cp + C₂, by positivity, ?_⟩
  intro Y n x c A ρ R hc hA hρ hR hball hdist hloc
  set S := departureRange Y n with hS
  have hk : ∀ z : Site 2, 0 ≤ (1 + euclidNorm (z - x)) ^ (-2 : ℝ) :=
    fun z => Real.rpow_nonneg (by linarith [euclidNorm_nonneg (z - x)]) _
  have hbra : braSum Y n x =
      ∑ z ∈ S, (localTime Y n z : ℝ) * (1 + euclidNorm (z - x)) ^ (-2 : ℝ) := by
    rw [braSum, CERW.Support.LocalTime.sum_range_eq_sum_localTime Y n
      (fun z => (1 + euclidNorm (z - x)) ^ (2 - 2 * ((2 : ℕ) : ℝ)))]
    norm_num [hS]
  have hterm : ∀ z ∈ S, (localTime Y n z : ℝ) * (1 + euclidNorm (z - x)) ^ (-2 : ℝ) ≤
      c * (1 + euclidNorm (z - x)) ^ (1 - ((2 : ℕ) : ℝ)) +
        A * (1 + euclidNorm (z - x)) ^ (-((2 : ℕ) : ℝ)) := by
    intro z hz
    have h1 := pl_mul_rpow_neg_two_le (euclidNorm_nonneg (z - x))
    have e1 : (1 : ℝ) - ((2 : ℕ) : ℝ) = -1 := by norm_num
    have e2 : -((2 : ℕ) : ℝ) = -2 := by norm_num
    rw [e1, e2]
    calc (localTime Y n z : ℝ) * (1 + euclidNorm (z - x)) ^ (-2 : ℝ)
        ≤ (c * euclidNorm (z - x) + A) * (1 + euclidNorm (z - x)) ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_right (hloc z hz) (hk z)
      _ = c * (euclidNorm (z - x) * (1 + euclidNorm (z - x)) ^ (-2 : ℝ)) +
            A * (1 + euclidNorm (z - x)) ^ (-2 : ℝ) := by ring
      _ ≤ c * (1 + euclidNorm (z - x)) ^ (-1 : ℝ) + A * (1 + euclidNorm (z - x)) ^ (-2 : ℝ) := by
          gcongr
  have hcard : (S.card : ℝ) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) ≤ 2 * ρ + 1 := by
    have h1 : (S.card : ℝ) ≤ (2 * ρ + 1) ^ 2 := by
      calc (S.card : ℝ) ≤ ((ballFinset 2 ρ).card : ℝ) := by exact_mod_cast Finset.card_le_card hball
        _ ≤ (2 * ρ + 1) ^ 2 := card_ballFinset_le 2 hρ
    calc (S.card : ℝ) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) ≤ ((2 * ρ + 1) ^ 2) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) h1 (by norm_num)
      _ = 2 * ρ + 1 := by
          rw [show (1 : ℝ) / ((2 : ℕ) : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
            Real.sqrt_sq (by linarith)]
  have hsum1 := (hpack S x).trans (mul_le_mul_of_nonneg_left hcard hCp.le)
  have hsum2 := hlog S x R hR hdist
  have hL : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  rw [hbra]
  calc ∑ z ∈ S, (localTime Y n z : ℝ) * (1 + euclidNorm (z - x)) ^ (-2 : ℝ)
      ≤ ∑ z ∈ S, (c * (1 + euclidNorm (z - x)) ^ (1 - ((2 : ℕ) : ℝ)) +
        A * (1 + euclidNorm (z - x)) ^ (-((2 : ℕ) : ℝ))) := Finset.sum_le_sum hterm
    _ = c * ∑ z ∈ S, (1 + euclidNorm (z - x)) ^ (1 - ((2 : ℕ) : ℝ)) +
          A * ∑ z ∈ S, (1 + euclidNorm (z - x)) ^ (-((2 : ℕ) : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ c * (Cp * (2 * ρ + 1)) + A * (C₂ * Real.log (R + 2)) := by gcongr
    _ ≤ (Cp + C₂) * (c * (2 * ρ + 1) + A * Real.log (R + 2)) := by
        have h1 : 0 ≤ c * (2 * ρ + 1) := by positivity
        have h2 : 0 ≤ A * Real.log (R + 2) := mul_nonneg hA hL
        nlinarith


/-- Step 1 of Section 7.3: if `ℓ_n(z) ≤ 4ε (r - |z|)_+ + a₁` on the departure range and
`|b - r| ≤ a₂`, then for `b ≤ |x| ≤ 3n` the bracket sum satisfies
`W_x ≤ K (4ε (2ρ + 1) + (4ε a₂ + a₁) log(4n + 2))`. -/
private lemma pl_braSum_le_of_cone {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Y : ℕ → Site 2) (n : ℕ) (r b ρ a₁ a₂ : ℝ), 0 ≤ a₁ → 0 ≤ a₂ →
      0 ≤ ρ → (1 : ℝ) ≤ n → ρ ≤ n → departureRange Y n ⊆ ballFinset 2 ρ →
      (∀ z ∈ departureRange Y n,
        (localTime Y n z : ℝ) ≤ 4 * ε * max (r - euclidNorm z) 0 + a₁) →
      |b - r| ≤ a₂ → ∀ x : Site 2, b ≤ euclidNorm x → euclidNorm x ≤ 3 * n →
      braSum Y n x ≤
        K * (4 * ε * (2 * ρ + 1) + (4 * ε * a₂ + a₁) * Real.log (4 * n + 2)) := by
  obtain ⟨K, hK, hsum⟩ := pl_braSum_le
  refine ⟨K, hK, ?_⟩
  intro Y n r b ρ a₁ a₂ ha₁ ha₂ hρ hn hρn hball hloc hbr x hbx hx3
  refine hsum Y n x (4 * ε) (4 * ε * a₂ + a₁) ρ (4 * n) (by positivity) (by positivity) hρ
    (by linarith) hball ?_ ?_
  · intro z hz
    have hz' : euclidNorm z ≤ ρ := mem_ballFinset_iff.mp (hball hz)
    have h1 : euclidNorm (z - x) ≤ euclidNorm z + euclidNorm x := by
      have := CERW.Support.Occupation.euclidNorm_add_le z (-x)
      rwa [← sub_eq_add_neg, CERW.Generic.Lattice.euclidNorm_neg] at this
    linarith
  · intro z hz
    have h1 := CERW.Support.Contact.max_sub_euclidNorm_le (x := z) (z := x) hbx
    have h2 : max (r - euclidNorm z) 0 ≤ euclidNorm (z - x) + a₂ := by
      refine max_le ?_ (by linarith [euclidNorm_nonneg (z - x)])
      have := le_max_left (b - euclidNorm z) 0
      linarith [(abs_le.mp hbr).1]
    calc (localTime Y n z : ℝ) ≤ 4 * ε * max (r - euclidNorm z) 0 + a₁ := hloc z hz
      _ ≤ 4 * ε * (euclidNorm (z - x) + a₂) + a₁ := by gcongr
      _ = 4 * ε * euclidNorm (z - x) + (4 * ε * a₂ + a₁) := by ring

/-- From `W ≤ K r`, `L ≤ 2 lg` and `lg ≤ √(r lg)`, the martingale error `C₁ (√(W L) + L)` is at
most `|C₁| (√(2K) + 2) √(r lg)`. -/
private lemma pl_err_le {C₁ K W L r lg : ℝ} (hK : 0 ≤ K) (hW : W ≤ K * r) (hL0 : 0 ≤ L)
    (hL : L ≤ 2 * lg) (hlg : lg ≤ Real.sqrt (r * lg)) (hr : 0 ≤ r) :
    C₁ * (Real.sqrt (W * L) + L) ≤ |C₁| * (Real.sqrt (2 * K) + 2) * Real.sqrt (r * lg) := by
  have hlg0 : 0 ≤ lg := by linarith
  have h1 : Real.sqrt (W * L) ≤ Real.sqrt (2 * K) * Real.sqrt (r * lg) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    calc W * L ≤ (K * r) * (2 * lg) := mul_le_mul hW hL hL0 (by positivity)
      _ = 2 * K * (r * lg) := by ring
  have h2 : 0 ≤ Real.sqrt (W * L) + L := by positivity
  calc C₁ * (Real.sqrt (W * L) + L) ≤ |C₁| * (Real.sqrt (W * L) + L) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) h2
    _ ≤ |C₁| * (Real.sqrt (2 * K) * Real.sqrt (r * lg) + 2 * Real.sqrt (r * lg)) := by
        gcongr
        linarith
    _ = |C₁| * (Real.sqrt (2 * K) + 2) * Real.sqrt (r * lg) := by ring

/-- The planar scales: with `q = √(lg/r)` and `σ = q^{1/2}`, `σ ≥ 0`, `σ² = q`, `r σ⁴ = lg` and
`r q = √(r lg)`. -/
private lemma pl_scales {r lg : ℝ} (hr : 0 < r) (hlg : 0 ≤ lg) :
    0 ≤ Real.sqrt (lg / r) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) ∧
    (Real.sqrt (lg / r) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) ^ 2 = Real.sqrt (lg / r) ∧
    r * (Real.sqrt (lg / r) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) ^ 4 = lg ∧
    r * Real.sqrt (lg / r) = Real.sqrt (r * lg) := by
  have hq : 0 ≤ Real.sqrt (lg / r) := Real.sqrt_nonneg _
  have hσ : Real.sqrt (lg / r) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) =
      Real.sqrt (Real.sqrt (lg / r)) := by
    rw [Real.sqrt_eq_rpow (Real.sqrt _)]
    norm_num
  rw [hσ]
  have h2 : Real.sqrt (Real.sqrt (lg / r)) ^ 2 = Real.sqrt (lg / r) := Real.sq_sqrt hq
  have h4 : Real.sqrt (lg / r) ^ 2 = lg / r := Real.sq_sqrt (div_nonneg hlg hr.le)
  refine ⟨Real.sqrt_nonneg _, h2, ?_, ?_⟩
  · calc r * Real.sqrt (Real.sqrt (lg / r)) ^ 4
        = r * (Real.sqrt (Real.sqrt (lg / r)) ^ 2) ^ 2 := by ring
      _ = lg := by
          rw [h2, h4]
          field_simp
  · have e : r * lg = r ^ 2 * (lg / r) := by
      field_simp
    rw [e, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]

/-- `√(√x) = x^{1/4}` for `x ≥ 0`. -/
private lemma pl_sqrt_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) = x ^ ((1 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

/-- `(K P w)^{1/2} ≤ K P^{1/2} w^{1/2}` for `K ≥ 1` and `P ≥ 0`. -/
private lemma pl_rpow_half_le {K P w : ℝ} (hK : 1 ≤ K) (hP : 0 ≤ P) :
    (K * P * w ^ (2 - 1)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) ≤
      K * (Real.sqrt P * Real.sqrt w) := by
  have e : (K * P * w ^ (2 - 1)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) = Real.sqrt (K * P * w) := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), mul_assoc]
  have hK' : Real.sqrt K ≤ K := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  exact mul_le_mul_of_nonneg_right hK' (by positivity)

/-- `log(x + 2) ≤ 2 log x` and `log(4x + 2) ≤ 2 log x` for `x ≥ 16`. -/
private lemma pl_logs {x : ℝ} (hx : 16 ≤ x) :
    Real.log (x + 2) ≤ 2 * Real.log x ∧ Real.log (4 * x + 2) ≤ 2 * Real.log x := by
  have h2 : 2 * Real.log x = Real.log (x ^ 2) := by
    rw [Real.log_pow]
    norm_num
  rw [h2]
  constructor <;> exact Real.log_le_log (by linarith) (by nlinarith)

/-- The numerical consequences of the scale bounds: with `r σ⁴ = lg`, `lg⁵ ≤ θ⁴ r`,
`P = r σ²` and `|b - r| ≤ C P`, we get `σ lg ≤ θ`, `σ ≤ 1`, `3r/4 ≤ b ≤ 5r/4` and
`lg ≤ P ≤ r`. -/
private lemma pl_numeric {θ Ci r lg σ b P : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hCi0 : 0 ≤ Ci)
    (hθCi : Ci * θ ≤ 1) (hlg4 : 4 ≤ lg) (hr0 : 0 < r) (hσ0 : 0 ≤ σ) (hσ4 : r * σ ^ 4 = lg)
    (hlg5 : lg ^ 5 ≤ θ ^ 4 * r) (hP : P = r * σ ^ 2) (hbr : |b - r| ≤ Ci * P) :
    σ * lg ≤ θ ∧ σ ≤ 1 ∧ 3 * r / 4 ≤ b ∧ b ≤ 5 * r / 4 ∧ P ≤ r ∧ lg ≤ P := by
  have hσlg : σ * lg ≤ θ := by
    have h1 : (σ * lg) ^ 4 * r ≤ θ ^ 4 * r := by
      calc (σ * lg) ^ 4 * r = (r * σ ^ 4) * lg ^ 4 := by ring
        _ = lg ^ 5 := by rw [hσ4]; ring
        _ ≤ θ ^ 4 * r := hlg5
    have h2 : (σ * lg) ^ 4 ≤ θ ^ 4 := le_of_mul_le_mul_right h1 hr0
    exact (pow_le_pow_iff_left₀ (mul_nonneg hσ0 (by linarith)) hθ0.le four_ne_zero).mp h2
  have hσ4' : 4 * σ ≤ θ := by
    have := mul_le_mul_of_nonneg_left hlg4 hσ0
    linarith
  have hσ1 : σ ≤ 1 := by linarith
  have hCiσ2 : Ci * σ ^ 2 ≤ 1 / 4 := by
    have h1 : Ci * σ ≤ 1 / 4 := by
      have := mul_le_mul_of_nonneg_left hσ4' hCi0
      linarith
    calc Ci * σ ^ 2 = (Ci * σ) * σ := by ring
      _ ≤ (1 / 4) * 1 := mul_le_mul h1 hσ1 hσ0 (by norm_num)
      _ = 1 / 4 := by ring
  have hCiP : Ci * P ≤ r / 4 := by
    rw [hP]
    calc Ci * (r * σ ^ 2) = r * (Ci * σ ^ 2) := by ring
      _ ≤ r * (1 / 4) := by gcongr
      _ = r / 4 := by ring
  have hσsq : σ ^ 2 ≤ 1 := pow_le_one₀ hσ0 hσ1
  refine ⟨hσlg, hσ1, by linarith [(abs_le.mp hbr).1], by linarith [(abs_le.mp hbr).2], ?_, ?_⟩
  · rw [hP]
    calc r * σ ^ 2 ≤ r * 1 := by gcongr
      _ = r := mul_one r
  · rw [hP, ← hσ4]
    have : σ ^ 4 ≤ σ ^ 2 := by
      calc σ ^ 4 = σ ^ 2 * σ ^ 2 := by ring
        _ ≤ σ ^ 2 * 1 := by gcongr
        _ = σ ^ 2 := mul_one _
    gcongr

/-- Beyond the inner ball the potentials of `D_n` and of `E = D_n ∖ B(0, b)` agree
(`eq:ballpotential-euclid`). -/
private lemma pl_split {ε : ℝ} (Y : ℕ → Site 2) (n : ℕ) {b : ℝ} (hb : innerRadius Y n = b)
    (hb0 : 0 < b) {y : EuclideanSpace ℝ (Fin 2)} (hy : b ≤ ‖y‖) :
    potential 2 ε (cellSet Y n) y = potential 2 ε (cellSet Y n \ Metric.ball 0 b) y := by
  have hDm := CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDb : Bornology.IsBounded (cellSet Y n) := Metric.isBounded_ball.subset
    (CERW.Support.Occupation.cellSet_subset_ball (by norm_num) Y n)
  have hball := ball_innerRadius_subset (d := 2) (by norm_num) Y n
  rw [hb] at hball
  rw [potential_split le_rfl ε hDm hDb hb0 hball y, max_eq_right (by linarith), mul_zero,
    zero_add]

/-- Step 1 of Section 7.3 and `eq:planar-exterior-pointwise`: beyond the inner radius the bracket
is `O(r)`, so `|ℓ_n(x) - U_{D_n}(x)| ≤ K √(r lg)` for `b ≤ |x| ≤ 3n`. -/
private lemma pl_first {ε : ℝ} (hε : 0 < ε) (C₀ C₁ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Y : ℕ → Site 2) (n : ℕ) (b r lg σ θ Ci : ℝ),
      PathFacts 2 ε C₀ C₁ Y n → 0 < r → 0 ≤ Ci → 0 ≤ σ → σ ≤ 1 → σ * lg ≤ θ →
      2 * Ci * (4 * ε + 1) * θ ≤ 1 → 16 ≤ (n : ℝ) → r ≤ n / 8 → 4 ≤ r →
      maxRadius Y n ≤ 3 * r / 2 → Real.log n = lg → lg ≤ Real.sqrt (r * lg) →
      Real.sqrt (r * lg) = r * σ ^ 2 → |b - r| ≤ Ci * Real.sqrt (r * lg) →
      (∀ z ∈ departureRange Y n,
        (localTime Y n z : ℝ) ≤ 4 * ε * max (r - euclidNorm z) 0 + Ci * r * σ) →
      ∀ x : Site 2, b ≤ euclidNorm x → euclidNorm x ≤ 3 * n →
        |(localTime Y n x : ℝ) - potential 2 ε (cellSet Y n) (toSpace x)| ≤
          K * Real.sqrt (r * lg) := by
  obtain ⟨KS, hKS, hbra⟩ := pl_braSum_le_of_cone hε
  refine ⟨|C₁| * (Real.sqrt (2 * (KS * (16 * ε + 1))) + 2), by positivity, ?_⟩
  intro Y n b r lg σ θ Ci hP hr0 hCi0 hσ0 hσ1 hσlg hθC hn16 hrn hr4 hR hlg hlgP hPeq hbr hloc
    x hbx hx3
  obtain ⟨hL, hlog4⟩ := pl_logs hn16
  rw [hlg] at hL hlog4
  have hlg0 : 0 ≤ lg := by
    rw [← hlg]
    exact Real.log_nonneg (by linarith)
  have hR0 : 0 ≤ maxRadius Y n :=
    (euclidNorm_nonneg (Y 0)).trans (euclidNorm_le_maxRadius Y (Nat.zero_le n))
  have hP0 : 0 ≤ Real.sqrt (r * lg) := Real.sqrt_nonneg _
  have hPlg : Real.sqrt (r * lg) * lg ≤ r * θ := by
    rw [hPeq]
    calc r * σ ^ 2 * lg = r * σ * (σ * lg) := by ring
      _ ≤ r * 1 * θ := by gcongr
      _ = r * θ := by ring
  have hrσlg : r * σ * lg ≤ r * θ := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hσlg hr0.le
  have hW : braSum Y n x ≤ KS * (16 * ε + 1) * r := by
    refine (hbra Y n r b (maxRadius Y n) (Ci * r * σ) (Ci * Real.sqrt (r * lg)) (by positivity)
      (by positivity) hR0 (by linarith) (by linarith)
      (CERW.Support.Occupation.departureRange_subset_ballFinset Y n) hloc hbr x hbx hx3).trans ?_
    calc KS * (4 * ε * (2 * maxRadius Y n + 1) +
          (4 * ε * (Ci * Real.sqrt (r * lg)) + Ci * r * σ) * Real.log (4 * n + 2))
        ≤ KS * (4 * ε * (4 * r) +
          (4 * ε * (Ci * Real.sqrt (r * lg)) + Ci * r * σ) * (2 * lg)) := by
          gcongr
          linarith
      _ = KS * (16 * ε * r +
          2 * Ci * (4 * ε * (Real.sqrt (r * lg) * lg) + r * σ * lg)) := by ring
      _ ≤ KS * (16 * ε * r + 2 * Ci * (4 * ε * (r * θ) + r * θ)) := by gcongr
      _ = KS * (16 * ε * r + r * (2 * Ci * (4 * ε + 1) * θ)) := by ring
      _ ≤ KS * (16 * ε * r + r * 1) := by gcongr
      _ = KS * (16 * ε + 1) * r := by ring
  refine (hP.point x hx3).trans ?_
  exact pl_err_le (by positivity) hW (Real.log_nonneg (by linarith)) hL hlgP hr0.le

/-- The probe of Step 2 of Section 7.3: at `y_t = (b + w + 4t) u` with `w ≤ t ≤ r/4`, the site of
the cell of `y_t` is unvisited, so the pointwise bound there and the cell modulus give
`U_E(y_t) ≥ -(K₂ + C ε) P`. -/
private lemma pl_probe {ε : ℝ} (hε : 0 < ε) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (Y : ℕ → Site 2) (n : ℕ) (b R w r P K2 : ℝ),
      innerRadius Y n = b → maxRadius Y n = R → w = R - b + 2 * Real.sqrt ((2 : ℕ) : ℝ) →
      0 < b → b ≤ 5 * r / 4 → 1 ≤ w → w ≤ r / 4 → 4 ≤ r → r ≤ n / 8 → 16 ≤ (n : ℝ) →
      Real.log (3 * r + 2) ≤ P →
      (∀ x : Site 2, b ≤ euclidNorm x → euclidNorm x ≤ 3 * n →
        |(localTime Y n x : ℝ) - potential 2 ε (cellSet Y n) (toSpace x)| ≤ K2 * P) →
      ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t → t ≤ r / 4 →
        -((K2 + Cc * ε) * P) ≤
          potential 2 ε (cellSet Y n \ Metric.ball 0 b) ((b + w + 4 * t) • u) := by
  obtain ⟨Cc, hCc, hcell⟩ :=
    CERW.Support.Geometry.exists_potential_cell_modulus (d := 2) le_rfl
  refine ⟨Cc, hCc, ?_⟩
  intro Y n b R w r P K2 hb hR hw hb0 hb2 hw1 hw2 hr4 hrn hn16 hlog3 hpt u hu t hwt htr
  have hs2 : 1 ≤ Real.sqrt ((2 : ℕ) : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have hs2' : Real.sqrt ((2 : ℕ) : ℝ) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hDm := CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDball := CERW.Support.Occupation.cellSet_subset_ball (d := 2) (by norm_num) Y n
  rw [hR] at hDball
  have hy : ‖(b + w + 4 * t) • u‖ = b + w + 4 * t := by
    rw [norm_smul, hu, mul_one, Real.norm_of_nonneg (by linarith)]
  have hyz := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell
    (mem_cell_cellCenter ((b + w + 4 * t) • u))
  generalize (b + w + 4 * t) • u = y at hy hyz ⊢
  generalize cellCenter y = z at hyz
  generalize Real.sqrt ((2 : ℕ) : ℝ) = s at hs2 hs2' hw hDball hcell hyz
  have hz1 := norm_le_norm_add_norm_sub' y (toSpace z)
  have hz2 := norm_le_norm_add_norm_sub' (toSpace z) y
  rw [norm_sub_rev] at hz2
  rw [norm_toSpace] at hz1 hz2
  have hz3 : ‖y‖ ≤ euclidNorm z + s / 2 := hz1.trans (add_le_add le_rfl hyz)
  have hz4 : euclidNorm z ≤ ‖y‖ + s / 2 := hz2.trans (add_le_add le_rfl hyz)
  have hℓ : localTime Y n z = 0 := by
    by_contra h
    have hz := mem_departureRange_iff.mpr (Nat.pos_of_ne_zero h)
    have := mem_ballFinset_iff.mp
      (CERW.Support.Occupation.departureRange_subset_ballFinset Y n hz)
    rw [hR] at this
    linarith
  have hzb : b ≤ ‖toSpace z‖ := by
    rw [norm_toSpace]
    linarith
  have hpz := hpt z (by linarith) (by linarith)
  rw [hℓ, Nat.cast_zero, zero_sub, abs_neg, pl_split (ε := ε) Y n hb hb0 hzb] at hpz
  have hc := hcell ε hε.le (3 * r) (by linarith) (cellSet Y n) hDm
    (hDball.trans (Metric.ball_subset_ball (by linarith))) y (toSpace z) (by linarith)
    (by linarith)
  rw [pl_split (ε := ε) Y n hb hb0 (y := y) (by linarith),
    pl_split (ε := ε) Y n hb hb0 hzb] at hc
  have hlogP : Cc * ε * Real.log (3 * r + 2) ≤ Cc * ε * P :=
    mul_le_mul_of_nonneg_left hlog3 (by positivity)
  have h1 := (abs_le.mp hc).1
  have h2 := (abs_le.mp hpz).1
  have e : (K2 + Cc * ε) * P = K2 * P + Cc * ε * P := by ring
  rw [e]
  linarith

/-- Step 2 of Section 7.3: from the pointwise bound, the probes give the cap volume bound
`|E ∩ B((b + w)u, t)| ≤ λ t` with `λ = K √(r lg)`, and Lemma 7.2 bounds `U_E^+` in the
annulus by `C ((r lg)^{1/4} √w + √(r lg))`. -/
private lemma pl_second (hnear : near_far) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / ((2 : ℕ) : ℝ)) {K2 Cm' : ℝ} (hK2 : 0 ≤ K2) (hCm0 : 0 ≤ Cm') :
    ∃ K : ℝ, 0 < K ∧ ∀ (Y : ℕ → Site 2) (n : ℕ) (b R w r lg : ℝ),
      innerRadius Y n = b → maxRadius Y n = R → w = R - b + 2 * Real.sqrt ((2 : ℕ) : ℝ) →
      0 < b → 3 * r / 4 ≤ b → b ≤ 5 * r / 4 → 1 ≤ w → w ≤ r / 4 → 4 ≤ r → r ≤ n / 8 →
      16 ≤ (n : ℝ) → 0 ≤ lg → 1 ≤ Real.sqrt (r * lg) →
      Real.log (3 * r + 2) ≤ Real.sqrt (r * lg) →
      (volume (cellSet Y n \ Metric.ball 0 b)).toReal ≤ Cm' * r * Real.sqrt (r * lg) →
      (∀ x : Site 2, b ≤ euclidNorm x → euclidNorm x ≤ 3 * n →
        |(localTime Y n x : ℝ) - potential 2 ε (cellSet Y n) (toSpace x)| ≤
          K2 * Real.sqrt (r * lg)) →
      ∀ y : EuclideanSpace ℝ (Fin 2), b ≤ ‖y‖ → ‖y‖ ≤ R + 2 * Real.sqrt ((2 : ℕ) : ℝ) →
        positivePotential 2 ε (cellSet Y n \ Metric.ball 0 b) y ≤
          K * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg)) := by
  obtain ⟨Cc, hCc, hprobe⟩ := pl_probe hε
  obtain ⟨Cnf, hCnf, hnf⟩ := hnear (d := 2) le_rfl ε hε hεd
  have hω := unitBallVolume_pos 2
  obtain ⟨K3, hK3⟩ : ∃ K3 : ℝ, K3 = K2 + Cc * ε := ⟨_, rfl⟩
  obtain ⟨K4, hK4⟩ : ∃ K4 : ℝ, K4 = 2 * ε * Cm' / unitBallVolume 2 := ⟨_, rfl⟩
  have hK30 : 0 ≤ K3 := by rw [hK3]; positivity
  have hK40 : 0 ≤ K4 := by rw [hK4]; positivity
  obtain ⟨K5, hK5⟩ : ∃ K5 : ℝ,
      K5 = unitBallVolume 2 / (2 * ε) * 5 ^ 2 * (K3 + K4) + 4 * Cm' + 1 := ⟨_, rfl⟩
  have hK5b : 0 ≤ unitBallVolume 2 / (2 * ε) * 5 ^ 2 * (K3 + K4) := by positivity
  have hK51 : 1 ≤ K5 := by linarith
  refine ⟨Cnf * K5, by positivity, ?_⟩
  intro Y n b R w r lg hb hR hw hb0 hb1 hb2 hw1 hw2 hr4 hrn hn16 hlg0 hP1 hlog3 hvolE hpt
    y hy1 hy2
  have hq4 : Real.sqrt (Real.sqrt (r * lg)) = (r * lg) ^ ((1 : ℝ) / 4) :=
    pl_sqrt_sqrt (by positivity)
  generalize Real.sqrt (r * lg) = P at hP1 hlog3 hvolE hpt hq4 ⊢
  have hP0 : 0 ≤ P := by linarith
  set E := cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) b with hE_def
  have hDb : Bornology.IsBounded (cellSet Y n) := Metric.isBounded_ball.subset
    (CERW.Support.Occupation.cellSet_subset_ball (by norm_num) Y n)
  have hEm : MeasurableSet E :=
    (CERW.Support.Occupation.measurableSet_cellSet Y n).diff measurableSet_ball
  have hEb : Bornology.IsBounded E := hDb.subset Set.sdiff_subset
  have hEsub : E ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w} := by
    have := sdiff_subset_annulus (d := 2) (by norm_num) Y n
    rw [hb, hR, ← hw] at this
    exact this
  have hEfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
  have hint : ∀ z, ∫ v in E, ‖v - z‖ ^ (2 - ((2 : ℕ) : ℝ)) = (volume E).toReal := by
    intro z
    have e : (2 : ℝ) - ((2 : ℕ) : ℝ) = 0 := by norm_num
    simp only [e, Real.rpow_zero, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  have hcap : ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t →
      volume (E ∩ Metric.ball ((b + w) • u) t) ≤ ENNReal.ofReal (K5 * P * t ^ (2 - 1)) := by
    intro u hu t hwt
    have ht0 : 0 < t := by linarith
    have ht1 : t ^ (2 - 1) = t := by norm_num
    rw [ENNReal.le_ofReal_iff_toReal_le ((hEb.subset Set.inter_subset_left).measure_lt_top.ne)
      (by positivity)]
    rcases le_or_gt t (r / 4) with htr | htr
    · have hlo := hprobe Y n b R w r P K2 hb hR hw hb0 hb2 hw1 hw2 hr4 hrn hn16 hlog3 hpt u hu t
        hwt htr
      rw [← hK3] at hlo
      have hy : ‖(b + w + 4 * t) • u‖ = b + w + 4 * t := by
        rw [norm_smul, hu, mul_one, Real.norm_of_nonneg (by linarith)]
      have hhi : positivePotential 2 ε E ((b + w + 4 * t) • u) ≤ K4 * P := by
        refine (positivePotential_le_of_outside le_rfl hε.le hEm hEb hb0 hEsub
          (by rw [hy]; linarith)).trans ?_
        rw [hint]
        calc ε / (unitBallVolume 2 * b) * (volume E).toReal
            ≤ ε / (unitBallVolume 2 * b) * (Cm' * r * P) := by gcongr
          _ ≤ K4 * P := by
            rw [hK4, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            have e : 2 * ε * Cm' / unitBallVolume 2 * P * (unitBallVolume 2 * b) =
                ε * Cm' * P * (2 * b) := by
              field_simp
            rw [e]
            calc ε * (Cm' * r * P) = ε * Cm' * P * r := by ring
              _ ≤ ε * Cm' * P * (2 * b) := by gcongr; linarith
      have h := cap_mass_of_probe le_rfl hε hEm hEb hEsub hb0 ht0 (by linarith) hu hlo hhi
      refine h.trans ?_
      rw [ht1]
      calc unitBallVolume 2 / (2 * ε) * 5 ^ 2 * (K3 * P + K4 * P) * t
          = (unitBallVolume 2 / (2 * ε) * 5 ^ 2 * (K3 + K4)) * P * t := by ring
        _ ≤ K5 * P * t := by gcongr; linarith
    · rw [ht1]
      calc (volume (E ∩ Metric.ball ((b + w) • u) t)).toReal ≤ (volume E).toReal :=
            ENNReal.toReal_mono hEfin (measure_mono Set.inter_subset_left)
        _ ≤ Cm' * r * P := hvolE
        _ ≤ Cm' * (4 * t) * P := by gcongr; linarith
        _ = (4 * Cm') * P * t := by ring
        _ ≤ K5 * P * t := by gcongr; linarith
  have hmass : ∀ z, ∫ v in E, ‖v - z‖ ^ (2 - ((2 : ℕ) : ℝ)) ≤ K5 * P * b := by
    intro z
    rw [hint]
    calc (volume E).toReal ≤ Cm' * r * P := hvolE
      _ ≤ Cm' * (2 * b) * P := by gcongr; linarith
      _ = (2 * Cm') * P * b := by ring
      _ ≤ K5 * P * b := by gcongr; linarith
  have hlam : 1 ≤ K5 * P := by
    calc (1 : ℝ) ≤ P := hP1
      _ = 1 * P := (one_mul P).symm
      _ ≤ K5 * P := mul_le_mul_of_nonneg_right hK51 hP0
  have hyw : ‖y‖ ≤ b + w := by
    rw [hw]
    convert hy2 using 1
    ring
  refine (hnf w b (K5 * P) hw1 (by linarith) hlam E hEm hEsub hcap hmass y hy1 hyw).trans ?_
  rw [← hq4]
  calc Cnf * (K5 * P * w ^ (2 - 1)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) + Cnf * (K5 * P)
      ≤ Cnf * (K5 * (Real.sqrt P * Real.sqrt w)) + Cnf * (K5 * P) := by
        gcongr
        exact pl_rpow_half_le hK51 hP0
    _ = Cnf * K5 * (Real.sqrt P * Real.sqrt w + P) := by ring

/-- Steps 1 to 3 of Section 7.3 (the planar case): with `w = R_out - b + 2√d` at most `r / log n`,
the local times outside the inner ball are within `C √(r log n)` of the potential of `E`, and the
positive potential of `E` in the annulus is at most `C ((r log n)^{1/4} √w + √(r log n))`. -/
private theorem planar_exterior (hd : d = 2) (hnear : near_far) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) (C₀ C₁ Cin Cm : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      PathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n → MassOK d ε Cm Y n →
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

end

/-! ### The maximum principle for the planar potential -/

/-- The identification of the complex plane with the Euclidean plane. -/
private noncomputable abbrev mp_e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr

/-- The complex kernel `u_v / (v - z)` whose real part is the planar potential integrand. -/
private noncomputable def mp_kernel (v : EuclideanSpace ℝ (Fin 2)) (z : ℂ) : ℂ :=
  mp_e.symm (unitDir v) * (mp_e.symm v - z)⁻¹

/-- `Re (a / w) = ⟨a, w⟩ / |w|²` for complex numbers seen as vectors of the plane. -/
private lemma mp_re_mul_inv (a w : ℂ) :
    (a * w⁻¹).re = inner ℝ (mp_e a) (mp_e w) / ‖mp_e w‖ ^ 2 := by
  rw [LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.norm_map, Complex.inner,
    Complex.sq_norm]
  simp only [Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The real part of the complex kernel is the integrand of the planar potential. -/
private lemma mp_re_kernel (v : EuclideanSpace ℝ (Fin 2)) (z : ℂ) :
    (mp_kernel v z).re = inner ℝ (unitDir v) (v - mp_e z) / ‖v - mp_e z‖ ^ 2 := by
  have h := mp_re_mul_inv (mp_e.symm (unitDir v)) (mp_e.symm v - z)
  rwa [LinearIsometryEquiv.apply_symm_apply, map_sub, LinearIsometryEquiv.apply_symm_apply] at h

/-- A point of norm at least `b` is at distance at least `b - |z|` from `z`. -/
private lemma mp_sub_norm_le {b : ℝ} {v : EuclideanSpace ℝ (Fin 2)} (hv : b ≤ ‖v‖) (z : ℂ) :
    b - ‖z‖ ≤ ‖mp_e.symm v - z‖ := by
  calc b - ‖z‖ ≤ ‖mp_e.symm v‖ - ‖z‖ := by rw [LinearIsometryEquiv.norm_map]; linarith
    _ ≤ ‖mp_e.symm v - z‖ := norm_sub_norm_le _ _

/-- The complex kernel is bounded by `1 / (b - |z|)` for `|v| ≥ b > |z|`. -/
private lemma mp_norm_kernel_le {b : ℝ} {v : EuclideanSpace ℝ (Fin 2)} (hv : b ≤ ‖v‖) {z : ℂ}
    (hz : ‖z‖ < b) : ‖mp_kernel v z‖ ≤ (b - ‖z‖)⁻¹ := by
  have hpos : 0 < b - ‖z‖ := sub_pos.2 hz
  have hw := mp_sub_norm_le hv z
  rw [mp_kernel, norm_mul, norm_inv, LinearIsometryEquiv.norm_map]
  calc ‖unitDir v‖ * ‖mp_e.symm v - z‖⁻¹ ≤ 1 * (b - ‖z‖)⁻¹ :=
        mul_le_mul (norm_unitDir_le v) (inv_anti₀ hpos hw) (inv_nonneg.2 (norm_nonneg _))
          zero_le_one
    _ = (b - ‖z‖)⁻¹ := one_mul _

/-- The direction `u_v`, seen in the complex plane, is measurable in `v`. -/
private lemma mp_measurable_dir :
    Measurable (fun v : EuclideanSpace ℝ (Fin 2) => mp_e.symm (unitDir v)) := by
  have hdir : Measurable (fun v : EuclideanSpace ℝ (Fin 2) => unitDir v) := by
    change Measurable (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖⁻¹ • v)
    fun_prop
  exact mp_e.symm.continuous.measurable.comp hdir

/-- The complex kernel is measurable in `v`. -/
private lemma mp_measurable_kernel (z : ℂ) : Measurable (fun v => mp_kernel v z) :=
  mp_measurable_dir.mul ((mp_e.symm.continuous.measurable.sub_const z).inv)

/-- The complex derivative of the kernel in `z`. -/
private lemma mp_hasDerivAt_kernel (v : EuclideanSpace ℝ (Fin 2)) {z : ℂ}
    (hz : mp_e.symm v - z ≠ 0) :
    HasDerivAt (fun z => mp_kernel v z) (mp_e.symm (unitDir v) / (mp_e.symm v - z) ^ 2) z := by
  have h1 : HasDerivAt (fun y : ℂ => mp_e.symm v - y) (-1) z := (hasDerivAt_id z).const_sub _
  have h2 : mp_e.symm (unitDir v) / (mp_e.symm v - z) ^ 2 =
      mp_e.symm (unitDir v) * (-(-1) / (mp_e.symm v - z) ^ 2) := by ring
  rw [h2]
  exact (h1.inv hz).const_mul _
/-- The integral `∫_E u_v / (v - z) dv` of the complex kernel. -/
private noncomputable def mp_field (E : Set (EuclideanSpace ℝ (Fin 2))) (z : ℂ) : ℂ :=
  ∫ v in E, mp_kernel v z

/-- For `E` bounded outside the disc `B(0,b)`, the kernel is integrable on `E` at every point `z`
of the disc. -/
private lemma mp_integrable_kernel {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : MeasurableSet E)
    (hEb : Bornology.IsBounded E) {b : ℝ} (hsub : E ⊆ {v | b ≤ ‖v‖}) {z : ℂ} (hz : ‖z‖ < b) :
    Integrable (fun v => mp_kernel v z) (volume.restrict E) :=
  IntegrableOn.of_bound hEb.measure_lt_top (mp_measurable_kernel z).aestronglyMeasurable
    (b - ‖z‖)⁻¹ (ae_restrict_of_forall_mem hE fun _ hv => mp_norm_kernel_le (hsub hv) hz)

/-- The field `∫_E u_v / (v - z) dv` is complex differentiable on the disc `B(0,b)`. -/
private lemma mp_differentiableOn_field {E : Set (EuclideanSpace ℝ (Fin 2))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) {b : ℝ} (hsub : E ⊆ {v | b ≤ ‖v‖}) :
    DifferentiableOn ℂ (mp_field E) (Metric.ball 0 b) := by
  intro z₀ hz₀
  rw [mem_ball_zero_iff] at hz₀
  haveI : IsFiniteMeasure (volume.restrict E) :=
    isFiniteMeasure_restrict.2 hEb.measure_lt_top.ne
  set δ : ℝ := (b - ‖z₀‖) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hnear : ∀ v ∈ E, ∀ z ∈ Metric.ball z₀ δ, δ ≤ ‖mp_e.symm v - z‖ := by
    intro v hv z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := norm_sub_norm_le z z₀
    have h2 := mp_sub_norm_le (hsub hv) z
    linarith
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict E)
    (F := fun z v => mp_kernel v z)
    (F' := fun z v => mp_e.symm (unitDir v) / (mp_e.symm v - z) ^ 2)
    (bound := fun _ => (δ ^ 2)⁻¹) (x₀ := z₀) (Metric.ball_mem_nhds z₀ hδ0)
    (Eventually.of_forall fun z => (mp_measurable_kernel z).aestronglyMeasurable)
    (mp_integrable_kernel hE hEb hsub hz₀)
    (mp_measurable_dir.div
      ((mp_e.symm.continuous.measurable.sub_const z₀).pow_const 2)).aestronglyMeasurable
    (ae_restrict_of_forall_mem hE fun v hv z hz => ?_) (integrable_const _)
    (ae_restrict_of_forall_mem hE fun v hv z hz =>
      mp_hasDerivAt_kernel v (norm_pos_iff.mp (hδ0.trans_le (hnear v hv z hz))))
  · exact hderiv.2.differentiableAt.differentiableWithinAt
  · rw [norm_div, norm_pow, LinearIsometryEquiv.norm_map, ← one_div]
    exact div_le_div₀ zero_le_one (norm_unitDir_le v) (pow_pos hδ0 2)
      (pow_le_pow_left₀ hδ0.le (hnear v hv z hz) 2)

/-- The planar potential is `2ε/ω_2` times the real part of the field inside the disc. -/
private lemma mp_potential_eq (ε : ℝ) {E : Set (EuclideanSpace ℝ (Fin 2))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) {b : ℝ} (hsub : E ⊆ {v | b ≤ ‖v‖})
    {z : ℂ} (hz : ‖z‖ < b) :
    potential 2 ε E (mp_e z) = 2 * ε / unitBallVolume 2 * (mp_field E z).re := by
  have h := integral_re (mp_integrable_kernel hE hEb hsub hz)
  simp only [RCLike.re_to_complex, mp_re_kernel] at h
  rw [potential, mp_field, h]

/-- Inside the disc, the exponential of the potential is the modulus of a holomorphic function. -/
private lemma mp_exists_holomorphic (ε : ℝ) {E : Set (EuclideanSpace ℝ (Fin 2))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) {b : ℝ} (hsub : E ⊆ {v | b ≤ ‖v‖}) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (Metric.ball 0 b) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) b, ‖H z‖ = Real.exp (potential 2 ε E (mp_e z)) := by
  refine ⟨fun z => Complex.exp (((2 * ε / unitBallVolume 2 : ℝ) : ℂ) * mp_field E z),
    ((mp_differentiableOn_field hE hEb hsub).const_mul _).cexp, fun z hz => ?_⟩
  rw [Complex.norm_exp, Complex.re_ofReal_mul,
    mp_potential_eq ε hE hEb hsub (mem_ball_zero_iff.mp hz)]

/-- The planar potential of a bounded measurable set is continuous. -/
private lemma mp_continuous_potential {ε : ℝ} (hε : 0 < ε) {E : Set (EuclideanSpace ℝ (Fin 2))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) : Continuous (potential 2 ε E) := by
  obtain ⟨C, hC0, hC⟩ := CERW.Support.Geometry.exists_potential_holder (d := 2) le_rfl
  exact CERW.Support.Geometry.continuous_of_holder_half (by positivity)
    (hC ε hε.le E hE hEb.measure_lt_top.ne)
/-- In the plane the potential of a set outside the disc `B(0,b)` is harmonic inside it, so its
supremum over the closed disc is attained on the circle. -/
private theorem planar_max_principle (hd : d = 2) {ε : ℝ} (hε : 0 < ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    {b M : ℝ} (hb : 0 < b) (hsub : E ⊆ {v | b ≤ ‖v‖})
    (hM : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ = b → potential d ε E y ≤ M) :
    ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ b → potential d ε E y ≤ M := by
  subst hd
  intro y hy
  rcases hy.lt_or_eq with hlt | heq
  swap
  · exact hM y heq
  by_contra hcon
  rw [not_le] at hcon
  have hcont : Continuous (fun z : ℂ => potential 2 ε E (mp_e z)) :=
    (mp_continuous_potential hε hE hEb).comp mp_e.continuous
  obtain ⟨z₀, hz₀K, hmax⟩ := (isCompact_closedBall (0 : ℂ) b).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self hb.le⟩ hcont.continuousOn
  rw [isMaxOn_iff] at hmax
  have hy' : mp_e.symm y ∈ Metric.closedBall (0 : ℂ) b := by
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact hy
  have hge : potential 2 ε E y ≤ potential 2 ε E (mp_e z₀) := by
    have h := hmax _ hy'
    simp only [LinearIsometryEquiv.apply_symm_apply] at h
    exact h
  have hz₀ : z₀ ∈ Metric.ball (0 : ℂ) b := by
    rw [mem_closedBall_zero_iff] at hz₀K
    rw [mem_ball_zero_iff]
    refine lt_of_le_of_ne hz₀K fun h => ?_
    have := hM (mp_e z₀) (by rw [LinearIsometryEquiv.norm_map, h])
    linarith
  obtain ⟨H, hHd, hHn⟩ := mp_exists_holomorphic ε hE hEb hsub
  have hHmax : IsMaxOn (norm ∘ H) (Metric.ball 0 b) z₀ := by
    rw [isMaxOn_iff]
    intro z hz
    simp only [Function.comp_apply]
    rw [hHn z hz, hHn z₀ hz₀]
    exact Real.exp_le_exp.2 (hmax z (Metric.ball_subset_closedBall hz))
  have heqOn := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
    (convex_ball (0 : ℂ) b).isPreconnected Metric.isOpen_ball hHd hz₀ hHmax
  have hconst : Set.EqOn (fun z : ℂ => potential 2 ε E (mp_e z))
      (fun _ => potential 2 ε E (mp_e z₀)) (Metric.ball 0 b) := by
    intro z hz
    have h := heqOn hz
    simp only [Function.comp_apply, Function.const_apply] at h
    rw [hHn z hz, hHn z₀ hz₀] at h
    exact Real.exp_injective h
  have hcl := hconst.closure hcont continuous_const
  rw [closure_ball 0 hb.ne'] at hcl
  have hbC : ‖(b : ℂ)‖ = b := Complex.norm_of_nonneg hb.le
  have h1 : potential 2 ε E (mp_e b) = potential 2 ε E (mp_e z₀) :=
    hcl (mem_closedBall_zero_iff.mpr hbC.le)
  have h2 := hM (mp_e b) (by rw [LinearIsometryEquiv.norm_map, hbC])
  linarith
/-! ### The crossing bound for the Euclidean walk -/

/-- The largest value of the Euclidean norm on the unit sphere is one. -/
private lemma cr_normMax_euclid (hd : 1 ≤ d) :
    normMax (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) = 1 := by
  have hmem : coordVec (⟨0, by omega⟩ : Fin d) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    rw [mem_sphere_zero_iff_norm]
    simp [coordVec, PiLp.norm_single]
  have himg : (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ''
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 = {1} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨_, hmem, ?_⟩, ?_⟩
    · exact mem_sphere_zero_iff_norm.mp hmem
    · rintro t ⟨v, hv, rfl⟩
      exact mem_sphere_zero_iff_norm.mp hv
  rw [normMax, himg, csSup_singleton]

/-- For `n ≥ 2` one has `log (n + 2) ≤ 2 log n`. -/
private lemma cr_log_add_two_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  calc Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log (by linarith) h1
    _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num

/-- The vector increment bound with `log (n + 2)` implies the one with `log n` and the
constant doubled. -/
private lemma cr_sqrt_le {a l l' C : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hl : 0 ≤ l)
    (hll : l' ≤ 2 * l) :
    C * Real.sqrt (a * l') ≤ 2 * C * Real.sqrt (a * l) := by
  have hsq : Real.sqrt (a * l') ≤ 2 * Real.sqrt (a * l) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h0 : Real.sqrt (a * l) ^ 2 = a * l := Real.sq_sqrt (mul_nonneg ha hl)
    calc a * l' ≤ a * (2 * l) := mul_le_mul_of_nonneg_left hll ha
      _ ≤ a * (4 * l) := mul_le_mul_of_nonneg_left (by linarith) ha
      _ = (2 * Real.sqrt (a * l)) ^ 2 := by rw [mul_pow, h0]; ring
  calc C * Real.sqrt (a * l') ≤ C * (2 * Real.sqrt (a * l)) :=
        mul_le_mul_of_nonneg_left hsq hC
    _ = 2 * C * Real.sqrt (a * l) := by ring

/-- The direction of a nonzero vector has norm one. -/
private lemma cr_norm_unitDir {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    ‖unitDir v‖ = 1 := by
  rw [unitDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

/-- The direction of a nonzero vector `v` has inner product `‖v‖` with `v`. -/
private lemma cr_inner_unitDir_self {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    inner ℝ (unitDir v) v = ‖v‖ := by
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [unitDir, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

/-- The inner product of `q` with the direction of `y` is `⟪q, y⟫ / ‖y‖`. -/
private lemma cr_inner_unitDir_right (q y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ q (unitDir y) = ‖y‖⁻¹ * inner ℝ q y := by
  rw [unitDir, real_inner_smul_right]

/-- `eq:euclid-crossing` from `lem:outer-crossing`. -/
private theorem euclid_crossing (hcross : outer_crossing) (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) (C₀ C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℕ → Site d) (n : ℕ), 2 ≤ n → PathFacts d ε C₀ C₁ Y n →
      LinOK d ε C₁ Y n → CrossOK d C Y n := by
  obtain ⟨hΨ, hsub, hξ0, hell⟩ := CERW.Support.Main.euclidean_norm_hypotheses (d := d) hεd
  have hΛ := cr_normMax_euclid (d := d) (by omega)
  obtain ⟨C, hC, hmain⟩ := hcross hd (fun v => ‖v‖) hΨ ε hε hell (1 / 2) (by norm_num)
    (2 * C₁) (by positivity)
  refine ⟨2 * C, by positivity, ?_⟩
  intro Y n hn hY hlin b hb
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hO : (0 : ℝ) ≤ (outerMax Y n b : ℝ) := Nat.cast_nonneg _
  by_cases hRb : maxRadius Y n ≤ b
  · have h0 : 0 ≤ 2 * C * (1 + (outerMax Y n b : ℝ)) * Real.log n := by positivity
    linarith
  have hRb' : b < maxRadius Y n := not_le.mp hRb
  obtain ⟨j₀, hj₀mem, hj₀⟩ := Finset.exists_mem_eq_sup'
    (⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩ : (Finset.range (n + 1)).Nonempty)
    (fun j => euclidNorm (Y j))
  have hj₀n : j₀ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₀mem)
  have hj₀' : maxRadius Y n = euclidNorm (Y j₀) := hj₀
  have hRpos : 0 < maxRadius Y n := lt_of_le_of_lt hb hRb'
  have hy0 : toSpace (Y j₀) ≠ 0 := by
    intro h
    have h1 : euclidNorm (Y j₀) = 0 := by rw [← norm_toSpace, h, norm_zero]
    linarith
  set q : EuclideanSpace ℝ (Fin d) := unitDir (toSpace (Y j₀)) with hqdef
  have hqn : ‖q‖ = 1 := cr_norm_unitDir hy0
  have hT : inner ℝ q (toSpace (Y j₀)) = maxRadius Y n := by
    rw [hqdef, cr_inner_unitDir_self hy0, norm_toSpace, hj₀']
  have hinner_le : ∀ z : Site d, inner ℝ q (toSpace z) ≤ euclidNorm z := by
    intro z
    calc inner ℝ q (toSpace z) ≤ ‖q‖ * ‖toSpace z‖ := real_inner_le_norm _ _
      _ = euclidNorm z := by rw [hqn, one_mul, norm_toSpace]
  have hq : ‖q‖ ≤ normMax (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) := by
    rw [hΛ, hqn]
  have key := hmain (fun z => unitDir (toSpace z)) hsub hξ0 n hn q hq Y hY.start hY.step
  rw [hΛ] at key
  simp only [mul_one] at key
  have hvecC : ∀ s t : ℕ, s < t → t ≤ n →
      ‖compPath d ε Y t - compPath d ε Y s‖ ≤
        2 * C₁ * Real.sqrt (((t : ℝ) - s) * Real.log n) := by
    intro s t hst htn
    have hst' : (s : ℝ) < t := by exact_mod_cast hst
    exact (hY.vec s t hst htn).trans
      (cr_sqrt_le hC₁.le (by linarith) hlog (cr_log_add_two_le hn))
  have hmartC : ∀ k : ℕ, k ≤ n →
      |dynkinMart (driftStepProb d ε (fun z => unitDir (toSpace z)))
          (fun z => max (inner ℝ q (toSpace z) - k) 0) Y n|
        ≤ 2 * C₁ * (Real.sqrt (Real.log n *
              ∑ z ∈ (departureRange Y n).filter
                (fun z => (k : ℝ) - 1 < inner ℝ q (toSpace z)),
              (localTime Y n z : ℝ)) + Real.log n) := by
    intro k hk
    have hs : euclidNorm (Y j₀) ≤ n :=
      (CERW.Support.Occupation.euclidNorm_le_of_steps Y hY.start hY.step j₀).trans
        (by exact_mod_cast hj₀n)
    exact hlin.mono (by linarith : C₁ ≤ 2 * C₁) (Y j₀) hs k hk
  have hmax : ∀ j ≤ n, inner ℝ q (toSpace (Y j)) ≤ inner ℝ q (toSpace (Y j₀)) := by
    intro j hj
    rw [hT]
    exact (hinner_le (Y j)).trans (hj₀' ▸ euclidNorm_le_maxRadius Y hj)
  have hdrift : ∀ j ≤ n, inner ℝ q (toSpace (Y j₀)) - maxRadius Y n / 2 <
      inner ℝ q (toSpace (Y j)) → (1 / 2 : ℝ) ≤ inner ℝ q (unitDir (toSpace (Y j))) := by
    intro j hj hlt
    rw [hT] at hlt
    have hpos : maxRadius Y n / 2 < inner ℝ q (toSpace (Y j)) := by linarith
    have hyj : toSpace (Y j) ≠ 0 := by
      intro h
      rw [h, inner_zero_right] at hpos
      linarith
    have hnyj : 0 < ‖toSpace (Y j)‖ := norm_pos_iff.mpr hyj
    have hnle : ‖toSpace (Y j)‖ ≤ maxRadius Y n := by
      rw [norm_toSpace]
      exact euclidNorm_le_maxRadius Y hj
    rw [cr_inner_unitDir_right, ← div_eq_inv_mul, le_div_iff₀ hnyj]
    linarith
  have fin : inner ℝ q (toSpace (Y j₀)) ≤ max (inner ℝ q (toSpace (Y j₀)) - maxRadius Y n / 2) b +
      C * (1 + ((((departureRange Y n).filter
        (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime Y n) : ℕ) : ℝ)) * Real.log n :=
    key hvecC hmartC j₀ hj₀n hmax (maxRadius Y n / 2) (by positivity) hdrift b hb
  rw [hT] at fin
  have hsup : ((departureRange Y n).filter
      (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime Y n) ≤ outerMax Y n b := by
    refine Finset.sup_mono ?_
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.trans (hinner_le z)⟩
  have hsup' : ((((departureRange Y n).filter
      (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime Y n) : ℕ) : ℝ) ≤
        (outerMax Y n b : ℝ) := by exact_mod_cast hsup
  have hX : C * (1 + ((((departureRange Y n).filter
      (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime Y n) : ℕ) : ℝ)) * Real.log n ≤
        C * (1 + (outerMax Y n b : ℝ)) * Real.log n :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC.le) hlog
  have hX0 : 0 ≤ C * (1 + (outerMax Y n b : ℝ)) * Real.log n := by positivity
  rcases le_total (maxRadius Y n - maxRadius Y n / 2) b with h | h
  · rw [max_eq_right h] at fin
    linarith
  · rw [max_eq_left h] at fin
    linarith
/-! ### The linear martingales -/

section LinMart

open CERW.Support.Law CERW.Support.LocalTime
open LatticeProb (ballFinset mem_ballFinset_iff card_ballFinset_le)

/-- The embedding of lattice sites is additive. -/
private lemma lm_toSpace_add (x y : Site d) : toSpace (x + y) = toSpace x + toSpace y := by
  ext i
  simp [toSpace]

/-- A unit step changes a projection `q · z` by at most one when `‖q‖ ≤ 1`. -/
private lemma lm_abs_inner_le {q : EuclideanSpace ℝ (Fin d)} (hq : ‖q‖ ≤ 1) {e : Site d}
    (he : e ∈ unitSteps d) : |inner ℝ q (toSpace e)| ≤ 1 := by
  calc |inner ℝ q (toSpace e)| ≤ ‖q‖ * ‖toSpace e‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 := by
      rw [norm_toSpace, euclidNorm_of_mem_unitSteps he, mul_one]
      exact hq

/-- One unit step changes the ramp `(q · z - a)₊` by at most one. -/
private lemma lm_ramp_step_abs {q : EuclideanSpace ℝ (Fin d)} (hq : ‖q‖ ≤ 1) (a : ℝ)
    (z : Site d) {e : Site d} (he : e ∈ unitSteps d) :
    |max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0| ≤ 1 := by
  calc |max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0|
      ≤ |(inner ℝ q (toSpace (z + e)) - a) - (inner ℝ q (toSpace z) - a)| :=
        abs_max_sub_max_le_abs _ _ _
    _ = |inner ℝ q (toSpace e)| := by
        rw [lm_toSpace_add, inner_add_right]
        congr 1
        ring
    _ ≤ 1 := lm_abs_inner_le hq he

/-- At `z` with `q · z ≤ a - 1` the ramp vanishes after every unit step. -/
private lemma lm_ramp_step_zero {q : EuclideanSpace ℝ (Fin d)} (hq : ‖q‖ ≤ 1) (a : ℝ)
    {z e : Site d} (he : e ∈ unitSteps d) (hz : inner ℝ q (toSpace z) ≤ a - 1) :
    max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0 = 0 := by
  have h2 := abs_le.mp (lm_abs_inner_le hq he)
  rw [lm_toSpace_add, inner_add_right, max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

/-- The squared increment of the ramp over a unit step is at most the indicator of the
half-space `q · z > a - 1`. -/
private lemma lm_ramp_step_sq {q : EuclideanSpace ℝ (Fin d)} (hq : ‖q‖ ≤ 1) (a : ℝ)
    (z : Site d) {e : Site d} (he : e ∈ unitSteps d) :
    (max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0) ^ 2 ≤
      if a - 1 < inner ℝ q (toSpace z) then 1 else 0 := by
  split_ifs with h
  · exact (sq_le_one_iff_abs_le_one _).mpr (lm_ramp_step_abs hq a z he)
  · rw [lm_ramp_step_zero hq a he (not_lt.mp h)]
    norm_num

/-- The number of times `j < t` at which the path lies in the half-space `q · z > a - 1`. -/
private noncomputable def lm_count {Ω : Type*} (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range t, if a - 1 < inner ℝ q (toSpace (X j ω)) then 1 else 0

/-- The count starts at `0`. -/
private lemma lm_count_zero {Ω : Type*} (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (X : ℕ → Ω → Site d) (ω : Ω) : lm_count q a X 0 ω = 0 := by
  simp [lm_count]

/-- The increment of the count is the indicator of the half-space at the current position. -/
private lemma lm_count_succ_sub {Ω : Type*} (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (X : ℕ → Ω → Site d) (j : ℕ) (ω : Ω) :
    lm_count q a X (j + 1) ω - lm_count q a X j ω =
      if a - 1 < inner ℝ q (toSpace (X j ω)) then 1 else 0 := by
  simp only [lm_count, Finset.sum_range_succ]
  ring

/-- The count is nondecreasing. -/
private lemma lm_count_mono {Ω : Type*} (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (X : ℕ → Ω → Site d) (j : ℕ) (ω : Ω) : lm_count q a X j ω ≤ lm_count q a X (j + 1) ω := by
  have h := lm_count_succ_sub q a X j ω
  split_ifs at h <;> linarith

/-- The count up to time `t` is at most `t`. -/
private lemma lm_count_le {Ω : Type*} (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) : lm_count q a X t ω ≤ t := by
  calc lm_count q a X t ω ≤ ∑ _j ∈ Finset.range t, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => by split_ifs <;> norm_num
    _ = t := by simp

/-- The count at time `j + 1` is a function of the past path up to time `j`. -/
private lemma lm_stronglyMeasurable_count {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ n, Measurable (X n)) (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (j : ℕ) : StronglyMeasurable[pathFiltration hX j] (lm_count q a X (j + 1)) := by
  have h := stronglyMeasurable_comp_pastPath hX j
    (fun p => ∑ i ∈ Finset.range (j + 1),
      if a - 1 < inner ℝ q (toSpace (extendPath p i)) then (1 : ℝ) else 0)
  have heq : lm_count q a X (j + 1) = fun ω => ∑ i ∈ Finset.range (j + 1),
      if a - 1 < inner ℝ q (toSpace (extendPath (pastPath X j ω) i)) then (1 : ℝ) else 0 := by
    funext ω
    simp only [lm_count]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [extendPath_pastPath X (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) ω]
  rw [heq]
  exact h

/-- The count up to time `n` is the sum of the local times over the part of the departure range
in the half-space `q · z > a - 1`. -/
private lemma lm_count_eq_sum {Ω : Type*} (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (X : ℕ → Ω → Site d) (n : ℕ) (ω : Ω) :
    lm_count q a X n ω = ∑ z ∈ (departureRange (fun j => X j ω) n).filter
        (fun z => a - 1 < inner ℝ q (toSpace z)), (localTime (fun j => X j ω) n z : ℝ) := by
  rw [lm_count, sum_range_eq_sum_localTime (fun j => X j ω) n
    (fun z => if a - 1 < inner ℝ q (toSpace z) then 1 else 0), Finset.sum_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> simp

/-- The pathwise Dynkin martingale for the drift law of the field `x ↦ u_x` is the Dynkin
martingale of the Euclidean walk. -/
private lemma lm_dynkinMart_eq (hd : 1 ≤ d) (ε : ℝ) (f : Site d → ℝ) {Ω : Type*}
    (X : ℕ → Ω → Site d) (n : ℕ) (ω : Ω) :
    dynkinMart (driftStepProb d ε (fun z => unitDir (toSpace z))) f (fun j => X j ω) n =
      dynkin ε f X n ω := by
  have h : stepProb d ε = driftStepProb d ε (fun z => unitDir (toSpace z)) := by
    funext x n e
    exact CERW.Support.Drift.stepProb_eq_driftStepProb ε x n e
  rw [← h]
  exact CERW.Support.Drift.dynkinMart_stepProb_eq_dynkin hd ε f X n ω

/-- The Dynkin martingale of a ramp agrees almost surely with a martingale whose increments are
at most `2` everywhere and whose conditional variances are at most the increments of the count. -/
private lemma lm_exists_clamped (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ)) {X : ℕ → Ω → Site d}
    (hX : IsCERW μ ε X) {q : EuclideanSpace ℝ (Fin d)} (hq : ‖q‖ ≤ 1) (a : ℝ) :
    ∃ M : ℕ → Ω → ℝ, Martingale M (pathFiltration hX.measurable) μ ∧
      (∀ i ω, |M (i + 1) ω - M i ω| ≤ 2) ∧
      (∀ j, μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | pathFiltration hX.measurable j] ≤ᵐ[μ]
        fun ω => lm_count q a X (j + 1) ω - lm_count q a X j ω) ∧
      ∀ᵐ ω ∂μ, ∀ i,
        M i ω = dynkin ε (fun z => max (inner ℝ q (toSpace z) - a) 0) X i ω := by
  set f : Site d → ℝ := fun z => max (inner ℝ q (toSpace z) - a) 0 with hf
  have hmart := martingale_dynkin hd hε hεd hX f
  have hinc : ∀ i, ∀ᵐ ω ∂μ, |dynkin ε f X (i + 1) ω - dynkin ε f X i ω| ≤ 2 := fun i =>
    (ae_abs_dynkin_succ_sub_le hd hε hεd hX f).mono fun ω hω => by
      simpa using hω i 1 fun e he => lm_ramp_step_abs hq a (X i ω) he
  obtain ⟨M, hM, hbd, -, hae⟩ := CERW.Generic.Martingale.exists_martingale_clamp hmart
    (b := 2) (by norm_num) hinc
  refine ⟨M, hM, hbd, fun j => ?_, hae⟩
  have hsq : (fun ω => (M (j + 1) ω - M j ω) ^ 2) =ᵐ[μ]
      fun ω => (dynkin ε f X (j + 1) ω - dynkin ε f X j ω) ^ 2 := by
    filter_upwards [hae] with ω hω
    rw [hω, hω]
  refine (condExp_congr_ae hsq).trans_le ?_
  filter_upwards [condExp_sq_dynkin_succ_sub_le hd hε hεd hX f j] with ω hω
  refine hω.trans ?_
  rw [lm_count_succ_sub]
  calc ∑ e ∈ unitSteps d, stepProb d ε (fun i => X i ω) j e * (f (X j ω + e) - f (X j ω)) ^ 2
      ≤ ∑ e ∈ unitSteps d, stepProb d ε (fun i => X i ω) j e *
          (if a - 1 < inner ℝ q (toSpace (X j ω)) then 1 else 0) :=
        Finset.sum_le_sum fun e he => mul_le_mul_of_nonneg_left (lm_ramp_step_sq hq a _ he)
          (stepProb_nonneg hε hεd _ j e)
    _ = if a - 1 < inner ℝ q (toSpace (X j ω)) then 1 else 0 := by
        rw [← Finset.sum_mul, sum_stepProb hd ε _ j, one_mul]

/-- One ramp: Freedman's inequality at dyadic brackets bounds the probability that the Dynkin
martingale of the ramp exceeds `c (√(max(V, 1) L) + 2L)`, `V` the count, `L = log (n + 2)`. -/
private lemma lm_event_bound (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d}, IsCERW μ ε X → ∀ n : ℕ, 1 ≤ n →
        ∀ {q : EuclideanSpace ℝ (Fin d)}, ‖q‖ ≤ 1 → ∀ a : ℝ,
        μ {ω | c * (Real.sqrt (max (lm_count q a X n ω) 1 * Real.log (n + 2)) +
            2 * Real.log (n + 2)) <
            |dynkin ε (fun z => max (inner ℝ q (toSpace z) - a) 0) X n ω|} ≤
          ENNReal.ofReal (((n : ℝ) + 1) * (2 * Real.exp (-(K * Real.log (n + 2))))) := by
  obtain ⟨c, hc1, hc⟩ := CERW.Generic.Martingale.exists_dyadic_bound hK
  refine ⟨c, hc1, ?_⟩
  intro Ω _ μ _ X hX n hn q hq a
  obtain ⟨M, hM, hbd, hvar, hae⟩ := lm_exists_clamped hd hε hεd hX hq a
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  have hVW : ∀ ω, lm_count q a X (0 + n) ω - lm_count q a X 0 ω ≤ n := by
    intro ω
    rw [zero_add, lm_count_zero, sub_zero]
    exact lm_count_le q a X n ω
  have hdy := hc hM (V := lm_count q a X) (lm_stronglyMeasurable_count hX.measurable q a)
    (lm_count_zero q a X) (lm_count_mono q a X) hvar (b := 2) (by norm_num) 0 n
    (fun i _ _ ω => hbd i ω) (W := n) hnR hL hVW
  refine le_trans (measure_mono_ae ?_) (hdy.trans ?_)
  · filter_upwards [hae] with ω hω hE
    change _ < _ at hE
    change _ < _
    rw [zero_add, lm_count_zero, sub_zero, hω n, hω 0, dynkin_zero, sub_zero]
    exact hE
  · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [Nat.ceil_natCast]
    have hclog : Nat.clog 2 n ≤ n := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
    have : (Nat.clog 2 n : ℝ) ≤ n := by exact_mod_cast hclog
    linarith

/-- The deterministic step: for `ℓ = log n ≥ 1/2` and `ℓ ≤ L ≤ 2ℓ`, the Freedman threshold
`c (√(max(V, 1) L) + 2L)` is at most `6c (√(ℓ V) + ℓ)`. -/
private lemma lm_threshold_arith {c : ℝ} (hc : 0 ≤ c) {V ℓ L : ℝ} (hV : 0 ≤ V) (hℓ : 1 / 2 ≤ ℓ)
    (hL2 : L ≤ 2 * ℓ) (hL0 : 0 ≤ L) :
    c * (Real.sqrt (max V 1 * L) + 2 * L) ≤ (6 * c) * (Real.sqrt (ℓ * V) + ℓ) := by
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hmax : max V 1 ≤ V + 1 := max_le (by linarith) (by linarith)
  have h1 : Real.sqrt (max V 1 * L) ≤ Real.sqrt (V * L) + Real.sqrt L := by
    calc Real.sqrt (max V 1 * L) ≤ Real.sqrt ((V + 1) * L) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hmax hL0)
      _ = Real.sqrt (V * L + L) := by
          congr 1
          ring
      _ ≤ Real.sqrt (V * L) + Real.sqrt L := sqrt_add_le_add (mul_nonneg hV hL0) hL0
  have h2 : Real.sqrt (V * L) ≤ 2 * Real.sqrt (ℓ * V) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hℓ0 hV)]
    nlinarith [mul_nonneg hℓ0 hV, mul_le_mul_of_nonneg_left hL2 hV]
  have h3 : Real.sqrt L ≤ 2 * ℓ := by
    refine Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩
    nlinarith
  have hsum : Real.sqrt (max V 1 * L) + 2 * L ≤ 6 * (Real.sqrt (ℓ * V) + ℓ) := by
    have := Real.sqrt_nonneg (ℓ * V)
    linarith
  calc c * (Real.sqrt (max V 1 * L) + 2 * L)
      ≤ c * (6 * (Real.sqrt (ℓ * V) + ℓ)) := mul_le_mul_of_nonneg_left hsum hc
    _ = (6 * c) * (Real.sqrt (ℓ * V) + ℓ) := by ring

/-- The arithmetic of the union bound: `(3(n+1))^D · (n+1) · (n+1) · 2 e^{-(p + D + 2)L}` is at
most `(3^D 2^{D+3}) n^{-p}`. -/
private lemma lm_union_arith {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 1 ≤ n) (D : ℕ) :
    (3 * ((n : ℝ) + 1)) ^ D * (((n : ℝ) + 1) * (((n : ℝ) + 1) *
      (2 * Real.exp (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))))) ≤
    (3 ^ D * 2 ^ (D + 3)) * (n : ℝ) ^ (-p) := by
  have h1 := CERW.Generic.Martingale.two_mul_exp_neg_mul_log_le
    (K := p + ((D + 2 : ℕ) : ℝ)) (by positivity) hn
  have h2 := CERW.Generic.Martingale.pow_mul_rpow_neg_le hn (D + 2) p
  have h3 : (0 : ℝ) ≤ 3 ^ D * ((n : ℝ) + 1) ^ (D + 2) := by positivity
  calc (3 * ((n : ℝ) + 1)) ^ D * (((n : ℝ) + 1) * (((n : ℝ) + 1) *
        (2 * Real.exp (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))))
      = (3 ^ D * ((n : ℝ) + 1) ^ (D + 2)) *
          (2 * Real.exp (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) := by
        rw [mul_pow]
        ring
    _ ≤ (3 ^ D * ((n : ℝ) + 1) ^ (D + 2)) * (2 * (n : ℝ) ^ (-(p + ((D + 2 : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left h1 h3
    _ = 2 * 3 ^ D * (((n : ℝ) + 1) ^ (D + 2) * (n : ℝ) ^ (-(p + ((D + 2 : ℕ) : ℝ)))) := by
        ring
    _ ≤ 2 * 3 ^ D * (2 ^ (D + 2) * (n : ℝ) ^ (-p)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (3 ^ D * 2 ^ (D + 3)) * (n : ℝ) ^ (-p) := by ring

/-- `eq:linear-mart`: with probability at least `1 - C n^{-p}` the martingales of the ramps
`(u_s · x - k)₊` are bounded simultaneously for `|s| ≤ n` and `k ≤ n`. -/
private theorem exists_linOK_prob (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) {p : ℝ}
    (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ LinOK d ε C (fun j => X j ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c, hc1, hc⟩ := lm_event_bound hd1 hε.le hεd (K := p + ((d + 2 : ℕ) : ℝ))
    (by positivity)
  have hc0 : 0 ≤ c := by linarith
  have hA : (0 : ℝ) ≤ 3 ^ d * 2 ^ (d + 3) := by positivity
  refine ⟨6 * c + 3 ^ d * 2 ^ (d + 3), by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set S : Finset (Site d × ℕ) := ballFinset d (n : ℝ) ×ˢ Finset.range (n + 1) with hS
  set B : Site d × ℕ → Set Ω := fun sk =>
    {ω | c * (Real.sqrt (max (lm_count (unitDir (toSpace sk.1)) (sk.2 : ℝ) X n ω) 1 *
        Real.log (n + 2)) + 2 * Real.log (n + 2)) <
      |dynkin ε (fun z => max (inner ℝ (unitDir (toSpace sk.1)) (toSpace z) - (sk.2 : ℝ)) 0)
        X n ω|} with hB
  have hbound : ∀ sk ∈ S, μ (B sk) ≤ ENNReal.ofReal (((n : ℝ) + 1) *
      (2 * Real.exp (-((p + ((d + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))) := fun sk _ =>
    hc hX n (by omega) (norm_unitDir_le _) (sk.2 : ℝ)
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log n := by
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
    linarith
  have hlogle : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
    have h1 : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    calc Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
          Real.log_le_log (by linarith) h1
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hScard : (S.card : ℝ) ≤ (3 * ((n : ℝ) + 1)) ^ d * ((n : ℝ) + 1) := by
    have h1 : (S.card : ℝ) = ((ballFinset d (n : ℝ)).card : ℝ) * ((n : ℝ) + 1) := by
      rw [hS, Finset.card_product, Finset.card_range]
      push_cast
      ring
    rw [h1]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact (card_ballFinset_le d (R := (n : ℝ)) (by positivity)).trans
      (pow_le_pow_left₀ (by positivity) (by linarith) d)
  set a : ℝ := ((n : ℝ) + 1) *
    (2 * Real.exp (-((p + ((d + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) with ha
  have ha0 : 0 ≤ a := by positivity
  refine (measure_mono (t := ⋃ sk ∈ S, B sk) ?_).trans ?_
  · intro ω hω
    have hω' : ¬ LinOK d ε (6 * c + 3 ^ d * 2 ^ (d + 3)) (fun j => X j ω) n := hω
    unfold LinOK at hω'
    push Not at hω'
    obtain ⟨s, hs, k, hk, hlt⟩ := hω'
    simp only [Set.mem_iUnion]
    refine ⟨(s, k), ?_, ?_⟩
    · rw [hS, Finset.mem_product, mem_ballFinset_iff, Finset.mem_range]
      exact ⟨hs, by omega⟩
    · rw [lm_dynkinMart_eq hd1 ε _ X n ω,
        ← lm_count_eq_sum (unitDir (toSpace s)) (k : ℝ) X n ω] at hlt
      have hV0 : 0 ≤ lm_count (unitDir (toSpace s)) (k : ℝ) X n ω := by
        rw [lm_count_eq_sum]
        exact Finset.sum_nonneg fun z _ => Nat.cast_nonneg _
      have hthr := lm_threshold_arith hc0 hV0 hlog2 hlogle hlog0
      have hterm : 0 ≤ Real.sqrt (Real.log n * lm_count (unitDir (toSpace s)) (k : ℝ) X n ω) +
          Real.log n :=
        add_nonneg (Real.sqrt_nonneg _) (by linarith)
      have hmono : (6 * c) * (Real.sqrt (Real.log n *
            lm_count (unitDir (toSpace s)) (k : ℝ) X n ω) + Real.log n) ≤
          (6 * c + 3 ^ d * 2 ^ (d + 3)) * (Real.sqrt (Real.log n *
            lm_count (unitDir (toSpace s)) (k : ℝ) X n ω) + Real.log n) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA) hterm
      exact lt_of_le_of_lt (hthr.trans hmono) hlt
  · calc μ (⋃ sk ∈ S, B sk) ≤ ∑ sk ∈ S, μ (B sk) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _sk ∈ S, ENNReal.ofReal a := Finset.sum_le_sum hbound
      _ = ENNReal.ofReal ((S.card : ℝ) * a) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul (p := (S.card : ℝ)) (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((6 * c + 3 ^ d * 2 ^ (d + 3)) * (n : ℝ) ^ (-p)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (S.card : ℝ) * a ≤
              (3 * ((n : ℝ) + 1)) ^ d * ((n : ℝ) + 1) * a :=
            mul_le_mul_of_nonneg_right hScard ha0
          have h2 := lm_union_arith hp.le (by omega : 1 ≤ n) d
          have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
          have h4 : (3 * ((n : ℝ) + 1)) ^ d * ((n : ℝ) + 1) * a =
              (3 * ((n : ℝ) + 1)) ^ d * (((n : ℝ) + 1) * (((n : ℝ) + 1) *
                (2 * Real.exp (-((p + ((d + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))))) := by
            rw [ha]
            ring
          have h5 : (0 : ℝ) ≤ (6 * c) * (n : ℝ) ^ (-p) := mul_nonneg (by linarith) h3
          rw [h4] at h1
          linarith

end LinMart
/-! ### The good event of Sections 4 and 5 -/

/-- The compensated position of the fluctuation event is `compPath` of the path. -/
private lemma pf_compensated_eq {Ω : Type*} (ε : ℝ) (X : ℕ → Ω → Site d) (ω : Ω) (t : ℕ) :
    CERW.Support.Coarse.compensated ε X t ω = compPath d ε (fun j => X j ω) t := by
  unfold CERW.Support.Coarse.compensated compPath
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h0 : X j ω = 0
  · simp [h0, departureRange, CERW.Support.Occupation.toSpace_zero]
  · simp [h0, departureRange]

/-- The good event of the fluctuation theorem's proof gives the path facts. -/
private lemma pf_of_fluctEvent {ε C₀ C₁ : ℝ} (hC₁ : 0 ≤ C₁) {b : Site d → ℝ} {bd r₀ : ℕ}
    {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) {n : ℕ}
    (h : CERW.Support.Main.fluctEvent d ε b C₀ C₁ bd r₀ X ω n) :
    PathFacts d ε C₀ (2 * C₁) (fun j => X j ω) n := by
  dsimp only [CERW.Support.Main.fluctEvent] at h
  obtain ⟨⟨h0, hs⟩, -, hM, hH, -, hglob, hpt, hlm, -, hvec, -⟩ := h
  have hL := mono_log_nonneg n
  refine ⟨h0, hs, hM, hH, fun y hy => ?_, fun x hx => ?_, fun s t hst htn => ?_⟩
  · refine (hglob y hy).trans (mul_le_mul_of_nonneg_right (by linarith) ?_)
    split_ifs
    · exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) hL
    · exact add_nonneg (Real.sqrt_nonneg _) hL
  · have h1 := hpt x hx
    have h2 := hlm x hx
    have hW : braSum (fun j => X j ω) n x = ∑ j ∈ Finset.range n,
        (1 + euclidNorm (X j ω - x)) ^ (2 - 2 * (d : ℝ)) := rfl
    rw [← hW] at h2
    have h3 : |(localTime (fun j => X j ω) n x : ℝ) -
        potential d ε (cellSet (fun j => X j ω) n) (toSpace x)| ≤
        |(localTime (fun j => X j ω) n x : ℝ) -
          potential d ε (cellSet (fun j => X j ω) n) (toSpace x) +
            CERW.Support.Law.dynkin ε (fun z => b (z - x)) X n ω| +
          |CERW.Support.Law.dynkin ε (fun z => b (z - x)) X n ω| := by
      have := abs_sub (a := (localTime (fun j => X j ω) n x : ℝ) -
          potential d ε (cellSet (fun j => X j ω) n) (toSpace x) +
            CERW.Support.Law.dynkin ε (fun z => b (z - x)) X n ω)
        (b := CERW.Support.Law.dynkin ε (fun z => b (z - x)) X n ω)
      simpa using this
    have h4 : 0 ≤ Real.sqrt (braSum (fun j => X j ω) n x * Real.log ((n : ℝ) + 2)) :=
      Real.sqrt_nonneg _
    calc _ ≤ C₁ * Real.log ((n : ℝ) + 2) +
          C₁ * (Real.sqrt (braSum (fun j => X j ω) n x * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2)) := h3.trans (add_le_add h1 h2)
      _ ≤ 2 * C₁ * (Real.sqrt (braSum (fun j => X j ω) n x * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2)) := by nlinarith [mul_nonneg hC₁ h4, mul_nonneg hC₁ hL]
  · rw [← pf_compensated_eq, ← pf_compensated_eq]
    refine (hvec s t hst htn).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))

/-- The events of `prop:coarse`, `lem:local`, `eq:pointwise`, `eq:localmart` and `eq:vector`. -/
private theorem exists_pathFacts_prob (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) {p : ℝ}
    (hp : 0 < p) :
    ∃ C₀ C₁ C : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ PathFacts d ε C₀ C₁ (fun j => X j ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨b, h, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts hd
  obtain ⟨r₀, hr₀⟩ := CERW.Support.Main.exists_event_prob.{u} hd hK
  obtain ⟨C₀, C₁, hC₀, hC₁, hprob⟩ := hr₀ ε hε hεd p hp
  refine ⟨C₀, 2 * C₁, C₁, hC₀, by positivity, hC₁, ?_⟩
  intro Ω _ μ _ X hX n hn
  refine le_trans (measure_mono ?_) (hprob μ X hX n hn)
  intro ω hω hE
  exact hω (pf_of_fluctEvent hC₁.le X ω hE)
/-! ### The deterministic cores -/

/-- The radius is `a n^{1/(d+1)}` with `a > 0`. -/
private lemma tk_radius_eq (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, radius d ε n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
  have hω := unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : 0 < ((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d) := by positivity
  refine ⟨(((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1)),
    Real.rpow_pos_of_pos hc _, fun n => ?_⟩
  unfold radius
  rw [show ((d : ℝ) + 1) * n / (2 * d * ε * unitBallVolume d) =
    (((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d)) * n by ring]
  exact Real.mul_rpow hc.le (Nat.cast_nonneg n)

/-- Every power of `log n` is eventually at most any positive power of the radius. -/
private lemma tk_log_pow_le (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {A : ℝ} (hA : 0 ≤ A) (K : ℝ)
    {s : ℝ} (hs : 0 < s) : ∀ᶠ n : ℕ in atTop, K * Real.log n ^ A ≤ radius d ε n ^ s := by
  obtain ⟨a, ha, hr⟩ := tk_radius_eq hd hε
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : 0 < ((1 : ℝ) / (d + 1)) * s := by positivity
  have hlim := CERW.Support.Main.tendsto_log_rpow_div_rpow A hc
  have hpos : 0 < a ^ s / (|K| + 1) := by positivity
  filter_upwards [hlim.eventually (gt_mem_nhds hpos), eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnc : 0 < (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * s) := Real.rpow_pos_of_pos hn0 _
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hlogle : Real.log n ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log hn0 (by linarith)
  have h1 : Real.log n ^ A ≤ Real.log ((n : ℝ) + 2) ^ A :=
    Real.rpow_le_rpow hlog0 hlogle hA
  have h2 : Real.log ((n : ℝ) + 2) ^ A <
      a ^ s / (|K| + 1) * (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * s) := by
    rwa [div_lt_iff₀ hnc] at hn
  rw [hr n, Real.mul_rpow ha.le (Real.rpow_nonneg hn0.le _), ← Real.rpow_mul hn0.le]
  have hK : K * Real.log n ^ A ≤ (|K| + 1) * Real.log n ^ A :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (Real.rpow_nonneg hlog0 _)
  calc K * Real.log n ^ A ≤ (|K| + 1) * Real.log n ^ A := hK
    _ ≤ (|K| + 1) * Real.log ((n : ℝ) + 2) ^ A :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (|K| + 1) * (a ^ s / (|K| + 1) * (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * s)) :=
        mul_le_mul_of_nonneg_left h2.le (by positivity)
    _ = a ^ s * (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * s) := by field_simp


/-- The radius is positive for `n ≥ 1`. -/
private lemma radius_pos (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    0 < radius d ε n := by
  unfold radius
  have hω := unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

/-- For `n ≥ 2`, `q_n = (log n / r_n)^β` with `β = 1/2` in the plane and `β = 1` otherwise. -/
private lemma tk_qrate_eq (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n) :
    qrate d ε n = (Real.log n / radius d ε n) ^ (if d = 2 then (1 : ℝ) / 2 else 1) := by
  have hr := radius_pos hd hε (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  unfold qrate
  split_ifs
  · exact Real.sqrt_eq_rpow _
  · exact (Real.rpow_one _).symm

/-- `r_n q_n^{1/d} = r_n^{1-γ} (log n)^γ` with `γ = β/d`. -/
private lemma tk_rq_rpow (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n) :
    radius d ε n * qrate d ε n ^ ((1 : ℝ) / d) =
      radius d ε n ^ (1 - (if d = 2 then (1 : ℝ) / 2 else 1) / d) *
        Real.log n ^ ((if d = 2 then (1 : ℝ) / 2 else 1) / d) := by
  have hr := radius_pos hd hε (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hx : 0 ≤ Real.log n / radius d ε n := div_nonneg hlog hr.le
  rw [tk_qrate_eq hd hε hn, ← Real.rpow_mul hx, Real.div_rpow hlog hr.le,
    show (if d = 2 then (1 : ℝ) / 2 else 1) * ((1 : ℝ) / d) =
      (if d = 2 then (1 : ℝ) / 2 else 1) / d by ring,
    Real.rpow_sub hr, Real.rpow_one]
  have hg : 0 < radius d ε n ^ ((if d = 2 then (1 : ℝ) / 2 else 1) / d) :=
    Real.rpow_pos_of_pos hr _
  field_simp

/-- `q_n ≤ 1` eventually. -/
private lemma tk_qrate_le_one (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, qrate d ε n ≤ 1 := by
  filter_upwards [tk_log_pow_le hd hε (A := 1) zero_le_one 1 (s := 1) one_pos,
    eventually_ge_atTop 2] with n hn hn2
  have hr := radius_pos hd hε (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  rw [Real.rpow_one, Real.rpow_one, one_mul] at hn
  have h1 : Real.log n / radius d ε n ≤ 1 := (div_le_one hr).2 hn
  unfold qrate
  split_ifs
  · exact Real.sqrt_le_one.mpr h1
  · exact h1

/-- The a priori smallness used to absorb the width: `B log^{d+1} (1 + r q^{1/d}) ≤ r`. -/
private lemma tk_small (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, B * Real.log n ^ ((d : ℝ) + 1) *
      (1 + radius d ε n * qrate d ε n ^ ((1 : ℝ) / d)) ≤ radius d ε n := by
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  set β : ℝ := if d = 2 then (1 : ℝ) / 2 else 1 with hβ
  have hβ0 : 0 < β := by rw [hβ]; split_ifs <;> norm_num
  have hβ1 : β ≤ 1 := by rw [hβ]; split_ifs <;> norm_num
  set γ : ℝ := β / d with hγ
  have hγ0 : 0 < γ := div_pos hβ0 hd0
  have hγ1 : γ ≤ 1 := by
    rw [hγ, div_le_one hd0]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    linarith
  filter_upwards [tk_log_pow_le hd1 hε (A := (d : ℝ) + 1) (by positivity) (2 * |B|)
      (s := 1) one_pos,
    tk_log_pow_le hd1 hε (A := (d : ℝ) + 1 + γ) (by positivity) (2 * |B|) hγ0,
    eventually_ge_atTop 2] with n h1 h2 hn2
  have hr := radius_pos hd1 hε (by omega : 1 ≤ n)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  rw [Real.rpow_one] at h1
  rw [tk_rq_rpow hd1 hε hn2, ← hβ, ← hγ]
  have hL1 : 0 ≤ Real.log n ^ ((d : ℝ) + 1) := Real.rpow_nonneg hlog.le _
  have hL2 : Real.log n ^ ((d : ℝ) + 1 + γ) =
      Real.log n ^ ((d : ℝ) + 1) * Real.log n ^ γ := Real.rpow_add hlog _ _
  have hr2 : radius d ε n ^ γ * radius d ε n ^ (1 - γ) = radius d ε n := by
    rw [← Real.rpow_add hr]; simp
  have hBb : B * Real.log n ^ ((d : ℝ) + 1) ≤ |B| * Real.log n ^ ((d : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self B) hL1
  have hpow : 0 ≤ radius d ε n ^ (1 - γ) := Real.rpow_nonneg hr.le _
  have hlg : 0 ≤ Real.log n ^ γ := Real.rpow_nonneg hlog.le _
  calc B * Real.log n ^ ((d : ℝ) + 1) *
        (1 + radius d ε n ^ (1 - γ) * Real.log n ^ γ)
      = B * Real.log n ^ ((d : ℝ) + 1) +
        B * Real.log n ^ ((d : ℝ) + 1) * (radius d ε n ^ (1 - γ) * Real.log n ^ γ) := by ring
    _ ≤ |B| * Real.log n ^ ((d : ℝ) + 1) +
        |B| * Real.log n ^ ((d : ℝ) + 1) * (radius d ε n ^ (1 - γ) * Real.log n ^ γ) := by
        refine add_le_add hBb (mul_le_mul_of_nonneg_right hBb (mul_nonneg hpow hlg))
    _ = |B| * Real.log n ^ ((d : ℝ) + 1) +
        |B| * Real.log n ^ ((d : ℝ) + 1 + γ) * radius d ε n ^ (1 - γ) := by
        rw [hL2]; ring
    _ ≤ radius d ε n / 2 + radius d ε n ^ γ / 2 * radius d ε n ^ (1 - γ) := by
        refine add_le_add (by linarith) (mul_le_mul_of_nonneg_right (by linarith) hpow)
    _ = radius d ε n := by rw [div_mul_eq_mul_div, hr2]; ring


/-- The rate `q_n` is nonnegative for `n ≥ 1`. -/
private lemma qrate_nonneg (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ qrate d ε n := by
  unfold qrate
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hr := radius_pos hd hε hn
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact div_nonneg hlog hr.le

/-- `r_n q_n` is `√(r_n log n)` in the plane and `log n` in higher dimensions. -/
private lemma radius_mul_qrate (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    radius d ε n * qrate d ε n =
      if d = 2 then Real.sqrt (radius d ε n * Real.log n) else Real.log n := by
  have hr := radius_pos hd hε hn
  unfold qrate
  split_ifs
  · have hnn : 0 ≤ radius d ε n := hr.le
    rw [← Real.sqrt_sq hnn, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnn]
    congr 1
    field_simp
  · field_simp


/-- For `n ≥ 2`, `log (n + 2) ≤ 2 log n`. -/
private lemma co_log_add_two_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log (by linarith) (by nlinarith)
    _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num

/-- The path stays within distance `n` of the origin. -/
private lemma co_maxRadius_le {Y : ℕ → Site d} {n : ℕ} (hpath : ∀ j, euclidNorm (Y j) ≤ j) :
    maxRadius Y n ≤ n := by
  unfold maxRadius
  refine Finset.sup'_le _ _ fun j hj => (hpath j).trans ?_
  exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)

/-- A visited site lies within the maximal radius, so off that ball the local time vanishes. -/
private lemma co_localTime_eq_zero {Y : ℕ → Site d} {n : ℕ} {x : Site d}
    (hx : maxRadius Y n < euclidNorm x) : localTime Y n x = 0 := by
  by_contra h
  have h1 : x ∈ departureRange Y n := mem_departureRange_iff.mpr (Nat.pos_of_ne_zero h)
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h1
  exact absurd (euclidNorm_le_maxRadius Y (Finset.mem_range.mp hj).le) (not_le.mpr hx)

/-- The maximal local time over the sites beyond a radius is bounded by a bound on each one. -/
private lemma co_outerMax_le {Y : ℕ → Site d} {n : ℕ} {b M : ℝ} (hM : 0 ≤ M)
    (h : ∀ z ∈ departureRange Y n, b ≤ euclidNorm z → (localTime Y n z : ℝ) ≤ M) :
    (outerMax Y n b : ℝ) ≤ M := by
  have h1 : outerMax Y n b ≤ ⌊M⌋₊ := by
    refine Finset.sup_le fun z hz => ?_
    rw [Finset.mem_filter] at hz
    exact Nat.le_floor (h z hz.1 hz.2)
  exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hM)

/-- The rate `q_n` is positive for `n ≥ 2`. -/
private lemma co_qrate_pos (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n) :
    0 < qrate d ε n := by
  rw [tk_qrate_eq hd hε hn]
  have hr := radius_pos hd hε (by omega : 1 ≤ n)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  exact Real.rpow_pos_of_pos (div_pos hlog hr) _

/-- Beyond the inner radius the local times are at most `C r q^{1/d}` (from the profile clause
of Proposition 6.1 and the inner radius clause). -/
private lemma co_local_le (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {Cin : ℝ} (hCin : 0 < Cin)
    {Y : ℕ → Site d} {n : ℕ} (hn : 2 ≤ n) (hI : InnerOK d ε Cin Y n)
    (hq : qrate d ε n ≤ 1) {z : Site d} (hz : innerRadius Y n ≤ euclidNorm z) :
    (localTime Y n z : ℝ) ≤
      (2 * d * ε + 1) * Cin * (radius d ε n * qrate d ε n ^ ((1 : ℝ) / d)) := by
  have hr := radius_pos hd hε (by omega : 1 ≤ n)
  have hq0 := co_qrate_pos hd hε hn
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨i1, -, i3⟩ := hI
  have h3 := i3 (toSpace z)
  rw [cellLocalTime_of_mem_cell _ _ (toSpace_mem_cell z), norm_toSpace] at h3
  have hb := (abs_le.mp i1).1
  have hmax : max (radius d ε n - euclidNorm z) 0 ≤ Cin * radius d ε n * qrate d ε n := by
    refine max_le (by linarith) (by positivity)
  have hqq : qrate d ε n ≤ qrate d ε n ^ ((1 : ℝ) / d) := by
    have h1 : (1 : ℝ) / d ≤ 1 := by
      rw [div_le_one hd0]; exact_mod_cast hd
    calc qrate d ε n = qrate d ε n ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ qrate d ε n ^ ((1 : ℝ) / d) :=
          Real.rpow_le_rpow_of_exponent_ge hq0 hq h1
  have hqd : 0 ≤ qrate d ε n ^ ((1 : ℝ) / d) := Real.rpow_nonneg hq0.le _
  have h4 := (abs_le.mp h3).2
  have h5 : 2 * d * ε * max (radius d ε n - euclidNorm z) 0 ≤
      2 * d * ε * (Cin * radius d ε n * qrate d ε n) :=
    mul_le_mul_of_nonneg_left hmax (by positivity)
  have h6 : Cin * radius d ε n * qrate d ε n ≤ Cin * radius d ε n * qrate d ε n ^ ((1 : ℝ) / d) :=
    mul_le_mul_of_nonneg_left hqq (by positivity)
  nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * d * ε) hCin.le) hr.le]

/-- Proposition 7.1, `d ≥ 3`, deterministically. -/
private theorem outer_core_high (hd : 3 ≤ d) (hN : NewtonConv d) (hnear : near_far) {ε : ℝ}
    (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) (C₀ C₁ Cin Ccr : ℝ) (hCin : 0 < Cin)
    (hCcr : 0 < Ccr) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      PathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n → CrossOK d Ccr Y n →
      maxRadius Y n ≤ radius d ε n + C * Real.log n ^ ((d : ℝ) + 1) := by
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Kh, hKh, nh, hhx⟩ := high_exterior hd hN hnear hε hεd C₀ C₁ Cin
    (Cin * (1 + d * unitBallVolume d))
  set K₁ : ℝ := Ccr + 2 * Real.sqrt d / Real.log 2 with hK₁
  have hK₁pos : 0 < K₁ := by positivity
  obtain ⟨Ka, hKa, harith⟩ := arith_high hd K₁ Kh Kh hK₁pos hKh hKh
  set Mc : ℝ := (2 * d * ε + 1) * Cin with hMc
  set B : ℝ := max Ka 8 * (K₁ * (1 + Mc)) with hB
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 ((tk_small hd2 hε B).and (tk_qrate_le_one hd1 hε))
  refine ⟨Cin + Ka, by positivity, max (max n₁ nh) 3, ?_⟩
  intro Y n hn hP hI hC
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn2 : 2 ≤ n := by omega
  have hnh : nh ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  obtain ⟨hsm, hq1⟩ := hn₁ n hn1
  have hr := radius_pos hd1 hε (by omega : 1 ≤ n)
  set r := radius d ε n with hr_def
  set lg := Real.log n with hlg_def
  have hlg1 : 1 ≤ lg := by
    rw [hlg_def, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    exact this.le.trans (by exact_mod_cast hn3)
  have hlg2 : Real.log 2 ≤ lg := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  set b := innerRadius Y n with hb_def
  set R := maxRadius Y n with hR_def
  set w := R - b + 2 * Real.sqrt d with hw_def
  have hbR := innerRadius_le hd1 Y n
  have hw0 : 0 < w := by rw [hw_def]; linarith
  have hb0 := innerRadius_nonneg Y n
  -- the maximal local time
  have hM0 : 0 ≤ Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)) := by
    have := co_qrate_pos hd1 hε hn2
    positivity
  have hL : (outerMax Y n b : ℝ) ≤ Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)) := by
    refine co_outerMax_le hM0 fun z _ hz => ?_
    exact co_local_le hd1 hε hCin hn2 hI hq1 hz
  have hcr := hC b hb0
  have hL0 : (0 : ℝ) ≤ (outerMax Y n b : ℝ) := Nat.cast_nonneg _
  have hw1 : w ≤ K₁ * lg * (1 + (outerMax Y n b : ℝ)) := by
    have h2 : 2 * Real.sqrt d ≤ (2 * Real.sqrt d / Real.log 2) * lg := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      exact mul_le_mul_of_nonneg_left hlg2 (by positivity)
    have h3 : (2 * Real.sqrt d / Real.log 2) * lg ≤
        (2 * Real.sqrt d / Real.log 2) * lg * (1 + (outerMax Y n b : ℝ)) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    have h4 : Ccr * (1 + (outerMax Y n b : ℝ)) * lg =
        Ccr * lg * (1 + (outerMax Y n b : ℝ)) := by ring
    have h5 : K₁ * lg * (1 + (outerMax Y n b : ℝ)) =
        Ccr * lg * (1 + (outerMax Y n b : ℝ)) +
          (2 * Real.sqrt d / Real.log 2) * lg * (1 + (outerMax Y n b : ℝ)) := by
      rw [hK₁]; ring
    rw [hw_def, h5]
    linarith
  -- smallness of the width
  have hw2 : w ≤ K₁ * lg * (1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d))) := by
    refine hw1.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hlgd : 1 ≤ lg ^ d := one_le_pow₀ hlg1
  have hsm' : B * lg ^ ((d : ℝ) + 1) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) ≤ r := hsm
  have hX0 : 0 ≤ r * qrate d ε n ^ ((1 : ℝ) / d) := by
    have := co_qrate_pos hd1 hε hn2
    positivity
  have hMc0 : 0 ≤ Mc := by rw [hMc]; positivity
  have hmax0 : 0 ≤ max Ka 8 := le_trans (by norm_num) (le_max_right _ _)
  have hpowcast : lg ^ ((d : ℝ) + 1) = lg ^ (d + 1) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  have hw3 : max Ka 8 * lg ^ d * w ≤ r := by
    calc max Ka 8 * lg ^ d * w ≤ max Ka 8 * lg ^ d * (K₁ * lg * (1 + Mc *
          (r * qrate d ε n ^ ((1 : ℝ) / d)))) :=
          mul_le_mul_of_nonneg_left hw2 (by positivity)
      _ = max Ka 8 * K₁ * lg ^ (d + 1) * (1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d))) := by
          rw [pow_succ]; ring
      _ ≤ B * lg ^ ((d : ℝ) + 1) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) := by
          rw [hpowcast, hB]
          have h1 : 1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)) ≤
              (1 + Mc) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) := by
            have h2 : (1 + Mc) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) =
                1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)) +
                  (r * qrate d ε n ^ ((1 : ℝ) / d) + Mc) := by ring
            rw [h2]
            linarith
          calc max Ka 8 * K₁ * lg ^ (d + 1) * (1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)))
              ≤ max Ka 8 * K₁ * lg ^ (d + 1) * ((1 + Mc) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d))) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = _ := by ring
      _ ≤ r := hsm'
  have hw4 : w ≤ r / 8 := by
    have h8 : 8 * w ≤ max Ka 8 * lg ^ d * w := by
      refine mul_le_mul_of_nonneg_right ?_ hw0.le
      calc (8 : ℝ) = 8 * 1 := by norm_num
        _ ≤ max Ka 8 * lg ^ d := mul_le_mul (le_max_right _ _) hlgd zero_le_one hmax0
    linarith
  have hw5 : Ka * lg ^ d * w ≤ r := by
    refine le_trans ?_ hw3
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity)) hw0.le
  have hmass := mass_of_inner hd2 hε hCin.le Y (by omega : 1 ≤ n) hI
  obtain ⟨Θ, hΘ1, hΘ2, hΘ3⟩ := hhx Y n hnh hP hI hmass (by rw [← hr_def]; exact hw4)
  have hfin := harith lg r w (outerMax Y n b : ℝ) Θ hlg1 hr hw0.le hL0 hw1 hΘ3 hΘ1 hΘ2 hw5
  have hbr : b ≤ r + Cin * lg := by
    have h1 := (abs_le.mp hI.1).2
    have h2 := radius_mul_qrate hd1 hε (by omega : 1 ≤ n)
    rw [if_neg (by omega : d ≠ 2)] at h2
    have h3 : Cin * r * qrate d ε n = Cin * (r * qrate d ε n) := by ring
    rw [h3, h2] at h1
    linarith
  have hlgle : lg ≤ lg ^ ((d : ℝ) + 1) := by
    calc lg = lg ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ lg ^ ((d : ℝ) + 1) :=
          Real.rpow_le_rpow_of_exponent_le hlg1 (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  have hpow0 : 0 ≤ lg ^ ((d : ℝ) + 1) := Real.rpow_nonneg (by linarith) _
  have hRw : R ≤ b + w := by rw [hw_def]; linarith
  rw [hpowcast] at hlgle hpow0 ⊢
  calc R ≤ b + w := hRw
    _ ≤ r + Cin * lg + Ka * lg ^ (d + 1) := by linarith
    _ ≤ r + (Cin + Ka) * lg ^ (d + 1) := by
        have h1 := mul_le_mul_of_nonneg_left hlgle hCin.le
        have h2 : (Cin + Ka) * lg ^ (d + 1) = Cin * lg ^ (d + 1) + Ka * lg ^ (d + 1) := by ring
        rw [h2]
        linarith

/-- The planar absorption: from `w ≤ K₁ lg (1 + L)` and `L ≤ C₂ (t √w + t²)` with `t⁴ = r lg`. -/
private lemma co_planar_arith {K₁ C₂ lg r w L : ℝ} (hK₁ : 0 ≤ K₁) (hC₂ : 0 ≤ C₂)
    (hlg : 1 ≤ lg) (hr : 1 ≤ r) (hw : 0 ≤ w)
    (h1 : w ≤ K₁ * lg * (1 + L))
    (h2 : L ≤ C₂ * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg))) :
    w ≤ (2 * K₁ + (K₁ * C₂) ^ 2 + 2 * K₁ * C₂) * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) := by
  have hr0 : 0 ≤ r := by linarith
  have hlg0 : 0 < lg := by linarith
  set t : ℝ := (r * lg) ^ ((1 : ℝ) / 4) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by positivity) _
  have ht2 : t ^ 2 = Real.sqrt r * lg ^ ((1 : ℝ) / 2) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    rw [show ((1 : ℝ) / 4) * ((2 : ℕ) : ℝ) = 1 / 2 by push_cast; ring,
      Real.mul_rpow hr0 hlg0.le, Real.sqrt_eq_rpow]
  have hsq : Real.sqrt (r * lg) = t ^ 2 := by
    rw [ht2, Real.sqrt_mul hr0, Real.sqrt_eq_rpow lg]
  set u : ℝ := Real.sqrt w with hu
  have hu2 : u ^ 2 = w := Real.sq_sqrt hw
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  rw [hsq] at h2
  have h3 : w ≤ K₁ * lg + K₁ * C₂ * lg * t * u + K₁ * C₂ * lg * t ^ 2 := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ K₁ * lg)
    nlinarith
  have hamgm : K₁ * C₂ * lg * t * u ≤ w / 2 + (K₁ * C₂ * lg * t) ^ 2 / 2 := by
    have := two_mul_le_add_sq u (K₁ * C₂ * lg * t)
    rw [hu2] at this
    nlinarith
  have h4 : w ≤ 2 * K₁ * lg + (K₁ * C₂) ^ 2 * lg ^ 2 * t ^ 2 + 2 * K₁ * C₂ * lg * t ^ 2 := by
    nlinarith
  have hl1 : lg ≤ Real.sqrt r * lg ^ ((5 : ℝ) / 2) := by
    have h5 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
    have h6 : lg ≤ lg ^ ((5 : ℝ) / 2) := by
      calc lg = lg ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ lg ^ ((5 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hlg (by norm_num)
    calc lg ≤ lg ^ ((5 : ℝ) / 2) := h6
      _ = 1 * lg ^ ((5 : ℝ) / 2) := (one_mul _).symm
      _ ≤ Real.sqrt r * lg ^ ((5 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hlg0.le _)
  have h52 : lg ^ 2 * t ^ 2 = Real.sqrt r * lg ^ ((5 : ℝ) / 2) := by
    rw [ht2, show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num, Real.rpow_add hlg0, Real.rpow_two]
    ring
  have h32 : lg * t ^ 2 ≤ Real.sqrt r * lg ^ ((5 : ℝ) / 2) := by
    rw [← h52, sq lg]
    have h7 : lg * t ^ 2 * 1 ≤ lg * t ^ 2 * lg :=
      mul_le_mul_of_nonneg_left hlg (by positivity)
    calc lg * t ^ 2 = lg * t ^ 2 * 1 := (mul_one _).symm
      _ ≤ lg * t ^ 2 * lg := h7
      _ = lg * lg * t ^ 2 := by ring
  have hK : 0 ≤ K₁ * C₂ := mul_nonneg hK₁ hC₂
  have e1 : 2 * K₁ * lg ≤ 2 * K₁ * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hl1 (by positivity)
  have e2 : (K₁ * C₂) ^ 2 * (lg ^ 2 * t ^ 2) =
      (K₁ * C₂) ^ 2 * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) := by
    rw [h52]
  have e3 : 2 * K₁ * C₂ * (lg * t ^ 2) ≤
      2 * K₁ * C₂ * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left h32 (by positivity)
  have e4 : (2 * K₁ + (K₁ * C₂) ^ 2 + 2 * K₁ * C₂) * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) =
      2 * K₁ * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) +
        (K₁ * C₂) ^ 2 * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) +
        2 * K₁ * C₂ * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) := by ring
  have e5 : (K₁ * C₂) ^ 2 * lg ^ 2 * t ^ 2 = (K₁ * C₂) ^ 2 * (lg ^ 2 * t ^ 2) := by ring
  have e6 : 2 * K₁ * C₂ * lg * t ^ 2 = 2 * K₁ * C₂ * (lg * t ^ 2) := by ring
  rw [e4]
  rw [e5, e6] at h4
  linarith

/-- The potential of a set outside the ball of radius `b` is nonnegative inside that ball. -/
private lemma co_potential_nonneg_inside (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) {b : ℝ}
    (hsub : E ⊆ {v | b ≤ ‖v‖}) {y : EuclideanSpace ℝ (Fin d)} (hy : ‖y‖ ≤ b) :
    0 ≤ potential d ε E y := by
  unfold potential
  refine mul_nonneg (by have := unitBallVolume_pos d; positivity) ?_
  refine setIntegral_nonneg hE fun v hv => ?_
  by_cases hvy : v = y
  · rw [hvy]; simp
  · have h1 := CERW.Support.Contact.rpow_le_inner_unitDir_div hd (hy.trans (hsub hv)) hvy
    exact le_trans (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (norm_nonneg _) _)) h1

/-- The potential is at most its positive part. -/
private lemma co_potential_le_positive (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (y : EuclideanSpace ℝ (Fin d)) : potential d ε E y ≤ positivePotential d ε E y := by
  unfold potential positivePotential
  refine mul_le_mul_of_nonneg_left ?_ (by have := unitBallVolume_pos d; positivity)
  have hint := CERW.Support.Geometry.integrableOn_potentialIntegrand hd hE
    hEb.measure_lt_top.ne y
  exact integral_mono hint hint.pos_part fun v => le_max_left _ _

/-- Proposition 7.1, `d = 2`, deterministically. -/
private theorem outer_core_planar (hd : d = 2) (hnear : near_far) {ε : ℝ}
    (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) (C₀ C₁ Cin Ccr : ℝ) (hCin : 0 < Cin)
    (hCcr : 0 < Ccr) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      PathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n → CrossOK d Ccr Y n →
      maxRadius Y n ≤
        radius d ε n + C * (Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)) := by
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Cp, hCp, np, hpl⟩ := planar_exterior hd hnear hε hεd C₀ C₁ Cin
    (Cin * (1 + d * unitBallVolume d))
  set K₁ : ℝ := Ccr + 2 * Real.sqrt d / Real.log 2 with hK₁
  have hK₁pos : 0 < K₁ := by positivity
  set Mc : ℝ := (2 * d * ε + 1) * Cin with hMc
  set B : ℝ := K₁ * (1 + Mc) with hB
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 ((tk_small hd2 hε B).and
    ((tk_qrate_le_one hd1 hε).and (tk_log_pow_le hd1 hε (A := 0) le_rfl 1 (s := 1) one_pos)))
  set Kw : ℝ := 2 * K₁ + (K₁ * (2 * Cp)) ^ 2 + 2 * K₁ * (2 * Cp) with hKw
  refine ⟨Cin + Kw, by positivity, max (max n₁ np) 3, ?_⟩
  intro Y n hn hP hI hC
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn2 : 2 ≤ n := by omega
  have hnp : np ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  obtain ⟨hsm, hq1, hr1⟩ := hn₁ n hn1
  have hr := radius_pos hd1 hε (by omega : 1 ≤ n)
  set r := radius d ε n with hr_def
  set lg := Real.log n with hlg_def
  have hlg1 : 1 ≤ lg := by
    rw [hlg_def, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    exact this.le.trans (by exact_mod_cast hn3)
  have hlg2 : Real.log 2 ≤ lg := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hlg0 : 0 < lg := by linarith
  simp only [Real.rpow_zero, mul_one, Real.rpow_one] at hr1
  set b := innerRadius Y n with hb_def
  set R := maxRadius Y n with hR_def
  set w := R - b + 2 * Real.sqrt d with hw_def
  have hbR := innerRadius_le hd1 Y n
  have hw0 : 0 < w := by rw [hw_def]; linarith
  have hb0 := innerRadius_nonneg Y n
  have hpath : ∀ j, euclidNorm (Y j) ≤ j :=
    CERW.Support.Occupation.euclidNorm_le_of_steps Y hP.start hP.step
  have hRn : R ≤ n := co_maxRadius_le hpath
  have hrq := radius_mul_qrate hd1 hε (by omega : 1 ≤ n)
  rw [if_pos hd] at hrq
  have hbr : |b - r| ≤ Cin * Real.sqrt (r * lg) := by
    have := hI.1
    calc |b - r| ≤ Cin * r * qrate d ε n := this
      _ = Cin * (r * qrate d ε n) := by ring
      _ = Cin * Real.sqrt (r * lg) := by rw [hrq]
  -- the maximal local time
  have hX0 : 0 ≤ r * qrate d ε n ^ ((1 : ℝ) / d) := by
    have := co_qrate_pos hd1 hε hn2
    positivity
  have hMc0 : 0 ≤ Mc := by rw [hMc]; positivity
  have hM0 : 0 ≤ Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)) := mul_nonneg hMc0 hX0
  have hL : (outerMax Y n b : ℝ) ≤ Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)) := by
    refine co_outerMax_le hM0 fun z _ hz => ?_
    exact co_local_le hd1 hε hCin hn2 hI hq1 hz
  have hcr := hC b hb0
  have hL0 : (0 : ℝ) ≤ (outerMax Y n b : ℝ) := Nat.cast_nonneg _
  have hw1 : w ≤ K₁ * lg * (1 + (outerMax Y n b : ℝ)) := by
    have h2 : 2 * Real.sqrt d ≤ (2 * Real.sqrt d / Real.log 2) * lg := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      exact mul_le_mul_of_nonneg_left hlg2 (by positivity)
    have h3 : (2 * Real.sqrt d / Real.log 2) * lg ≤
        (2 * Real.sqrt d / Real.log 2) * lg * (1 + (outerMax Y n b : ℝ)) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    have h4 : Ccr * (1 + (outerMax Y n b : ℝ)) * lg =
        Ccr * lg * (1 + (outerMax Y n b : ℝ)) := by ring
    have h5 : K₁ * lg * (1 + (outerMax Y n b : ℝ)) =
        Ccr * lg * (1 + (outerMax Y n b : ℝ)) +
          (2 * Real.sqrt d / Real.log 2) * lg * (1 + (outerMax Y n b : ℝ)) := by
      rw [hK₁]; ring
    rw [hw_def, h5]
    linarith
  have hw2 : w ≤ K₁ * lg * (1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d))) :=
    hw1.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hpowcast : lg ^ ((d : ℝ) + 1) = lg ^ (d + 1) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  have hwr : w ≤ r / lg := by
    rw [le_div_iff₀ hlg0]
    have hsm' : B * lg ^ (d + 1) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) ≤ r := by
      rw [← hpowcast]; exact hsm
    have hlg2' : lg ^ 2 ≤ lg ^ (d + 1) := pow_le_pow_right₀ hlg1 (by omega)
    calc w * lg ≤ K₁ * lg * (1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d))) * lg :=
          mul_le_mul_of_nonneg_right hw2 hlg0.le
      _ = K₁ * lg ^ 2 * (1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d))) := by ring
      _ ≤ K₁ * lg ^ (d + 1) * ((1 + Mc) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d))) := by
          have h1 : 1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)) ≤
              (1 + Mc) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) := by
            have h2 : (1 + Mc) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) =
                1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)) +
                  (r * qrate d ε n ^ ((1 : ℝ) / d) + Mc) := by ring
            rw [h2]
            linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left hlg2' hK₁pos.le) h1 (by positivity)
            (by positivity)
      _ = B * lg ^ (d + 1) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) := by rw [hB]; ring
      _ ≤ r := hsm'
  have hmass := mass_of_inner hd2 hε hCin.le Y (by omega : 1 ≤ n) hI
  obtain ⟨hpt, hpos⟩ := hpl Y n hnp hP hI hmass (by rw [← hr_def]; exact hwr)
  have hE : MeasurableSet (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) :=
    (CERW.Support.Occupation.measurableSet_cellSet Y n).diff Metric.isOpen_ball.measurableSet
  have hEb : Bornology.IsBounded (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) :=
    (Metric.isBounded_ball.subset
      (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n)).subset Set.sdiff_subset
  have hL2 : (outerMax Y n b : ℝ) ≤ (2 * Cp) * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w +
      Real.sqrt (r * lg)) := by
    have hbound0 : 0 ≤ (2 * Cp) * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w +
        Real.sqrt (r * lg)) := by positivity
    refine co_outerMax_le hbound0 fun z hz hbz => ?_
    have hzR : euclidNorm z ≤ R :=
      LatticeProb.mem_ballFinset_iff.mp
        (CERW.Support.Occupation.departureRange_subset_ballFinset Y n hz)
    have hRn' : (R : ℝ) ≤ n := hRn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : |(localTime Y n z : ℝ) - potential d ε (cellSet Y n \ Metric.ball 0 b)
        (toSpace z)| ≤ Cp * Real.sqrt (r * lg) := hpt z hbz (by linarith)
    have h2 : positivePotential d ε (cellSet Y n \ Metric.ball 0 b) (toSpace z) ≤
        Cp * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg)) :=
      hpos (toSpace z) (by rw [norm_toSpace]; exact hbz) (by rw [norm_toSpace]; linarith)
    have h3 := co_potential_le_positive hd1 hε.le hE hEb (toSpace z)
    have h4 := (abs_le.mp h1).2
    have hA : 0 ≤ Cp * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w) := by positivity
    linarith
  have hw3 := co_planar_arith (K₁ := K₁) (C₂ := 2 * Cp) hK₁pos.le (by positivity) hlg1 hr1
    hw0.le hw1 hL2
  have hT : Real.sqrt (r * lg) ≤ Real.sqrt r * lg ^ ((5 : ℝ) / 2) := by
    have h5 : Real.sqrt lg ≤ lg ^ ((5 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hlg1 (by norm_num)
    rw [Real.sqrt_mul hr.le]
    exact mul_le_mul_of_nonneg_left h5 (Real.sqrt_nonneg _)
  have hRb : R ≤ b + w := by rw [hw_def]; linarith
  have hb2 := (abs_le.mp hbr).2
  have hZ0 : 0 ≤ Real.sqrt r * lg ^ ((5 : ℝ) / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlg0.le _)
  have h6 : Cin * Real.sqrt (r * lg) ≤ Cin * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hT hCin.le
  have h7 : (Cin + Kw) * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) =
      Cin * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) + Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) := by
    ring
  rw [h7]
  linarith

/-- Theorem 1.2 (iii), `d ≥ 3`, deterministically. -/
private theorem local_core_high (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (C₀ C₁ Cin Cout : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hCin : 0 < Cin) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      PathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n →
      maxRadius Y n ≤ radius d ε n + Cout * Real.log n ^ ((d : ℝ) + 1) →
      ∀ x : Site d, |(localTime Y n x : ℝ) - 2 * d * ε * max (radius d ε n - euclidNorm x) 0| ≤
        C * Real.sqrt (radius d ε n * Real.log n) := by
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  obtain ⟨a, ha, hra⟩ := tk_radius_eq hd1 hε
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1
    (((tk_log_pow_le hd1 hε (A := (d : ℝ) + 1) (by positivity) 1 (s := 1 / 2)
        (by norm_num)).and
      (tk_log_pow_le hd1 hε (A := 1) zero_le_one (2 * Cin) (s := 1) one_pos)).and
      (tk_log_pow_le hd1 hε (A := 1) zero_le_one 1 (s := 1) one_pos))
  set Cδ : ℝ := C₁ * (Real.sqrt (2 * C₀ / a) + 2) with hCδ
  set Cw : ℝ := Cin + max Cout 0 + 2 * Real.sqrt d with hCw
  set C : ℝ := Cδ + 2 * d * ε * (Cw + Cin + Real.sqrt d) with hC
  have hCpos : 0 < C := by rw [hC, hCδ, hCw]; positivity
  refine ⟨C, hCpos, max n₁ 3, ?_⟩
  intro Y n hn hP hI hout x
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn2 : 2 ≤ n := by omega
  have hn1 : n₁ ≤ n := le_trans (le_max_left _ _) hn
  obtain ⟨⟨h1, h2⟩, h3⟩ := hn₁ n hn1
  have hr := radius_pos hd1 hε (by omega : 1 ≤ n)
  set r := radius d ε n with hr_def
  set lg := Real.log n with hlg_def
  have hlg1 : 1 ≤ lg := by
    rw [hlg_def, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    exact this.le.trans (by exact_mod_cast hn3)
  have hlg0 : 0 < lg := by linarith
  simp only [Real.rpow_one, one_mul] at h2 h3
  rw [one_mul] at h1
  have hb0 := innerRadius_nonneg Y n
  have hbR := innerRadius_le hd1 Y n
  set b := innerRadius Y n with hb_def
  set R := maxRadius Y n with hR_def
  have hrq := radius_mul_qrate hd1 hε (by omega : 1 ≤ n)
  rw [if_neg (by omega : d ≠ 2)] at hrq
  have hbr : |b - r| ≤ Cin * lg := by
    have := hI.1
    calc |b - r| ≤ Cin * r * qrate d ε n := this
      _ = Cin * (r * qrate d ε n) := by ring
      _ = Cin * lg := by rw [hrq]
  have hbr1 := abs_le.mp hbr
  have hbpos : 0 < b := by nlinarith
  have hpow1 : lg ≤ lg ^ ((d : ℝ) + 1) := by
    calc lg = lg ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ lg ^ ((d : ℝ) + 1) :=
          Real.rpow_le_rpow_of_exponent_le hlg1 (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  set P := lg ^ ((d : ℝ) + 1) with hP_def
  have hS : P ≤ Real.sqrt (r * lg) := by
    calc P ≤ r ^ ((1 : ℝ) / 2) := h1
      _ = Real.sqrt r := (Real.sqrt_eq_rpow r).symm
      _ ≤ Real.sqrt (r * lg) := Real.sqrt_le_sqrt (le_mul_of_one_le_right hr.le hlg1)
  set S := Real.sqrt (r * lg) with hS_def
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hlgS : lg ≤ S := hpow1.trans hS
  have hw0 : 0 < R - b + 2 * Real.sqrt d := by linarith
  have hwP : R - b + 2 * Real.sqrt d ≤ Cw * P := by
    have hout' : R ≤ r + Cout * P := hout
    have hc : Cout * P ≤ max Cout 0 * P :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    have h4 : Cin * lg ≤ Cin * P := mul_le_mul_of_nonneg_left hpow1 hCin.le
    have h5 : 2 * Real.sqrt d ≤ 2 * Real.sqrt d * P :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    have h6 : Cw * P = Cin * P + max Cout 0 * P + 2 * Real.sqrt d * P := by rw [hCw]; ring
    rw [h6]
    linarith [hbr1.1]
  have hD := CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDb : Bornology.IsBounded (cellSet Y n) :=
    Metric.isBounded_ball.subset (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n)
  have hE : MeasurableSet (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) :=
    hD.diff Metric.isOpen_ball.measurableSet
  have hpath : ∀ j, euclidNorm (Y j) ≤ j :=
    CERW.Support.Occupation.euclidNorm_le_of_steps Y hP.start hP.step
  have hRn : R ≤ n := co_maxRadius_le hpath
  have hCS : 0 ≤ 2 * d * ε := by positivity
  by_cases hxR : euclidNorm x ≤ R
  · -- inside the ball of radius R
    have hy : ‖toSpace x‖ ≤ 2 * n := by
      rw [norm_toSpace]
      have : (R : ℝ) ≤ n := hRn
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hg := hP.glob (toSpace x) hy
    rw [cellLocalTime_of_mem_cell _ _ (toSpace_mem_cell x), if_neg (by omega : d ≠ 2)] at hg
    have hsplit := potential_split hd2 ε hD hDb hbpos (ball_innerRadius_subset hd1 Y n)
      (toSpace x)
    have hann := annulus_potential_le hd2 hε hw0 hE (sdiff_subset_annulus hd1 Y n) (toSpace x)
    rw [norm_toSpace] at hsplit
    have hM : (maxLocalTime Y n : ℝ) ≤ C₀ * (r / a) := by
      have h1 := hP.maxLoc
      have h2 : r / a = (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
        rw [hr_def, hra n]; field_simp
      rw [h2]; exact h1
    have hL' : Real.log ((n : ℝ) + 2) ≤ 2 * lg := co_log_add_two_le hn2
    have hL'0 : 0 ≤ Real.log ((n : ℝ) + 2) := mono_log_nonneg n
    have hM0 : (0 : ℝ) ≤ (maxLocalTime Y n : ℝ) := Nat.cast_nonneg _
    have hsq : Real.sqrt ((maxLocalTime Y n : ℝ) * Real.log ((n : ℝ) + 2)) ≤
        Real.sqrt (2 * C₀ / a) * S := by
      rw [hS_def, ← Real.sqrt_mul (by positivity)]
      refine Real.sqrt_le_sqrt ?_
      calc (maxLocalTime Y n : ℝ) * Real.log ((n : ℝ) + 2) ≤ (C₀ * (r / a)) * (2 * lg) :=
            mul_le_mul hM hL' hL'0 (by positivity)
        _ = 2 * C₀ / a * (r * lg) := by ring
    have hδ : C₁ * (Real.sqrt ((maxLocalTime Y n : ℝ) * Real.log ((n : ℝ) + 2)) +
        Real.log ((n : ℝ) + 2)) ≤ Cδ * S := by
      rw [hCδ]
      have : Real.sqrt ((maxLocalTime Y n : ℝ) * Real.log ((n : ℝ) + 2)) +
          Real.log ((n : ℝ) + 2) ≤ (Real.sqrt (2 * C₀ / a) + 2) * S := by
        rw [add_mul]; linarith
      exact mul_le_mul_of_nonneg_left this hC₁.le |>.trans_eq (by ring)
    have hcone : |max (b - euclidNorm x) 0 - max (r - euclidNorm x) 0| ≤ Cin * lg := by
      refine (abs_max_sub_max_le_abs _ _ _).trans ?_
      have : (b - euclidNorm x) - (r - euclidNorm x) = b - r := by ring
      rw [this]; exact hbr
    have hCwP : 2 * d * ε * (Cw * P) ≤ 2 * d * ε * (Cw * S) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS (by rw [hCw]; positivity)) hCS
    have hCinlg : 2 * d * ε * (Cin * lg) ≤ 2 * d * ε * (Cin * S) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlgS hCin.le) hCS
    have hann' : |potential d ε (cellSet Y n \ Metric.ball 0 b) (toSpace x)| ≤
        2 * d * ε * (Cw * P) :=
      hann.trans (mul_le_mul_of_nonneg_left hwP hCS)
    have hconeb : 2 * d * ε * |max (b - euclidNorm x) 0 - max (r - euclidNorm x) 0| ≤
        2 * d * ε * (Cin * lg) := mul_le_mul_of_nonneg_left hcone hCS
    have hfinal : |(localTime Y n x : ℝ) - 2 * d * ε * max (r - euclidNorm x) 0| ≤
        Cδ * S + 2 * d * ε * (Cin * lg) + 2 * d * ε * (Cw * P) := by
      have e1 : (localTime Y n x : ℝ) - 2 * d * ε * max (r - euclidNorm x) 0 =
          ((localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)) +
            (2 * d * ε * (max (b - euclidNorm x) 0 - max (r - euclidNorm x) 0) +
              potential d ε (cellSet Y n \ Metric.ball 0 b) (toSpace x)) := by
        rw [hsplit]; ring
      rw [e1]
      refine (abs_add_le _ _).trans ?_
      have h2 := (abs_add_le (2 * d * ε * (max (b - euclidNorm x) 0 - max (r - euclidNorm x) 0))
        (potential d ε (cellSet Y n \ Metric.ball 0 b) (toSpace x)))
      rw [abs_mul, abs_of_nonneg hCS] at h2
      linarith
    have hCS' : 0 ≤ Cδ * S := by rw [hCδ]; positivity
    calc _ ≤ Cδ * S + 2 * d * ε * (Cin * lg) + 2 * d * ε * (Cw * P) := hfinal
      _ ≤ Cδ * S + 2 * d * ε * (Cin * S) + 2 * d * ε * (Cw * S) := by linarith
      _ ≤ C * S := by
        have h8 : C * S = Cδ * S + 2 * d * ε * (Cin * S) + 2 * d * ε * (Cw * S) +
            2 * d * ε * (Real.sqrt d * S) := by rw [hC]; ring
        have h9 : 0 ≤ 2 * d * ε * (Real.sqrt d * S) := by positivity
        rw [h8]
        linarith
  · -- outside the ball of radius R
    rw [not_le] at hxR
    rw [co_localTime_eq_zero hxR]
    have hrR : r - euclidNorm x ≤ (Cin + Real.sqrt d) * S := by
      have h1 : r - R ≤ r - b + Real.sqrt d / 2 := by linarith
      have h2 : r - b ≤ Cin * lg := by linarith [hbr1.1]
      have h3 : Real.sqrt d / 2 ≤ Real.sqrt d * S := by
        calc Real.sqrt d / 2 ≤ Real.sqrt d * 1 := by linarith
          _ ≤ Real.sqrt d * S := mul_le_mul_of_nonneg_left (hlg1.trans hlgS) hsd.le
      have h4 : Cin * lg ≤ Cin * S := mul_le_mul_of_nonneg_left hlgS hCin.le
      have h5 : (Cin + Real.sqrt d) * S = Cin * S + Real.sqrt d * S := by ring
      rw [h5]
      linarith
    have hmax : max (r - euclidNorm x) 0 ≤ (Cin + Real.sqrt d) * S :=
      max_le hrR (by positivity)
    simp only [Nat.cast_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg (by positivity)]
    calc 2 * d * ε * max (r - euclidNorm x) 0 ≤ 2 * d * ε * ((Cin + Real.sqrt d) * S) :=
          mul_le_mul_of_nonneg_left hmax hCS
      _ ≤ C * S := by
        rw [hC]
        have : 0 ≤ Cδ * S := by rw [hCδ]; positivity
        have h6 : 2 * d * ε * (Cw + Cin + Real.sqrt d) * S =
            2 * d * ε * ((Cin + Real.sqrt d) * S) + 2 * d * ε * (Cw * S) := by ring
        have h7 : 0 ≤ 2 * d * ε * (Cw * S) := by rw [hCw]; positivity
        have h8 : C * S = Cδ * S + 2 * d * ε * (Cw + Cin + Real.sqrt d) * S := by rw [hC]; ring
        rw [h8, h6]
        linarith

/-- If `w ≤ Kw √r lg^{5/2}` then `(r lg)^{1/4} √w ≤ √Kw √r lg^{3/2}`. -/
private lemma co_planar_bd {Kw lg r w : ℝ} (hKw : 0 ≤ Kw) (hlg : 1 ≤ lg) (hr : 1 ≤ r)
    (h : w ≤ Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2))) :
    (r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w ≤ Real.sqrt Kw * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) := by
  have hr0 : 0 ≤ r := by linarith
  have hlg0 : 0 < lg := by linarith
  set t : ℝ := (r * lg) ^ ((1 : ℝ) / 4) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by positivity) _
  have ht2 : t ^ 2 = Real.sqrt r * lg ^ ((1 : ℝ) / 2) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    rw [show ((1 : ℝ) / 4) * ((2 : ℕ) : ℝ) = 1 / 2 by push_cast; ring,
      Real.mul_rpow hr0 hlg0.le, Real.sqrt_eq_rpow]
  have hZ : (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) ^ 2 = r * lg ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hr0, ← Real.rpow_natCast, ← Real.rpow_mul hlg0.le]
    norm_num
  have h1 : t ^ 2 * w ≤ Kw * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) ^ 2 := by
    rw [hZ, ht2]
    have e : Real.sqrt r * lg ^ ((1 : ℝ) / 2) * (Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2))) =
        Kw * (r * lg ^ 3) := by
      have e1 : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0
      have e2 : lg ^ ((1 : ℝ) / 2) * lg ^ ((5 : ℝ) / 2) = lg ^ 3 := by
        rw [← Real.rpow_add hlg0, ← Real.rpow_natCast]; norm_num
      calc Real.sqrt r * lg ^ ((1 : ℝ) / 2) * (Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)))
          = Kw * ((Real.sqrt r * Real.sqrt r) * (lg ^ ((1 : ℝ) / 2) * lg ^ ((5 : ℝ) / 2))) := by
            ring
        _ = Kw * (r * lg ^ 3) := by rw [e1, e2]
    rw [← e]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have h2 : t * Real.sqrt w = Real.sqrt (t ^ 2 * w) := by
    rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht0]
  rw [h2]
  calc Real.sqrt (t ^ 2 * w) ≤ Real.sqrt (Kw * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = Real.sqrt Kw * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) := by
        rw [Real.sqrt_mul hKw, Real.sqrt_sq (by positivity)]

/-- The width of the range in the plane: from the crossing bound and the inner radius bound,
`R - b + 2√d` is at most `Kw √r (log n)^{5/2}` and `r / log n`, and `b ≥ r/2`. -/
private lemma co_planar_width {Cin Cout Kw sd r lg R b : ℝ} (hCin : 0 < Cin) (hsd : 0 < sd)
    (hKw : Kw = Cin + max Cout 0 + 2 * sd) (hr : 1 ≤ r) (hlg : 1 ≤ lg)
    (h1 : Kw * lg ^ ((7 : ℝ) / 2) ≤ r ^ ((1 : ℝ) / 2))
    (h2 : 2 * Cin * lg ^ ((1 : ℝ) / 2) ≤ r ^ ((1 : ℝ) / 2))
    (hbr : |b - r| ≤ Cin * Real.sqrt (r * lg))
    (hout : R ≤ r + Cout * (Real.sqrt r * lg ^ ((5 : ℝ) / 2))) :
    R - b + 2 * sd ≤ Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) ∧ R - b + 2 * sd ≤ r / lg ∧
      r / 2 ≤ b := by
  have hr0 : 0 < r := by linarith
  have hlg0 : 0 < lg := by linarith
  have hbr1 := abs_le.mp hbr
  have hsq1 : Real.sqrt lg ≤ lg ^ ((5 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hlg (by norm_num)
  have hT5 : Real.sqrt (r * lg) ≤ Real.sqrt r * lg ^ ((5 : ℝ) / 2) := by
    rw [Real.sqrt_mul hr0.le]
    exact mul_le_mul_of_nonneg_left hsq1 (Real.sqrt_nonneg _)
  have hZ5 : 1 ≤ Real.sqrt r * lg ^ ((5 : ℝ) / 2) := by
    have h5 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
    have h6 : 1 ≤ lg ^ ((5 : ℝ) / 2) := Real.one_le_rpow hlg (by norm_num)
    exact one_le_mul_of_one_le_of_one_le h5 h6
  have hwb : R - b + 2 * sd ≤ Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) := by
    have hc : Cout * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) ≤
        max Cout 0 * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    have h4 : Cin * Real.sqrt (r * lg) ≤ Cin * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hT5 hCin.le
    have h5 : 2 * sd ≤ 2 * sd * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) :=
      le_mul_of_one_le_right (by positivity) hZ5
    have h6 : Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) =
        Cin * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) +
          max Cout 0 * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) +
            2 * sd * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) := by rw [hKw]; ring
    rw [h6]
    linarith [hbr1.1]
  have hpr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0.le
  refine ⟨hwb, ?_, ?_⟩
  · rw [le_div_iff₀ hlg0]
    have hq : lg ^ ((5 : ℝ) / 2) * lg = lg ^ ((7 : ℝ) / 2) := by
      rw [← Real.rpow_add_one hlg0.ne']; norm_num
    calc (R - b + 2 * sd) * lg ≤ Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) * lg :=
          mul_le_mul_of_nonneg_right hwb hlg0.le
      _ = Real.sqrt r * (Kw * lg ^ ((7 : ℝ) / 2)) := by rw [← hq]; ring
      _ ≤ Real.sqrt r * Real.sqrt r := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          rw [Real.sqrt_eq_rpow]
          simpa using h1
      _ = r := hpr
  · have h7 : Cin * Real.sqrt (r * lg) ≤ r / 2 := by
      rw [Real.sqrt_mul hr0.le, Real.sqrt_eq_rpow lg]
      have h8 : 2 * Cin * lg ^ ((1 : ℝ) / 2) ≤ Real.sqrt r := by
        rw [Real.sqrt_eq_rpow]; simpa using h2
      calc Cin * (Real.sqrt r * lg ^ ((1 : ℝ) / 2)) =
          Real.sqrt r * (Cin * lg ^ ((1 : ℝ) / 2)) := by ring
        _ ≤ Real.sqrt r * (Real.sqrt r / 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
            linarith
        _ = (Real.sqrt r * Real.sqrt r) / 2 := by ring
        _ = r / 2 := by rw [hpr]
    linarith [hbr1.1]

/-- The bound on the error of the global local-time approximation in the plane. -/
private lemma co_planar_delta {C₀ C₁ a r lg M L' : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 < C₁)
    (ha : 0 < a) (hr : 1 ≤ r) (hlg : 1 ≤ lg) (hM : M ≤ C₀ * (r / a))
    (hL'0 : 0 ≤ L') (hL' : L' ≤ 2 * lg) :
    C₁ * (Real.sqrt M * L' + L') ≤
      C₁ * (2 * Real.sqrt (C₀ / a) + 2) * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) := by
  have hr0 : 0 ≤ r := by linarith
  have hlg32 : lg ≤ lg ^ ((3 : ℝ) / 2) := by
    calc lg = lg ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ lg ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hlg (by norm_num)
  have hsr1 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
  have hZ0 : 0 ≤ Real.sqrt r * lg ^ ((3 : ℝ) / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by linarith) _)
  have hlgZ : lg ≤ Real.sqrt r * lg ^ ((3 : ℝ) / 2) := by
    calc lg ≤ 1 * lg ^ ((3 : ℝ) / 2) := by rw [one_mul]; exact hlg32
      _ ≤ Real.sqrt r * lg ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hsr1 (Real.rpow_nonneg (by linarith) _)
  have hsq : Real.sqrt M ≤ Real.sqrt (C₀ / a) * Real.sqrt r := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    calc M ≤ C₀ * (r / a) := hM
      _ = C₀ / a * r := by ring
  have h1 : Real.sqrt M * L' ≤ Real.sqrt (C₀ / a) * Real.sqrt r * (2 * lg) :=
    mul_le_mul hsq hL' hL'0 (by positivity)
  have h2 : Real.sqrt (C₀ / a) * Real.sqrt r * (2 * lg) ≤
      2 * Real.sqrt (C₀ / a) * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) := by
    have : Real.sqrt r * lg ≤ Real.sqrt r * lg ^ ((3 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hlg32 (Real.sqrt_nonneg _)
    calc Real.sqrt (C₀ / a) * Real.sqrt r * (2 * lg)
        = 2 * Real.sqrt (C₀ / a) * (Real.sqrt r * lg) := by ring
      _ ≤ 2 * Real.sqrt (C₀ / a) * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
  have h3 : L' ≤ 2 * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) := by linarith
  have h4 : Real.sqrt M * L' + L' ≤
      (2 * Real.sqrt (C₀ / a) + 2) * (Real.sqrt r * lg ^ ((3 : ℝ) / 2)) := by
    rw [add_mul]; linarith
  exact (mul_le_mul_of_nonneg_left h4 hC₁.le).trans_eq (by ring)

/-- Inside the inner ball the local time is within `C Z` of the cone. -/
private lemma co_planar_inside {ℓ U Ub UE cone δ Bd Cδ Cbd Z T D Cin C : ℝ} (hD : 0 ≤ D)
    (hg : |ℓ - U| ≤ δ) (hU : U = Ub + UE) (hdiff : |Ub - cone| ≤ D * (Cin * T))
    (hUE0 : 0 ≤ UE) (hUE : UE ≤ Bd) (hδ : δ ≤ Cδ * Z) (hBd : Bd ≤ Cbd * Z) (hT : T ≤ Z)
    (hCin : 0 ≤ Cin) (hC : Cδ * Z + D * (Cin * Z) + Cbd * Z ≤ C * Z) : |ℓ - cone| ≤ C * Z := by
  have h1 : D * (Cin * T) ≤ D * (Cin * Z) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT hCin) hD
  have h2 : ℓ - cone = (ℓ - U) + (Ub - cone) + UE := by rw [hU]; ring
  rw [h2]
  have h3 := abs_add_le ((ℓ - U) + (Ub - cone)) UE
  have h4 := abs_add_le (ℓ - U) (Ub - cone)
  rw [abs_of_nonneg hUE0] at h3
  linarith

/-- Between the inner ball and the outer radius the local time and the cone are nonnegative and
bounded by `C Z`. -/
private lemma co_planar_between {ℓ UE cone Bd Cδ Cbd Z T D Cin C : ℝ} (hD : 0 ≤ D)
    (hℓ0 : 0 ≤ ℓ) (hcone0 : 0 ≤ cone) (hℓ : ℓ ≤ Cδ * Z + UE) (hUE : UE ≤ Bd)
    (hcone : cone ≤ D * (Cin * T)) (hBd : Bd ≤ Cbd * Z) (hT : T ≤ Z) (hCin : 0 ≤ Cin)
    (hZ0 : 0 ≤ Z)
    (hC : Cδ * Z + D * (Cin * Z) + Cbd * Z ≤ C * Z) : |ℓ - cone| ≤ C * Z := by
  have h1 : D * (Cin * T) ≤ D * (Cin * Z) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT hCin) hD
  have h2 : 0 ≤ D * (Cin * Z) := mul_nonneg hD (mul_nonneg hCin hZ0)
  rw [abs_le]
  constructor <;> linarith

/-- Beyond the outer radius the local time vanishes and the cone is at most `C Z`. -/
private lemma co_planar_outside {D Cin sd r lg Z b R ν Cδ Cbd C : ℝ} (hD : 0 ≤ D)
    (hCin : 0 < Cin) (hsd : 0 < sd) (hlg : 1 ≤ lg) (hlgZ : lg ≤ Z)
    (hT : Real.sqrt (r * lg) ≤ Z) (hbr : |b - r| ≤ Cin * Real.sqrt (r * lg))
    (hbR : b ≤ R + sd / 2) (hν : R < ν)
    (hC : C * Z = Cδ * Z + D * ((Cin + sd) * Z) + Cbd * Z) (hCδZ : 0 ≤ Cδ * Z)
    (hCbdZ : 0 ≤ Cbd * Z) : D * max (r - ν) 0 ≤ C * Z := by
  have hZ1 : 1 ≤ Z := hlg.trans hlgZ
  have hr1 := (abs_le.mp hbr).1
  have hrν : r - ν ≤ (Cin + sd) * Z := by
    have h1 : r - R ≤ r - b + sd / 2 := by linarith
    have h3 : sd / 2 ≤ sd * Z := by
      calc sd / 2 ≤ sd * 1 := by linarith
        _ ≤ sd * Z := mul_le_mul_of_nonneg_left hZ1 hsd.le
    have h4 : Cin * Real.sqrt (r * lg) ≤ Cin * Z := mul_le_mul_of_nonneg_left hT hCin.le
    have h5 : (Cin + sd) * Z = Cin * Z + sd * Z := by ring
    rw [h5]
    linarith
  have hmax : max (r - ν) 0 ≤ (Cin + sd) * Z :=
    max_le hrν (by positivity)
  calc D * max (r - ν) 0 ≤ D * ((Cin + sd) * Z) := mul_le_mul_of_nonneg_left hmax hD
    _ ≤ C * Z := by rw [hC]; linarith

/-- Theorem 1.2 (iii), `d = 2`, deterministically. -/
private theorem local_core_planar (hd : d = 2) (hnear : near_far) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) (C₀ C₁ Cin Cout : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hCin : 0 < Cin) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      PathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n →
      maxRadius Y n ≤
        radius d ε n + Cout * (Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)) →
      ∀ x : Site d, |(localTime Y n x : ℝ) - 2 * d * ε * max (radius d ε n - euclidNorm x) 0| ≤
        C * (Real.sqrt (radius d ε n) * Real.log n ^ ((3 : ℝ) / 2)) := by
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  obtain ⟨a, ha, hra⟩ := tk_radius_eq hd1 hε
  obtain ⟨Cp, hCp, np, hpl⟩ := planar_exterior hd hnear hε hεd C₀ C₁ Cin
    (Cin * (1 + d * unitBallVolume d))
  set Kw : ℝ := Cin + max Cout 0 + 2 * Real.sqrt d with hKw
  have hKw0 : 0 < Kw := by rw [hKw]; positivity
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1
    ((tk_log_pow_le hd1 hε (A := (7 : ℝ) / 2) (by norm_num) Kw (s := 1 / 2) (by norm_num)).and
      ((tk_log_pow_le hd1 hε (A := (1 : ℝ) / 2) (by norm_num) (2 * Cin) (s := 1 / 2)
        (by norm_num)).and
      (tk_log_pow_le hd1 hε (A := 0) le_rfl 1 (s := 1) one_pos)))
  set Cδ : ℝ := C₁ * (2 * Real.sqrt (C₀ / a) + 2) with hCδ
  set Cbd : ℝ := Cp * (Real.sqrt Kw + 1) with hCbd
  set C : ℝ := Cδ + 2 * d * ε * (Cin + Real.sqrt d) + Cbd with hC
  have hCpos : 0 < C := by rw [hC, hCδ, hCbd]; positivity
  refine ⟨C, hCpos, max (max n₁ np) 3, ?_⟩
  intro Y n hn hP hI hout x
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn2 : 2 ≤ n := by omega
  have hnp : np ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  obtain ⟨h1, h2, h3⟩ := hn₁ n hn1
  have hr := radius_pos hd1 hε (by omega : 1 ≤ n)
  set r := radius d ε n with hr_def
  set lg := Real.log n with hlg_def
  have hlg1 : 1 ≤ lg := by
    rw [hlg_def, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    exact this.le.trans (by exact_mod_cast hn3)
  have hlg0 : 0 < lg := by linarith
  simp only [Real.rpow_zero, mul_one, Real.rpow_one] at h3
  set b := innerRadius Y n with hb_def
  set R := maxRadius Y n with hR_def
  set w := R - b + 2 * Real.sqrt d with hw_def
  have hbR := innerRadius_le hd1 Y n
  have hb0 := innerRadius_nonneg Y n
  have hw0 : 0 < w := by rw [hw_def]; linarith
  have hpath : ∀ j, euclidNorm (Y j) ≤ j :=
    CERW.Support.Occupation.euclidNorm_le_of_steps Y hP.start hP.step
  have hRn : R ≤ n := co_maxRadius_le hpath
  have hrq := radius_mul_qrate hd1 hε (by omega : 1 ≤ n)
  rw [if_pos hd] at hrq
  have hbr : |b - r| ≤ Cin * Real.sqrt (r * lg) := by
    have := hI.1
    calc |b - r| ≤ Cin * r * qrate d ε n := this
      _ = Cin * (r * qrate d ε n) := by ring
      _ = Cin * Real.sqrt (r * lg) := by rw [hrq]
  have hbr1 := abs_le.mp hbr
  obtain ⟨hwb, hwr, hbhalf⟩ := co_planar_width (Kw := Kw) hCin hsd hKw h3 hlg1 h1 h2 hbr hout
  have hbpos : 0 < b := by linarith
  have hmass := mass_of_inner hd2 hε hCin.le Y (by omega : 1 ≤ n) hI
  obtain ⟨-, hpos⟩ := hpl Y n hnp hP hI hmass (by rw [← hr_def]; exact hwr)
  have hD := CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDb : Bornology.IsBounded (cellSet Y n) :=
    Metric.isBounded_ball.subset (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n)
  have hE : MeasurableSet (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) :=
    hD.diff Metric.isOpen_ball.measurableSet
  have hEb : Bornology.IsBounded (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) :=
    hDb.subset Set.sdiff_subset
  have hsubE : cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ {v | b ≤ ‖v‖} := by
    intro v hv
    have h := hv.2
    rw [Metric.mem_ball, dist_zero_right, not_lt] at h
    exact h
  set Z : ℝ := Real.sqrt r * lg ^ ((3 : ℝ) / 2) with hZ
  have hlg32 : lg ≤ lg ^ ((3 : ℝ) / 2) := by
    calc lg = lg ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ lg ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hlg1 (by norm_num)
  have hlg12 : Real.sqrt lg ≤ lg ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hlg1 (by norm_num)
  have hsr1 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr h3
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hT : Real.sqrt (r * lg) ≤ Z := by
    rw [Real.sqrt_mul hr.le, hZ]
    exact mul_le_mul_of_nonneg_left hlg12 (Real.sqrt_nonneg _)
  have hlgZ : lg ≤ Z := by
    calc lg ≤ 1 * lg ^ ((3 : ℝ) / 2) := by rw [one_mul]; exact hlg32
      _ ≤ Real.sqrt r * lg ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hsr1 (Real.rpow_nonneg hlg0.le _)
  have hbd1 := co_planar_bd hKw0.le hlg1 h3 hwb
  have hBd : Cp * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg)) ≤ Cbd * Z := by
    have : (r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg) ≤
        (Real.sqrt Kw + 1) * Z := by
      rw [add_mul, one_mul]; exact add_le_add hbd1 hT
    rw [hCbd, mul_assoc]
    exact mul_le_mul_of_nonneg_left this hCp.le
  have hposy : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ R + 2 * Real.sqrt d →
      positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y ≤
        Cp * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg)) :=
    fun y h1 h2 => hpos y h1 h2
  have hM : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ = b → potential d ε
      (cellSet Y n \ Metric.ball 0 b) y ≤
        Cp * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg)) := fun y hy =>
    (co_potential_le_positive hd1 hε.le hE hEb y).trans
      (hposy y hy.ge (by rw [hy]; linarith))
  have hmp := planar_max_principle hd hε hE hEb hbpos hsubE hM
  have hCS : 0 ≤ 2 * d * ε := by positivity
  set Bd : ℝ := Cp * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg)) with hBd_def
  have hBd0 : 0 ≤ Bd := by rw [hBd_def]; positivity
  have hCδZ : 0 ≤ Cδ * Z := by rw [hCδ]; positivity
  have hCbdZ : 0 ≤ Cbd * Z := by rw [hCbd]; positivity
  by_cases hxR : euclidNorm x ≤ R
  · have hy : ‖toSpace x‖ ≤ 2 * n := by
      rw [norm_toSpace]
      have : (R : ℝ) ≤ n := hRn
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hg := hP.glob (toSpace x) hy
    rw [cellLocalTime_of_mem_cell _ _ (toSpace_mem_cell x), if_pos hd] at hg
    have hsplit := potential_split hd2 ε hD hDb hbpos (ball_innerRadius_subset hd1 Y n)
      (toSpace x)
    rw [norm_toSpace] at hsplit
    have hM' : (maxLocalTime Y n : ℝ) ≤ C₀ * (r / a) := by
      have h1 := hP.maxLoc
      have h2 : r / a = (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
        rw [hr_def, hra n]; field_simp
      rw [h2]; exact h1
    have hδ : C₁ * (Real.sqrt (maxLocalTime Y n : ℝ) * Real.log ((n : ℝ) + 2) +
        Real.log ((n : ℝ) + 2)) ≤ Cδ * Z := by
      rw [hCδ, hZ]
      exact co_planar_delta hC₀.le hC₁ ha h3 hlg1 hM' (mono_log_nonneg n)
        (co_log_add_two_le hn2)
    have hcone : |max (b - euclidNorm x) 0 - max (r - euclidNorm x) 0| ≤
        Cin * Real.sqrt (r * lg) := by
      refine (abs_max_sub_max_le_abs _ _ _).trans ?_
      have : (b - euclidNorm x) - (r - euclidNorm x) = b - r := by ring
      rw [this]; exact hbr
    have hCZ : Cδ * Z + 2 * d * ε * (Cin * Z) + Cbd * Z ≤ C * Z := by
      have h8 : C * Z = Cδ * Z + 2 * d * ε * (Cin * Z) + 2 * d * ε * (Real.sqrt d * Z) +
          Cbd * Z := by rw [hC]; ring
      have h9 : 0 ≤ 2 * d * ε * (Real.sqrt d * Z) := by positivity
      rw [h8]; linarith
    have hCin0 := hCin.le
    by_cases hxb : euclidNorm x ≤ b
    · -- inside the inner ball
      have hUE0 := co_potential_nonneg_inside hd2 hε.le hE hsubE
        (y := toSpace x) (by rw [norm_toSpace]; exact hxb)
      have hUEM : potential d ε (cellSet Y n \ Metric.ball 0 b) (toSpace x) ≤ Bd :=
        hmp (toSpace x) (by rw [norm_toSpace]; exact hxb)
      have hdiff : |2 * d * ε * max (b - euclidNorm x) 0 - 2 * d * ε * max (r - euclidNorm x) 0| ≤
          2 * d * ε * (Cin * Real.sqrt (r * lg)) := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hCS]
        exact mul_le_mul_of_nonneg_left hcone hCS
      exact co_planar_inside hCS hg hsplit hdiff hUE0 hUEM hδ hBd hT hCin0 hCZ
    · -- between the inner ball and the outer radius
      rw [not_le] at hxb
      have hUE : potential d ε (cellSet Y n \ Metric.ball 0 b) (toSpace x) ≤ Bd :=
        (co_potential_le_positive hd1 hε.le hE hEb _).trans
          (hposy (toSpace x) (by rw [norm_toSpace]; exact hxb.le)
            (by rw [norm_toSpace]; linarith))
      have hU0 : 2 * d * ε * max (b - euclidNorm x) 0 = 0 := by
        rw [max_eq_right (by linarith)]; ring
      have hlow : (localTime Y n x : ℝ) ≤ Cδ * Z +
          potential d ε (cellSet Y n \ Metric.ball 0 b) (toSpace x) := by
        have h1 := (abs_le.mp hg).2
        rw [hsplit, hU0] at h1
        linarith
      have hconeN : 2 * d * ε * max (r - euclidNorm x) 0 ≤
          2 * d * ε * (Cin * Real.sqrt (r * lg)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCS
        refine max_le ?_ (by positivity)
        linarith [hbr1.1]
      exact co_planar_between hCS (Nat.cast_nonneg _) (by positivity) hlow hUE hconeN hBd hT
        hCin0 hZ0 hCZ
  · rw [not_le] at hxR
    rw [co_localTime_eq_zero hxR]
    simp only [Nat.cast_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg (by positivity)]
    have h8 : C * Z = Cδ * Z + 2 * d * ε * ((Cin + Real.sqrt d) * Z) + Cbd * Z := by
      rw [hC]; ring
    exact co_planar_outside hCS hCin hsd hlg1 hlgZ hT hbr hbR hxR h8 hCδZ hCbdZ

/-! ### Proposition 7.1 -/

/-- A set covered by three sets of small measure has small measure. -/
private lemma measure_le_union_three {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S E₁ E₂ E₃ : Set Ω} {a₁ a₂ a₃ C : ℝ} (hS : S ⊆ E₁ ∪ E₂ ∪ E₃)
    (h₁ : μ E₁ ≤ ENNReal.ofReal a₁) (h₂ : μ E₂ ≤ ENNReal.ofReal a₂)
    (h₃ : μ E₃ ≤ ENNReal.ofReal a₃) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hC : a₁ + a₂ + a₃ ≤ C)
    (ha₃ : 0 ≤ a₃) : μ S ≤ ENNReal.ofReal C := by
  calc μ S ≤ μ (E₁ ∪ E₂ ∪ E₃) := measure_mono hS
    _ ≤ μ (E₁ ∪ E₂) + μ E₃ := measure_union_le _ _
    _ ≤ (μ E₁ + μ E₂) + μ E₃ := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ (ENNReal.ofReal a₁ + ENNReal.ofReal a₂) + ENNReal.ofReal a₃ := by gcongr
    _ = ENNReal.ofReal (a₁ + a₂ + a₃) := by
        rw [ENNReal.ofReal_add (add_nonneg ha₁ ha₂) ha₃, ENNReal.ofReal_add ha₁ ha₂]
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC

/-- If `n < n₀` the bound `C n^{-p}` with `C ≥ (n₀+1)^p` is at least `1`. -/
private lemma one_le_ofReal_mul_rpow {C p : ℝ} {n n₀ : ℕ} (hp : 0 < p) (hn : 0 < n)
    (hnn : n < n₀) (hC : ((n₀ : ℝ) + 1) ^ p ≤ C) :
    (1 : ENNReal) ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  rw [ENNReal.one_le_ofReal]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos hn0 p
  have hnle : (n : ℝ) ≤ (n₀ : ℝ) + 1 := by
    have : (n : ℝ) ≤ n₀ := by exact_mod_cast hnn.le
    linarith
  have hle : (n : ℝ) ^ p ≤ ((n₀ : ℝ) + 1) ^ p := Real.rpow_le_rpow hn0.le hnle hp.le
  rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, le_div_iff₀ hnp, one_mul]
  linarith

/-- Proposition 7.1 (the outer radius), from Proposition 6.1, the near-far lemma and the
outer-crossing lemma. -/
theorem outer_radius_of (hinner : inner_radius.{u}) (hnear : near_far)
    (houter : outer_crossing) : outer_radius.{u} := by
  intro d hd ωd ε hε hεd r p hp
  obtain ⟨C₀, C₁, Cf, hC₀, hC₁, hCf, hfl⟩ := exists_pathFacts_prob hd hε hεd hp
  obtain ⟨Cin, hCin, hin⟩ := hinner hd ε hε hεd p hp
  obtain ⟨Cl, hCl, hlin⟩ := exists_linOK_prob hd hε hεd hp
  have hC₁' : 0 < max C₁ Cl := lt_max_of_lt_left hC₁
  obtain ⟨Ccr, hCcr, hcr⟩ := euclid_crossing houter hd hε hεd C₀ (max C₁ Cl) hC₁'
  obtain ⟨C, hC, n₀, hcore⟩ : ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      PathFacts d ε C₀ (max C₁ Cl) Y n → InnerOK d ε Cin Y n → CrossOK d Ccr Y n →
      maxRadius Y n ≤ radius d ε n + C * (if d = 2 then Real.sqrt (radius d ε n) *
        Real.log n ^ ((5 : ℝ) / 2) else Real.log n ^ ((d : ℝ) + 1)) := by
    by_cases h2 : d = 2
    · obtain ⟨C, hC, n₀, h⟩ := outer_core_planar h2 hnear hε hεd C₀ (max C₁ Cl) Cin Ccr hCin hCcr
      exact ⟨C, hC, n₀, fun Y n hn h1 h3 h4 => by rw [if_pos h2]; exact h Y n hn h1 h3 h4⟩
    · obtain ⟨C, hC, n₀, h⟩ := outer_core_high (by omega) (newton_conv (by omega)) hnear hε hεd
        C₀ (max C₁ Cl) Cin Ccr hCin hCcr
      exact ⟨C, hC, n₀, fun Y n hn h1 h3 h4 => by rw [if_neg h2]; exact h Y n hn h1 h3 h4⟩
  have hn₀p : 0 < ((n₀ : ℝ) + 1) ^ p := Real.rpow_pos_of_pos (by positivity) p
  set Cfin : ℝ := C + Cf + Cin + Cl + ((n₀ : ℝ) + 1) ^ p with hCfin
  have hCfin0 : 0 < Cfin := by positivity
  refine ⟨Cfin, hCfin0, ?_⟩
  intro Ω _ μ _ X hX n hn2
  have hnp0 : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  by_cases hnb : n₀ ≤ n
  · have h1 : μ {ω | ¬ PathFacts d ε C₀ C₁ (fun j => X j ω) n} ≤ _ := hfl μ X hX n hn2
    have h2 : μ {ω | ¬ InnerOK d ε Cin (fun j => X j ω) n} ≤ _ := hin μ X hX n hn2
    have h3 : μ {ω | ¬ LinOK d ε Cl (fun j => X j ω) n} ≤ _ := hlin μ X hX n hn2
    refine measure_le_union_three (hS := ?_) h1 h2 h3 (mul_nonneg hCf.le hnp0)
      (mul_nonneg hCin.le hnp0) ?_ (mul_nonneg hCl.le hnp0)
    · intro ω hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
      obtain ⟨⟨hA, hB⟩, hD⟩ := hcon
      apply hω
      have hA' := hA.mono (le_max_left C₁ Cl)
      have hD' := hD.mono (le_max_right C₁ Cl)
      have hmain := hcore (fun j => X j ω) n hnb hA' hB (hcr _ n hn2 hA' hD')
      refine hmain.trans ?_
      have hrhs : 0 ≤ (if d = 2 then Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)
          else Real.log n ^ ((d : ℝ) + 1)) := by
        have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
        split_ifs
        · exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlog _)
        · exact Real.rpow_nonneg hlog _
      have hCle : C ≤ Cfin := by
        rw [hCfin]
        linarith [hCf, hCin, hCl, hn₀p]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hCle hrhs)
    · calc Cf * (n : ℝ) ^ (-p) + Cin * (n : ℝ) ^ (-p) + Cl * (n : ℝ) ^ (-p)
          = (Cf + Cin + Cl) * (n : ℝ) ^ (-p) := by ring
        _ ≤ Cfin * (n : ℝ) ^ (-p) := by
          refine mul_le_mul_of_nonneg_right ?_ hnp0
          rw [hCfin]
          linarith [hC, hn₀p]
  · rw [not_le] at hnb
    exact (prob_le_one).trans (one_le_ofReal_mul_rpow hp (by omega) hnb
      (by rw [hCfin]; linarith [hC, hCf, hCin, hCl]))


/-! ### Theorem 1.2 -/

/-- Proposition 7.1 and Theorem 1.2: the clauses of the good event from the three inputs. -/
theorem fluctuation_rates_of (hinner : inner_radius.{u}) (houter : outer_radius.{u})
    (hnear : near_far) : fluctuation_rates.{u} := by
  intro d hd ωd ε hε hεd r Good p hp
  have hd1 : 1 ≤ d := by omega
  have hmono : ∀ C C' : ℝ, C ≤ C' → ∀ (Y : ℕ → Site d) (n : ℕ), 1 ≤ n →
      Good C Y n → Good C' Y n := by
    intro C C' hCC Y n hn hG
    have hr : 0 < radius d ε n := radius_pos hd1 hε hn
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have hq : 0 ≤ qrate d ε n := qrate_nonneg hd1 hε hn
    obtain ⟨h1, h2, h3⟩ := hG
    refine ⟨?_, ?_, ?_⟩
    · by_cases h : d = 2
      · simp only [if_pos h] at h1 ⊢
        obtain ⟨a, b⟩ := h1
        refine ⟨a.trans ?_, b.trans ?_⟩ <;> gcongr
      · simp only [if_neg h] at h1 ⊢
        obtain ⟨a, b⟩ := h1
        refine ⟨a.trans ?_, b.trans ?_⟩ <;> gcongr
    · refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
      have : 0 ≤ (if d = 2 then Real.sqrt (Real.log n / radius d ε n)
          else Real.log n / radius d ε n) := hq
      gcongr
    · intro x
      refine (h3 x).trans ?_
      by_cases h : d = 2
      · simp only [if_pos h]
        gcongr
      · simp only [if_neg h]
        gcongr
  have key : ∀ q : ℝ, 0 < q → ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ Good C (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-q)) := by
    intro q hq
    obtain ⟨C₀, C₁, Cf, hC₀, hC₁, hCf, hfl⟩ := exists_pathFacts_prob.{u} hd hε hεd hq
    obtain ⟨Cin, hCin, hin⟩ := hinner hd ε hε hεd q hq
    obtain ⟨Co, hCo, hout⟩ := houter hd ε hε hεd q hq
    obtain ⟨Cl, hCl, n₀, hcore⟩ : ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ),
        n₀ ≤ n → PathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n →
        maxRadius Y n ≤ radius d ε n + Co * (if d = 2 then Real.sqrt (radius d ε n) *
          Real.log n ^ ((5 : ℝ) / 2) else Real.log n ^ ((d : ℝ) + 1)) →
        ∀ x : Site d, |(localTime Y n x : ℝ) - 2 * d * ε * max (radius d ε n - euclidNorm x) 0| ≤
          C * (if d = 2 then Real.sqrt (radius d ε n) * Real.log n ^ ((3 : ℝ) / 2)
            else Real.sqrt (radius d ε n * Real.log n)) := by
      by_cases h2 : d = 2
      · obtain ⟨C, hC, n₀, h⟩ := local_core_planar h2 hnear hε hεd C₀ C₁ Cin Co hC₀ hC₁ hCin
        exact ⟨C, hC, n₀, fun Y n hn h1 h3 h4 x => by
          rw [if_pos h2]
          exact h Y n hn h1 h3 (by rw [if_pos h2] at h4; exact h4) x⟩
      · obtain ⟨C, hC, n₀, h⟩ := local_core_high (d := d) (by omega) hε C₀ C₁ Cin Co hC₀ hC₁ hCin
        exact ⟨C, hC, n₀, fun Y n hn h1 h3 h4 x => by
          rw [if_neg h2]
          exact h Y n hn h1 h3 (by rw [if_neg h2] at h4; exact h4) x⟩
    set Cg : ℝ := max (max Cin Co) Cl with hCg
    have hCin_g : Cin ≤ Cg := (le_max_left _ _).trans (le_max_left _ _)
    have hCo_g : Co ≤ Cg := (le_max_right _ _).trans (le_max_left _ _)
    have hCl_g : Cl ≤ Cg := le_max_right _ _
    have hdet : ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n → 2 ≤ n → PathFacts d ε C₀ C₁ Y n →
        InnerOK d ε Cin Y n →
        maxRadius Y n ≤ radius d ε n + Co * (if d = 2 then Real.sqrt (radius d ε n) *
          Real.log n ^ ((5 : ℝ) / 2) else Real.log n ^ ((d : ℝ) + 1)) → Good Cg Y n := by
      intro Y n hn0 hn2 h1 h2 h3
      have hloc := hcore Y n hn0 h1 h2 h3
      have hrq := radius_mul_qrate hd1 hε (by omega : 1 ≤ n)
      have hr : 0 < radius d ε n := radius_pos hd1 hε (by omega : 1 ≤ n)
      have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      obtain ⟨i1, i2, -⟩ := h2
      refine ⟨?_, ?_, fun x => (hloc x).trans ?_⟩
      · by_cases h : d = 2
        · simp only [if_pos h]
          refine ⟨?_, ?_⟩
          · calc |innerRadius Y n - radius d ε n| ≤ Cin * radius d ε n * qrate d ε n := i1
              _ = Cin * (radius d ε n * qrate d ε n) := by ring
              _ = Cin * Real.sqrt (radius d ε n * Real.log n) := by rw [hrq, if_pos h]
              _ ≤ Cg * Real.sqrt (radius d ε n * Real.log n) := by gcongr
          · rw [if_pos h] at h3
            have hnn : 0 ≤ Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2) :=
              mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlog _)
            calc maxRadius Y n - radius d ε n
                ≤ Co * (Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)) := by linarith
              _ ≤ Cg * (Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)) := by gcongr
              _ = Cg * Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2) := by ring
        · simp only [if_neg h]
          refine ⟨?_, ?_⟩
          · calc |innerRadius Y n - radius d ε n| ≤ Cin * radius d ε n * qrate d ε n := i1
              _ = Cin * (radius d ε n * qrate d ε n) := by ring
              _ = Cin * Real.log n := by rw [hrq, if_neg h]
              _ ≤ Cg * Real.log n := by gcongr
          · rw [if_neg h] at h3
            have hnn : 0 ≤ Real.log n ^ ((d : ℝ) + 1) := Real.rpow_nonneg hlog _
            calc maxRadius Y n - radius d ε n ≤ Co * Real.log n ^ ((d : ℝ) + 1) := by linarith
              _ ≤ Cg * Real.log n ^ ((d : ℝ) + 1) := by gcongr
      · refine i2.trans (ENNReal.ofReal_le_ofReal ?_)
        have hq : 0 ≤ qrate d ε n := qrate_nonneg hd1 hε (by omega)
        show Cin * qrate d ε n ≤ Cg * qrate d ε n
        exact mul_le_mul_of_nonneg_right hCin_g hq
      · have hnn : 0 ≤ (if d = 2 then Real.sqrt (radius d ε n) * Real.log n ^ ((3 : ℝ) / 2)
            else Real.sqrt (radius d ε n * Real.log n)) := by
          split_ifs
          · exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlog _)
          · exact Real.sqrt_nonneg _
        exact mul_le_mul_of_nonneg_right hCl_g hnn
    have hn₀ : 0 < (((max n₀ 2 : ℕ) : ℝ) + 1) ^ q :=
      Real.rpow_pos_of_pos (by positivity) q
    set Cfin : ℝ := Cg + Cf + Cin + Co + (((max n₀ 2 : ℕ) : ℝ) + 1) ^ q with hCfin
    have hCg0 : 0 < Cg := lt_of_lt_of_le hCin hCin_g
    have hCfin0 : 0 < Cfin := by positivity
    refine ⟨Cfin, hCfin0, ?_⟩
    intro Ω _ μ _ X hX n hn2
    have hnp0 : 0 ≤ (n : ℝ) ^ (-q) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    by_cases hnb : max n₀ 2 ≤ n
    · have e1 : μ {ω | ¬ PathFacts d ε C₀ C₁ (fun j => X j ω) n} ≤ _ := hfl μ X hX n hn2
      have e2 : μ {ω | ¬ InnerOK d ε Cin (fun j => X j ω) n} ≤ _ := hin μ X hX n hn2
      have e3 := hout μ X hX n hn2
      refine measure_le_union_three (hS := ?_) e1 e2 e3 (mul_nonneg hCf.le hnp0)
        (mul_nonneg hCin.le hnp0) ?_ (mul_nonneg hCo.le hnp0)
      · intro ω hω
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
        obtain ⟨⟨hA, hB⟩, hD⟩ := hcon
        apply hω
        have hG := hdet (fun j => X j ω) n (le_trans (le_max_left _ _) hnb) hn2 hA hB hD
        exact hmono _ _ (by rw [hCfin]; linarith [hCf, hCin, hCo, hn₀]) _ n (by omega) hG
      · calc Cf * (n : ℝ) ^ (-q) + Cin * (n : ℝ) ^ (-q) + Co * (n : ℝ) ^ (-q)
            = (Cf + Cin + Co) * (n : ℝ) ^ (-q) := by ring
          _ ≤ Cfin * (n : ℝ) ^ (-q) := by
            refine mul_le_mul_of_nonneg_right ?_ hnp0
            rw [hCfin]
            linarith [hCg0, hn₀]
    · rw [not_le] at hnb
      exact (prob_le_one).trans (one_le_ofReal_mul_rpow hq (by omega) hnb
        (by rw [hCfin]; linarith [hCg0, hCf, hCin, hCo]))
  obtain ⟨Cp, hCp, hprob⟩ := key p hp
  obtain ⟨C2, hC2, hprob2⟩ := key 2 (by norm_num)
  refine ⟨max Cp C2, lt_max_of_lt_left hCp, ?_, ?_⟩
  · intro Ω _ μ _ X hX n hn
    have hnp0 : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    refine (measure_mono ?_).trans ((hprob μ X hX n hn).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hnp0)))
    intro ω hω hG
    exact hω (hmono _ _ (le_max_left _ _) _ n (by omega) hG)
  · intro Ω _ μ _ X hX
    have hbc := CERW.Support.Main.ae_eventually_of_le_rpow (μ := μ) (C := C2) (p := 2)
      (P := fun n ω => Good C2 (X · ω) n) (by norm_num) (n₀ := 2) (fun n hn => by
        simpa using hprob2 μ X hX n hn)
    filter_upwards [hbc] with ω hω
    filter_upwards [hω, Filter.eventually_ge_atTop 1] with n hGn hn1
    exact hmono _ _ (le_max_right _ _) _ n hn1 hGn

end CERW.Support.Outer
