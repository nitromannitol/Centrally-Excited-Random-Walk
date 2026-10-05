import CERW.Support.Lower.PlanarGap.Clt
import LatticeProb.Prob.CramerWold

/-!
# The compensated planar position: every linear form and the vector law

For the planar walk, `Z_n = X_n + ε Σ_{x ∈ A_n} u_x ∈ ℝ²` is the compensated position. For every
`q ∈ ℝ²` the linear form `⟨q, Z_n⟩` is the Dynkin martingale of `z ↦ q · z` (a first departure from
`x ≠ 0` lowers the mean of `q · X` by `ε q · u_x`, a simple random walk step by nothing). Its
increments are bounded, its predictable bracket is
`n |q|²/2 - ε² Σ_{first departures} (q · u)²`, and the number of first departures is at most the
size of the departure range, which is `o(n)` almost surely by the proved fluctuation rates. The
proved martingale central limit theorem therefore gives `⟨q, Z_n⟩/√n ⇒ N(0, |q|²/2)` for every `q`,
the case `q = 0` included. The characteristic-function (Lévy) form of the Cramér–Wold device of the
library then gives `Z_n / √n ⇒ N(0, I/2)`, the Mathlib multivariate Gaussian with covariance
`(1/2) I`. Nothing about the walk, the covariance or the limit law is assumed.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal
open LatticeProb (Site euclidNorm unit)

namespace CERW.Support.Lower.PlanarGap

open CERW CERW.Support.Law

/-! ### The linear form and its next-step mean -/

/-- The linear form `z ↦ Σ_i q_i z_i` on lattice sites of the plane. -/
private noncomputable def lf (q : EuclideanSpace ℝ (Fin 2)) (z : Site 2) : ℝ :=
  ∑ i, q i * ((z i : ℤ) : ℝ)

/-- The inner product in the plane is the sum of the products of the coordinates. -/
private lemma inner_eq_sum (a b : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ a b = ∑ i, a i * b i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The embedding of the origin is the origin of Euclidean space. -/
private lemma toSpace_zero_plane : toSpace (0 : Site 2) = 0 := by
  apply PiLp.ext
  intro i
  simp [toSpace_apply]

/-- The linear form changes by `q_j` under the step `e_j`. -/
private lemma lf_add_unit (q : EuclideanSpace ℝ (Fin 2)) (x : Site 2) (j : Fin 2) :
    lf q (x + unit j) - lf q x = q j := by
  unfold lf
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ i : Fin 2, q i * (((x + unit j) i : ℤ) : ℝ) - q i * ((x i : ℤ) : ℝ) =
      if j = i then q i else 0 := by
    intro i
    simp only [Pi.add_apply, unit_apply_coord]
    split_ifs <;> push_cast <;> ring
  simp_rw [hterm]
  simp

/-- The linear form changes by `-q_j` under the step `-e_j`. -/
private lemma lf_add_neg_unit (q : EuclideanSpace ℝ (Fin 2)) (x : Site 2) (j : Fin 2) :
    lf q (x + -unit j) - lf q x = -q j := by
  unfold lf
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ i : Fin 2, q i * (((x + -unit j) i : ℤ) : ℝ) - q i * ((x i : ℤ) : ℝ) =
      if j = i then -q i else 0 := by
    intro i
    simp only [Pi.add_apply, Pi.neg_apply, unit_apply_coord]
    split_ifs <;> push_cast <;> ring
  simp_rw [hterm]
  simp

/-- The next-step mean of the linear form is its value minus `ε q · u_x` at a first departure
from a nonzero site `x`, and its value otherwise. -/
private lemma nextMean_lf (ε : ℝ) (x : ℕ → Site 2) (t : ℕ) (q : EuclideanSpace ℝ (Fin 2)) :
    nextMean ε (lf q) x t = lf q (x t) -
      (if x t ≠ 0 ∧ x t ∉ (Finset.range t).image x then
        ε * inner ℝ q (unitDir (toSpace (x t))) else 0) := by
  have hlin : nextMean ε (lf q) x t =
      ∑ i, q i * nextMean ε (fun z : Site 2 => ((z i : ℤ) : ℝ)) x t := by
    simp only [nextMean, lf, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e _ => by ring
  rw [hlin]
  simp only [nextMean_coord (by norm_num : 1 ≤ 2)]
  by_cases h : x t ≠ 0 ∧ x t ∉ (Finset.range t).image x
  · simp only [if_pos h]
    rw [inner_eq_sum]
    unfold lf
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [if_neg h, sub_zero]
    rfl

/-- Summing over first departures from nonzero sites a function of the departure site is
summing over the departure range, the origin contributing nothing for the direction. -/
private lemma sum_fresh_inner (x : ℕ → Site 2) (n : ℕ) (q : EuclideanSpace ℝ (Fin 2)) :
    ∑ j ∈ Finset.range n, (if x j ≠ 0 ∧ x j ∉ (Finset.range j).image x then
      inner ℝ q (unitDir (toSpace (x j))) else 0) =
      ∑ z ∈ departureRange x n, inner ℝ q (unitDir (toSpace z)) := by
  rw [CERW.Support.Occupation.sum_fresh_ne_zero_eq_sum_departureRange x n
    (fun z => inner ℝ q (unitDir (toSpace z)))]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : z = 0
  · subst hz
    simp [toSpace_zero_plane]
  · simp [hz]

/-- The Dynkin martingale of the linear form of a walk started at the origin is the linear form
of the compensated position `X_n + ε Σ_{x ∈ A_n} u_x`. -/
private lemma dynkin_lf_eq {Ω : Type*} (ε : ℝ) (X : ℕ → Ω → Site 2)
    (q : EuclideanSpace ℝ (Fin 2)) (ω : Ω) (h0 : X 0 ω = 0) (n : ℕ) :
    dynkin ε (lf q) X n ω = lf q (X n ω) +
      ε * ∑ x ∈ departureRange (fun j => X j ω) n, inner ℝ q (unitDir (toSpace x)) := by
  have hterm : ∀ j, nextMean ε (lf q) (fun i => X i ω) j - lf q (X j ω) =
      -(ε * (if X j ω ≠ 0 ∧ X j ω ∉ (Finset.range j).image (fun i => X i ω) then
        inner ℝ q (unitDir (toSpace (X j ω))) else 0)) := by
    intro j
    rw [nextMean_lf]
    split_ifs <;> ring
  have hlf0 : lf q 0 = 0 := by simp [lf]
  rw [dynkin, h0, hlf0, Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_neg_distrib,
    ← Finset.mul_sum, sum_fresh_inner (fun j => X j ω) n q]
  ring

/-! ### The martingale of a linear form -/

/-- The probabilities of the steps `e_k` and `-e_k` add up to `1/2`. -/
private lemma stepProb_unit_add_neg_plane (ε : ℝ) (x : ℕ → Site 2) (t : ℕ) (k : Fin 2) :
    stepProb 2 ε x t (unit k) + stepProb 2 ε x t (-unit k) = 1 / ((2 : ℕ) : ℝ) := by
  unfold stepProb
  split_ifs
  · rw [firstStep_unit, firstStep_neg_unit]
    ring
  · rw [srwStep_unit, srwStep_neg_unit]
    ring

/-- The mean square oscillation of the linear form at the next step is `|q|²/2`. -/
private lemma sum_stepProb_lf_sq (ε : ℝ) (x : ℕ → Site 2) (t : ℕ)
    (q : EuclideanSpace ℝ (Fin 2)) :
    ∑ e ∈ unitSteps 2, stepProb 2 ε x t e * (lf q (x t + e) - lf q (x t)) ^ 2 =
      (q 0 ^ 2 + q 1 ^ 2) / 2 := by
  rw [sum_unitSteps]
  have hpair : ∀ i : Fin 2,
      stepProb 2 ε x t (unit i) * (lf q (x t + unit i) - lf q (x t)) ^ 2 +
        stepProb 2 ε x t (-unit i) * (lf q (x t + -unit i) - lf q (x t)) ^ 2 =
      (1 / ((2 : ℕ) : ℝ)) * q i ^ 2 := by
    intro i
    rw [lf_add_unit, lf_add_neg_unit, ← stepProb_unit_add_neg_plane ε x t i]
    ring
  simp_rw [hpair]
  rw [Fin.sum_univ_two]
  push_cast
  ring

/-- The conditional variance of an increment of the Dynkin martingale is the mean square
oscillation minus the square of the drift. -/
private theorem condExp_sq_dynkin_eq {Ω : Type*} [MeasurableSpace Ω] {ε : ℝ} (hε : 0 ≤ ε)
    (hεd : ε < 1 / ((2 : ℕ) : ℝ)) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X) (f : Site 2 → ℝ) (t : ℕ) :
    μ[fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) ^ 2 |
        pathFiltration hX.measurable t] =ᵐ[μ]
      fun ω => ∑ e ∈ unitSteps 2,
        stepProb 2 ε (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω)) ^ 2 -
          (nextMean ε f (fun j => X j ω) t - f (X t ω)) ^ 2 := by
  have hd : 1 ≤ 2 := by norm_num
  set h : ((i : Finset.Iic t) → Site 2) → Site 2 → ℝ :=
    fun p z => (f z - nextMean ε f (extendPath p) t) ^ 2 with hh
  have hsq : (fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) ^ 2) =
      fun ω => h (pastPath X t ω) (X (t + 1) ω) := by
    funext ω
    rw [dynkin_succ_sub, nextMean_pastPath]
  have hint := integrable_path_next hd hε hεd hX t h
  rw [hsq]
  filter_upwards [condExp_path_next hd hε hεd hX t h hint] with ω hω
  rw [hω]
  simp only [hh, ← nextMean_pastPath]
  have hvar := sum_mul_sub_mean_sq (unitSteps 2)
    (fun e => stepProb 2 ε (fun j => X j ω) t e) (fun e => f (X t ω + e))
    (sum_stepProb hd ε _ t) (f (X t ω))
  simp only [nextMean]
  exact hvar

/-- The conditional variance of an increment of a process that almost surely agrees with the
Dynkin martingale of the linear form of `q` is `|q|²/2` minus the square of the drift
`ε q · u_{X_t}` at a first departure from a nonzero site. -/
private theorem condExp_sq_lf_eq {Ω : Type*} [MeasurableSpace Ω] {ε : ℝ} (hε : 0 ≤ ε)
    (hεd : ε < 1 / ((2 : ℕ) : ℝ)) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X) (q : EuclideanSpace ℝ (Fin 2))
    {Y : ℕ → Ω → ℝ} (hae : ∀ᵐ ω ∂μ, ∀ i, Y i ω = dynkin ε (lf q) X i ω) (t : ℕ) :
    μ[fun ω => (Y (t + 1) ω - Y t ω) * (Y (t + 1) ω - Y t ω) | pathFiltration hX.measurable t]
      =ᵐ[μ] fun ω => (q 0 ^ 2 + q 1 ^ 2) / 2 -
        (if X t ω ≠ 0 ∧ X t ω ∉ (Finset.range t).image (fun i => X i ω) then
          ε * inner ℝ q (unitDir (toSpace (X t ω))) else 0) ^ 2 := by
  have hsq : (fun ω => (Y (t + 1) ω - Y t ω) * (Y (t + 1) ω - Y t ω)) =ᵐ[μ]
      fun ω => (dynkin ε (lf q) X (t + 1) ω - dynkin ε (lf q) X t ω) ^ 2 := by
    filter_upwards [hae] with ω hω
    rw [hω (t + 1), hω t, sq]
  refine (condExp_congr_ae hsq).trans ?_
  filter_upwards [condExp_sq_dynkin_eq hε hεd hX (lf q) t] with ω hω
  have h2 : nextMean ε (lf q) (fun j => X j ω) t - lf q (X t ω) =
      -(if X t ω ≠ 0 ∧ X t ω ∉ (Finset.range t).image (fun i => X i ω) then
        ε * inner ℝ q (unitDir (toSpace (X t ω))) else 0) := by
    rw [nextMean_lf]
    ring
  rw [hω, sum_stepProb_lf_sq, h2, neg_sq]

/-- The squared norm in the plane. -/
private lemma norm_sq_plane (q : EuclideanSpace ℝ (Fin 2)) : ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

/-- The linear form of `q` against a direction is at most `|q|` in absolute value. -/
private lemma inner_unitDir_sq_le (q : EuclideanSpace ℝ (Fin 2)) (x : Site 2) :
    inner ℝ q (unitDir (toSpace x)) ^ 2 ≤ q 0 ^ 2 + q 1 ^ 2 := by
  rw [← norm_sq_plane]
  have h1 : |inner ℝ q (unitDir (toSpace x))| ≤ ‖q‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
      (norm_unitDir_le _))
  calc inner ℝ q (unitDir (toSpace x)) ^ 2 = |inner ℝ q (unitDir (toSpace x))| ^ 2 :=
        (sq_abs _).symm
    _ ≤ ‖q‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2

/-- A process with increments at most `b` that starts at `0` is at most `b n` at time `n`. -/
private lemma abs_le_mul_of_increments {Ω : Type*} {Y : ℕ → Ω → ℝ} {b : ℝ}
    (h0 : ∀ ω, Y 0 ω = 0) (hbd : ∀ i ω, |Y (i + 1) ω - Y i ω| ≤ b) (n : ℕ) (ω : Ω) :
    |Y n ω| ≤ b * n := by
  induction n with
  | zero => simp [h0 ω]
  | succ n ih =>
    have h1 := hbd n ω
    have h2 : |Y (n + 1) ω| ≤ |Y (n + 1) ω - Y n ω| + |Y n ω| := by
      calc |Y (n + 1) ω| = |(Y (n + 1) ω - Y n ω) + Y n ω| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    push_cast
    linarith

/-- The number of first departures from nonzero sites before time `n` is at most the size of the
departure range. -/
private lemma sum_fresh_indicator_le_card (x : ℕ → Site 2) (n : ℕ) :
    ∑ j ∈ Finset.range n, (if x j ≠ 0 ∧ x j ∉ (Finset.range j).image x then (1 : ℝ) else 0) ≤
      ((departureRange x n).card : ℝ) := by
  rw [CERW.Support.Occupation.sum_fresh_ne_zero_eq_sum_departureRange x n (fun _ => (1 : ℝ))]
  calc ∑ z ∈ departureRange x n, (if z ≠ 0 then (1 : ℝ) else 0)
      ≤ ∑ _z ∈ departureRange x n, (1 : ℝ) :=
        Finset.sum_le_sum fun z _ => by split_ifs <;> norm_num
    _ = ((departureRange x n).card : ℝ) := by simp

/-- **The martingale of a linear form.** For every `q ∈ ℝ²` there is a martingale `Y` for the
natural filtration with `Y_0 = 0`, increments at most `2 (|q_0| + |q_1|)` everywhere, square
integrable, almost surely equal to `⟨q, X_n + ε Σ_{x ∈ A_n} u_x⟩`, with predictable bracket between
`n |q|²/2 - ε² |q|² |A_n|` and `n |q|²/2`. -/
private theorem exists_lf_martingale {ε : ℝ} (hε0 : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X) (q : EuclideanSpace ℝ (Fin 2)) :
    ∃ Y : ℕ → Ω → ℝ, Martingale Y (pathFiltration hX.measurable) μ ∧
      (∀ ω, Y 0 ω = 0) ∧ (∀ i ω, |Y (i + 1) ω - Y i ω| ≤ 2 * (|q 0| + |q 1|)) ∧
      (∀ n, MemLp (Y n) 2 μ) ∧
      (∀ᵐ ω ∂μ, ∀ n, Y n ω = lf q (X n ω) + ε * ∑ x ∈ departureRange (fun j => X j ω) n,
          inner ℝ q (unitDir (toSpace x))) ∧
      (∀ᵐ ω ∂μ, ∀ n,
        predBracket μ (pathFiltration hX.measurable) Y Y n ω ≤ n * ((q 0 ^ 2 + q 1 ^ 2) / 2) ∧
          n * ((q 0 ^ 2 + q 1 ^ 2) / 2) - ε ^ 2 * (q 0 ^ 2 + q 1 ^ 2) *
              ((departureRange (fun j => X j ω) n).card : ℝ) ≤
            predBracket μ (pathFiltration hX.measurable) Y Y n ω) := by
  have hd : 1 ≤ 2 := by norm_num
  have hε : 0 ≤ ε := hε0.le
  have hmart := martingale_dynkin (d := 2) hd hε hεd hX (lf q)
  have hB : ∀ j : Fin 2, |q j| ≤ |q 0| + |q 1| := by
    intro j
    fin_cases j
    · simp only [Fin.zero_eta]
      linarith [abs_nonneg (q 1)]
    · simp only [Fin.mk_one]
      linarith [abs_nonneg (q 0)]
  have hosc : ∀ (x : Site 2), ∀ e ∈ unitSteps 2, |lf q (x + e) - lf q x| ≤ |q 0| + |q 1| := by
    intro x e he
    obtain ⟨j, rfl | rfl⟩ := mem_unitSteps.mp he
    · rw [lf_add_unit]
      exact hB j
    · rw [lf_add_neg_unit, abs_neg]
      exact hB j
  have hinc : ∀ i, ∀ᵐ ω ∂μ, |dynkin ε (lf q) X (i + 1) ω - dynkin ε (lf q) X i ω| ≤
      2 * (|q 0| + |q 1|) := fun i =>
    (ae_abs_dynkin_succ_sub_le hd hε hεd hX (lf q)).mono fun ω hω =>
      hω i (|q 0| + |q 1|) (hosc (X i ω))
  obtain ⟨Y, hY, hbd, h0, hae⟩ := CERW.Generic.Martingale.exists_martingale_clamp hmart
    (b := 2 * (|q 0| + |q 1|)) (by positivity) hinc
  have hY0 : ∀ ω, Y 0 ω = 0 := fun ω => by rw [h0 ω, dynkin_zero]
  have hX0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    rw [ae_iff]
    exact hX.start
  refine ⟨Y, hY, hY0, hbd, fun n => ?_, ?_, ?_⟩
  · refine MemLp.of_bound
      ((hY.stronglyMeasurable n).mono ((pathFiltration hX.measurable).le n)).aestronglyMeasurable
      (2 * (|q 0| + |q 1|) * n) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_le_mul_of_increments hY0 hbd n ω
  · filter_upwards [hae, hX0] with ω hω hω0 n
    rw [hω n]
    exact dynkin_lf_eq ε X q ω hω0 n
  · have hvar := fun t => condExp_sq_lf_eq hε hεd hX q hae t
    filter_upwards [ae_all_iff.mpr hvar] with ω hω n
    have hsum : predBracket μ (pathFiltration hX.measurable) Y Y n ω = ∑ t ∈ Finset.range n,
        ((q 0 ^ 2 + q 1 ^ 2) / 2 -
          (if X t ω ≠ 0 ∧ X t ω ∉ (Finset.range t).image (fun i => X i ω) then
            ε * inner ℝ q (unitDir (toSpace (X t ω))) else 0) ^ 2) := by
      rw [predBracket, Finset.sum_apply]
      exact Finset.sum_congr rfl fun t _ => hω t
    rw [hsum]
    refine ⟨?_, ?_⟩
    · calc _ ≤ ∑ _t ∈ Finset.range n, ((q 0 ^ 2 + q 1 ^ 2) / 2) :=
          Finset.sum_le_sum fun t _ => sub_le_self _ (sq_nonneg _)
        _ = n * ((q 0 ^ 2 + q 1 ^ 2) / 2) := by simp
    · have hterm : ∀ t ∈ Finset.range n,
          (q 0 ^ 2 + q 1 ^ 2) / 2 - ε ^ 2 * (q 0 ^ 2 + q 1 ^ 2) *
            (if X t ω ≠ 0 ∧ X t ω ∉ (Finset.range t).image (fun i => X i ω) then
              (1 : ℝ) else 0) ≤
          (q 0 ^ 2 + q 1 ^ 2) / 2 -
            (if X t ω ≠ 0 ∧ X t ω ∉ (Finset.range t).image (fun i => X i ω) then
              ε * inner ℝ q (unitDir (toSpace (X t ω))) else 0) ^ 2 := by
        intro t _
        refine sub_le_sub_left ?_ _
        split_ifs
        · rw [mul_pow, mul_one]
          exact mul_le_mul_of_nonneg_left (inner_unitDir_sq_le q _) (sq_nonneg ε)
            |>.trans_eq (by ring)
        · simp
      refine le_trans ?_ (Finset.sum_le_sum hterm)
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hcount := sum_fresh_indicator_le_card (fun j => X j ω) n
      have h2 : (0 : ℝ) ≤ ε ^ 2 * (q 0 ^ 2 + q 1 ^ 2) := by positivity
      have h3 := mul_le_mul_of_nonneg_left hcount h2
      have hc : ∑ _t ∈ Finset.range n, ((q 0 ^ 2 + q 1 ^ 2) / 2) =
          n * ((q 0 ^ 2 + q 1 ^ 2) / 2) := by simp
      rw [hc]
      linarith

/-! ### The range is a vanishing fraction of the time -/

/-- **The range is a vanishing fraction of the time.** Almost surely
`|A_n| / n → 0`: the proved fluctuation rates keep the walk in the disk of radius `2 r_n`, which
has `O(r_n²) = O(n^{2/3})` lattice points. -/
theorem card_departureRange_div_tendsto_zero {ε : ℝ} (hε0 : 0 < ε)
    (hεd : ε < 1 / ((2 : ℕ) : ℝ)) {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ((departureRange (fun j => X j ω) n).card : ℝ) / n)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, -, hae⟩ := planar_radii_rates hε0 hεd (p := 1) one_pos
  have hK : 0 < (3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) := by positivity
  have hev := eventually_sqrt_mul_log_le hK C one_pos
  have hg := tendsto_card_ratio_bound ((3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3)) 1
  filter_upwards [hae μ X hX] with ω hgoodω
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => by positivity) ?_ hg
  filter_upwards [hgoodω, hev, eventually_ge_atTop 1] with n hgood hn hn1
  have hr : ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal)) ^
      ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1)) =
      (3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 :=
    planar_radius_eq hε0 n
  rw [hr] at hgood
  set r := (3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 with hrdef
  have hM : maxRadius (fun j => X j ω) n ≤ 2 * r := by linarith [hgood.2, hn]
  have hM0 : 0 ≤ maxRadius (fun j => X j ω) n :=
    (LatticeProb.euclidNorm_nonneg (X 0 ω)).trans
      (euclidNorm_le_maxRadius (fun j => X j ω) (Nat.zero_le n))
  have hcard : ((departureRange (fun j => X j ω) n).card : ℝ) ≤ (4 * r + 1) ^ 2 :=
    (card_departureRange_le (fun j => X j ω) n).trans
      (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  calc ((departureRange (fun j => X j ω) n).card : ℝ) / n ≤ (4 * r + 1) ^ 2 / n :=
        div_le_div_of_nonneg_right hcard hn0.le
    _ = 1 ^ 2 * (4 * r + 1) ^ 2 / n := by ring

/-! ### The central limit theorem for every linear form -/

/-- The linear form of `q` against the compensated position. -/
private lemma inner_compensated (ε : ℝ) (q : EuclideanSpace ℝ (Fin 2)) (x : Site 2)
    (A : Finset (Site 2)) :
    inner ℝ q (toSpace x + ε • ∑ z ∈ A, unitDir (toSpace z)) =
      lf q x + ε * ∑ z ∈ A, inner ℝ q (unitDir (toSpace z)) := by
  have h1 : inner ℝ q (toSpace x) = lf q x := by
    rw [inner_eq_sum]
    simp [lf, toSpace_apply]
  rw [inner_add_right, real_inner_smul_right, inner_sum, h1]

/-- A predictable bracket is almost everywhere strongly measurable. -/
private theorem aestronglyMeasurable_predBracket' {Ω : Type*} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ) (n : ℕ) :
    AEStronglyMeasurable (predBracket μ ℱ S S n) μ := by
  have h := Finset.stronglyMeasurable_sum (Finset.range n)
    (f := fun t => μ[fun ω => (S (t + 1) ω - S t ω) * (S (t + 1) ω - S t ω) | ℱ t])
    fun t _ => stronglyMeasurable_condExp.mono (ℱ.le t)
  exact (h.aestronglyMeasurable).congr (Filter.Eventually.of_forall fun ω => by
    simp [predBracket])

/-- A sequence of functions that is eventually identically zero tends to zero in measure. -/
private theorem tendstoInMeasure_zero_of_eventually_eq' {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : ℕ → Ω → ℝ} (h : ∀ᶠ n in atTop, f n = fun _ => 0) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h] with n hn
  symm
  have hempty : {x | ε ≤ edist (f n x) ((fun _ => (0 : ℝ)) x)} = ∅ := by
    ext x
    simp [hn, not_le.mpr hε]
  rw [hempty, measure_empty]

/-- The normalization `max (√n) 1`, positive for every `n` and equal to `√n` from `n = 1` on. -/
private noncomputable def scaleN (n : ℕ) : ℝ := max (Real.sqrt n) 1

private lemma scaleN_pos (n : ℕ) : 0 < scaleN n := lt_of_lt_of_le one_pos (le_max_right _ _)

private lemma scaleN_tendsto : Tendsto scaleN atTop atTop :=
  tendsto_atTop_mono (fun _ => le_max_left _ _)
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

private lemma scaleN_eq_sqrt {n : ℕ} (hn : 1 ≤ n) : scaleN n = Real.sqrt n := by
  have h1 : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  exact max_eq_left h1

private lemma scaleN_sq {n : ℕ} (hn : 1 ≤ n) : scaleN n ^ 2 = n := by
  rw [scaleN_eq_sqrt hn, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- The conditional Lindeberg sums of a martingale with increments bounded by `b` vanish once the
normalization exceeds `b / δ`. -/
private theorem tendstoInMeasure_lindeberg_bounded {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) (ℱ : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) {b : ℝ}
    (hYinc : ∀ i ω, |Y (i + 1) ω - Y i ω| ≤ b) (δ : ℝ) (hδ : 0 < δ) :
    TendstoInMeasure μ
      (fun n => ∑ i ∈ Finset.range n,
        μ[fun ω => ((Y (i + 1) ω - Y i ω) / scaleN n) ^ 2 *
          (if δ < |Y (i + 1) ω - Y i ω| / scaleN n then 1 else 0) | ℱ i])
      atTop (fun _ => 0) := by
  refine tendstoInMeasure_zero_of_eventually_eq' ?_
  filter_upwards [scaleN_tendsto.eventually_gt_atTop (b / δ)] with n hn
  have hzero : ∀ i, (fun ω => ((Y (i + 1) ω - Y i ω) / scaleN n) ^ 2 *
        (if δ < |Y (i + 1) ω - Y i ω| / scaleN n then 1 else 0)) = 0 := by
    intro i
    funext ω
    have h1 : |Y (i + 1) ω - Y i ω| / scaleN n ≤ δ := by
      rw [div_le_iff₀ (scaleN_pos n)]
      have h2 : b < scaleN n * δ := (div_lt_iff₀ hδ).1 hn
      calc |Y (i + 1) ω - Y i ω| ≤ b := hYinc i ω
        _ ≤ δ * scaleN n := by rw [mul_comm]; exact h2.le
    simp [not_lt.mpr h1]
  funext ω
  simp only [hzero, condExp_zero, Finset.sum_apply, Pi.zero_apply, Finset.sum_const_zero]

/-- A sequence squeezed between `c n - k C_n` and `c n`, with `C_n / n → 0`, has ratio to `n`
tending to `c`. -/
private lemma tendsto_ratio_of_sandwich {c k : ℝ} {P C : ℕ → ℝ}
    (hC : Tendsto (fun n : ℕ => C n / n) atTop (𝓝 0))
    (hup : ∀ n : ℕ, P n ≤ n * c) (hlow : ∀ n : ℕ, n * c - k * C n ≤ P n) :
    Tendsto (fun n : ℕ => P n / n) atTop (𝓝 c) := by
  have hlower : Tendsto (fun n : ℕ => c - k * (C n / n)) atTop (𝓝 c) := by
    have h := (hC.const_mul k).const_sub c
    rw [mul_zero, sub_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have h3 := div_le_div_of_nonneg_right (hlow n) hn0.le
    have h4 : ((n : ℝ) * c - k * C n) / n = c - k * (C n / n) := by
      field_simp
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have h3 := div_le_div_of_nonneg_right (hup n) hn0.le
    have h4 : (n : ℝ) * c / n = c := by
      field_simp
    linarith

/-- The martingale central limit theorem for a square-integrable martingale with bounded
increments whose predictable bracket over `scaleN n ^ 2` tends to `v` in measure. -/
private theorem clt_of_bounded {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (hY : Martingale Y ℱ μ)
    (hYL2 : ∀ n, MemLp (Y n) 2 μ) (hY0 : ∀ ω, Y 0 ω = 0) {b : ℝ}
    (hYinc : ∀ i ω, |Y (i + 1) ω - Y i ω| ≤ b) (v : ℝ≥0)
    (hbr : TendstoInMeasure μ (fun n ω => predBracket μ ℱ Y Y n ω / scaleN n ^ 2) atTop
      (fun _ => (v : ℝ))) :
    TendstoInDistribution (fun n ω => Y n ω / scaleN n) atTop id (fun _ => μ)
      (gaussianReal 0 v) :=
  CERW.Generic.Martingale.CLT.martingaleCLT_proved.{u} μ ℱ Y hY hYL2 hY0 scaleN
    (fun n => scaleN_pos n) v (fun δ hδ => tendstoInMeasure_lindeberg_bounded μ ℱ Y hYinc δ hδ)
    hbr

/-- **The central limit theorem for every linear form of the compensated position.** In the plane,
for `0 < ε < 1/2` and every `q ∈ ℝ²` (the case `q = 0` included),
`⟨q, X_n + ε Σ_{x ∈ A_n} u_x⟩ / √n ⇒ N(0, |q|²/2)`. Bounded increments, the predictable bracket,
the Lindeberg condition and `|A_n| / n → 0` are all derived from `IsCERW`. -/
theorem linearForm_clt {ε : ℝ} (hε0 : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X) (q : EuclideanSpace ℝ (Fin 2)) :
    TendstoInDistribution
      (fun n ω => inner ℝ q (toSpace (X n ω) +
        ε • ∑ x ∈ departureRange (fun j => X j ω) n, unitDir (toSpace x)) / Real.sqrt n)
      atTop id (fun _ => μ) (gaussianReal 0 (‖q‖ ^ 2 / 2).toNNReal) := by
  obtain ⟨Y, hY, hY0, hYinc, hYL2, hYform, hYbr⟩ := exists_lf_martingale hε0 hεd hX q
  have hq2 : ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 := norm_sq_plane q
  have hrange := card_departureRange_div_tendsto_zero hε0 hεd μ hX
  have hbr : TendstoInMeasure μ
      (fun n ω => predBracket μ (pathFiltration hX.measurable) Y Y n ω / scaleN n ^ 2) atTop
      (fun _ => (((‖q‖ ^ 2 / 2).toNNReal : ℝ≥0) : ℝ)) := by
    have hv : (((‖q‖ ^ 2 / 2).toNNReal : ℝ≥0) : ℝ) = ‖q‖ ^ 2 / 2 :=
      Real.coe_toNNReal _ (by positivity)
    rw [hv]
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
    · simpa only [div_eq_mul_inv] using
        (aestronglyMeasurable_predBracket' μ (pathFiltration hX.measurable) Y n).mul_const
          ((scaleN n ^ 2)⁻¹)
    · filter_upwards [hYbr, hrange] with ω hbrω hrω
      have hrat := tendsto_ratio_of_sandwich (c := ‖q‖ ^ 2 / 2) (k := ε ^ 2 * ‖q‖ ^ 2)
        (P := fun n => predBracket μ (pathFiltration hX.measurable) Y Y n ω)
        (C := fun n => ((departureRange (fun j => X j ω) n).card : ℝ)) hrω
        (fun n => by rw [hq2]; exact (hbrω n).1)
        (fun n => by rw [hq2]; exact (hbrω n).2)
      refine hrat.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn1
      rw [scaleN_sq hn1]
  have hX2 := clt_of_bounded μ (pathFiltration hX.measurable) Y hY hYL2 hY0 hYinc
    _ hbr
  refine hX2.congr (fun n => ?_) Filter.EventuallyEq.rfl
  filter_upwards [hYform] with ω hω
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [scaleN, hY0 ω]
  · show Y n ω / scaleN n = _
    rw [hω n, scaleN_eq_sqrt hn, inner_compensated]

/-! ### The vector law -/

/-- The canonical covariance `(1/2) I` of the planar limit is positive definite. -/
theorem half_identity_posDef : (((1 : ℝ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.posDef_diagonal_iff]
  intro i
  norm_num

/-- The departure range depends on the path only up to time `n - 1`. -/
private lemma departureRange_congr_plane {x y : ℕ → Site 2} {n : ℕ}
    (h : ∀ j ≤ n, x j = y j) : departureRange x n = departureRange y n := by
  unfold departureRange
  exact Finset.image_congr fun j hj => h j (Finset.mem_range.mp hj).le

/-- The compensated position at time `n` is a measurable function of the sample point: it is a
function of the past path, which takes countably many values. -/
theorem measurable_compensated {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → Site 2}
    (hX : ∀ n, Measurable (X n)) (ε : ℝ) (n : ℕ) :
    Measurable (fun ω => toSpace (X n ω) +
      ε • ∑ x ∈ departureRange (fun j => X j ω) n, unitDir (toSpace x)) := by
  have hG : (fun ω => toSpace (X n ω) +
      ε • ∑ x ∈ departureRange (fun j => X j ω) n, unitDir (toSpace x)) =
      fun ω => (fun p : (i : Finset.Iic n) → Site 2 => toSpace (extendPath p n) +
        ε • ∑ x ∈ departureRange (extendPath p) n, unitDir (toSpace x)) (pastPath X n ω) := by
    funext ω
    have h : ∀ j ≤ n, (fun j => X j ω) j = extendPath (pastPath X n ω) j := fun j hj =>
      (extendPath_pastPath X hj ω).symm
    simp only [departureRange_congr_plane h, extendPath_pastPath X le_rfl ω]
  rw [hG]
  exact (measurable_of_countable (fun p : (i : Finset.Iic n) → Site 2 =>
    toSpace (extendPath p n) + ε • ∑ x ∈ departureRange (extendPath p) n,
      unitDir (toSpace x))).comp (measurable_pastPath hX n)

/-- The law of the normalized compensated position at time `n` is a probability measure. -/
theorem isProbabilityMeasure_map_compensated {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site 2} (hX : ∀ n, Measurable (X n)) (ε : ℝ)
    (n : ℕ) :
    IsProbabilityMeasure (μ.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ • (toSpace (X n ω) +
      ε • ∑ x ∈ departureRange (fun j => X j ω) n, unitDir (toSpace x)))) :=
  Measure.isProbabilityMeasure_map
    (((measurable_compensated hX ε n).const_smul ((Real.sqrt (n : ℝ))⁻¹)).aemeasurable)

/-- **The one-dimensional marginals of the Gaussian with covariance `(1/2) I`.** The image of
`N(0, I/2)` under `z ↦ ⟨z, t⟩` is `N(0, |t|²/2)`. -/
theorem map_inner_multivariateGaussian_half (t : EuclideanSpace ℝ (Fin 2)) :
    (multivariateGaussian 0 (((1 : ℝ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ))).map
        (fun z => inner ℝ z t) = gaussianReal 0 (‖t‖ ^ 2 / 2).toNNReal := by
  have hS := half_identity_posDef.posSemidef
  have hL := IsGaussian.map_eq_gaussianReal
    (μ := multivariateGaussian 0 (((1 : ℝ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) (innerSL ℝ t)
  have hfun : (fun z : EuclideanSpace ℝ (Fin 2) => inner ℝ z t) = innerSL ℝ t := by
    funext z
    simp [real_inner_comm]
  have hvar : Var[⇑(innerSL ℝ t);
      multivariateGaussian 0 (((1 : ℝ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ))] =
      ‖t‖ ^ 2 / 2 := by
    have h1 := covarianceBilin_self
      (μ := multivariateGaussian 0 (((1 : ℝ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      IsGaussian.memLp_two_id t
    rw [covarianceBilin_multivariateGaussian hS] at h1
    have h2 : (fun u : EuclideanSpace ℝ (Fin 2) => inner ℝ t u) = ⇑(innerSL ℝ t) := by
      funext u
      simp
    rw [h2] at h1
    rw [← h1, norm_sq_plane]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.one_apply]
    ring
  rw [hfun, hL, hvar, (innerSL ℝ t).integral_comp_id_comm IsGaussian.integrable_id]
  simp

/-- **The actual vector law is asymptotically Gaussian.** In the plane, for `0 < ε < 1/2`,
`(X_n + ε Σ_{x ∈ A_n} u_x) / √n` converges in distribution, as `ℝ²`-valued random variables on the
probability space of the walk, to the Mathlib multivariate Gaussian with mean `0` and covariance
`(1/2) I`. The device is the Cramér–Wold theorem of the library, whose proof is Lévy's convergence
theorem; its hypotheses are the linear-form central limit theorems `linearForm_clt` and the
identification `map_inner_multivariateGaussian_half` of the one-dimensional marginals. -/
theorem vector_clt {ε : ℝ} (hε0 : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) => (Real.sqrt n)⁻¹ • (toSpace (X n ω) +
        ε • ∑ x ∈ departureRange (fun j => X j ω) n, unitDir (toSpace x)))
      atTop id (fun _ => μ)
      (multivariateGaussian 0 (((1 : ℝ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) := by
  refine LatticeProb.CramerWold.tendstoInDistribution_of_forall_inner _ id μ _
    (fun n => ((measurable_compensated hX.measurable ε n).const_smul
      ((Real.sqrt (n : ℝ))⁻¹)).aemeasurable)
    aemeasurable_id fun t => ?_
  have hscalar := (linearForm_clt hε0 hεd μ hX t).congr (Y := fun (n : ℕ) (ω : Ω) => inner ℝ
    ((Real.sqrt n)⁻¹ • (toSpace (X n ω) +
      ε • ∑ x ∈ departureRange (fun j => X j ω) n, unitDir (toSpace x))) t)
    (fun n => Filter.Eventually.of_forall fun ω => by
      beta_reduce
      rw [real_inner_smul_left, real_inner_comm, div_eq_inv_mul]) Filter.EventuallyEq.rfl
  exact LatticeProb.CramerWold.tendstoInDistribution_of_map_eq hscalar
    (fun z : EuclideanSpace ℝ (Fin 2) => inner ℝ (id z) t)
    (by fun_prop) (map_inner_multivariateGaussian_half t)

end CERW.Support.Lower.PlanarGap
