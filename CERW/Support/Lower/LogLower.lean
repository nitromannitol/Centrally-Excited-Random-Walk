import CERW.Support.Statements
import CERW.Support.Contact.Quadratic
import CERW.Generic.Martingale.Clamp
import CERW.Generic.Kernel.RadialPacking
import CERW.Support.Main.BorelCantelli
import CERW.Support.Occupation.SiteArith
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.Cells
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Occupation.Facts
import CERW.Support.Law.CondStep
import LatticeProb.Prob.Freedman

/-!
# Logarithmic lower bounds for the radii

`prop:log-lower` of the paper (Proposition 9.4): for centrally excited random walk in dimension
`d ≥ 2` with `0 < ε < 1/d`, there are `c, C, h₀` such that for all large `n` and every `h` with
`h₀ ≤ h ≤ r_n/8`,
`P(R_in(n) ≥ r_n - h, R_out(n) ≤ r_n + h) ≤ exp(-c r_n^{d-1} e^{-C h})` and
`P(R_out(n) ≤ r_n + h) ≤ exp(-c r_n^{d-1} e^{-C h}) + exp(-c r_n^{d-3} h²)`, and almost surely,
for all large `n`, `max(r_n - R_in(n), R_out(n) - r_n) > c log n`, and `R_out(n) - r_n > c log n`
if `d ≥ 3`.

The proof follows the paper. A deterministic set of sites `Λ` with a straight path leaving the
ball of radius `r_n + h` from each of its sites gives a sequence of trials, each succeeding with
conditional probability at least `p₀^T`; the trial bound is proved on path space by induction on
the number of trials (`trials_bound`). Two shells of lattice sites are counted by comparison with
unit cells (`exists_card_shell`). Where `R_out(n) ≤ r_n + h` and few sites of the outer shell are
visited, the quadratic martingale `𝒬` stopped at the exit from the ball of radius `r_n + h` is
pushed far down, which has exponentially small probability by Freedman's inequality
(`quadratic_lower_tail`). The almost-sure bounds follow by Borel-Cantelli at
`h = (d - 1) log r_n / (4C)`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm ballFinset unit)

namespace CERW.Support.Lower

section Trials

open CERW.Support.Statements CERW CERW.Support.Law

variable {d : ℕ}

/-- Every conditional one-step probability of a unit step is at least `1/(2d) - ε/2`. -/
private theorem stepProb_ge {ε : ℝ} (hε : 0 ≤ ε) (x : ℕ → Site d) (n : ℕ) {e : Site d}
    (he : e ∈ unitSteps d) : 1 / (2 * (d : ℝ)) - ε / 2 ≤ stepProb d ε x n e := by
  have hsrw : 1 / (2 * (d : ℝ)) - ε / 2 ≤ 1 / (2 * (d : ℝ)) := by linarith
  unfold stepProb
  split_ifs with h
  · obtain ⟨i, rfl | rfl⟩ := mem_unitSteps.mp he
    · rw [firstStep_unit]
      set r := ((x n i : ℤ) : ℝ) / euclidNorm (x n) with hr
      have habs : |r| ≤ 1 := abs_coord_div_euclidNorm_le_one (x n) i
      have h2 : ε / 2 * r ≤ ε / 2 :=
        calc ε / 2 * r ≤ ε / 2 * 1 :=
              mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) habs) (by linarith)
          _ = ε / 2 := mul_one _
      linarith
    · rw [firstStep_neg_unit]
      set r := ((x n i : ℤ) : ℝ) / euclidNorm (x n) with hr
      have habs : |r| ≤ 1 := abs_coord_div_euclidNorm_le_one (x n) i
      have hr1 : -1 ≤ r := by linarith [neg_abs_le r]
      have h2 : ε / 2 * (-1) ≤ ε / 2 * r := mul_le_mul_of_nonneg_left hr1 (by linarith)
      linarith
  · obtain ⟨i, rfl | rfl⟩ := mem_unitSteps.mp he
    · rw [srwStep_unit]
      exact hsrw
    · rw [srwStep_neg_unit]
      exact hsrw

/-- A set of paths is determined by the positions at times `0, …, s` when changing a path after
time `s` does not change membership. -/
private def DetUpTo (s : ℕ) (B : Set (ℕ → Site d)) : Prop :=
  ∀ x y : ℕ → Site d, (∀ i ≤ s, x i = y i) → (x ∈ B ↔ y ∈ B)

/-- A set determined up to time `s` is determined up to any later time. -/
private lemma DetUpTo.mono {s s' : ℕ} {B : Set (ℕ → Site d)} (hB : DetUpTo s B) (h : s ≤ s') :
    DetUpTo s' B :=
  fun x y hxy => hB x y fun i hi => hxy i (hi.trans h)

/-- The intersection of two sets determined up to time `s` is determined up to time `s`. -/
private lemma DetUpTo.inter {s : ℕ} {A B : Set (ℕ → Site d)} (hA : DetUpTo s A)
    (hB : DetUpTo s B) : DetUpTo s (A ∩ B) :=
  fun x y hxy => and_congr (hA x y hxy) (hB x y hxy)

/-- The complement of a set determined up to time `s` is determined up to time `s`. -/
private lemma DetUpTo.compl {s : ℕ} {B : Set (ℕ → Site d)} (hB : DetUpTo s B) :
    DetUpTo s Bᶜ :=
  fun x y hxy => not_congr (hB x y hxy)

/-- A set determined up to time `s` is measurable. -/
private lemma DetUpTo.measurableSet {s : ℕ} {B : Set (ℕ → Site d)} (hB : DetUpTo s B) :
    MeasurableSet B := by
  have hr : Measurable (fun (x : ℕ → Site d) (i : Finset.Iic s) => x i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hBeq : B = (fun (x : ℕ → Site d) (i : Finset.Iic s) => x i) ⁻¹'
      ((fun (x : ℕ → Site d) (i : Finset.Iic s) => x i) '' B) := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact (hB y x fun i hi => congrFun hyx ⟨i, Finset.mem_Iic.mpr hi⟩).mp hy
  rw [hBeq]
  exact hr MeasurableSet.of_discrete

/-- The cylinder of paths that agree with `y` at times `0, …, s`. -/
private def cyl (s : ℕ) (y : ℕ → Site d) : Set (ℕ → Site d) := {x | ∀ j ≤ s, x j = y j}

/-- A cylinder up to time `s` is determined up to time `s`. -/
private lemma detUpTo_cyl (s : ℕ) (y : ℕ → Site d) : DetUpTo s (cyl s y) := by
  intro x z hxz
  simp only [cyl, Set.mem_setOf_eq]
  exact forall₂_congr fun j hj => by rw [hxz j hj]

/-- The cylinder factorization of the path law `ν`: the mass of a cylinder up to time `n + 1`
is the mass of the cylinder up to time `n` times the one-step probability. -/
private def StepFactors (ε : ℝ) (ν : Measure (ℕ → Site d)) : Prop :=
  ∀ (n : ℕ) (y : ℕ → Site d),
    ν (cyl (n + 1) y) = ν (cyl n y) * ENNReal.ofReal (stepProb d ε y n (y (n + 1) - y n))

/-- The mass of a measurable set is the sum of its masses on the cylinders up to time `s`. -/
private lemma measure_eq_tsum_cyl (ν : Measure (ℕ → Site d)) (s : ℕ) {A : Set (ℕ → Site d)}
    (hA : MeasurableSet A) :
    ν A = ∑' p : (i : Finset.Iic s) → Site d, ν (A ∩ cyl s (extendPath p)) := by
  have hunion : A = ⋃ p : (i : Finset.Iic s) → Site d, A ∩ cyl s (extendPath p) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    refine ⟨fun hx => ⟨fun i => x i, hx, fun j hj => ?_⟩, fun ⟨_, hx, _⟩ => hx⟩
    rw [extendPath_of_le _ hj]
  conv_lhs => rw [hunion]
  refine measure_iUnion ?_ fun p => hA.inter (detUpTo_cyl s _).measurableSet
  intro p q hpq
  refine Set.disjoint_left.mpr fun x hxp hxq => hpq ?_
  funext i
  have hi : (i : ℕ) ≤ s := Finset.mem_Iic.mp i.2
  have h1 := hxp.2 i hi
  have h2 := hxq.2 i hi
  rw [extendPath_of_le _ hi] at h1 h2
  exact h1.symm.trans h2

/-- The one-step event `x (s + 1) = x s + E x` is determined up to time `s + 1` when `E` is
determined up to time `s`. -/
private lemma detUpTo_step {s : ℕ} {E : (ℕ → Site d) → Site d}
    (hE : ∀ x y : ℕ → Site d, (∀ i ≤ s, x i = y i) → E x = E y) :
    DetUpTo (s + 1) {x | x (s + 1) = x s + E x} := by
  intro x y hxy
  simp only [Set.mem_setOf_eq]
  rw [hxy (s + 1) le_rfl, hxy s (Nat.le_succ s), hE x y fun i hi => hxy i (Nat.le_succ_of_le hi)]

/-- One step of the trial: a set `B` determined up to time `s` loses at most the factor
`1/(2d) - ε/2` when the next step is required to be the prescribed unit step `E`. -/
private lemma step_bound {ε : ℝ} (hε : 0 ≤ ε) {ν : Measure (ℕ → Site d)} [IsFiniteMeasure ν]
    (hν : StepFactors ε ν) {s : ℕ} {B : Set (ℕ → Site d)} (hB : DetUpTo s B)
    {E : (ℕ → Site d) → Site d} (hE : ∀ x y : ℕ → Site d, (∀ i ≤ s, x i = y i) → E x = E y)
    (hEu : ∀ x ∈ B, E x ∈ unitSteps d) :
    ENNReal.ofReal (1 / (2 * (d : ℝ)) - ε / 2) * ν B ≤
      ν (B ∩ {x | x (s + 1) = x s + E x}) := by
  have hBm : MeasurableSet B := hB.measurableSet
  have hSm : MeasurableSet (B ∩ {x | x (s + 1) = x s + E x}) :=
    ((hB.mono (Nat.le_succ s)).inter (detUpTo_step hE)).measurableSet
  rw [measure_eq_tsum_cyl ν s hBm, measure_eq_tsum_cyl ν s hSm, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun p => ?_
  set y : ℕ → Site d := extendPath p with hy
  by_cases hyB : y ∈ B
  · set y' : ℕ → Site d := fun j => if j = s + 1 then y s + E y else y j with hy'
    have hy's : y' s = y s := by simp [hy']
    have hy'1 : y' (s + 1) = y s + E y := by simp [hy']
    have hcylB : B ∩ cyl s y = cyl s y := by
      refine Set.inter_eq_right.mpr fun x hx => ?_
      exact (hB x y hx).mpr hyB
    have hset : (B ∩ {x | x (s + 1) = x s + E x}) ∩ cyl s y = cyl (s + 1) y' := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, cyl]
      constructor
      · rintro ⟨⟨hxB, hxs⟩, hxc⟩ j hj
        by_cases hj1 : j = s + 1
        · rw [hj1, hy'1, hxs, hxc s le_rfl, hE x y hxc]
        · have hjs : j ≤ s := by omega
          simp only [hy', if_neg hj1]
          exact hxc j hjs
      · intro h
        have hxc : ∀ j ≤ s, x j = y j := fun j hj => by
          rw [h j (Nat.le_succ_of_le hj)]
          simp only [hy', if_neg (by omega : j ≠ s + 1)]
        refine ⟨⟨(hB x y hxc).mpr hyB, ?_⟩, hxc⟩
        rw [h (s + 1) le_rfl, hy'1, hxc s le_rfl, hE x y hxc]
    have hcyl' : cyl s y' = cyl s y := by
      ext x
      simp only [cyl, Set.mem_setOf_eq]
      refine forall₂_congr fun j hj => ?_
      simp only [hy', if_neg (by omega : j ≠ s + 1)]
    have hdiff : y' (s + 1) - y' s = E y := by
      rw [hy'1, hy's, add_sub_cancel_left]
    rw [hcylB, hset, hν s y', hcyl', hdiff, mul_comm]
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
      (by rw [← hdiff]; exact stepProb_ge hε y' s (by rw [hdiff]; exact hEu y hyB))) _
  · have hempty : B ∩ cyl s y = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx => hyB ?_
      exact (hB x y hx.2).mp hx.1
    have hempty2 : (B ∩ {x | x (s + 1) = x s + E x}) ∩ cyl s y = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx => hyB ?_
      exact (hB x y hx.2).mp hx.1.1
    rw [hempty, hempty2]
    simp

/-- The event that the walk steps by `w (x t)` at each of the times `t, …, t + m - 1`. -/
private def stepsAlong (w : Site d → Site d) (t m : ℕ) : Set (ℕ → Site d) :=
  {x | ∀ i < m, x (t + i + 1) = x (t + i) + w (x t)}

/-- The event `stepsAlong w t m` is determined up to time `t + m`. -/
private lemma detUpTo_stepsAlong (w : Site d → Site d) (t m : ℕ) :
    DetUpTo (t + m) (stepsAlong w t m) := by
  intro x y hxy
  simp only [stepsAlong, Set.mem_setOf_eq]
  have h0 : x t = y t := hxy t (by omega)
  refine forall₂_congr fun i hi => ?_
  rw [hxy (t + i + 1) (by omega), hxy (t + i) (by omega), h0]

/-- A set `B` determined up to time `t` and contained in `{x t ∈ Λ}` keeps the mass fraction
`p₀ ^ m` when the walk is required to step `m` times by `w (x t)` after time `t`. -/
private lemma trial_iter {ε : ℝ} (hε : 0 ≤ ε) (hp0 : 0 ≤ 1 / (2 * (d : ℝ)) - ε / 2)
    {ν : Measure (ℕ → Site d)} [IsFiniteMeasure ν] (hν : StepFactors ε ν)
    {Λ : Finset (Site d)} {w : Site d → Site d} (hw : ∀ x ∈ Λ, w x ∈ unitSteps d)
    {t : ℕ} {B : Set (ℕ → Site d)} (hB : DetUpTo t B) (hBΛ : ∀ x ∈ B, x t ∈ Λ) (m : ℕ) :
    ENNReal.ofReal ((1 / (2 * (d : ℝ)) - ε / 2) ^ m) * ν B ≤ ν (B ∩ stepsAlong w t m) := by
  induction m with
  | zero => simp [stepsAlong]
  | succ m ih =>
    have hBm : DetUpTo (t + m) (B ∩ stepsAlong w t m) :=
      (hB.mono (Nat.le_add_right t m)).inter (detUpTo_stepsAlong w t m)
    have hE : ∀ x y : ℕ → Site d, (∀ i ≤ t + m, x i = y i) → w (x t) = w (y t) :=
      fun x y h => by rw [h t (Nat.le_add_right t m)]
    have hEu : ∀ x ∈ B ∩ stepsAlong w t m, w (x t) ∈ unitSteps d :=
      fun x hx => hw _ (hBΛ x hx.1)
    have hstep := step_bound (E := fun x => w (x t)) hε hν hBm hE hEu
    have hset : (B ∩ stepsAlong w t m) ∩ {x | x (t + m + 1) = x (t + m) + w (x t)} =
        B ∩ stepsAlong w t (m + 1) := by
      ext x
      simp only [stepsAlong, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨hxB, hxm⟩, hxs⟩
        refine ⟨hxB, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with him | him
        · exact hxm i him
        · rw [him]
          exact hxs
      · rintro ⟨hxB, hx⟩
        exact ⟨⟨hxB, fun i hi => hx i (Nat.lt_succ_of_lt hi)⟩, hx m (Nat.lt_succ_self m)⟩
    rw [hset] at hstep
    rw [pow_succ', ENNReal.ofReal_mul hp0, mul_assoc]
    exact (mul_le_mul_right ih _).trans hstep

/-- A set `B` determined up to time `t` and contained in `{x t ∈ Λ}` loses at most the fraction
`1 - p₀ ^ m` of its mass when the `m` steps after time `t` along `w (x t)` fail to all occur. -/
private lemma trial_fail {ε : ℝ} (hε : 0 ≤ ε) (hp0 : 0 ≤ 1 / (2 * (d : ℝ)) - ε / 2)
    {ν : Measure (ℕ → Site d)} [IsFiniteMeasure ν] (hν : StepFactors ε ν)
    {Λ : Finset (Site d)} {w : Site d → Site d} (hw : ∀ x ∈ Λ, w x ∈ unitSteps d)
    {t : ℕ} {B : Set (ℕ → Site d)} (hB : DetUpTo t B) (hBΛ : ∀ x ∈ B, x t ∈ Λ) (m : ℕ)
    (hq : (1 / (2 * (d : ℝ)) - ε / 2) ^ m ≤ 1) :
    ν (B ∩ (stepsAlong w t m)ᶜ) ≤
      ENNReal.ofReal (1 - (1 / (2 * (d : ℝ)) - ε / 2) ^ m) * ν B := by
  set q : ℝ := (1 / (2 * (d : ℝ)) - ε / 2) ^ m with hq'
  have hq0 : 0 ≤ q := pow_nonneg hp0 m
  have hSm : MeasurableSet (stepsAlong w t m) := (detUpTo_stepsAlong w t m).measurableSet
  have hsplit : ν (B ∩ stepsAlong w t m) + ν (B \ stepsAlong w t m) = ν B :=
    measure_inter_add_sdiff B hSm
  have hlow := trial_iter hε hp0 hν hw hB hBΛ m
  have hfin : ENNReal.ofReal q * ν B ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν B)
  have hsum : ENNReal.ofReal (1 - q) * ν B + ENNReal.ofReal q * ν B = ν B := by
    rw [← add_mul, ← ENNReal.ofReal_add (sub_nonneg.mpr hq) hq0, sub_add_cancel,
      ENNReal.ofReal_one, one_mul]
  rw [← Set.sdiff_eq]
  refine (ENNReal.add_le_add_iff_right hfin).mp ?_
  rw [hsum]
  calc ν (B \ stepsAlong w t m) + ENNReal.ofReal q * ν B
      ≤ ν (B \ stepsAlong w t m) + ν (B ∩ stepsAlong w t m) := by gcongr
    _ = ν B := by rw [add_comm, hsplit]

/-- Time `t` is a first arrival at `Λ`: the walk is in `Λ` at time `t` and has not been at that
site before. -/
private def FirstArrival (Λ : Finset (Site d)) (x : ℕ → Site d) (t : ℕ) : Prop :=
  x t ∈ Λ ∧ ∀ i < t, x i ≠ x t

/-- Being a first arrival at time `s ≤ t` depends only on the positions up to time `t`. -/
private lemma firstArrival_congr {Λ : Finset (Site d)} {x y : ℕ → Site d} {t s : ℕ}
    (hs : s ≤ t) (h : ∀ i ≤ t, x i = y i) : FirstArrival Λ x s ↔ FirstArrival Λ y s := by
  unfold FirstArrival
  rw [h s hs]
  exact and_congr Iff.rfl (forall₂_congr fun i hi => by rw [h i (by omega)])

/-- A trial starts at time `t` when searching from time `s₀`: `t` is the first arrival at `Λ`
at or after `s₀`, and the trial of `T` steps from `t` ends by time `n`. -/
private def startSet (Λ : Finset (Site d)) (T n s₀ t : ℕ) : Set (ℕ → Site d) :=
  {x | s₀ ≤ t ∧ t + T ≤ n ∧ FirstArrival Λ x t ∧ ∀ s, s₀ ≤ s → s < t → ¬ FirstArrival Λ x s}

/-- The event that a trial starts at time `t` is determined up to time `t`. -/
private lemma detUpTo_startSet (Λ : Finset (Site d)) (T n s₀ t : ℕ) :
    DetUpTo t (startSet Λ T n s₀ t) := by
  intro x y hxy
  simp only [startSet, Set.mem_setOf_eq]
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr (firstArrival_congr le_rfl hxy)
    (forall_congr' fun s => imp_congr_right fun _ => imp_congr_right fun hst =>
      not_congr (firstArrival_congr hst.le hxy))))

/-- Trials that start at different times when searching from `s₀` are disjoint events. -/
private lemma startSet_disjoint (Λ : Finset (Site d)) (T n s₀ : ℕ) {t t' : ℕ} (h : t < t') :
    Disjoint (startSet Λ T n s₀ t) (startSet Λ T n s₀ t') := by
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  exact hx'.2.2.2 t hx.1 h hx.2.2.1

/-- The event "searching from time `s₀`, at least `j` trials start, and the first `j` all
fail", where each trial lasts `T` steps and the next search starts at the end of the trial. -/
private def trialSet (Λ : Finset (Site d)) (w : Site d → Site d) (T n : ℕ) :
    ℕ → ℕ → Set (ℕ → Site d)
  | 0, _ => Set.univ
  | j + 1, s₀ => {x | ∃ t, x ∈ startSet Λ T n s₀ t ∧ x ∉ stepsAlong w t T ∧
      x ∈ trialSet Λ w T n j (t + T)}

/-- The mass of the event that, from time `s₀` inside a set `A` determined up to time `s₀`,
at least `j` trials start and the first `j` fail is at most `(1 - p₀ ^ T) ^ j` times the mass
of `A`. -/
private lemma trialSet_bound {ε : ℝ} (hε : 0 ≤ ε) (hp0 : 0 ≤ 1 / (2 * (d : ℝ)) - ε / 2)
    {ν : Measure (ℕ → Site d)} [IsFiniteMeasure ν] (hν : StepFactors ε ν)
    {Λ : Finset (Site d)} {w : Site d → Site d} (hw : ∀ x ∈ Λ, w x ∈ unitSteps d) (T n : ℕ)
    (hq : (1 / (2 * (d : ℝ)) - ε / 2) ^ T ≤ 1) (j : ℕ) :
    ∀ (s₀ : ℕ) (A : Set (ℕ → Site d)), DetUpTo s₀ A →
      ν (A ∩ trialSet Λ w T n j s₀) ≤
        ENNReal.ofReal ((1 - (1 / (2 * (d : ℝ)) - ε / 2) ^ T) ^ j) * ν A := by
  induction j with
  | zero =>
    intro s₀ A _
    simp [trialSet]
  | succ j ih =>
    intro s₀ A hA
    set q : ℝ := (1 / (2 * (d : ℝ)) - ε / 2) ^ T with hq'
    have hq1 : 0 ≤ 1 - q := sub_nonneg.mpr hq
    set B : ℕ → Set (ℕ → Site d) := fun t => A ∩ startSet Λ T n s₀ t with hB
    have hBdet : ∀ t, DetUpTo t (B t) := by
      intro t
      by_cases hst : s₀ ≤ t
      · exact (hA.mono hst).inter (detUpTo_startSet Λ T n s₀ t)
      · exact fun x y _ => iff_of_false (fun hx => hst hx.2.1) (fun hy => hst hy.2.1)
    have hBΛ : ∀ t, ∀ x ∈ B t, x t ∈ Λ := fun t x hx => hx.2.2.2.1.1
    have hdet : ∀ t, DetUpTo (t + T) (B t ∩ (stepsAlong w t T)ᶜ) := fun t =>
      ((hBdet t).mono (Nat.le_add_right t T)).inter (detUpTo_stepsAlong w t T).compl
    have hsub : A ∩ trialSet Λ w T n (j + 1) s₀ ⊆
        ⋃ t, (B t ∩ (stepsAlong w t T)ᶜ) ∩ trialSet Λ w T n j (t + T) := by
      rintro x ⟨hxA, t, hxt, hxs, hxG⟩
      exact Set.mem_iUnion.mpr ⟨t, ⟨⟨hxA, hxt⟩, hxs⟩, hxG⟩
    have hdisj : Pairwise (Function.onFun Disjoint B) := by
      intro t t' htt'
      rcases lt_or_gt_of_ne htt' with h | h
      · exact (startSet_disjoint Λ T n s₀ h).mono Set.inter_subset_right Set.inter_subset_right
      · exact ((startSet_disjoint Λ T n s₀ h).mono Set.inter_subset_right
          Set.inter_subset_right).symm
    have hsum : ∑' t, ν (B t) ≤ ν A := by
      rw [← measure_iUnion hdisj fun t => (hBdet t).measurableSet]
      exact measure_mono (Set.iUnion_subset fun t => Set.inter_subset_left)
    calc ν (A ∩ trialSet Λ w T n (j + 1) s₀)
        ≤ ν (⋃ t, (B t ∩ (stepsAlong w t T)ᶜ) ∩ trialSet Λ w T n j (t + T)) :=
          measure_mono hsub
      _ ≤ ∑' t, ν ((B t ∩ (stepsAlong w t T)ᶜ) ∩ trialSet Λ w T n j (t + T)) :=
          measure_iUnion_le _
      _ ≤ ∑' t, ENNReal.ofReal ((1 - q) ^ (j + 1)) * ν (B t) := by
          refine ENNReal.tsum_le_tsum fun t => ?_
          refine (ih (t + T) _ (hdet t)).trans ?_
          rw [pow_succ, ENNReal.ofReal_mul (pow_nonneg hq1 j), mul_assoc]
          exact mul_le_mul_right (trial_fail hε hp0 hν hw (hBdet t) (hBΛ t) T hq) _
      _ = ENNReal.ofReal ((1 - q) ^ (j + 1)) * ∑' t, ν (B t) := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal ((1 - q) ^ (j + 1)) * ν A := mul_le_mul_right hsum _

open scoped Classical in
/-- The number of first arrivals at `Λ` at times in `[s₀, n + 1 - T)`, the times from which a
trial of `T` steps fits before time `n`. -/
private noncomputable def arrivalCount (Λ : Finset (Site d)) (T n s₀ : ℕ) (x : ℕ → Site d) :
    ℕ :=
  ((Finset.Ico s₀ (n + 1 - T)).filter fun t => FirstArrival Λ x t).card

/-- On `{maxRadius ≤ ρ}` no trial that fits before time `n` succeeds, because a successful trial
would end outside the ball of radius `ρ` by time `n`. -/
private lemma not_mem_stepsAlong {Λ : Finset (Site d)} {w : Site d → Site d} {T n : ℕ} {ρ : ℝ}
    (hw : ∀ x ∈ Λ, w x ∈ unitSteps d ∧ ρ < euclidNorm (x + T • w x)) {x : ℕ → Site d}
    (hx : maxRadius x n ≤ ρ) {t : ℕ} (htn : t + T ≤ n) (hfa : FirstArrival Λ x t) :
    x ∉ stepsAlong w t T := by
  intro hs
  have hlin : ∀ m ≤ T, x (t + m) = x t + m • w (x t) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp
    | succ m ih =>
      intro hm
      have hstep := hs m (by omega)
      rw [show t + (m + 1) = t + m + 1 by omega, hstep, ih (by omega), succ_nsmul, add_assoc]
  have h1 := (hw _ hfa.1).2
  have h2 := euclidNorm_le_maxRadius x htn
  rw [hlin T le_rfl] at h2
  linarith

/-- If no trial that fits before time `n` succeeds and there are more than `j * T - T` first
arrivals at times `≥ s₀` from which a trial fits, then searching from `s₀` the first `j`
trials start and fail. -/
private lemma mem_trialSet {Λ : Finset (Site d)} {w : Site d → Site d} {T n : ℕ}
    {x : ℕ → Site d} (hns : ∀ t, t + T ≤ n → FirstArrival Λ x t → x ∉ stepsAlong w t T)
    (j : ℕ) : ∀ s₀ : ℕ, j * T < arrivalCount Λ T n s₀ x + T → x ∈ trialSet Λ w T n j s₀ := by
  classical
  induction j with
  | zero =>
    intro s₀ _
    simp [trialSet]
  | succ j ih =>
    intro s₀ hj
    rw [Nat.succ_mul] at hj
    set S : Finset ℕ := (Finset.Ico s₀ (n + 1 - T)).filter fun t => FirstArrival Λ x t with hS
    have hcard : arrivalCount Λ T n s₀ x = S.card := rfl
    have hne : S.Nonempty := by
      rw [← Finset.card_pos]
      omega
    set t : ℕ := S.min' hne with ht
    have htS : t ∈ S := Finset.min'_mem S hne
    have htS' := Finset.mem_filter.mp htS
    have hlo := (Finset.mem_Ico.mp htS'.1).1
    have hhi := (Finset.mem_Ico.mp htS'.1).2
    have hmin : ∀ s, s₀ ≤ s → s < t → ¬ FirstArrival Λ x s := by
      intro s h1 h2 hfs
      have hsS : s ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h1, by omega⟩, hfs⟩
      have := Finset.min'_le S s hsS
      omega
    have hsub : S ⊆ ((Finset.Ico t (t + T)).filter fun t => FirstArrival Λ x t) ∪
        ((Finset.Ico (t + T) (n + 1 - T)).filter fun t => FirstArrival Λ x t) := by
      intro a ha
      have ha' := Finset.mem_filter.mp ha
      have hta : t ≤ a := Finset.min'_le S a ha
      have hab := (Finset.mem_Ico.mp ha'.1).2
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ico,
        Finset.mem_Ico]
      by_cases hat : a < t + T
      · exact Or.inl ⟨⟨hta, hat⟩, ha'.2⟩
      · exact Or.inr ⟨⟨by omega, hab⟩, ha'.2⟩
    have hcount : S.card ≤ T + arrivalCount Λ T n (t + T) x := by
      refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
      refine Nat.add_le_add ((Finset.card_filter_le _ _).trans ?_) le_rfl
      rw [Nat.card_Ico]
      omega
    exact ⟨t, ⟨hlo, by omega, htS'.2, hmin⟩, hns t (by omega) htS'.2,
      ih (t + T) (by omega)⟩

/-- Every site of `A_n ∩ Λ` is the position at a first arrival at `Λ` before time `n`, so
`|A_n ∩ Λ|` is at most the number of such first arrivals. -/
private lemma card_departureRange_inter_le (Λ : Finset (Site d)) (x : ℕ → Site d) (n : ℕ) :
    (departureRange x n ∩ Λ).card ≤
      (by classical exact ((Finset.range n).filter fun t => FirstArrival Λ x t).card) := by
  classical
  refine le_trans (Finset.card_le_card (t := ((Finset.range n).filter
      fun t => FirstArrival Λ x t).image x) ?_) Finset.card_image_le
  intro a ha
  obtain ⟨hA, hΛ⟩ := Finset.mem_inter.mp ha
  obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.mp hA
  have hex : ∃ t, x t = x t0 := ⟨t0, rfl⟩
  have hle : Nat.find hex ≤ t0 := Nat.find_min' hex rfl
  have hspec : x (Nat.find hex) = x t0 := Nat.find_spec hex
  refine Finset.mem_image.mpr ⟨Nat.find hex, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,
    ⟨by rw [hspec]; exact hΛ, fun i hi => ?_⟩⟩, hspec⟩
  · exact lt_of_le_of_lt hle (Finset.mem_range.mp ht0)
  · rw [hspec]
    exact fun h => Nat.find_min hex hi h

/-- Among the first arrivals before time `n`, all but at most `T - 1` occur at a time from which
a trial of `T` steps fits before time `n`. -/
private lemma card_arrivals_le {Λ : Finset (Site d)} {T n : ℕ} (hT : 1 ≤ T) (hTn : T ≤ n)
    (x : ℕ → Site d) :
    (by classical exact ((Finset.range n).filter fun t => FirstArrival Λ x t).card) ≤
      arrivalCount Λ T n 0 x + (T - 1) := by
  classical
  have hsub : (Finset.range n).filter (fun t => FirstArrival Λ x t) ⊆
      ((Finset.Ico 0 (n + 1 - T)).filter fun t => FirstArrival Λ x t) ∪
        ((Finset.Ico (n + 1 - T) n).filter fun t => FirstArrival Λ x t) := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have han := Finset.mem_range.mp ha'.1
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ico,
      Finset.mem_Ico]
    by_cases hat : a < n + 1 - T
    · exact Or.inl ⟨⟨Nat.zero_le _, hat⟩, ha'.2⟩
    · exact Or.inr ⟨⟨by omega, han⟩, ha'.2⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  refine Nat.add_le_add le_rfl ((Finset.card_filter_le _ _).trans ?_)
  rw [Nat.card_Ico]
  omega

/-- On `{maxRadius ≤ ρ}` with `|A_n ∩ Λ| ≥ k`, searching from time `0` the first `⌊k / T⌋`
trials start and fail. -/
private lemma mem_trialSet_of_card {Λ : Finset (Site d)} {w : Site d → Site d} {T n k : ℕ}
    {ρ : ℝ} (hT : 1 ≤ T) (hTn : T ≤ n)
    (hw : ∀ x ∈ Λ, w x ∈ unitSteps d ∧ ρ < euclidNorm (x + T • w x)) {x : ℕ → Site d}
    (hx : maxRadius x n ≤ ρ) (hk : k ≤ (departureRange x n ∩ Λ).card) :
    x ∈ trialSet Λ w T n (k / T) 0 := by
  refine mem_trialSet (fun t htn hfa => not_mem_stepsAlong hw hx htn hfa) (k / T) 0 ?_
  have h1 : k / T * T ≤ k := Nat.div_mul_le_self k T
  have h2 := card_departureRange_inter_le Λ x n
  have h3 := card_arrivals_le (Λ := Λ) hT hTn x
  omega

/-- The trials bound of Proposition 9.4, Step 1: if every site of a deterministic set `Λ` has a
`T`-step path `w x` ending outside the ball of radius `ρ`, then the probability that the walk
stays in that ball up to time `n` and still visits at least `k` sites of `Λ` before time `n` is
at most `(1 - p₀ ^ T) ^ (k / T)`, where `p₀ = 1/(2d) - ε/2`. -/
private theorem trials_bound (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) (Λ : Finset (Site d)) (w : Site d → Site d)
    {T n k : ℕ} {ρ : ℝ} (hT : 1 ≤ T) (hTn : T ≤ n)
    (hw : ∀ x ∈ Λ, w x ∈ unitSteps d ∧ ρ < euclidNorm (x + T • w x)) :
    μ {ω | maxRadius (fun j => X j ω) n ≤ ρ ∧
        k ≤ (departureRange (fun j => X j ω) n ∩ Λ).card} ≤
      ENNReal.ofReal ((1 - (1 / (2 * (d : ℝ)) - ε / 2) ^ T) ^ (k / T)) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hhalf : ε / 2 < 1 / (2 * (d : ℝ)) := by
    have h : 1 / (2 * (d : ℝ)) = 1 / (d : ℝ) / 2 := by field_simp
    rw [h]
    linarith
  have hp0 : 0 ≤ 1 / (2 * (d : ℝ)) - ε / 2 := by linarith
  have hhalf1 : 1 / (2 * (d : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hp1 : 1 / (2 * (d : ℝ)) - ε / 2 ≤ 1 := by linarith
  have hq : (1 / (2 * (d : ℝ)) - ε / 2) ^ T ≤ 1 := pow_le_one₀ hp0 hp1
  have hP : Measurable (fun (ω : Ω) (j : ℕ) => X j ω) := measurable_pi_lambda _ hX.measurable
  set ν : Measure (ℕ → Site d) := μ.map (fun (ω : Ω) (j : ℕ) => X j ω) with hν
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hP.aemeasurable
  have hfac : StepFactors ε ν := by
    intro n y
    have hc : ∀ s, ν (cyl s y) = μ {ω | ∀ j ≤ s, X j ω = y j} := fun s => by
      rw [hν, Measure.map_apply hP (detUpTo_cyl s y).measurableSet]
      rfl
    rw [hc, hc, hX.step n y]
  have hsub : {ω | maxRadius (fun j => X j ω) n ≤ ρ ∧
        k ≤ (departureRange (fun j => X j ω) n ∩ Λ).card} ⊆
      (fun (ω : Ω) (j : ℕ) => X j ω) ⁻¹' trialSet Λ w T n (k / T) 0 :=
    fun ω hω => mem_trialSet_of_card hT hTn hw hω.1 hω.2
  calc μ {ω | maxRadius (fun j => X j ω) n ≤ ρ ∧
        k ≤ (departureRange (fun j => X j ω) n ∩ Λ).card}
      ≤ μ ((fun (ω : Ω) (j : ℕ) => X j ω) ⁻¹' trialSet Λ w T n (k / T) 0) := measure_mono hsub
    _ ≤ ν (trialSet Λ w T n (k / T) 0) := Measure.le_map_apply hP.aemeasurable _
    _ = ν (Set.univ ∩ trialSet Λ w T n (k / T) 0) := by rw [Set.univ_inter]
    _ ≤ ENNReal.ofReal ((1 - (1 / (2 * (d : ℝ)) - ε / 2) ^ T) ^ (k / T)) * ν Set.univ :=
        trialSet_bound hε.le hp0 hfac (fun x hx => (hw x hx).1) T n hq (k / T) 0 Set.univ
          (fun _ _ _ => Iff.rfl)
    _ = ENNReal.ofReal ((1 - (1 / (2 * (d : ℝ)) - ε / 2) ^ T) ^ (k / T)) := by
        rw [measure_univ, mul_one]

end Trials

section StraightPaths

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- Moving `T` steps along the unit step `s • e_i`, `s = ±1`, changes the squared norm by
`2 T s x_i + T²`. -/
private theorem euclidNorm_sq_add_nsmul (x : Site d) (i : Fin d) {s : ℤ} (hs : s = 1 ∨ s = -1)
    (T : ℕ) :
    euclidNorm (x + T • (s • unit i)) ^ 2 =
      euclidNorm x ^ 2 + (2 * T * (s : ℝ) * ((x i : ℤ) : ℝ) + (T : ℝ) ^ 2) := by
  have hs2 : ((s : ℤ) : ℝ) ^ 2 = 1 := by
    rcases hs with rfl | rfl <;> norm_num
  rw [CERW.Support.Occupation.euclidNorm_sq_eq_sum, CERW.Support.Occupation.euclidNorm_sq_eq_sum]
  have hpoint : ∀ j : Fin d, (((x + T • (s • unit i)) j : ℤ) : ℝ) ^ 2 =
      ((x j : ℤ) : ℝ) ^ 2 +
        (if j = i then 2 * T * (s : ℝ) * ((x i : ℤ) : ℝ) + (T : ℝ) ^ 2 else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj
      have h1 : (((x + T • (s • unit j)) j : ℤ) : ℝ) = ((x j : ℤ) : ℝ) + T * s := by
        simp [unit]
      rw [h1, if_pos rfl]
      nlinarith [hs2]
    · have h1 : (((x + T • (s • unit i)) j : ℤ) : ℝ) = ((x j : ℤ) : ℝ) := by
        simp [unit, hj]
      rw [h1, if_neg hj, add_zero]
  rw [Finset.sum_congr rfl fun j _ => hpoint j, Finset.sum_add_distrib]
  simp

/-- From each site a straight path of `T` steps moves the Euclidean norm out by at least
`T / √d`: the step is along the coordinate of largest modulus, in the direction of its sign. -/
private theorem exists_straight_step (hd : 1 ≤ d) (x : Site d) (T : ℕ) :
    ∃ e ∈ unitSteps d, euclidNorm x + (T : ℝ) / Real.sqrt d ≤ euclidNorm (x + T • e) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨i, hi⟩ := Finite.exists_max (fun j : Fin d => |((x j : ℤ) : ℝ)|)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
  have hsqsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hdpos.le
  have hxi : euclidNorm x ≤ Real.sqrt d * |((x i : ℤ) : ℝ)| := by
    rw [euclidNorm]
    calc Real.sqrt (∑ j : Fin d, ((x j : ℤ) : ℝ) ^ 2)
        ≤ Real.sqrt (∑ _j : Fin d, |((x i : ℤ) : ℝ)| ^ 2) := by
          refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => ?_)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hi j) 2
      _ = Real.sqrt d * |((x i : ℤ) : ℝ)| := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul hdpos.le, Real.sqrt_sq (abs_nonneg _)]
  have hmain : ∀ s : ℤ, (s = 1 ∨ s = -1) → (s : ℝ) * ((x i : ℤ) : ℝ) = |((x i : ℤ) : ℝ)| →
      euclidNorm x + (T : ℝ) / Real.sqrt d ≤ euclidNorm (x + T • (s • unit i)) := by
    intro s hs hsx
    have hnorm := euclidNorm_sq_add_nsmul x i hs T
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have h1 : euclidNorm x / Real.sqrt d ≤ |((x i : ℤ) : ℝ)| := by
      rw [div_le_iff₀ hsq]
      linarith
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have h2 : ((T : ℝ) / Real.sqrt d) ^ 2 ≤ (T : ℝ) ^ 2 := by
      rw [div_pow, hsqsq, div_le_iff₀ hdpos]
      nlinarith [sq_nonneg (T : ℝ)]
    have h3 : (euclidNorm x + (T : ℝ) / Real.sqrt d) ^ 2 ≤
        euclidNorm (x + T • (s • unit i)) ^ 2 := by
      rw [hnorm]
      have h4 : 2 * (T : ℝ) * (euclidNorm x / Real.sqrt d) ≤
          2 * T * ((s : ℝ) * ((x i : ℤ) : ℝ)) := by
        rw [hsx]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have h5 : (euclidNorm x + (T : ℝ) / Real.sqrt d) ^ 2 =
          euclidNorm x ^ 2 + 2 * (T : ℝ) * (euclidNorm x / Real.sqrt d) +
            ((T : ℝ) / Real.sqrt d) ^ 2 := by
        ring
      rw [h5]
      nlinarith [h2, h4]
    exact le_of_sq_le_sq (by simpa using h3) (LatticeProb.euclidNorm_nonneg _)
  by_cases hxs : 0 ≤ ((x i : ℤ) : ℝ)
  · refine ⟨(1 : ℤ) • unit i, mem_unitSteps.mpr ⟨i, Or.inl (one_smul _ _)⟩,
      hmain 1 (Or.inl rfl) ?_⟩
    rw [abs_of_nonneg hxs]
    simp
  · refine ⟨(-1 : ℤ) • unit i, mem_unitSteps.mpr ⟨i, Or.inr (by simp)⟩,
      hmain (-1) (Or.inr rfl) ?_⟩
    rw [abs_of_neg (not_le.mp hxs)]
    simp

/-- Straight paths leave a ball: if the norms of the sites of `Λ` exceed `a` and
`ρ - a ≤ T / √d`, there is a choice of a unit step `w x` for each `x ∈ Λ` such that `T` steps in
the direction `w x` end at distance greater than `ρ` from the origin. -/
private theorem exists_leaving_steps (hd : 1 ≤ d) (Λ : Finset (Site d)) {a ρ : ℝ} {T : ℕ}
    (hΛ : ∀ x ∈ Λ, a < euclidNorm x) (hT : ρ - a ≤ (T : ℝ) / Real.sqrt d) :
    ∃ w : Site d → Site d, ∀ x ∈ Λ, w x ∈ unitSteps d ∧ ρ < euclidNorm (x + T • w x) := by
  have hex : ∀ x : Site d, ∃ e ∈ unitSteps d, x ∈ Λ → ρ < euclidNorm (x + T • e) := by
    intro x
    obtain ⟨e, he, hnorm⟩ := exists_straight_step hd x T
    refine ⟨e, he, fun hx => ?_⟩
    have := hΛ x hx
    linarith
  choose w hw using hex
  exact ⟨w, fun x hx => ⟨(hw x).1, (hw x).2 hx⟩⟩

end StraightPaths

section ShellCount

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- Bernoulli-type inequality: `(n+1) x^n (y - x) ≤ y^(n+1) - x^(n+1)` for `0 ≤ x ≤ y`. -/
private theorem succ_mul_pow_mul_sub_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    ((n : ℝ) + 1) * x ^ n * (y - x) ≤ y ^ (n + 1) - x ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hy : 0 ≤ y := hx.trans hxy
    have hP : 0 ≤ ((n : ℝ) + 1) * x ^ n * (y - x) :=
      mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hx n)) (sub_nonneg.mpr hxy)
    have h1 : x * (((n : ℝ) + 1) * x ^ n * (y - x)) ≤
        y * (((n : ℝ) + 1) * x ^ n * (y - x)) :=
      mul_le_mul_of_nonneg_right hxy hP
    have h2 : y * (((n : ℝ) + 1) * x ^ n * (y - x)) ≤ y * (y ^ (n + 1) - x ^ (n + 1)) :=
      mul_le_mul_of_nonneg_left ih hy
    have h3 : y ^ (n + 1 + 1) - x ^ (n + 1 + 1) =
        y * (y ^ (n + 1) - x ^ (n + 1)) + x ^ (n + 1) * (y - x) := by ring
    have h4 : (((n + 1 : ℕ) : ℝ) + 1) * x ^ (n + 1) * (y - x) =
        x * (((n : ℝ) + 1) * x ^ n * (y - x)) + x ^ (n + 1) * (y - x) := by
      push_cast
      ring
    rw [h3, h4]
    linarith

/-- For `d ≥ 1` and `0 ≤ x ≤ y`, `d x^(d-1) (y - x) ≤ y^d - x^d`. -/
private theorem nat_mul_pow_pred_mul_sub_le (hd : 1 ≤ d) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) :
    (d : ℝ) * x ^ (d - 1) * (y - x) ≤ y ^ d - x ^ d := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have h := succ_mul_pow_mul_sub_le hx hxy m
  rw [Nat.add_sub_cancel]
  push_cast
  exact h

/-- The volume of a closed ball of radius `ρ ≥ 0` in `ℝ^d` is `ω_d ρ^d`. -/
private theorem volume_closedBall_eq {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ)
      = ENNReal.ofReal (unitBallVolume d * ρ ^ d) := by
  rw [Measure.addHaar_closedBall volume _ hρ, finrank_euclideanSpace_fin]
  have hball : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
      = ENNReal.ofReal (unitBallVolume d) :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  rw [hball, ← ENNReal.ofReal_mul (pow_nonneg hρ d), mul_comm]

/-- The number of lattice sites `x` with `a < |x| ≤ b` is at least the volume `ω_d (y^d - x^d)`
of the annulus `a + √d/2 < |v| ≤ b - √d/2`, hence at least `ω_d d (a + √d/2)^{d-1} (b - a - √d)`:
each point of the annulus lies in the unit cell of such a site. -/
private theorem card_annulus_ge (hd : 1 ≤ d) {a b : ℝ} (ha : 0 ≤ a) (hab : a + Real.sqrt d ≤ b) :
    unitBallVolume d * d * (a + Real.sqrt d / 2) ^ (d - 1) * (b - a - Real.sqrt d) ≤
      (((ballFinset d b).filter fun x => a < euclidNorm x).card : ℝ) := by
  classical
  set S : Finset (Site d) := (ballFinset d b).filter fun x => a < euclidNorm x with hS
  set x : ℝ := a + Real.sqrt d / 2 with hxdef
  set y : ℝ := b - Real.sqrt d / 2 with hydef
  have hsqrt : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hx0 : 0 ≤ x := by rw [hxdef]; linarith
  have hxy : x ≤ y := by rw [hxdef, hydef]; linarith
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) y ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) x ∪ ⋃ z ∈ S, cell z := by
    intro v hv
    by_cases hvx : ‖v‖ ≤ x
    · exact Or.inl (mem_closedBall_zero_iff.mpr hvx)
    · refine Or.inr (Set.mem_iUnion₂.mpr ⟨cellCenter v, ?_, mem_cell_cellCenter v⟩)
      have hvy : ‖v‖ ≤ y := mem_closedBall_zero_iff.mp hv
      have hdist : |‖v‖ - euclidNorm (cellCenter v)| ≤ Real.sqrt d / 2 := by
        have h := (abs_norm_sub_norm_le v (toSpace (cellCenter v))).trans
          (CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter v))
        rwa [norm_toSpace] at h
      rw [abs_le] at hdist
      rw [hS, Finset.mem_filter, LatticeProb.mem_ballFinset_iff]
      rw [hxdef] at hvx
      rw [hydef] at hvy
      constructor <;> linarith [hdist.1, hdist.2, not_le.mp hvx]
  have hcard : volume (⋃ z ∈ S, cell z) = ENNReal.ofReal (S.card : ℝ) := by
    rw [CERW.Support.Occupation.volume_biUnion_cell S, ENNReal.ofReal_natCast]
  have hmain : ENNReal.ofReal (unitBallVolume d * y ^ d) ≤
      ENNReal.ofReal (unitBallVolume d * x ^ d + (S.card : ℝ)) := by
    calc ENNReal.ofReal (unitBallVolume d * y ^ d)
        = volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) y) :=
          (volume_closedBall_eq (hx0.trans hxy)).symm
      _ ≤ volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) x ∪ ⋃ z ∈ S, cell z) :=
          measure_mono hsub
      _ ≤ volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) x) +
            volume (⋃ z ∈ S, cell z) := measure_union_le _ _
      _ = ENNReal.ofReal (unitBallVolume d * x ^ d) + ENNReal.ofReal (S.card : ℝ) := by
          rw [volume_closedBall_eq hx0, hcard]
      _ = ENNReal.ofReal (unitBallVolume d * x ^ d + (S.card : ℝ)) :=
          (ENNReal.ofReal_add (mul_nonneg hω.le (pow_nonneg hx0 d)) (Nat.cast_nonneg _)).symm
  have hreal : unitBallVolume d * y ^ d ≤ unitBallVolume d * x ^ d + (S.card : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff
      (add_nonneg (mul_nonneg hω.le (pow_nonneg hx0 d)) (Nat.cast_nonneg _))).mp hmain
  have hbern := nat_mul_pow_pred_mul_sub_le hd hx0 hxy
  have hyx : y - x = b - a - Real.sqrt d := by rw [hxdef, hydef]; ring
  rw [hyx] at hbern
  calc unitBallVolume d * d * x ^ (d - 1) * (b - a - Real.sqrt d)
      = unitBallVolume d * ((d : ℝ) * x ^ (d - 1) * (b - a - Real.sqrt d)) := by ring
    _ ≤ unitBallVolume d * (y ^ d - x ^ d) := mul_le_mul_of_nonneg_left hbern hω.le
    _ = unitBallVolume d * y ^ d - unitBallVolume d * x ^ d := by ring
    _ ≤ (S.card : ℝ) := by linarith

/-- The shell `r - 2h < |x| ≤ r - h - 1` of the lattice contains at least `c r^{d-1} h` sites
when `h` is large and `8 h ≤ r` (comparison with unit cells). -/
private theorem exists_card_shell (hd : 1 ≤ d) :
    ∃ c h₁ : ℝ, 0 < c ∧ 0 < h₁ ∧ ∀ r h : ℝ, h₁ ≤ h → 8 * h ≤ r →
      c * r ^ (d - 1) * h ≤
        (((ballFinset d (r - h - 1)).filter fun x => r - 2 * h < euclidNorm x).card : ℝ) := by
  have hsqrt : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨unitBallVolume d * d * (3 / 4) ^ (d - 1) / 2, 2 + 2 * Real.sqrt d,
    by positivity, by positivity, fun r h hh hr => ?_⟩
  have hh2 : 2 ≤ h := by linarith
  have ha : 0 ≤ r - 2 * h := by linarith
  have hab : (r - 2 * h) + Real.sqrt d ≤ r - h - 1 := by linarith
  have hcard := card_annulus_ge hd ha hab
  have hbase : 3 / 4 * r ≤ (r - 2 * h) + Real.sqrt d / 2 := by linarith
  have hpow : (3 / 4 * r) ^ (d - 1) ≤ ((r - 2 * h) + Real.sqrt d / 2) ^ (d - 1) :=
    pow_le_pow_left₀ (by linarith) hbase _
  have hlen : h / 2 ≤ r - h - 1 - (r - 2 * h) - Real.sqrt d := by linarith
  have hfac : 0 ≤ unitBallVolume d * d := mul_nonneg hω.le hd0.le
  calc unitBallVolume d * d * (3 / 4) ^ (d - 1) / 2 * r ^ (d - 1) * h
      = unitBallVolume d * d * (3 / 4 * r) ^ (d - 1) * (h / 2) := by
        rw [mul_pow]
        ring
    _ ≤ unitBallVolume d * d * ((r - 2 * h) + Real.sqrt d / 2) ^ (d - 1) *
          (r - h - 1 - (r - 2 * h) - Real.sqrt d) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hfac) hlen (by linarith)
          (mul_nonneg hfac (pow_nonneg (by linarith) _))
    _ ≤ _ := hcard

end ShellCount

section QuadraticSum

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- The volume of the Euclidean ball of radius `ρ ≥ 0` is `ω_d ρ^d`. -/
private theorem volume_ball_toReal (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ)).toReal
      = unitBallVolume d * ρ ^ d := by
  rcases hρ.eq_or_lt with rfl | hρpos
  · simp [zero_pow (by omega : d ≠ 0)]
  · rw [Measure.addHaar_ball_of_pos volume _ hρpos, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hρ _), mul_comm]
    rfl

/-- The norm is integrable on every ball. -/
private theorem integrableOn_norm_ball (ρ : ℝ) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (Metric.ball 0 ρ) :=
  (continuous_norm.continuousOn.integrableOn_compact (isCompact_closedBall 0 ρ)).mono_set
    Metric.ball_subset_closedBall

/-- The cell of a site of norm at most `ρ` lies in the open ball of radius `ρ + √d`. -/
private theorem cell_subset_ball (hd : 1 ≤ d) {y : Site d} {ρ : ℝ} (hy : euclidNorm y ≤ ρ) :
    CERW.cell y ⊆ Metric.ball 0 (ρ + Real.sqrt d) := by
  intro v hv
  rw [mem_ball_zero_iff]
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hpos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  calc ‖v‖ ≤ ‖toSpace y‖ + ‖v - toSpace y‖ := norm_le_norm_add_norm_sub' v (toSpace y)
    _ = euclidNorm y + ‖v - toSpace y‖ := by rw [norm_toSpace y]
    _ < ρ + Real.sqrt d := by
        linarith [CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hv]

/-- On the cell of `y`, the norm has integral at least `|y| - √d/2`, as the cell has volume one
and the norm exceeds `|y| - √d/2` there. -/
private theorem euclidNorm_sub_le_setIntegral_cell (y : Site d)
    (hint : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (CERW.cell y)) :
    euclidNorm y - Real.sqrt d / 2 ≤ ∫ v in CERW.cell y, ‖v‖ := by
  have hfin : volume (CERW.cell y) ≠ ⊤ := by
    rw [CERW.Support.Occupation.volume_cell]
    exact ENNReal.one_ne_top
  have hconst : IntegrableOn
      (fun _ : EuclideanSpace ℝ (Fin d) => euclidNorm y - Real.sqrt d / 2) (CERW.cell y) :=
    integrableOn_const hfin
  have hmono := setIntegral_mono_on hconst hint (CERW.Support.Occupation.measurableSet_cell y)
    (fun v hv => by
      have h1 : ‖toSpace y‖ ≤ ‖v‖ + ‖toSpace y - v‖ := norm_le_norm_add_norm_sub' _ _
      have h2 : ‖toSpace y - v‖ ≤ Real.sqrt d / 2 := by
        rw [norm_sub_rev]
        exact CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hv
      rw [norm_toSpace y] at h1
      linarith)
  rw [setIntegral_const, smul_eq_mul, Measure.real_def, CERW.Support.Occupation.volume_cell]
    at hmono
  simpa using hmono

/-- A finite set of sites of norm at most `ρ` has norm sum at most
`I(ρ + √d) + (√d/2) ω_d (ρ + √d)^d`, where `I(s) = d ω_d s^{d+1}/(d+1)`. -/
private theorem sum_euclidNorm_le (hd : 1 ≤ d) (S : Finset (Site d)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hS : ∀ y ∈ S, euclidNorm y ≤ ρ) :
    ∑ y ∈ S, euclidNorm y ≤
      d * unitBallVolume d * (ρ + Real.sqrt d) ^ (d + 1) / (d + 1)
        + Real.sqrt d / 2 * (unitBallVolume d * (ρ + Real.sqrt d) ^ d) := by
  have hR0 : 0 ≤ ρ + Real.sqrt d := add_nonneg hρ (Real.sqrt_nonneg _)
  have hsub : ∀ y ∈ S, CERW.cell y ⊆ Metric.ball 0 (ρ + Real.sqrt d) :=
    fun y hy => cell_subset_ball hd (hS y hy)
  have hUsub : (⋃ y ∈ S, CERW.cell y) ⊆ Metric.ball 0 (ρ + Real.sqrt d) :=
    Set.iUnion₂_subset hsub
  have hint : ∀ y ∈ S, IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (CERW.cell y) :=
    fun y hy => (integrableOn_norm_ball _).mono_set (hsub y hy)
  have hsum : ∑ y ∈ S, (euclidNorm y - Real.sqrt d / 2) ≤ ∫ v in ⋃ y ∈ S, CERW.cell y, ‖v‖ := by
    rw [integral_biUnion_finset S (fun y _ => CERW.Support.Occupation.measurableSet_cell y)
      (fun x _ y _ hxy => CERW.cell_disjoint hxy) hint]
    exact Finset.sum_le_sum fun y hy => euclidNorm_sub_le_setIntegral_cell y (hint y hy)
  have hU : ∫ v in ⋃ y ∈ S, CERW.cell y, ‖v‖
      ≤ ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (ρ + Real.sqrt d), ‖v‖ :=
    setIntegral_mono_set (integrableOn_norm_ball _)
      (Filter.Eventually.of_forall fun v => norm_nonneg v)
      (Filter.Eventually.of_forall hUsub)
  have hcard : (S.card : ℝ) ≤ unitBallVolume d * (ρ + Real.sqrt d) ^ d := by
    have hfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (ρ + Real.sqrt d)) ≠ ⊤ :=
      measure_ball_lt_top.ne
    have h := ENNReal.toReal_mono hfin (measure_mono hUsub)
    rwa [CERW.Support.Occupation.volume_biUnion_cell, ENNReal.toReal_natCast,
      volume_ball_toReal hd hR0] at h
  rw [CERW.Generic.Kernel.integral_ball_norm hd hR0] at hU
  have hsplit : ∑ y ∈ S, (euclidNorm y - Real.sqrt d / 2)
      = ∑ y ∈ S, euclidNorm y - S.card * (Real.sqrt d / 2) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hcard' : (S.card : ℝ) * (Real.sqrt d / 2)
      ≤ (unitBallVolume d * (ρ + Real.sqrt d) ^ d) * (Real.sqrt d / 2) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  linarith

/-- For `0 < s ≤ r`, `(n + 1) s^n (r - s) ≤ r^{n+1} - s^{n+1}`. -/
private theorem pow_succ_sub_pow_succ_ge (n : ℕ) {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    ((n : ℝ) + 1) * s ^ n * (r - s) ≤ r ^ (n + 1) - s ^ (n + 1) := by
  have hs' : 0 < s ^ (n + 1) := pow_pos hs _
  have hrs : -2 ≤ r / s - 1 := by
    have : 0 ≤ r / s := div_nonneg (hs.le.trans hsr) hs.le
    linarith
  have h := one_add_mul_le_pow hrs (n + 1)
  rw [add_sub_cancel, div_pow, le_div_iff₀ hs'] at h
  have hexp : (1 + ((n + 1 : ℕ) : ℝ) * (r / s - 1)) * s ^ (n + 1)
      = s ^ (n + 1) + ((n : ℝ) + 1) * s ^ n * (r - s) := by
    have hs0 : s ≠ 0 := hs.ne'
    push_cast
    field_simp
    ring
  linarith

/-- Deterministic core of Step 3 of `prop:log-lower`: if `R_out(n) ≤ r + h` and fewer than
`c₁ r^{d-1} h` sites of the shell `r - 2h < |x| ≤ r + h` have been visited, then
`𝒬_n ≤ -c₂ r^d h`, where `n = 2 ε I(r)` and `I(s) = ∫_{B(0,s)} |v| dv`. -/
private theorem exists_quadraticMart_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ c₁ c₂ h₁ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < h₁ ∧
      ∀ (x : ℕ → Site d) (n : ℕ) (r h : ℝ), 1 ≤ r → h₁ ≤ h → 8 * h ≤ r →
        (n : ℝ) = 2 * d * ε * unitBallVolume d * r ^ (d + 1) / (d + 1) →
        maxRadius x n ≤ r + h →
        ((departureRange x n ∩
          ((ballFinset d (r + h)).filter fun y => r - 2 * h < euclidNorm y)).card : ℝ)
          < c₁ * r ^ (d - 1) * h →
        quadraticMart ε x n ≤ -(c₂ * r ^ d * h) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by linarith)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = unitBallVolume d * d * (3 / 4) ^ d := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; positivity
  have hεK : 0 < ε * K := mul_pos hε hKpos
  refine ⟨K / 8, ε * K, max (2 * Real.sqrt d) (2 / (ε * K)), by positivity, hεK,
    lt_max_of_lt_left (by positivity), ?_⟩
  intro x n r h hr hh h8 hn hmax hm
  have h1 : 2 * Real.sqrt d ≤ h := (le_max_left _ _).trans hh
  have h2 : 2 / (ε * K) ≤ h := (le_max_right _ _).trans hh
  have hhpos : 0 < h := by linarith
  have hεKh : 2 ≤ h * (ε * K) := (div_le_iff₀ hεK).mp h2
  have hr0 : 0 < r := by linarith
  -- the radius `s = r - 2h + √d` lies between `3r/4` and `r`
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = r - 2 * h + Real.sqrt d := ⟨_, rfl⟩
  have hs3 : 3 / 4 * r ≤ s := by rw [hs]; linarith
  have hsr : s ≤ r := by rw [hs]; linarith
  have hspos : 0 < s := by linarith
  have hρ0 : 0 ≤ r - 2 * h := by linarith
  -- the departure range splits at radius `r - 2h`
  have hA1 := sum_euclidNorm_le hd1
    ((departureRange x n).filter fun y => euclidNorm y ≤ r - 2 * h) hρ0
    (fun y hy => (Finset.mem_filter.mp hy).2)
  rw [← hs] at hA1
  have hA2mem : ∀ y ∈ (departureRange x n).filter fun y => ¬ euclidNorm y ≤ r - 2 * h,
      euclidNorm y ≤ r + h := by
    intro y hy
    have hyA := (Finset.mem_filter.mp hy).1
    have := LatticeProb.mem_ballFinset_iff.mp
      (CERW.Support.Occupation.departureRange_subset_ballFinset x n hyA)
    linarith
  have hA2 : ∑ y ∈ (departureRange x n).filter (fun y => ¬ euclidNorm y ≤ r - 2 * h),
        euclidNorm y
      ≤ ((departureRange x n ∩
          ((ballFinset d (r + h)).filter fun y => r - 2 * h < euclidNorm y)).card : ℝ)
          * (r + h) := by
    have hcard : ((departureRange x n).filter fun y => ¬ euclidNorm y ≤ r - 2 * h).card
        ≤ (departureRange x n ∩
          ((ballFinset d (r + h)).filter fun y => r - 2 * h < euclidNorm y)).card := by
      refine Finset.card_le_card fun y hy => ?_
      have hy' := hA2mem y hy
      have hyA := (Finset.mem_filter.mp hy).1
      have hyn := (Finset.mem_filter.mp hy).2
      exact Finset.mem_inter.mpr ⟨hyA, Finset.mem_filter.mpr
        ⟨LatticeProb.mem_ballFinset_iff.mpr hy', not_le.mp hyn⟩⟩
    have hsum := Finset.sum_le_card_nsmul _ (fun y => euclidNorm y) (r + h) hA2mem
    rw [nsmul_eq_mul] at hsum
    have hcardR : (((departureRange x n).filter fun y => ¬ euclidNorm y ≤ r - 2 * h).card : ℝ)
        ≤ ((departureRange x n ∩
          ((ballFinset d (r + h)).filter fun y => r - 2 * h < euclidNorm y)).card : ℝ) :=
      by exact_mod_cast hcard
    exact hsum.trans (mul_le_mul_of_nonneg_right hcardR (by linarith))
  have hsplit := Finset.sum_filter_add_sum_filter_not (departureRange x n)
    (fun y => euclidNorm y ≤ r - 2 * h) (fun y => euclidNorm y)
  -- abbreviations
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = ((departureRange x n ∩
      ((ballFinset d (r + h)).filter fun y => r - 2 * h < euclidNorm y)).card : ℝ) :=
    ⟨_, rfl⟩
  rw [← hmdef] at hA2 hm
  have hm0 : 0 ≤ m := by rw [hmdef]; exact Nat.cast_nonneg _
  obtain ⟨J, hJ⟩ : ∃ J : ℝ, J = d * unitBallVolume d / (d + 1) := ⟨_, rfl⟩
  have hJ0 : 0 ≤ J := by rw [hJ]; positivity
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = unitBallVolume d * s ^ d := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hI : ∀ t : ℝ, d * unitBallVolume d * t ^ (d + 1) / (d + 1) = J * t ^ (d + 1) := by
    intro t
    rw [hJ]
    ring
  rw [hI] at hA1
  rw [← hP] at hA1
  have hn' : (n : ℝ) = 2 * ε * (J * r ^ (d + 1)) := by
    rw [hn, hJ]
    ring
  -- the Bernoulli-type lower bound on `I(r) - I(s)`
  have hbern := pow_succ_sub_pow_succ_ge d hspos hsr
  have hbern' : d * P * (r - s) ≤ J * (r ^ (d + 1) - s ^ (d + 1)) := by
    have h3 := mul_le_mul_of_nonneg_left hbern hJ0
    have h4 : J * (((d : ℝ) + 1) * s ^ d * (r - s)) = d * P * (r - s) := by
      rw [hJ, hP]
      field_simp
    linarith
  -- `d (r - s) - √d/2 ≥ d h`
  have hq : (d : ℝ) * h ≤ d * (r - s) - Real.sqrt d / 2 := by
    have e1 : (0 : ℝ) ≤ d * (h - 2 * Real.sqrt d) :=
      mul_nonneg (by linarith) (by linarith)
    have e2 : (0 : ℝ) ≤ (d - 1) * Real.sqrt d :=
      mul_nonneg (by linarith) hsqrt.le
    have e3 : r - s = 2 * h - Real.sqrt d := by rw [hs]; ring
    rw [e3]
    linarith
  have hPq : P * (d * h) ≤ P * (d * (r - s) - Real.sqrt d / 2) :=
    mul_le_mul_of_nonneg_left hq hP0
  -- `P ≥ ω (3/4)^d r^d`
  have hPlow : unitBallVolume d * ((3 / 4) ^ d * r ^ d) ≤ P := by
    rw [hP, ← mul_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hs3 d) hω.le
  have hKlow : K * r ^ d * h ≤ P * (d * h) := by
    have := mul_le_mul_of_nonneg_left hPlow (by positivity : (0 : ℝ) ≤ d * h)
    calc K * r ^ d * h = d * h * (unitBallVolume d * ((3 / 4) ^ d * r ^ d)) := by
          rw [hK]; ring
      _ ≤ d * h * P := this
      _ = P * (d * h) := by ring
  -- the combined estimate on `Σ_{A_n} |y| - I(r)`
  have hab : ∑ y ∈ departureRange x n, euclidNorm y - J * r ^ (d + 1)
      ≤ -(K * r ^ d * h) + m * (r + h) := by
    rw [← hsplit]
    linarith
  -- the terms of the final estimate
  have hrh : r + h ≤ 9 / 8 * r := by linarith
  have hrd : r * r ^ (d - 1) = r ^ d := by
    rw [← pow_succ']
    congr 1
    omega
  have hmr : m * (r + h) ≤ 9 / 64 * K * r ^ d * h := by
    have h5 : m * (r + h) ≤ (K / 8 * r ^ (d - 1) * h) * (9 / 8 * r) :=
      mul_le_mul hm.le hrh (by linarith) (by positivity)
    calc m * (r + h) ≤ (K / 8 * r ^ (d - 1) * h) * (9 / 8 * r) := h5
      _ = 9 / 64 * K * (r * r ^ (d - 1)) * h := by ring
      _ = 9 / 64 * K * r ^ d * h := by rw [hrd]
  have hxn : euclidNorm (x n) ^ 2 ≤ 81 / 64 * r ^ d := by
    have h6 : euclidNorm (x n) ≤ r + h :=
      (CERW.euclidNorm_le_maxRadius x (le_refl n)).trans hmax
    have h7 : euclidNorm (x n) ^ 2 ≤ (9 / 8 * r) ^ 2 :=
      pow_le_pow_left₀ (by unfold euclidNorm; exact Real.sqrt_nonneg _)
        (h6.trans hrh) 2
    have h8' : r ^ 2 ≤ r ^ d := pow_le_pow_right₀ hr hd
    calc euclidNorm (x n) ^ 2 ≤ (9 / 8 * r) ^ 2 := h7
      _ = 81 / 64 * r ^ 2 := by ring
      _ ≤ 81 / 64 * r ^ d := by linarith
  have hrdh : r ^ d ≤ r ^ d * (h * (ε * K) / 2) := by
    have hrd0 : 0 ≤ r ^ d := by positivity
    exact le_mul_of_one_le_right hrd0 (by linarith)
  have hpos : 0 ≤ ε * K * r ^ d * h := by positivity
  unfold quadraticMart
  rw [hn']
  have hab2 := mul_le_mul_of_nonneg_left hab (by linarith : (0 : ℝ) ≤ 2 * ε)
  have hmr2 := mul_le_mul_of_nonneg_left hmr (by linarith : (0 : ℝ) ≤ 2 * ε)
  linarith

end QuadraticSum

section QuadraticTail

open CERW.Support.Statements CERW CERW.Support.Law Finset

variable {d : ℕ}

/-- The squared norm changes by at most `2 |x| + 1` under a unit step. -/
private theorem abs_sq_euclidNorm_add_unit_le (x e : Site d) (he : e ∈ unitSteps d) :
    |euclidNorm (x + e) ^ 2 - euclidNorm x ^ 2| ≤ 2 * euclidNorm x + 1 := by
  have hto : toSpace (x + e) = toSpace x + toSpace e := by
    apply PiLp.ext
    intro i
    simp [toSpace_apply, Pi.add_apply, Int.cast_add]
  have he1 : euclidNorm e = 1 := CERW.Support.Law.euclidNorm_of_mem_unitSteps he
  have hnorm : ‖toSpace e‖ = 1 := by rw [norm_toSpace, he1]
  have hdecomp : euclidNorm (x + e) ^ 2 - euclidNorm x ^ 2 =
      2 * inner ℝ (toSpace x) (toSpace e) + 1 := by
    rw [← norm_toSpace (x + e), ← norm_toSpace x, hto, norm_add_sq_real, hnorm]
    ring
  rw [hdecomp]
  have hinner : |inner ℝ (toSpace x) (toSpace e)| ≤ euclidNorm x := by
    calc |inner ℝ (toSpace x) (toSpace e)| ≤ ‖toSpace x‖ * ‖toSpace e‖ :=
          abs_real_inner_le_norm _ _
      _ = euclidNorm x := by rw [norm_toSpace, hnorm, mul_one]
  rw [abs_le] at hinner ⊢
  constructor <;> linarith [hinner.1, hinner.2]

/-- The indicator that the walk at time `j` is still inside the ball of radius `R`. -/
private noncomputable def stayIndicator (R : ℝ) {Ω : Type*} (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : ℝ :=
  if euclidNorm (X j ω) ≤ R then 1 else 0

/-- The Dynkin martingale of `|x|²` with its increments kept only while the walk is inside the
ball of radius `R`. -/
private noncomputable def stoppedQuadratic (ε R : ℝ) {Ω : Type*}
    (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range t, stayIndicator R X j ω *
    (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
      dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω)

/-- The ball indicator is nonnegative. -/
private theorem stayIndicator_nonneg (R : ℝ) {Ω : Type*} (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : 0 ≤ stayIndicator R X j ω := by
  rw [stayIndicator]
  split_ifs <;> norm_num

/-- The ball indicator is at most one. -/
private theorem stayIndicator_le_one (R : ℝ) {Ω : Type*} (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : stayIndicator R X j ω ≤ 1 := by
  rw [stayIndicator]
  split_ifs <;> norm_num

/-- The ball indicator is a function of the past path. -/
private theorem stronglyMeasurable_stayIndicator {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ n, Measurable (X n)) (R : ℝ) (j : ℕ) :
    StronglyMeasurable[pathFiltration hX j] (stayIndicator R X j) := by
  have h := stronglyMeasurable_comp_pastPath hX j
    (fun q : ((i : Finset.Iic j) → Site d) =>
      if euclidNorm (q ⟨j, Finset.mem_Iic.mpr le_rfl⟩) ≤ R then (1 : ℝ) else 0)
  exact h

/-- One step of the truncated quadratic martingale keeps the indicator times the Dynkin
increment. -/
private theorem stoppedQuadratic_succ_sub (ε R : ℝ) {Ω : Type*} (X : ℕ → Ω → Site d)
    (t : ℕ) (ω : Ω) :
    stoppedQuadratic ε R X (t + 1) ω - stoppedQuadratic ε R X t ω =
      stayIndicator R X t ω *
        (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω -
          dynkin ε (fun z : Site d => euclidNorm z ^ 2) X t ω) := by
  simp only [stoppedQuadratic, Finset.sum_range_succ]
  ring

/-- The truncated quadratic martingale vanishes at time zero. -/
private theorem stoppedQuadratic_zero (ε R : ℝ) {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) :
    stoppedQuadratic ε R X 0 ω = 0 := by
  simp only [stoppedQuadratic, Finset.range_zero, Finset.sum_empty]

/-- The truncated Dynkin martingale of `|x|²`, clamped so that its increments are surely
bounded, has increments at most `2 (2 R + 1)`, conditional variances at most
`(2 R + 1)²`, starts at `0` and agrees almost surely with `𝒬` on the event that the walk
stays in the ball of radius `R` up to time `n`. -/
private theorem exists_clamped_stopped_quadratic (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    (hεd : ε < 1 / (d : ℝ)) {R : ℝ} (hR : 0 ≤ R) (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) :
    ∃ M : ℕ → Ω → ℝ, Martingale M (pathFiltration hX.measurable) μ ∧
      (∀ i ω, |M (i + 1) ω - M i ω| ≤ 2 * (2 * R + 1)) ∧
      (∀ j, μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | pathFiltration hX.measurable j] ≤ᵐ[μ]
        fun _ => (2 * R + 1) ^ 2) ∧
      (∀ ω, M 0 ω = 0) ∧
      ∀ᵐ ω ∂μ, (∀ j ≤ n, euclidNorm (X j ω) ≤ R) →
        M n ω = dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω := by
  have hd1 : 1 ≤ d := by omega
  have hQmart : Martingale (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X)
      (pathFiltration hX.measurable) μ :=
    martingale_dynkin hd1 hε hεd hX (fun z : Site d => euclidNorm z ^ 2)
  have hI_sm : ∀ j, StronglyMeasurable[pathFiltration hX.measurable j]
      (stayIndicator R X j) := fun j => stronglyMeasurable_stayIndicator hX.measurable R j
  have hQ'adp : StronglyAdapted (pathFiltration hX.measurable)
      (stoppedQuadratic ε R X) := by
    intro t
    show StronglyMeasurable[pathFiltration hX.measurable t]
      (fun ω => ∑ j ∈ Finset.range t, stayIndicator R X j ω *
        (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
          dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω))
    refine Finset.stronglyMeasurable_fun_sum _ fun j hj => ?_
    have hjt : j + 1 ≤ t := Finset.mem_range.mp hj
    have hjt' : j ≤ t := le_of_lt hjt
    exact ((hI_sm j).mono ((pathFiltration hX.measurable).mono hjt')).mul
      (((hQmart.stronglyMeasurable (j + 1)).mono ((pathFiltration hX.measurable).mono hjt)).sub
        ((hQmart.stronglyMeasurable j).mono ((pathFiltration hX.measurable).mono hjt')))
  have hQ'int : ∀ t, Integrable (stoppedQuadratic ε R X t) μ := by
    intro t
    have hterm : ∀ j ∈ Finset.range t, Integrable (fun ω => stayIndicator R X j ω *
        (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
          dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω)) μ := by
      intro j _
      refine Integrable.bdd_mul ((hQmart.integrable (j + 1)).sub (hQmart.integrable j))
        (((hI_sm j).mono ((pathFiltration hX.measurable).le j))).aestronglyMeasurable
        (c := 1) (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (stayIndicator_nonneg R X j ω)]
      exact stayIndicator_le_one R X j ω
    change Integrable (fun ω => ∑ j ∈ Finset.range t, stayIndicator R X j ω *
      (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
        dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω)) μ
    exact integrable_finsetSum (Finset.range t) hterm
  have hQ'cond : ∀ k, μ[stoppedQuadratic ε R X (k + 1) - stoppedQuadratic ε R X k
      | pathFiltration hX.measurable k] =ᵐ[μ] 0 := by
    intro k
    have hfun : stoppedQuadratic ε R X (k + 1) - stoppedQuadratic ε R X k =
        stayIndicator R X k * (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (k + 1) -
          dynkin ε (fun z : Site d => euclidNorm z ^ 2) X k) := by
      funext ω
      exact stoppedQuadratic_succ_sub ε R X k ω
    rw [hfun]
    have hpull := condExp_stronglyMeasurable_mul_of_bound (μ := μ)
      ((pathFiltration hX.measurable).le k) (hI_sm k)
      ((hQmart.integrable (k + 1)).sub (hQmart.integrable k)) 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (stayIndicator_nonneg R X k ω)]
        exact stayIndicator_le_one R X k ω)
    have hcent : μ[dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (k + 1) -
        dynkin ε (fun z : Site d => euclidNorm z ^ 2) X k | pathFiltration hX.measurable k]
        =ᵐ[μ] 0 := by
      have h3 := condExp_sub (hQmart.integrable (k + 1)) (hQmart.integrable k)
        (pathFiltration hX.measurable k)
      have h1 := hQmart.condExp_ae_eq (Nat.le_succ k)
      have h2 : μ[dynkin ε (fun z : Site d => euclidNorm z ^ 2) X k
          | pathFiltration hX.measurable k] =
          dynkin ε (fun z : Site d => euclidNorm z ^ 2) X k :=
        condExp_of_stronglyMeasurable ((pathFiltration hX.measurable).le k)
          (hQmart.stronglyMeasurable k) (hQmart.integrable k)
      filter_upwards [h3, h1] with ω e3 e1
      rw [e3, Pi.sub_apply, e1, h2, sub_self]
      rfl
    filter_upwards [hpull, hcent] with ω e1 e2
    rw [e1, Pi.mul_apply, e2, Pi.zero_apply, mul_zero]
  have hmartQ' : Martingale (stoppedQuadratic ε R X) (pathFiltration hX.measurable) μ :=
    martingale_of_condExp_sub_eq_zero_nat hQ'adp hQ'int hQ'cond
  have hinc : ∀ i, ∀ᵐ ω ∂μ, |stoppedQuadratic ε R X (i + 1) ω -
      stoppedQuadratic ε R X i ω| ≤ 2 * (2 * R + 1) := by
    intro i
    filter_upwards [ae_abs_dynkin_succ_sub_le hd1 hε hεd hX
      (fun z : Site d => euclidNorm z ^ 2)] with ω hω
    rw [stoppedQuadratic_succ_sub]
    by_cases hb : euclidNorm (X i ω) ≤ R
    · have hI1 : stayIndicator R X i ω = 1 := by rw [stayIndicator, if_pos hb]
      rw [hI1, one_mul]
      exact hω i (2 * R + 1) fun e he => by
        have h1 := abs_sq_euclidNorm_add_unit_le (X i ω) e he
        linarith
    · have hI0 : stayIndicator R X i ω = 0 := by rw [stayIndicator, if_neg hb]
      rw [hI0, zero_mul, abs_zero]
      positivity
  have hvarQ' : ∀ j, μ[fun ω => (stoppedQuadratic ε R X (j + 1) ω -
      stoppedQuadratic ε R X j ω) ^ 2 | pathFiltration hX.measurable j] ≤ᵐ[μ]
      fun _ => (2 * R + 1) ^ 2 := by
    intro j
    have hsquare : (fun ω => (stoppedQuadratic ε R X (j + 1) ω -
        stoppedQuadratic ε R X j ω) ^ 2) =ᵐ[μ]
        stayIndicator R X j * fun ω =>
          (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
            dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω) ^ 2 := by
      filter_upwards with ω
      rw [stoppedQuadratic_succ_sub, Pi.mul_apply, mul_pow, stayIndicator]
      split_ifs <;> ring
    refine (condExp_congr_ae hsquare).trans_le ?_
    have hIntDelta2 : Integrable (fun ω =>
        (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
          dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω) ^ 2) μ := by
      have hpath := integrable_path_next hd1 hε hεd hX j
        (fun p z => (euclidNorm z ^ 2 - nextMean ε (fun z : Site d => euclidNorm z ^ 2)
          (extendPath p) j) ^ 2)
      simpa only [dynkin_succ_sub, nextMean_pastPath] using hpath
    have hpull := condExp_stronglyMeasurable_mul_of_bound (μ := μ)
      ((pathFiltration hX.measurable).le j) (hI_sm j) hIntDelta2 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (stayIndicator_nonneg R X j ω)]
        exact stayIndicator_le_one R X j ω)
    filter_upwards [hpull, condExp_sq_dynkin_succ_sub_le hd1 hε hεd hX
      (fun z : Site d => euclidNorm z ^ 2) j] with ω e1 e2
    rw [e1, Pi.mul_apply]
    by_cases hb : euclidNorm (X j ω) ≤ R
    · have hI1 : stayIndicator R X j ω = 1 := by rw [stayIndicator, if_pos hb]
      rw [hI1, one_mul]
      refine e2.trans ?_
      calc ∑ e ∈ unitSteps d, stepProb d ε (fun i => X i ω) j e *
            (euclidNorm (X j ω + e) ^ 2 - euclidNorm (X j ω) ^ 2) ^ 2
          ≤ ∑ e ∈ unitSteps d, stepProb d ε (fun i => X i ω) j e * (2 * R + 1) ^ 2 := by
            refine sum_le_sum fun e he => mul_le_mul_of_nonneg_left ?_
              (stepProb_nonneg hε hεd _ j e)
            have h1 := abs_sq_euclidNorm_add_unit_le (X j ω) e he
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
        _ = (2 * R + 1) ^ 2 := by
            rw [← sum_mul, sum_stepProb hd1 ε _ j, one_mul]
    · have hI0 : stayIndicator R X j ω = 0 := by rw [stayIndicator, if_neg hb]
      rw [hI0, zero_mul]
      positivity
  obtain ⟨M, hMmart, hMinc, hM0, hMae⟩ :=
    CERW.Generic.Martingale.exists_martingale_clamp hmartQ'
      (b := 2 * (2 * R + 1)) (by positivity) hinc
  refine ⟨M, hMmart, hMinc, ?_, ?_, ?_⟩
  · intro j
    have hsq : (fun ω => (M (j + 1) ω - M j ω) ^ 2) =ᵐ[μ]
        fun ω => (stoppedQuadratic ε R X (j + 1) ω -
          stoppedQuadratic ε R X j ω) ^ 2 := by
      filter_upwards [hMae] with ω hω
      rw [hω (j + 1), hω j]
    exact (condExp_congr_ae hsq).trans_le (hvarQ' j)
  · intro ω
    rw [hM0 ω, stoppedQuadratic_zero]
  · have hQ'eq : ∀ ω, (∀ j ≤ n, euclidNorm (X j ω) ≤ R) →
        stoppedQuadratic ε R X n ω =
          dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω := by
      intro ω hball
      have hsum : stoppedQuadratic ε R X n ω =
          ∑ j ∈ Finset.range n,
            (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
              dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω) := by
        simp only [stoppedQuadratic]
        refine sum_congr rfl fun j hj => ?_
        have hjn : j ≤ n := le_of_lt (Finset.mem_range.mp hj)
        have hI1 : stayIndicator R X j ω = 1 := by rw [stayIndicator, if_pos (hball j hjn)]
        rw [hI1, one_mul]
      rw [hsum, Finset.sum_range_sub
        (fun j => dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω) n,
        dynkin_zero, sub_zero]
    filter_upwards [hMae] with ω hω hball
    rw [hω n, hQ'eq ω hball]


/-- Lower tail of the quadratic martingale: on the event that the walk stays in the ball of
radius `R` up to time `n`, `𝒬_n ≤ -t` has probability at most `exp(-t²/(2(v + b t/3)))`, with
`v = n (2R+1)²` and `b = 2(2R+1)`. -/
private theorem quadratic_lower_tail (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (n : ℕ) :
    μ {ω | (∀ j ≤ n, euclidNorm (X j ω) ≤ R) ∧ quadraticMart ε (fun j => X j ω) n ≤ -t} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2 /
        (2 * ((n : ℝ) * (2 * R + 1) ^ 2 + 2 * (2 * R + 1) * t / 3))))) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨M, hMmart, hMinc, hMvar, hM0, hMae⟩ :=
    exists_clamped_stopped_quadratic hd hε.le hεd hR n hX
  have hb : 0 < 2 * (2 * R + 1) := by positivity
  have hv : 0 ≤ (n : ℝ) * (2 * R + 1) ^ 2 := by positivity
  have hqv : ∀ᵐ ω ∂μ, ∑ i ∈ Finset.range n,
      (μ[fun ω' => (M (i + 1) ω' - M i ω') ^ 2 | pathFiltration hX.measurable i]) ω ≤
        (n : ℝ) * (2 * R + 1) ^ 2 := by
    have hall := (Filter.eventually_all_finset (Finset.range n)).mpr fun i _ => hMvar i
    filter_upwards [hall] with ω hω
    calc ∑ i ∈ Finset.range n,
          (μ[fun ω' => (M (i + 1) ω' - M i ω') ^ 2 | pathFiltration hX.measurable i]) ω
        ≤ ∑ _i ∈ Finset.range n, (2 * R + 1) ^ 2 := Finset.sum_le_sum fun i hi => hω i hi
      _ = (n : ℝ) * (2 * R + 1) ^ 2 := by simp
  have hfree := LatticeProb.freedman hMmart (funext hM0) hb hv (fun i _ ω => hMinc i ω) hqv t ht
  have hstart : ∀ᵐ ω ∂μ, X 0 ω = 0 := ae_iff.mpr hX.start
  have hsub : {ω | (∀ j ≤ n, euclidNorm (X j ω) ≤ R) ∧
      quadraticMart ε (fun j => X j ω) n ≤ -t} ≤ᵐ[μ] {ω | M n ω ≤ -t} := by
    filter_upwards [hMae, hstart] with ω hω h0 hmem
    obtain ⟨hball, hQ⟩ := hmem
    have hsq := CERW.Support.Contact.sq_euclidNorm_eq hd1 ε X ω h0 n
    have hQd : quadraticMart ε (fun j => X j ω) n =
        dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω := by
      unfold quadraticMart
      linarith
    show M n ω ≤ -t
    rw [hω hball, ← hQd]
    exact hQ
  have hle : μ {ω | M n ω ≤ -t} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 /
      (2 * ((n : ℝ) * (2 * R + 1) ^ 2 + 2 * (2 * R + 1) * t / 3))))) := by
    refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr ?_
    convert hfree using 4
  exact (measure_mono_ae hsub).trans hle

end QuadraticTail

section Arithmetic

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- The radius `r_n = ((d+1) n / (2 d ε ω_d))^{1/(d+1)}` of the limit shape. -/
private noncomputable def radius (d : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  ((d + 1) * n / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))

/-- The constant `(d+1) / (2 d ε ω_d)` relating `r_n^{d+1}` to `n`. -/
private noncomputable def radiusConst (d : ℕ) (ε : ℝ) : ℝ :=
  (d + 1) / (2 * d * ε * unitBallVolume d)

/-- The constant relating `r_n^{d+1}` to `n` is positive. -/
private theorem radiusConst_pos (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) : 0 < radiusConst d ε := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have := unitBallVolume_pos d
  unfold radiusConst
  positivity

/-- The radius in terms of the constant: `r_n = (κ n)^{1/(d+1)}`. -/
private theorem radius_eq (d : ℕ) (ε : ℝ) (n : ℕ) :
    radius d ε n = (radiusConst d ε * n) ^ ((1 : ℝ) / (d + 1)) := by
  unfold radius radiusConst
  rw [div_mul_eq_mul_div]

/-- The radius is nonnegative. -/
private theorem radius_nonneg (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 ≤ radius d ε n := by
  rw [radius_eq]
  exact Real.rpow_nonneg (mul_nonneg (radiusConst_pos hd hε).le (Nat.cast_nonneg n)) _

/-- `r_n^{d+1} = κ n`. -/
private theorem radius_pow (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    radius d ε n ^ (d + 1) = radiusConst d ε * n := by
  rw [radius_eq, ← Real.rpow_natCast, ← Real.rpow_mul
    (mul_nonneg (radiusConst_pos hd hε).le (Nat.cast_nonneg n))]
  have : (1 : ℝ) / (d + 1) * ((d + 1 : ℕ) : ℝ) = 1 := by
    push_cast
    field_simp
  rw [this, Real.rpow_one]

/-- `n = 2 d ε ω_d r_n^{d+1} / (d+1)`. -/
private theorem nat_eq_radius (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    (n : ℝ) = 2 * d * ε * unitBallVolume d * radius d ε n ^ (d + 1) / (d + 1) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have := unitBallVolume_pos d
  rw [radius_pow hd hε]
  unfold radiusConst
  field_simp

/-- The radius tends to infinity: it exceeds any bound for large `n`. -/
private theorem exists_radius_ge (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → R ≤ radius d ε n := by
  have hκ := radiusConst_pos hd hε
  by_cases hR : R ≤ 0
  · exact ⟨0, fun n _ => hR.trans (radius_nonneg hd hε n)⟩
  · replace hR := not_le.mp hR
    refine ⟨⌈R ^ (d + 1) / radiusConst d ε⌉₊, fun n hn => ?_⟩
    by_contra hlt
    replace hlt := not_le.mp hlt
    have h1 : radius d ε n ^ (d + 1) < R ^ (d + 1) :=
      pow_lt_pow_left₀ hlt (radius_nonneg hd hε n) (by omega)
    rw [radius_pow hd hε] at h1
    have h2 : R ^ (d + 1) / radiusConst d ε ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn)
    rw [div_le_iff₀ hκ] at h2
    linarith

/-- The trial bound `(1 - p₀^T)^{⌊k/T⌋}` in exponential form, for `T = ⌈4 h √d⌉`,
`k ≥ c_k Y h` and `Y` large. -/
private theorem trial_exponent (hd : 1 ≤ d) {p₀ Y h ck : ℝ} {k : ℕ} (hp : 0 < p₀)
    (hp1 : p₀ ≤ 1 / 2) (hh : 1 ≤ h) (hck : 0 < ck) (hY : 0 ≤ Y) (hk : ck * Y * h ≤ k)
    (hY1 : 1 ≤ ck / (2 * (4 * Real.sqrt d + 1)) * Y) :
    (1 - p₀ ^ ⌈4 * h * Real.sqrt d⌉₊) ^ (k / ⌈4 * h * Real.sqrt d⌉₊) ≤
      Real.exp (-(ck / (2 * (4 * Real.sqrt d + 1)) * Y *
        Real.exp (-((4 * Real.sqrt d + 1) * (-Real.log p₀) * h)))) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
  set s : ℝ := Real.sqrt d with hsdef
  set T : ℕ := ⌈4 * h * s⌉₊ with hTdef
  have hT1 : 1 ≤ T := Nat.ceil_pos.mpr (by positivity)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
  have hTle : (T : ℝ) ≤ (4 * s + 1) * h := by
    have h1 : (T : ℝ) < 4 * h * s + 1 := Nat.ceil_lt_add_one (by positivity)
    nlinarith
  set q : ℝ := p₀ ^ T with hqdef
  have hq0 : 0 < q := pow_pos hp T
  have hq1 : q ≤ 1 := pow_le_one₀ hp.le (by linarith)
  have hlogp : Real.log p₀ ≤ 0 := Real.log_nonpos hp.le (by linarith)
  have hqexp : Real.exp (-((4 * s + 1) * (-Real.log p₀) * h)) ≤ q := by
    have h1 : q = Real.exp ((T : ℝ) * Real.log p₀) := by
      rw [Real.exp_nat_mul, Real.exp_log hp]
    rw [h1]
    refine Real.exp_le_exp.mpr ?_
    have h2 : (T : ℝ) * Real.log p₀ ≥ ((4 * s + 1) * h) * Real.log p₀ :=
      mul_le_mul_of_nonpos_right hTle hlogp
    linarith
  set j : ℕ := k / T with hjdef
  have hjlt : (k : ℝ) < (j : ℝ) * T + T := by
    have := Nat.lt_div_mul_add (a := k) hT1
    exact_mod_cast this
  have hj : ck / (2 * (4 * s + 1)) * Y ≤ (j : ℝ) := by
    have h1 : ck * Y * h / ((4 * s + 1) * h) ≤ (k : ℝ) / T := by
      calc ck * Y * h / ((4 * s + 1) * h) ≤ ck * Y * h / T :=
            div_le_div_of_nonneg_left (by positivity) hTpos hTle
        _ ≤ (k : ℝ) / T := div_le_div_of_nonneg_right hk hTpos.le
    have h2 : ck * Y * h / ((4 * s + 1) * h) = ck * Y / (4 * s + 1) := by
      field_simp
    have h3 : (k : ℝ) / T < (j : ℝ) + 1 := by
      rw [div_lt_iff₀ hTpos]
      linarith
    have h4 : ck / (2 * (4 * s + 1)) * Y * 2 = ck * Y / (4 * s + 1) := by
      field_simp
    linarith
  have hexp : (1 - q) ^ j ≤ Real.exp (-(q * j)) := by
    calc (1 - q) ^ j ≤ Real.exp (-q) ^ j :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg q) j
      _ = Real.exp (-(q * j)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  refine hexp.trans (Real.exp_le_exp.mpr ?_)
  have h1 : ck / (2 * (4 * s + 1)) * Y * Real.exp (-((4 * s + 1) * (-Real.log p₀) * h)) ≤
      q * j := by
    calc ck / (2 * (4 * s + 1)) * Y * Real.exp (-((4 * s + 1) * (-Real.log p₀) * h))
        = Real.exp (-((4 * s + 1) * (-Real.log p₀) * h)) * (ck / (2 * (4 * s + 1)) * Y) := by
          ring
      _ ≤ q * j := mul_le_mul hqexp hj (by positivity) hq0.le
  linarith

/-- The Freedman exponent `t² / (2 (v + b t / 3))` with `t = c₂ r^d h`, `v = n (2 (r+h) + 1)²`
and `b = 2 (2 (r+h) + 1)` is at least a constant times `r^{d-3} h²`. -/
private theorem freedman_exponent (hd : 2 ≤ d) {ε ω c₂ r h n : ℝ} (hε : 0 < ε) (hω : 0 < ω)
    (hc₂ : 0 < c₂) (hr : 1 ≤ r) (hh : 0 < h) (hhr : 8 * h ≤ r)
    (hn : n = 2 * d * ε * ω * r ^ (d + 1) / (d + 1)) :
    c₂ ^ 2 / (2 * ((169 / 8) * ε * ω + (13 / 48) * c₂)) * r ^ ((d : ℝ) - 3) * h ^ 2 ≤
      (c₂ * r ^ d * h) ^ 2 /
        (2 * (n * (2 * (r + h) + 1) ^ 2 + 2 * (2 * (r + h) + 1) * (c₂ * r ^ d * h) / 3)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hr0 : 0 < r := by linarith
  have hrd : 0 < r ^ d := pow_pos hr0 d
  have hA : 2 * (r + h) + 1 ≤ 13 / 4 * r := by linarith
  have hA0 : 0 ≤ 2 * (r + h) + 1 := by linarith
  have hn0 : 0 < n := by
    rw [hn]
    positivity
  have hnle : n ≤ 2 * ε * ω * r ^ (d + 1) := by
    rw [hn, div_le_iff₀ (by positivity)]
    have h1 : 0 ≤ 2 * ε * ω * r ^ (d + 1) := by positivity
    nlinarith
  have hA2 : (2 * (r + h) + 1) ^ 2 ≤ (13 / 4 * r) ^ 2 := pow_le_pow_left₀ hA0 hA 2
  have hterm1 : n * (2 * (r + h) + 1) ^ 2 ≤ (169 / 8) * ε * ω * r ^ (d + 3) := by
    calc n * (2 * (r + h) + 1) ^ 2 ≤ (2 * ε * ω * r ^ (d + 1)) * (13 / 4 * r) ^ 2 :=
          mul_le_mul hnle hA2 (by positivity) (by positivity)
      _ = (169 / 8) * ε * ω * r ^ (d + 3) := by ring
  have hterm2 : 2 * (2 * (r + h) + 1) * (c₂ * r ^ d * h) / 3 ≤ (13 / 48) * c₂ * r ^ (d + 3) := by
    have h1 : 2 * (2 * (r + h) + 1) * (c₂ * r ^ d * h) / 3 ≤
        2 * (13 / 4 * r) * (c₂ * r ^ d * (r / 8)) / 3 := by
      have h2 : c₂ * r ^ d * h ≤ c₂ * r ^ d * (r / 8) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h3 : 2 * (2 * (r + h) + 1) ≤ 2 * (13 / 4 * r) := by linarith
      have h4 := mul_le_mul h3 h2 (by positivity) (by positivity)
      linarith
    have h5 : 2 * (13 / 4 * r) * (c₂ * r ^ d * (r / 8)) / 3 = (13 / 48) * c₂ * (r ^ d * r ^ 2) := by
      ring
    have h6 : r ^ d * r ^ 2 ≤ r ^ (d + 3) := by
      rw [← pow_add, pow_add]
      calc r ^ d * r ^ 2 = r ^ d * r ^ 2 * 1 := by ring
        _ ≤ r ^ d * r ^ 2 * r := by
            exact mul_le_mul_of_nonneg_left hr (by positivity)
        _ = r ^ (d + 2) * r := by ring
        _ = r ^ (d + 2 + 1) := by ring
    calc 2 * (2 * (r + h) + 1) * (c₂ * r ^ d * h) / 3
        ≤ 2 * (13 / 4 * r) * (c₂ * r ^ d * (r / 8)) / 3 := h1
      _ = (13 / 48) * c₂ * (r ^ d * r ^ 2) := h5
      _ ≤ (13 / 48) * c₂ * r ^ (d + 3) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
  set V : ℝ := (169 / 8) * ε * ω + (13 / 48) * c₂ with hVdef
  have hV : 0 < V := by positivity
  have hinner_pos : 0 < n * (2 * (r + h) + 1) ^ 2 +
      2 * (2 * (r + h) + 1) * (c₂ * r ^ d * h) / 3 := by positivity
  have hinner_le : n * (2 * (r + h) + 1) ^ 2 +
      2 * (2 * (r + h) + 1) * (c₂ * r ^ d * h) / 3 ≤ V * r ^ (d + 3) := by
    have : V * r ^ (d + 3) = (169 / 8) * ε * ω * r ^ (d + 3) + (13 / 48) * c₂ * r ^ (d + 3) := by
      rw [hVdef]
      ring
    linarith
  have hrpow : r ^ ((d : ℝ) - 3) = r ^ d / r ^ 3 := by
    rw [Real.rpow_sub hr0, Real.rpow_natCast]
    norm_num
  calc c₂ ^ 2 / (2 * V) * r ^ ((d : ℝ) - 3) * h ^ 2
      = (c₂ * r ^ d * h) ^ 2 / (2 * (V * r ^ (d + 3))) := by
        rw [hrpow]
        field_simp
        ring
    _ ≤ (c₂ * r ^ d * h) ^ 2 /
        (2 * (n * (2 * (r + h) + 1) ^ 2 +
          2 * (2 * (r + h) + 1) * (c₂ * r ^ d * h) / 3)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          (mul_le_mul_of_nonneg_left hinner_le (by norm_num))

/-- Polynomial decay of the trial bound at `h = (d-1) log r / (4C)`: with `r^{d+1} = κ n`,
`exp(-c r^{d-1} e^{-C h}) ≤ 8!/(c^8 κ²) n^{-2}`. -/
private theorem exp_decay_shell (hd : 2 ≤ d) {c C κ r : ℝ} {n : ℕ} (hc : 0 < c) (hC : 0 < C)
    (hκ : 0 < κ) (hr : 1 ≤ r) (hrn : r ^ (d + 1) = κ * n) :
    Real.exp (-(c * r ^ (d - 1) *
        Real.exp (-(C * (((d : ℝ) - 1) * Real.log r / (4 * C)))))) ≤
      (Nat.factorial 8 : ℝ) / (c ^ 8 * κ ^ 2) * (n : ℝ) ^ (-(2 : ℝ)) := by
  have hr0 : 0 < r := by linarith
  have hL : 0 ≤ Real.log r := Real.log_nonneg hr
  have hexp : Real.exp (Real.log r) = r := Real.exp_log hr0
  have hrpow : ∀ m : ℕ, r ^ m = Real.exp ((m : ℝ) * Real.log r) := fun m => by
    rw [Real.exp_nat_mul, hexp]
  have hδ : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  set Z : ℝ := r ^ (d - 1) * Real.exp (-(C * (((d : ℝ) - 1) * Real.log r / (4 * C)))) with hZdef
  have hZ0 : 0 < Z := by positivity
  have hZexp : Z = Real.exp (3 / 4 * (((d : ℝ) - 1) * Real.log r)) := by
    rw [hZdef, hrpow, ← Real.exp_add, hδ]
    congr 1
    field_simp
    ring
  have hn : 0 < (n : ℝ) := by
    have h1 : 1 ≤ r ^ (d + 1) := one_le_pow₀ hr
    rw [hrn] at h1
    by_contra hneg
    have : (n : ℝ) = 0 := le_antisymm (not_lt.mp hneg) (Nat.cast_nonneg n)
    rw [this, mul_zero] at h1
    linarith
  have hZ8 : (κ * n) ^ 2 ≤ Z ^ 8 := by
    rw [← hrn, ← pow_mul, hrpow, hZexp, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    push_cast
    have h1 : ((d : ℝ) + 1) * 2 ≤ 8 * (3 / 4 * ((d : ℝ) - 1)) := by linarith
    calc ((d : ℝ) + 1) * 2 * Real.log r ≤ (8 * (3 / 4 * ((d : ℝ) - 1))) * Real.log r :=
          mul_le_mul_of_nonneg_right h1 hL
      _ = 8 * (3 / 4 * (((d : ℝ) - 1) * Real.log r)) := by ring
  have hcZ : 0 < c * Z := mul_pos hc hZ0
  have hfact : (0 : ℝ) < (Nat.factorial 8 : ℝ) := by positivity
  have h1 : Real.exp (-(c * Z)) ≤ (Nat.factorial 8 : ℝ) / (c * Z) ^ 8 := by
    have h2 := Real.pow_div_factorial_le_exp (c * Z) hcZ.le 8
    rw [Real.exp_neg]
    calc (Real.exp (c * Z))⁻¹ ≤ ((c * Z) ^ 8 / (Nat.factorial 8 : ℝ))⁻¹ :=
          inv_anti₀ (by positivity) h2
      _ = (Nat.factorial 8 : ℝ) / (c * Z) ^ 8 := by rw [inv_div]
  have h3 : (Nat.factorial 8 : ℝ) / (c * Z) ^ 8 ≤
      (Nat.factorial 8 : ℝ) / (c ^ 8 * (κ * n) ^ 2) := by
    rw [mul_pow]
    exact div_le_div_of_nonneg_left hfact.le (by positivity)
      (mul_le_mul_of_nonneg_left hZ8 (by positivity))
  have h4 : (Nat.factorial 8 : ℝ) / (c ^ 8 * (κ * n) ^ 2) =
      (Nat.factorial 8 : ℝ) / (c ^ 8 * κ ^ 2) * (n : ℝ) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hn.le, Real.rpow_two]
    field_simp
  have hcZ' : c * r ^ (d - 1) *
      Real.exp (-(C * (((d : ℝ) - 1) * Real.log r / (4 * C)))) = c * Z := by
    rw [hZdef, mul_assoc]
  rw [hcZ', ← h4]
  exact h1.trans h3

/-- `n` is positive when `r ≥ 1` and `r^{d+1} = κ n`. -/
private theorem pos_of_pow_eq {κ r : ℝ} {n : ℕ} (hr : 1 ≤ r) (hrn : r ^ (d + 1) = κ * n) :
    0 < (n : ℝ) := by
  have h1 : 1 ≤ r ^ (d + 1) := one_le_pow₀ hr
  rw [hrn] at h1
  by_contra hneg
  have : (n : ℝ) = 0 := le_antisymm (not_lt.mp hneg) (Nat.cast_nonneg n)
  rw [this, mul_zero] at h1
  linarith

/-- `n ≤ r^{d+2}` when `1/κ ≤ r` and `r^{d+1} = κ n`. -/
private theorem le_pow_of_pow_eq {κ r : ℝ} {n : ℕ} (hκ : 0 < κ) (hr : 1 ≤ r)
    (hrκ : 1 / κ ≤ r) (hrn : r ^ (d + 1) = κ * n) : (n : ℝ) ≤ r ^ (d + 2) := by
  have h1 : (n : ℝ) = (1 / κ) * r ^ (d + 1) := by
    rw [hrn]
    field_simp
  have hr0 : 0 < r := by linarith
  rw [h1]
  calc 1 / κ * r ^ (d + 1) ≤ r * r ^ (d + 1) :=
        mul_le_mul_of_nonneg_right hrκ (by positivity)
    _ = r ^ (d + 2) := by ring

/-- For `d ≥ 3`, `exp(-c r^{d-3} h²) ≤ n^{-2}` at `h = (d-1) log r / (4C)` once `log r` is
large. -/
private theorem exp_decay_gauss (hd : 3 ≤ d) {c C κ r : ℝ} {n : ℕ} (hc : 0 < c) (hC : 0 < C)
    (hκ : 0 < κ) (hr : 1 ≤ r) (hrκ : 1 / κ ≤ r) (hrn : r ^ (d + 1) = κ * n)
    (hL : 2 * ((d : ℝ) + 2) / (c * (((d : ℝ) - 1) / (4 * C)) ^ 2) ≤ Real.log r) :
    Real.exp (-(c * r ^ ((d : ℝ) - 3) * (((d : ℝ) - 1) * Real.log r / (4 * C)) ^ 2)) ≤
      (n : ℝ) ^ (-(2 : ℝ)) := by
  have hr0 : 0 < r := by linarith
  have hL0 : 0 ≤ Real.log r := Real.log_nonneg hr
  have hexp : Real.exp (Real.log r) = r := Real.exp_log hr0
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hn : 0 < (n : ℝ) := pos_of_pow_eq hr hrn
  have hc₅pos : 0 < c * (((d : ℝ) - 1) / (4 * C)) ^ 2 := by
    have : 0 < ((d : ℝ) - 1) / (4 * C) := div_pos (by linarith) (by positivity)
    positivity
  have h1 : 1 ≤ r ^ ((d : ℝ) - 3) := Real.one_le_rpow hr (by linarith)
  have hsq : (((d : ℝ) - 1) * Real.log r / (4 * C)) ^ 2 =
      (((d : ℝ) - 1) / (4 * C)) ^ 2 * Real.log r ^ 2 := by
    ring
  have h2 : 2 * ((d : ℝ) + 2) * Real.log r ≤
      c * r ^ ((d : ℝ) - 3) * (((d : ℝ) - 1) * Real.log r / (4 * C)) ^ 2 := by
    rw [hsq]
    have h3 : 2 * ((d : ℝ) + 2) ≤ c * (((d : ℝ) - 1) / (4 * C)) ^ 2 * Real.log r := by
      rw [div_le_iff₀ hc₅pos] at hL
      linarith
    calc 2 * ((d : ℝ) + 2) * Real.log r
        ≤ (c * (((d : ℝ) - 1) / (4 * C)) ^ 2 * Real.log r) * Real.log r :=
          mul_le_mul_of_nonneg_right h3 hL0
      _ = c * ((((d : ℝ) - 1) / (4 * C)) ^ 2 * Real.log r ^ 2) := by ring
      _ ≤ c * r ^ ((d : ℝ) - 3) * ((((d : ℝ) - 1) / (4 * C)) ^ 2 * Real.log r ^ 2) := by
          have h4 : 0 ≤ (((d : ℝ) - 1) / (4 * C)) ^ 2 * Real.log r ^ 2 := by positivity
          calc c * ((((d : ℝ) - 1) / (4 * C)) ^ 2 * Real.log r ^ 2)
              = c * 1 * ((((d : ℝ) - 1) / (4 * C)) ^ 2 * Real.log r ^ 2) := by ring
            _ ≤ c * r ^ ((d : ℝ) - 3) * ((((d : ℝ) - 1) / (4 * C)) ^ 2 * Real.log r ^ 2) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hc.le) h4
  have h4 : Real.exp (-(c * r ^ ((d : ℝ) - 3) *
      (((d : ℝ) - 1) * Real.log r / (4 * C)) ^ 2)) ≤
      Real.exp (-(2 * ((d : ℝ) + 2) * Real.log r)) :=
    Real.exp_le_exp.mpr (neg_le_neg h2)
  have h5 : Real.exp (-(2 * ((d : ℝ) + 2) * Real.log r)) = (r ^ (2 * (d + 2)))⁻¹ := by
    have h6 : -(2 * ((d : ℝ) + 2) * Real.log r) = -(((2 * (d + 2) : ℕ) : ℝ) * Real.log r) := by
      push_cast
      ring
    rw [h6, Real.exp_neg, Real.exp_nat_mul, hexp]
  have h7 : (n : ℝ) ^ 2 ≤ r ^ (2 * (d + 2)) := by
    rw [mul_comm 2 (d + 2), pow_mul]
    exact pow_le_pow_left₀ hn.le (le_pow_of_pow_eq hκ hr hrκ hrn) 2
  have h8 : (r ^ (2 * (d + 2)))⁻¹ ≤ (n : ℝ) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hn.le, Real.rpow_two]
    exact inv_anti₀ (by positivity) h7
  rw [h5] at h4
  exact h4.trans h8

/-- At `h = (d-1) log r / (4C)`, `h₀ ≤ h ≤ r/8` once `r` is large. -/
private theorem height_range (hd : 2 ≤ d) {C h₀ r : ℝ} (hC : 0 < C) (hr : 1 ≤ r)
    (h1 : 4 * C * h₀ / ((d : ℝ) - 1) ≤ Real.log r) (h2 : (4 * ((d : ℝ) - 1) / C) ^ 2 ≤ r) :
    h₀ ≤ ((d : ℝ) - 1) * Real.log r / (4 * C) ∧
      ((d : ℝ) - 1) * Real.log r / (4 * C) ≤ r / 8 := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 < (d : ℝ) - 1 := by linarith
  have hr0 : 0 < r := by linarith
  constructor
  · rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ hd1] at h1
    linarith
  · set s : ℝ := Real.sqrt r with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr hr0
    have hss : s * s = r := Real.mul_self_sqrt hr0.le
    have hs4 : 4 * ((d : ℝ) - 1) / C ≤ s := by
      rw [hs]
      exact Real.le_sqrt_of_sq_le h2
    have hlog : Real.log r ≤ 2 * s := by
      have h3 : Real.log s = Real.log r / 2 := Real.log_sqrt hr0.le
      have h4 := Real.log_le_sub_one_of_pos hs0
      linarith
    rw [div_le_iff₀ (by positivity)]
    have h5 : 4 * ((d : ℝ) - 1) ≤ s * C := by
      rwa [div_le_iff₀ hC] at hs4
    calc ((d : ℝ) - 1) * Real.log r ≤ ((d : ℝ) - 1) * (2 * s) :=
          mul_le_mul_of_nonneg_left hlog hd1.le
      _ = (2 * s) * ((d : ℝ) - 1) := by ring
      _ ≤ (2 * s) * (s * C / 4) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = r / 8 * (4 * C) := by
          rw [← hss]
          ring

/-- `log n ≤ (d+2) log r` when `1/κ ≤ r` and `r^{d+1} = κ n`. -/
private theorem log_le_of_pow_eq {κ r : ℝ} {n : ℕ} (hκ : 0 < κ) (hr : 1 ≤ r)
    (hrκ : 1 / κ ≤ r) (hrn : r ^ (d + 1) = κ * n) :
    Real.log n ≤ ((d : ℝ) + 2) * Real.log r := by
  have hn : 0 < (n : ℝ) := pos_of_pow_eq hr hrn
  have h1 := Real.log_le_log hn (le_pow_of_pow_eq hκ hr hrκ hrn)
  rw [Real.log_pow] at h1
  push_cast at h1
  exact h1

end Arithmetic

section Main

open CERW.Support.Statements CERW CERW.Support.Law

variable {d : ℕ}

/-- The trial length `⌈4 h √d⌉` is at most `(4 √d + 1) h` when `h ≥ 1`. -/
private theorem trial_length_le {h : ℝ} (hh : 1 ≤ h) :
    ((⌈4 * h * Real.sqrt d⌉₊ : ℕ) : ℝ) ≤ (4 * Real.sqrt d + 1) * h := by
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have h1 : ((⌈4 * h * Real.sqrt d⌉₊ : ℕ) : ℝ) < 4 * h * Real.sqrt d + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  nlinarith

/-- A site of norm less than `a` lies in the departure range when `a ≤ R_in`. -/
private theorem mem_departureRange_of_lt_innerRadius {x : ℕ → Site d} {n : ℕ} {a : ℝ}
    {y : Site d} (hin : a ≤ innerRadius x n) (hy : euclidNorm y < a) :
    y ∈ departureRange x n := by
  rw [← CERW.Support.Occupation.toSpace_mem_cellSet_iff]
  by_contra hnot
  have hbdd : BddBelow ((fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) '' (cellSet x n)ᶜ) :=
    ⟨0, by
      rintro _ ⟨v, _, rfl⟩
      exact norm_nonneg v⟩
  have h1 : sInf ((fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) '' (cellSet x n)ᶜ) ≤
      ‖toSpace y‖ := csInf_le hbdd ⟨toSpace y, hnot, rfl⟩
  unfold innerRadius at hin
  rw [norm_toSpace] at h1
  linarith

end Main

section TailPieces

open CERW.Support.Statements CERW CERW.Support.Law

variable {d : ℕ}

/-- The one-step probability bound `p₀ = 1/(2d) - ε/2` lies in `(0, 1/2]`. -/
private theorem stepBound_mem (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) :
    0 < 1 / (2 * (d : ℝ)) - ε / 2 ∧ 1 / (2 * (d : ℝ)) - ε / 2 ≤ 1 / 2 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · have h1 : ε / 2 < 1 / (2 * (d : ℝ)) := by
      calc ε / 2 < 1 / (d : ℝ) / 2 := by linarith
        _ = 1 / (2 * d) := by field_simp
    linarith
  · have h1 : 1 / (2 * (d : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    linarith

/-- The trial length `⌈4 h √d⌉` is at most `n` when `(4 √d + 1) r / 8 ≤ n` and `h ≤ r / 8`. -/
private theorem trial_length_le_count {h r : ℝ} {n : ℕ} (hh1 : 1 ≤ h) (hh8 : 8 * h ≤ r)
    (hn : (4 * Real.sqrt d + 1) * r / 8 ≤ (n : ℝ)) : ⌈4 * h * Real.sqrt d⌉₊ ≤ n := by
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have h1 : ((⌈4 * h * Real.sqrt d⌉₊ : ℕ) : ℝ) ≤ (4 * Real.sqrt d + 1) * r / 8 := by
    calc ((⌈4 * h * Real.sqrt d⌉₊ : ℕ) : ℝ) ≤ (4 * Real.sqrt d + 1) * h := trial_length_le hh1
      _ ≤ (4 * Real.sqrt d + 1) * (r / 8) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (4 * Real.sqrt d + 1) * r / 8 := by ring
  exact_mod_cast h1.trans hn

/-- For `r ≥ (4 √d + 1) / (8 κ')` with `κ' = 2 d ε ω_d / (d + 1)`, the number `n` of steps
`n = κ' r^{d+1}` is at least `(4 √d + 1) r / 8`. -/
private theorem count_ge_length (hd : 2 ≤ d) {κ' r : ℝ} {n : ℕ} (hκ' : 0 < κ') (hr1 : 1 ≤ r)
    (hrC : (4 * Real.sqrt d + 1) / (8 * κ') ≤ r) (hn : (n : ℝ) = κ' * r ^ (d + 1)) :
    (4 * Real.sqrt d + 1) * r / 8 ≤ (n : ℝ) := by
  have h3 := hrC
  rw [div_le_iff₀ (by positivity)] at h3
  have h4 : κ' * r ^ 2 ≤ (n : ℝ) := by
    rw [hn]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 (by omega)) hκ'.le
  calc (4 * Real.sqrt d + 1) * r / 8 ≤ (r * (8 * κ')) * r / 8 := by
        have := mul_le_mul_of_nonneg_right h3 (by linarith : (0 : ℝ) ≤ r)
        linarith
    _ = κ' * r ^ 2 := by ring
    _ ≤ n := h4

/-- The trial bound for a finite set `Λ` of sites at distance more than `r - 2h`: if at least
`k ≥ c_k Y h` sites of `Λ` are visited and `R_out(n) ≤ r + h`, then the probability is at most
`exp(-c_k/(2 (4 √d + 1)) · Y · e^{-(4 √d + 1)(-log p₀) h})`. -/
private theorem trial_tail (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) (Λ : Finset (Site d)) {r h ck Y : ℝ} {n k : ℕ}
    (hΛ : ∀ x ∈ Λ, r - 2 * h < euclidNorm x) (hh1 : 1 ≤ h) (hck : 0 < ck) (hY : 0 ≤ Y)
    (hk : ck * Y * h ≤ k) (hY1 : 1 ≤ ck / (2 * (4 * Real.sqrt d + 1)) * Y)
    (hTn : ⌈4 * h * Real.sqrt d⌉₊ ≤ n) :
    μ {ω | maxRadius (fun j => X j ω) n ≤ r + h ∧
        k ≤ (departureRange (fun j => X j ω) n ∩ Λ).card} ≤
      ENNReal.ofReal (Real.exp (-(ck / (2 * (4 * Real.sqrt d + 1)) * Y *
        Real.exp (-((4 * Real.sqrt d + 1) *
          (-Real.log (1 / (2 * (d : ℝ)) - ε / 2)) * h))))) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
  obtain ⟨hp₀, hp₀1⟩ := stepBound_mem hd hε hεd
  have hT1 : 1 ≤ ⌈4 * h * Real.sqrt d⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hT3 : r + h - (r - 2 * h) ≤ (⌈4 * h * Real.sqrt d⌉₊ : ℝ) / Real.sqrt d := by
    rw [le_div_iff₀ hs]
    have h1 : 4 * h * Real.sqrt d ≤ ⌈4 * h * Real.sqrt d⌉₊ := Nat.le_ceil _
    have h2 : 0 < h * Real.sqrt d := mul_pos (by linarith) hs
    have h3 : (r + h - (r - 2 * h)) * Real.sqrt d = 3 * (h * Real.sqrt d) := by ring
    rw [h3]
    linarith
  obtain ⟨w, hw⟩ := exists_leaving_steps hd Λ (a := r - 2 * h) (ρ := r + h)
    (T := ⌈4 * h * Real.sqrt d⌉₊) hΛ hT3
  exact (trials_bound hd hε hεd hX Λ w hT1 hTn hw).trans
    (ENNReal.ofReal_le_ofReal (trial_exponent hd hp₀ hp₀1 hh1 hck hY hk hY1))

/-- The quadratic martingale is far below zero with exponentially small probability: if
`(n : ℝ) = 2 d ε ω_d r^{d+1} / (d + 1)`, `1 ≤ r`, `0 < h` and `8 h ≤ r`, the event that the walk
stays in the ball of radius `r + h` while `𝒬_n ≤ -c₂ r^d h` has probability at most
`exp(-c_A r^{d-3} h²)`. -/
private theorem outer_quadratic_tail (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) {c₂ r h : ℝ} {n : ℕ} (hc₂ : 0 < c₂) (hr1 : 1 ≤ r)
    (hhpos : 0 < h) (hh8 : 8 * h ≤ r)
    (hn_eq : (n : ℝ) = 2 * d * ε * unitBallVolume d * r ^ (d + 1) / (d + 1)) :
    μ {ω | (∀ j ≤ n, euclidNorm (X j ω) ≤ r + h) ∧
        quadraticMart ε (fun j => X j ω) n ≤ -(c₂ * r ^ d * h)} ≤
      ENNReal.ofReal (Real.exp (-(c₂ ^ 2 /
        (2 * ((169 / 8) * ε * unitBallVolume d + (13 / 48) * c₂)) *
          r ^ ((d : ℝ) - 3) * h ^ 2))) := by
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have ht : 0 ≤ c₂ * r ^ d * h := by positivity
  have hfe := freedman_exponent hd hε hω hc₂ hr1 hhpos hh8 hn_eq
  exact (quadratic_lower_tail hd hε hεd hX (by linarith) ht n).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hfe)))

end TailPieces

section TailBounds

open CERW.Support.Statements CERW CERW.Support.Law

variable {d : ℕ}

/-- The tail bounds of `prop:log-lower` (i): for large `n` and `h₀ ≤ h ≤ r_n/8`, the probability
of `{R_in ≥ r_n - h, R_out ≤ r_n + h}` is at most `exp(-c r_n^{d-1} e^{-C h})`, and the probability
of `{R_out ≤ r_n + h}` is at most that plus `exp(-c r_n^{d-3} h²)`. -/
private theorem radii_tail_bounds (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) :
    ∃ c C h₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < h₀ ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X →
        ∀ n : ℕ, n₀ ≤ n → ∀ h : ℝ, h₀ ≤ h → h ≤ radius d ε n / 8 →
          μ {ω | radius d ε n - h ≤ innerRadius (X · ω) n ∧
              maxRadius (X · ω) n ≤ radius d ε n + h} ≤
            ENNReal.ofReal (Real.exp (-(c * radius d ε n ^ (d - 1) * Real.exp (-(C * h))))) ∧
          μ {ω | maxRadius (X · ω) n ≤ radius d ε n + h} ≤
            ENNReal.ofReal (Real.exp (-(c * radius d ε n ^ (d - 1) * Real.exp (-(C * h)))) +
              Real.exp (-(c * radius d ε n ^ ((d : ℝ) - 3) * h ^ 2))) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
  obtain ⟨hp₀, hp₀1⟩ := stepBound_mem hd1 hε hεd
  obtain ⟨cS, hS, hcS, hhS, hshell⟩ := exists_card_shell hd1
  obtain ⟨c₁, c₂, hD, hc₁, hc₂, hhD, hdet⟩ := exists_quadraticMart_le hd hε
  set s : ℝ := Real.sqrt d with hsdef
  set p₀ : ℝ := 1 / (2 * (d : ℝ)) - ε / 2 with hp₀def
  set C : ℝ := (4 * s + 1) * (-Real.log p₀) with hCdef
  have hC : 0 < C := by
    have : Real.log p₀ < 0 := Real.log_neg hp₀ (by linarith)
    exact mul_pos (by positivity) (by linarith)
  set c₃ : ℝ := cS / (2 * (4 * s + 1)) with hc₃def
  set c₄ : ℝ := c₁ / (2 * (4 * s + 1)) with hc₄def
  set cA : ℝ := c₂ ^ 2 / (2 * ((169 / 8) * ε * unitBallVolume d + (13 / 48) * c₂)) with hcAdef
  have hc₃ : 0 < c₃ := by positivity
  have hc₄ : 0 < c₄ := by positivity
  have hcA : 0 < cA := by positivity
  set c : ℝ := min c₃ (min c₄ cA) with hcdef
  have hcpos : 0 < c := lt_min hc₃ (lt_min hc₄ hcA)
  have hc₃c : c ≤ c₃ := min_le_left _ _
  have hc₄c : c ≤ c₄ := (min_le_right _ _).trans (min_le_left _ _)
  have hcAc : c ≤ cA := (min_le_right _ _).trans (min_le_right _ _)
  set h₀ : ℝ := max (max hS hD) 1 with hh₀def
  set κ' : ℝ := 2 * d * ε * unitBallVolume d / (d + 1) with hκ'def
  have hκ' : 0 < κ' := by positivity
  set r₁ : ℝ := max 1 (max (1 / c₃) (max (1 / c₄) ((4 * s + 1) / (8 * κ')))) with hr₁def
  obtain ⟨n₀, hn₀⟩ := exists_radius_ge hd1 hε r₁
  refine ⟨c, C, h₀, hcpos, hC, lt_of_lt_of_le one_pos (le_max_right _ _), n₀, ?_⟩
  intro Ω _ μ _ X hX n hn h hhh hhr
  set r : ℝ := radius d ε n with hrdef
  have hrr : r₁ ≤ r := hn₀ n hn
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hrr
  have hrA : 1 / c₃ ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans hrr)
  have hrB : 1 / c₄ ≤ r :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans ((le_max_right _ _).trans hrr)
  have hrC : (4 * s + 1) / (8 * κ') ≤ r :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hrr))
  have hh1 : 1 ≤ h := (le_max_right _ _).trans hhh
  have hhS' : hS ≤ h := ((le_max_left _ _).trans (le_max_left _ _)).trans hhh
  have hhD' : hD ≤ h := ((le_max_right _ _).trans (le_max_left _ _)).trans hhh
  have hh8 : 8 * h ≤ r := by linarith
  have hhpos : 0 < h := by linarith
  have hn_eq : (n : ℝ) = 2 * d * ε * unitBallVolume d * r ^ (d + 1) / (d + 1) :=
    nat_eq_radius hd1 hε n
  have hTn : ⌈4 * h * s⌉₊ ≤ n := by
    refine trial_length_le_count hh1 hh8 (count_ge_length hd hκ' hr1 hrC ?_)
    rw [hn_eq, hκ'def]
    ring
  have hY1 : r ≤ r ^ (d - 1) := le_self_pow₀ hr1 (by omega)
  have hY0 : 0 ≤ r ^ (d - 1) := pow_nonneg (by linarith) _
  have hE0 : 0 ≤ Real.exp (-(C * h)) := (Real.exp_pos _).le
  have hc₃Y : 1 ≤ c₃ * r ^ (d - 1) := by
    have h1 : 1 ≤ r * c₃ := by
      have := hrA
      rwa [div_le_iff₀ hc₃] at this
    calc 1 ≤ r * c₃ := h1
      _ = c₃ * r := mul_comm _ _
      _ ≤ c₃ * r ^ (d - 1) := mul_le_mul_of_nonneg_left hY1 hc₃.le
  have hc₄Y : 1 ≤ c₄ * r ^ (d - 1) := by
    have h1 : 1 ≤ r * c₄ := by
      have := hrB
      rwa [div_le_iff₀ hc₄] at this
    calc 1 ≤ r * c₄ := h1
      _ = c₄ * r := mul_comm _ _
      _ ≤ c₄ * r ^ (d - 1) := mul_le_mul_of_nonneg_left hY1 hc₄.le
  have hb1 : μ {ω | r - h ≤ innerRadius (X · ω) n ∧ maxRadius (X · ω) n ≤ r + h} ≤
      ENNReal.ofReal (Real.exp (-(c * r ^ (d - 1) * Real.exp (-(C * h))))) := by
    set S : Finset (Site d) :=
      (ballFinset d (r - h - 1)).filter fun x => r - 2 * h < euclidNorm x with hSdef
    have hsub : {ω | r - h ≤ innerRadius (X · ω) n ∧ maxRadius (X · ω) n ≤ r + h} ⊆
        {ω | maxRadius (fun j => X j ω) n ≤ r + h ∧
          S.card ≤ (departureRange (fun j => X j ω) n ∩ S).card} := by
      rintro ω ⟨hin, hmax⟩
      refine ⟨hmax, ?_⟩
      have hSA : S ⊆ departureRange (fun j => X j ω) n := by
        intro y hy
        have hy' := Finset.mem_filter.mp hy
        have h1 : euclidNorm y ≤ r - h - 1 := LatticeProb.mem_ballFinset_iff.mp hy'.1
        exact mem_departureRange_of_lt_innerRadius hin (by linarith)
      rw [Finset.inter_eq_right.mpr hSA]
    have hk : cS * r ^ (d - 1) * h ≤ (S.card : ℝ) := hshell r h hhS' hh8
    exact (measure_mono hsub).trans ((trial_tail hd1 hε hεd hX S
      (fun x hx => (Finset.mem_filter.mp hx).2) hh1 hcS hY0 hk hc₃Y hTn).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₃c hY0) hE0)))))
  have hb2 : μ {ω | maxRadius (X · ω) n ≤ r + h} ≤
      ENNReal.ofReal (Real.exp (-(c * r ^ (d - 1) * Real.exp (-(C * h)))) +
        Real.exp (-(c * r ^ ((d : ℝ) - 3) * h ^ 2))) := by
    set Λ : Finset (Site d) :=
      (ballFinset d (r + h)).filter fun y => r - 2 * h < euclidNorm y with hΛdef
    set k₁ : ℕ := ⌈c₁ * r ^ (d - 1) * h⌉₊ with hk₁def
    have hsub : {ω | maxRadius (X · ω) n ≤ r + h} ⊆
        {ω | maxRadius (fun j => X j ω) n ≤ r + h ∧
          k₁ ≤ (departureRange (fun j => X j ω) n ∩ Λ).card} ∪
        {ω | (∀ j ≤ n, euclidNorm (X j ω) ≤ r + h) ∧
          quadraticMart ε (fun j => X j ω) n ≤ -(c₂ * r ^ d * h)} := by
      intro ω hω
      by_cases hk : k₁ ≤ (departureRange (fun j => X j ω) n ∩ Λ).card
      · exact Or.inl ⟨hω, hk⟩
      · right
        refine ⟨fun j hj => (euclidNorm_le_maxRadius _ hj).trans hω, ?_⟩
        have hm : (((departureRange (fun j => X j ω) n ∩ Λ).card : ℕ) : ℝ) <
            c₁ * r ^ (d - 1) * h := Nat.lt_ceil.mp (not_le.mp hk)
        exact hdet (fun j => X j ω) n r h hr1 hhD' hh8 hn_eq hω hm
    have hEa : μ {ω | maxRadius (fun j => X j ω) n ≤ r + h ∧
          k₁ ≤ (departureRange (fun j => X j ω) n ∩ Λ).card} ≤
        ENNReal.ofReal (Real.exp (-(c * r ^ (d - 1) * Real.exp (-(C * h))))) :=
      (trial_tail hd1 hε hεd hX Λ (fun x hx => (Finset.mem_filter.mp hx).2) hh1 hc₁ hY0
        (Nat.le_ceil _) hc₄Y hTn).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₄c hY0) hE0))))
    have hr3 : 0 ≤ r ^ ((d : ℝ) - 3) := Real.rpow_nonneg (by linarith) _
    have hEb : μ {ω | (∀ j ≤ n, euclidNorm (X j ω) ≤ r + h) ∧
          quadraticMart ε (fun j => X j ω) n ≤ -(c₂ * r ^ d * h)} ≤
        ENNReal.ofReal (Real.exp (-(c * r ^ ((d : ℝ) - 3) * h ^ 2))) :=
      (outer_quadratic_tail hd hε hεd hX hc₂ hr1 hhpos hh8 hn_eq).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcAc hr3)
            (sq_nonneg h)))))
    calc μ {ω | maxRadius (X · ω) n ≤ r + h}
        ≤ μ ({ω | maxRadius (fun j => X j ω) n ≤ r + h ∧
          k₁ ≤ (departureRange (fun j => X j ω) n ∩ Λ).card} ∪
          {ω | (∀ j ≤ n, euclidNorm (X j ω) ≤ r + h) ∧
            quadraticMart ε (fun j => X j ω) n ≤ -(c₂ * r ^ d * h)}) := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-(c * r ^ (d - 1) * Real.exp (-(C * h))))) +
          ENNReal.ofReal (Real.exp (-(c * r ^ ((d : ℝ) - 3) * h ^ 2))) := add_le_add hEa hEb
      _ = ENNReal.ofReal (Real.exp (-(c * r ^ (d - 1) * Real.exp (-(C * h)))) +
          Real.exp (-(c * r ^ ((d : ℝ) - 3) * h ^ 2))) :=
          (ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le).symm
  exact ⟨hb1, hb2⟩

end TailBounds

section AlmostSure

open CERW.Support.Statements CERW CERW.Support.Law

variable {d : ℕ}

/-- The almost-sure bounds of `prop:log-lower` (ii) follow from the tail bounds of (i):
Borel-Cantelli at `h = (d-1) log r_n / (4C)`. -/
private theorem radii_as_bounds (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {c C h₀ : ℝ} (hc : 0 < c)
    (hC : 0 < C) {n₀ : ℕ} {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → Site d}
    (hb : ∀ n : ℕ, n₀ ≤ n → ∀ h : ℝ, h₀ ≤ h → h ≤ radius d ε n / 8 →
      μ {ω | radius d ε n - h ≤ innerRadius (X · ω) n ∧
          maxRadius (X · ω) n ≤ radius d ε n + h} ≤
        ENNReal.ofReal (Real.exp (-(c * radius d ε n ^ (d - 1) * Real.exp (-(C * h))))) ∧
      μ {ω | maxRadius (X · ω) n ≤ radius d ε n + h} ≤
        ENNReal.ofReal (Real.exp (-(c * radius d ε n ^ (d - 1) * Real.exp (-(C * h)))) +
          Real.exp (-(c * radius d ε n ^ ((d : ℝ) - 3) * h ^ 2)))) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      ((d : ℝ) - 1) / (4 * C * ((d : ℝ) + 2)) * Real.log n <
          max (radius d ε n - innerRadius (X · ω) n) (maxRadius (X · ω) n - radius d ε n) ∧
        (3 ≤ d → ((d : ℝ) - 1) / (4 * C * ((d : ℝ) + 2)) * Real.log n <
          maxRadius (X · ω) n - radius d ε n) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdm : 0 < (d : ℝ) - 1 := by linarith
  have hκ := radiusConst_pos hd1 hε
  set κ : ℝ := radiusConst d ε with hκdef
  set L₀ : ℝ := 2 * ((d : ℝ) + 2) / (c * (((d : ℝ) - 1) / (4 * C)) ^ 2) with hL₀
  set Rbig : ℝ := max (max 1 (1 / κ)) (max (Real.exp (max (4 * C * h₀ / ((d : ℝ) - 1)) L₀))
    ((4 * ((d : ℝ) - 1) / C) ^ 2)) with hRbig
  obtain ⟨N₁, hN₁⟩ := exists_radius_ge hd1 hε Rbig
  set C₁ : ℝ := (Nat.factorial 8 : ℝ) / (c ^ 8 * κ ^ 2) with hC₁
  have hkey : ∀ n : ℕ, max N₁ n₀ ≤ n →
      μ {ω | ¬ (((d : ℝ) - 1) * Real.log (radius d ε n) / (4 * C) <
          max (radius d ε n - innerRadius (X · ω) n) (maxRadius (X · ω) n - radius d ε n) ∧
        (3 ≤ d → ((d : ℝ) - 1) * Real.log (radius d ε n) / (4 * C) <
          maxRadius (X · ω) n - radius d ε n))} ≤
        ENNReal.ofReal ((2 * C₁ + 1) * (n : ℝ) ^ (-(2 : ℝ))) ∧
      ((d : ℝ) - 1) / (4 * C * ((d : ℝ) + 2)) * Real.log n ≤
        ((d : ℝ) - 1) * Real.log (radius d ε n) / (4 * C) := by
    intro n hn
    have hnN : N₁ ≤ n := (le_max_left _ _).trans hn
    have hnn₀ : n₀ ≤ n := (le_max_right _ _).trans hn
    set r : ℝ := radius d ε n with hrdef
    have hrR : Rbig ≤ r := hN₁ n hnN
    have hr1 : 1 ≤ r := ((le_max_left _ _).trans (le_max_left _ _)).trans hrR
    have hrκ : 1 / κ ≤ r := ((le_max_right _ _).trans (le_max_left _ _)).trans hrR
    have hr0 : 0 < r := by linarith
    have hrexp : Real.exp (max (4 * C * h₀ / ((d : ℝ) - 1)) L₀) ≤ r :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans hrR
    have hrsq : (4 * ((d : ℝ) - 1) / C) ^ 2 ≤ r :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hrR)
    have hlogmax : max (4 * C * h₀ / ((d : ℝ) - 1)) L₀ ≤ Real.log r := by
      have := Real.log_le_log (Real.exp_pos _) hrexp
      rwa [Real.log_exp] at this
    have hlog1 : 4 * C * h₀ / ((d : ℝ) - 1) ≤ Real.log r := (le_max_left _ _).trans hlogmax
    have hlogL : L₀ ≤ Real.log r := (le_max_right _ _).trans hlogmax
    have hrn : r ^ (d + 1) = κ * n := radius_pow hd1 hε n
    obtain ⟨hh1, hh2⟩ := height_range hd hC hr1 hlog1 hrsq
    obtain ⟨hb1, hb2⟩ := hb n hnn₀ _ hh1 hh2
    have hn0 : 0 < (n : ℝ) := pos_of_pow_eq hr1 hrn
    have hdec := exp_decay_shell hd hc hC hκ hr1 hrn
    refine ⟨?_, ?_⟩
    · set hh : ℝ := ((d : ℝ) - 1) * Real.log r / (4 * C) with hhdef
      set E₁ : Set Ω := {ω | r - hh ≤ innerRadius (X · ω) n ∧ maxRadius (X · ω) n ≤ r + hh}
        with hE₁
      have hE₁le : μ E₁ ≤ ENNReal.ofReal (C₁ * (n : ℝ) ^ (-(2 : ℝ))) :=
        hb1.trans (ENNReal.ofReal_le_ofReal hdec)
      have hnn : 0 ≤ (n : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg hn0.le _
      have hC₁0 : 0 ≤ C₁ := by positivity
      by_cases hd3 : 3 ≤ d
      · set E₂ : Set Ω := {ω | maxRadius (X · ω) n ≤ r + hh} with hE₂
        have hgauss := exp_decay_gauss hd3 hc hC hκ hr1 hrκ hrn hlogL
        have hE₂le : μ E₂ ≤ ENNReal.ofReal ((C₁ + 1) * (n : ℝ) ^ (-(2 : ℝ))) := by
          refine hb2.trans (ENNReal.ofReal_le_ofReal ?_)
          calc _ ≤ C₁ * (n : ℝ) ^ (-(2 : ℝ)) + (n : ℝ) ^ (-(2 : ℝ)) := add_le_add hdec hgauss
            _ = (C₁ + 1) * (n : ℝ) ^ (-(2 : ℝ)) := by ring
        have hsub : {ω | ¬ (hh < max (r - innerRadius (X · ω) n) (maxRadius (X · ω) n - r) ∧
            (3 ≤ d → hh < maxRadius (X · ω) n - r))} ⊆ E₁ ∪ E₂ := by
          intro ω hω
          by_cases hA : hh < max (r - innerRadius (X · ω) n) (maxRadius (X · ω) n - r)
          · right
            have hB : ¬ (3 ≤ d → hh < maxRadius (X · ω) n - r) := fun hB => hω ⟨hA, hB⟩
            have hB' : maxRadius (X · ω) n - r ≤ hh := not_lt.mp fun h' => hB fun _ => h'
            show maxRadius (X · ω) n ≤ r + hh
            linarith
          · left
            have hA' := not_lt.mp hA
            exact ⟨by linarith [(max_le_iff.mp hA').1], by linarith [(max_le_iff.mp hA').2]⟩
        calc μ _ ≤ μ (E₁ ∪ E₂) := measure_mono hsub
          _ ≤ μ E₁ + μ E₂ := measure_union_le _ _
          _ ≤ ENNReal.ofReal (C₁ * (n : ℝ) ^ (-(2 : ℝ))) +
              ENNReal.ofReal ((C₁ + 1) * (n : ℝ) ^ (-(2 : ℝ))) := add_le_add hE₁le hE₂le
          _ = ENNReal.ofReal ((2 * C₁ + 1) * (n : ℝ) ^ (-(2 : ℝ))) := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1
              ring
      · have hsub : {ω | ¬ (hh < max (r - innerRadius (X · ω) n) (maxRadius (X · ω) n - r) ∧
            (3 ≤ d → hh < maxRadius (X · ω) n - r))} ⊆ E₁ := by
          intro ω hω
          by_cases hA : hh < max (r - innerRadius (X · ω) n) (maxRadius (X · ω) n - r)
          · exact absurd ⟨hA, fun h3 => absurd h3 hd3⟩ hω
          · have hA' := not_lt.mp hA
            exact ⟨by linarith [(max_le_iff.mp hA').1], by linarith [(max_le_iff.mp hA').2]⟩
        calc μ _ ≤ μ E₁ := measure_mono hsub
          _ ≤ ENNReal.ofReal (C₁ * (n : ℝ) ^ (-(2 : ℝ))) := hE₁le
          _ ≤ ENNReal.ofReal ((2 * C₁ + 1) * (n : ℝ) ^ (-(2 : ℝ))) :=
              ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right (by linarith) hnn)
    · have hlogn := log_le_of_pow_eq hκ hr1 hrκ hrn
      have hcoef : 0 ≤ ((d : ℝ) - 1) / (4 * C * ((d : ℝ) + 2)) := by positivity
      calc ((d : ℝ) - 1) / (4 * C * ((d : ℝ) + 2)) * Real.log n
          ≤ ((d : ℝ) - 1) / (4 * C * ((d : ℝ) + 2)) * (((d : ℝ) + 2) * Real.log r) :=
            mul_le_mul_of_nonneg_left hlogn hcoef
        _ = ((d : ℝ) - 1) * Real.log r / (4 * C) := by
            field_simp
  have hae := CERW.Support.Main.ae_eventually_of_le_rpow (μ := μ)
    (P := fun n ω => ((d : ℝ) - 1) * Real.log (radius d ε n) / (4 * C) <
        max (radius d ε n - innerRadius (X · ω) n) (maxRadius (X · ω) n - radius d ε n) ∧
      (3 ≤ d → ((d : ℝ) - 1) * Real.log (radius d ε n) / (4 * C) <
        maxRadius (X · ω) n - radius d ε n))
    (C := 2 * C₁ + 1) (p := 2) (by norm_num) (n₀ := max N₁ n₀)
    (fun n hn => (hkey n hn).1)
  filter_upwards [hae] with ω hω
  filter_upwards [hω, Filter.eventually_ge_atTop (max N₁ n₀)] with n hPn hn
  obtain ⟨h1, h2⟩ := hPn
  have h3 := (hkey n hn).2
  exact ⟨lt_of_le_of_lt h3 h1, fun h4 => lt_of_le_of_lt h3 (h2 h4)⟩

end AlmostSure

section Final

open CERW.Support.Statements CERW CERW.Support.Law

/-- Shrinking the constant `c` weakens an exponential bound `exp(-(c Y E))`. -/
private theorem exp_neg_mul_le {c c' Y E : ℝ} (hcc : c' ≤ c) (hY : 0 ≤ Y) (hE : 0 ≤ E) :
    Real.exp (-(c * Y * E)) ≤ Real.exp (-(c' * Y * E)) :=
  Real.exp_le_exp.mpr (neg_le_neg
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcc hY) hE))

/-- **Proposition 9.4** (`prop:log-lower`): lower bounds for the radii. -/
theorem log_lower_bounds_holds : log_lower_bounds.{u} := by
  intro d hd ωd ε hε hεd r
  have hr : r = radius d ε := rfl
  rw [hr]
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c, C, h₀, hc, hC, hh₀, n₀, hb⟩ := radii_tail_bounds hd hε hεd
  have hdm : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcstar : 0 < ((d : ℝ) - 1) / (4 * C * ((d : ℝ) + 2)) := by positivity
  set c' : ℝ := min c (((d : ℝ) - 1) / (4 * C * ((d : ℝ) + 2))) with hc'
  have hc'pos : 0 < c' := lt_min hc hcstar
  have hc'c : c' ≤ c := min_le_left _ _
  have hc'star : c' ≤ ((d : ℝ) - 1) / (4 * C * ((d : ℝ) + 2)) := min_le_right _ _
  refine ⟨c', C, h₀, hc'pos, hC, hh₀, n₀, ?_⟩
  intro Ω _ μ _ X hX
  refine ⟨?_, ?_⟩
  · intro n hn h hhh hhr
    obtain ⟨b1, b2⟩ := hb μ X hX n hn h hhh hhr
    have hr0 : 0 ≤ radius d ε n := radius_nonneg hd1 hε n
    have hY : 0 ≤ radius d ε n ^ (d - 1) := pow_nonneg hr0 _
    have hE : 0 ≤ Real.exp (-(C * h)) := (Real.exp_pos _).le
    have hZ : 0 ≤ radius d ε n ^ ((d : ℝ) - 3) := Real.rpow_nonneg hr0 _
    refine ⟨b1.trans (ENNReal.ofReal_le_ofReal (exp_neg_mul_le hc'c hY hE)), ?_⟩
    refine b2.trans (ENNReal.ofReal_le_ofReal (add_le_add (exp_neg_mul_le hc'c hY hE)
      (exp_neg_mul_le hc'c hZ (sq_nonneg h))))
  · have has := radii_as_bounds hd hε hc hC (fun n hn h hhh hhr => hb μ X hX n hn h hhh hhr)
    filter_upwards [has] with ω hω
    filter_upwards [hω, Filter.eventually_ge_atTop 1] with n hn hn1
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hmono : c' * Real.log n ≤ ((d : ℝ) - 1) / (4 * C * ((d : ℝ) + 2)) * Real.log n :=
      mul_le_mul_of_nonneg_right hc'star hlog
    exact ⟨lt_of_le_of_lt hmono hn.1, fun h3 => lt_of_le_of_lt hmono (hn.2 h3)⟩

end Final

end CERW.Support.Lower
