import CERW.Support.Drift.Dynkin
import CERW.Support.Occupation
import CERW.Support.LocalTime.DynkinLocal
import CERW.Support.LocalTime.Bracket

/-!
# Site-grouped shifted-square energy

The finite algebraic Dynkin identity for the shifted square in `lem:contact`, grouped
by occupation counts and first departures as in `eq:dynkin`.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb

/-- The occupation-weighted nearest-neighbour kernel energy in `lem:contact`. -/
noncomputable def kernelEnergy {d : ℕ} (g : Site d → ℝ)
    (X : ℕ → Site d) (n : ℕ) : ℝ :=
  (1 / (2 * (d : ℝ))) * ∑ x ∈ CERW.departureRange X n,
    (CERW.localTime X n x : ℝ) *
      ∑ e ∈ CERW.unitSteps d, (g (x + e) - g x) ^ 2

/-- Occupation grouping expresses the kernel energy as a sum over departure times. -/
theorem kernelEnergy_eq_time_sum {d : ℕ} (g : Site d → ℝ)
    (X : ℕ → Site d) (n : ℕ) :
    kernelEnergy g X n = (1 / (2 * (d : ℝ))) *
      ∑ j ∈ Finset.range n, ∑ e ∈ CERW.unitSteps d,
        (g (X j + e) - g (X j)) ^ 2 := by
  unfold kernelEnergy
  rw [CERW.Support.LocalTime.sum_range_eq_sum_localTime X n
    (fun x => ∑ e ∈ unitSteps d, (g (x + e) - g x) ^ 2)]

/-- The simple random walk Laplacian is the uniform average of increments. -/
private theorem walkOp_sub_eq {d : ℕ} (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    walkOp f x - f x = (1 / (2 * (d : ℝ))) *
      ∑ e ∈ unitSteps d, (f (x + e) - f x) := by
  have h : ∑ e ∈ unitSteps d, srwStep d e * (f (x + e) - f x) =
      walkOp f x - f x := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      CERW.Support.Law.sum_srwStep_mul, CERW.Support.Law.sum_srwStep hd, one_mul]
  rw [← h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨i, rfl | rfl⟩ := mem_unitSteps.mp he
  · rw [CERW.Support.Law.srwStep_unit]
  · rw [CERW.Support.Law.srwStep_neg_unit]

/-- Expansion of the shifted square separates its energy and Poisson terms. -/
private theorem shifted_square_laplacian {d : ℕ} (hd : 1 ≤ d)
    (g : Site d → ℝ) (γ : ℝ) (x : Site d) :
    walkOp (fun z => (g z - γ) ^ 2) x - (g x - γ) ^ 2 =
      (1 / (2 * (d : ℝ))) * ∑ e ∈ unitSteps d, (g (x + e) - g x) ^ 2 +
        2 * (g x - γ) * (walkOp g x - g x) := by
  rw [walkOp_sub_eq hd, walkOp_sub_eq hd]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- The site-grouped shifted-square Dynkin identity in `lem:contact`. -/
theorem shifted_square_energy_identity {d : ℕ} (hd : 1 ≤ d)
    (g : Site d → ℝ) (y : Site d)
    (hg : ∀ x, LatticeProb.walkOp g x - g x = if x = y then 1 else 0)
    (ε γ : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (hξ0 : ξ 0 = 0)
    (X : ℕ → Site d) (n : ℕ) :
    kernelEnergy g X n = 2 * (γ - g y) * (CERW.localTime X n y : ℝ) +
      (g (X n) - γ) ^ 2 - (g (X 0) - γ) ^ 2 -
      CERW.dynkinMart (CERW.driftStepProb d ε ξ) (fun z => (g z - γ) ^ 2) X n +
      ε * ∑ x ∈ CERW.departureRange X n,
        inner ℝ (ξ x) (CERW.Support.Law.centralDiff (fun z => (g z - γ) ^ 2) x) := by
  classical
  let f : Site d → ℝ := fun z => (g z - γ) ^ 2
  let b : Site d → ℝ := fun x => inner ℝ (ξ x) (CERW.Support.Law.centralDiff f x)
  have hb : b 0 = 0 := by simp [b, hξ0]
  have hdrift : (∑ j ∈ Finset.range n,
      if X j ≠ 0 ∧ X j ∉ (Finset.range j).image X then ε * b (X j) else 0) =
      ε * ∑ x ∈ departureRange X n, b x := by
    rw [← CERW.Support.Occupation.sum_fresh_eq_sum_departureRange X n b,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hz : X j = 0 <;> by_cases hf : X j ∈ (Finset.range j).image X <;>
      simp [hz, hf, hb]
  have hlap (x : Site d) : walkOp f x - f x =
      (1 / (2 * (d : ℝ))) * ∑ e ∈ unitSteps d, (g (x + e) - g x) ^ 2 +
        2 * (g y - γ) * (if x = y then 1 else 0) := by
    rw [shifted_square_laplacian hd g γ x, hg]
    split_ifs with h
    · subst x; rfl
    · ring
  have hstep (j : ℕ) : stepMean (driftStepProb d ε ξ) f X j =
      (1 / (2 * (d : ℝ))) * ∑ e ∈ unitSteps d, (g (X j + e) - g (X j)) ^ 2 +
        2 * (g y - γ) * (if X j = y then 1 else 0) -
        (if X j ≠ 0 ∧ X j ∉ (Finset.range j).image X then ε * b (X j) else 0) := by
    rw [CERW.Support.Drift.stepMean_driftStepProb hd,
      CERW.Support.Drift.driftNextMean, CERW.Support.Drift.sum_driftStepProb_mul]
    rw [sub_right_comm, hlap]
  have hsum := Finset.sum_congr (s₁ := Finset.range n) rfl (fun j _ => hstep j)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    CERW.Support.Occupation.sum_ite_eq_localTime, hdrift] at hsum
  rw [← kernelEnergy_eq_time_sum] at hsum
  change kernelEnergy g X n = 2 * (γ - g y) * (localTime X n y : ℝ) +
    f (X n) - f (X 0) - dynkinMart (driftStepProb d ε ξ) f X n +
    ε * ∑ x ∈ departureRange X n, b x
  unfold dynkinMart
  rw [hsum]
  ring

end CERW.LimitShapes.Energy
