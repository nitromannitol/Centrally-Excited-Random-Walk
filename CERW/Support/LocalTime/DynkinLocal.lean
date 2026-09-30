import CERW.Support.Law.Dynkin
import CERW.Support.Law.StepMean
import CERW.Support.Occupation.FreshSum
import CERW.Support.Occupation.SiteArith

/-!
# The Dynkin decomposition of the local time

`eq:dynkin`: for a kernel `b` with `(P - I) b = 1_{0}` and a target `y`, the Dynkin martingale
`𝓜^y` of `b(X_j - y)` satisfies
`ℓ_n(y) = b(X_n - y) - b(-y) + ε Σ_{x ∈ A_n} u_x · Db(x - y) - 𝓜^y_n`
on every path from the origin. The compensator increment at time `j` is the visit indicator
`1{X_j = y}` minus the first-departure drift `ε I_j u_{X_j} · Db(X_j - y)`. A sum over first
departures is a sum over the departure range, and `u_0 = 0`.
-/

namespace CERW.Support.LocalTime

open LatticeProb CERW CERW.Support.Law CERW.Support.Occupation Finset

variable {d : ℕ}

/-- The walk operator commutes with translations. -/
theorem walkOp_comp_sub (b : Site d → ℝ) (x y : Site d) :
    walkOp (fun z => b (z - y)) x = walkOp b (x - y) := by
  simp only [walkOp, nbrSum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (x + unit i) - y = (x - y) + unit i by abel,
    show (x - unit i) - y = (x - y) - unit i by abel]

/-- The central difference commutes with translations. -/
theorem centralDiff_comp_sub (b : Site d → ℝ) (x y : Site d) :
    centralDiff (fun z => b (z - y)) x = centralDiff b (x - y) := by
  simp only [centralDiff]
  congr 1
  funext i
  rw [show (x + unit i) - y = (x - y) + unit i by abel,
    show (x - unit i) - y = (x - y) - unit i by abel]

/-- At the origin the first-departure drift vanishes, so the nonzero indicator may be dropped. -/
private theorem ite_ne_zero_drift (b : Site d → ℝ) (ε : ℝ) (y z : Site d) :
    (if z ≠ 0 then ε * inner ℝ (unitDir (toSpace z)) (centralDiff b (z - y)) else 0) =
      ε * inner ℝ (unitDir (toSpace z)) (centralDiff b (z - y)) := by
  by_cases hz : z = 0
  · subst z
    simp [toSpace_zero]
  · simp [hz]

/-- A sum of the first-departure drift over the departure range is unaffected by omitting `0`. -/
private theorem sum_departureRange_drift (b : Site d → ℝ) (ε : ℝ) (x : ℕ → Site d)
    (y : Site d) (n : ℕ) :
    ∑ z ∈ departureRange x n,
        (if z ≠ 0 then ε * inner ℝ (unitDir (toSpace z)) (centralDiff b (z - y)) else 0) =
      ε * ∑ z ∈ departureRange x n,
        inner ℝ (unitDir (toSpace z)) (centralDiff b (z - y)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => ite_ne_zero_drift b ε y z

/-- The Dynkin compensator increment of `b(· - y)` at time `j` is the visit indicator at `y`
minus the first-departure drift. -/
private theorem nextMean_sub_self {b : Site d → ℝ}
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0) (ε : ℝ)
    (x : ℕ → Site d) (y : Site d) (j : ℕ) :
    nextMean ε (fun z => b (z - y)) x j - b (x j - y) =
      (if x j = y then 1 else 0) -
        (if x j ≠ 0 ∧ x j ∉ (range j).image x then
          ε * inner ℝ (unitDir (toSpace (x j))) (centralDiff b (x j - y)) else 0) := by
  rw [show nextMean ε (fun z => b (z - y)) x j =
        walkOp (fun z => b (z - y)) (x j) -
          (if x j ≠ 0 ∧ x j ∉ (range j).image x then
            ε * inner ℝ (unitDir (toSpace (x j)))
              (centralDiff (fun z => b (z - y)) (x j)) else 0)
      from sum_stepProb_mul ε x j (fun z => b (z - y)),
    walkOp_comp_sub, centralDiff_comp_sub, sub_right_comm, hb (x j - y)]
  simp only [sub_eq_zero]

/-- The first-departure drift sum of the path `X` over first visits equals the drift sum over
its departure range, with the origin included only through the vanishing drift there. -/
private theorem sum_fresh_drift (b : Site d → ℝ) (ε : ℝ) {Ω : Type*}
    (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ) (y : Site d) :
    ∑ j ∈ range n,
        (if X j ω ≠ 0 ∧
            X j ω ∉ (range j).image (fun i => X i ω) then
          ε * inner ℝ (unitDir (toSpace (X j ω))) (centralDiff b (X j ω - y)) else 0) =
      ∑ z ∈ departureRange (fun i => X i ω) n,
        (if z ≠ 0 then ε * inner ℝ (unitDir (toSpace z)) (centralDiff b (z - y)) else 0) :=
  sum_fresh_ne_zero_eq_sum_departureRange (fun i => X i ω) n
    (fun z => ε * inner ℝ (unitDir (toSpace z)) (centralDiff b (z - y)))

/-- `eq:dynkin`, pathwise: if `(P - I) b = 1_{0}` and the path starts at the origin, then
`ℓ_n(y) = b(X_n - y) - b(-y) + ε Σ_{x ∈ A_n} u_x · Db(x - y) - 𝓜^y_n`. -/
theorem localTime_eq_dynkin {b : Site d → ℝ}
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0) (ε : ℝ) {Ω : Type*}
    (X : ℕ → Ω → Site d) (ω : Ω) (h0 : X 0 ω = 0) (n : ℕ) (y : Site d) :
    (localTime (fun j => X j ω) n y : ℝ) =
      b (X n ω - y) - b (-y) +
        ε * (∑ z ∈ departureRange (fun j => X j ω) n,
          inner ℝ (unitDir (toSpace z)) (centralDiff b (z - y))) -
        dynkin ε (fun z => b (z - y)) X n ω := by
  have hstep :
      ∑ j ∈ range n,
          (nextMean ε (fun z => b (z - y)) (fun i => X i ω) j - b (X j ω - y)) =
        (localTime (fun j => X j ω) n y : ℝ) -
          ε * ∑ z ∈ departureRange (fun j => X j ω) n,
              inner ℝ (unitDir (toSpace z)) (centralDiff b (z - y)) := by
    simp_rw [nextMean_sub_self hb ε (fun i => X i ω) y]
    rw [Finset.sum_sub_distrib, sum_ite_eq_localTime, sum_fresh_drift, sum_departureRange_drift]
  simp only [dynkin]
  rw [h0, zero_sub, hstep]
  ring

end CERW.Support.LocalTime
