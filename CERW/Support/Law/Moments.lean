import CERW.Model.Kernel

/-!
# The algebra of the first-departure kernel

The first-departure probabilities `q_x` of `eq:kernel` and the simple random walk step
probabilities are supported on the `2d` unit steps. They are nonnegative when `0 ≤ ε < 1/d`,
and they sum to one. The mean of `q_x` is `-ε u_x`, and the mean of a simple random walk step
is zero. The same holds for `stepProb`, whichever case applies.
-/

namespace CERW.Support.Law

open LatticeProb CERW

variable {d : ℕ}

/-- The map `i ↦ unit i` is injective. -/
theorem unit_injective : Function.Injective (unit : Fin d → Site d) := by
  intro i j h
  by_cases hij : j = i
  · exact hij.symm
  · have := congrFun h i
    simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)] at this

/-- `unit i` and `-unit j` are never equal, for any indices `i` and `j`. -/
theorem unit_ne_neg_unit' (i j : Fin d) : unit i ≠ -unit j := by
  intro h
  have := congrFun h i
  by_cases hij : j = i
  · subst hij
    simp [unit, Pi.single_eq_same] at this
  · simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)] at this

/-- A coordinate of a lattice site is at most its Euclidean norm in absolute value. -/
theorem abs_coord_le_euclidNorm (x : Site d) (i : Fin d) : |((x i : ℤ) : ℝ)| ≤ euclidNorm x := by
  rw [euclidNorm, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j : Fin d => ((x j : ℤ) : ℝ) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- A unit vector is not its own negative. -/
theorem unit_ne_neg_unit (i : Fin d) : unit i ≠ -unit i := unit_ne_neg_unit' i i

/-- A sum over the unit steps is the sum over coordinates of the values at `e_i` and `-e_i`. -/
theorem sum_unitSteps {M : Type*} [AddCommMonoid M] (f : Site d → M) :
    ∑ e ∈ unitSteps d, f e = ∑ i : Fin d, (f (unit i) + f (-unit i)) := by
  rw [unitSteps, Finset.sum_biUnion (by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact fun h => hij (unit_injective h)
    · exact unit_ne_neg_unit' i j
    · intro h
      have := congrFun h i
      simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne hij] at this
    · intro h
      have := congrFun h i
      simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne hij] at this)]
  simp only [Finset.sum_pair (unit_ne_neg_unit' _ _)]

/-- There are `2d` unit steps. -/
theorem card_unitSteps : (unitSteps d).card = 2 * d := by
  rw [Finset.card_eq_sum_ones]
  rw [sum_unitSteps (fun _ : Site d => (1 : ℕ))]
  simp [Finset.sum_const, mul_comm]

/-- Every unit step has Euclidean norm one. -/
theorem euclidNorm_of_mem_unitSteps {e : Site d} (he : e ∈ unitSteps d) : euclidNorm e = 1 := by
  rw [mem_unitSteps] at he
  obtain ⟨i, rfl | rfl⟩ := he
  · rw [euclidNorm]
    have h : ∑ j : Fin d, ((unit i j : ℤ) : ℝ) ^ 2 = 1 := by
      simp [unit, Pi.single_apply]
    rw [h, Real.sqrt_one]
  · rw [euclidNorm]
    have h : ∑ j : Fin d, (((-unit i) j : ℤ) : ℝ) ^ 2 = 1 := by
      simp [unit, Pi.single_apply]
    rw [h, Real.sqrt_one]

/-- The first-departure probability of the step `e_i`. -/
theorem firstStep_unit (ε : ℝ) (x : Site d) (i : Fin d) :
    firstStep d ε x (unit i) = 1 / (2 * d) - ε / 2 * (((x i : ℤ) : ℝ) / euclidNorm x) := by
  unfold firstStep
  rw [Finset.sum_eq_single i]
  · simp [unit_ne_neg_unit i]
  · intro j _ hj
    have h1 : unit i ≠ unit j := fun h => hj (unit_injective h).symm
    have h2 : unit i ≠ -unit j := unit_ne_neg_unit' i j
    simp [h1, h2]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The first-departure probability of the step `-e_i`. -/
theorem firstStep_neg_unit (ε : ℝ) (x : Site d) (i : Fin d) :
    firstStep d ε x (-unit i) = 1 / (2 * d) + ε / 2 * (((x i : ℤ) : ℝ) / euclidNorm x) := by
  unfold firstStep
  rw [Finset.sum_eq_single i]
  · simp [(unit_ne_neg_unit i).symm]
  · intro j _ hj
    have h1 : -unit i ≠ unit j := by
      intro h
      have := congrFun h i
      simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hj)] at this
    have h2 : -unit i ≠ -unit j := by
      intro h
      have := congrFun h i
      simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hj)] at this
    simp [h1, h2]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The first-departure probabilities vanish off the unit steps. -/
theorem firstStep_eq_zero (ε : ℝ) (x : Site d) {e : Site d} (he : e ∉ unitSteps d) :
    firstStep d ε x e = 0 := by
  unfold firstStep
  apply Finset.sum_eq_zero
  intro i _
  have h1 : e ≠ unit i := fun h => he (mem_unitSteps.mpr ⟨i, Or.inl h⟩)
  have h2 : e ≠ -unit i := fun h => he (mem_unitSteps.mpr ⟨i, Or.inr h⟩)
  simp [h1, h2]

/-- The simple random walk step probability of the step `e_i`. -/
theorem srwStep_unit (i : Fin d) : srwStep d (unit i) = 1 / (2 * d) := by
  unfold srwStep
  rw [Finset.sum_eq_single i]
  · simp [unit_ne_neg_unit i]
  · intro j _ hj
    have h1 : unit i ≠ unit j := fun h => hj (unit_injective h).symm
    have h2 : unit i ≠ -unit j := unit_ne_neg_unit' i j
    simp [h1, h2]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The simple random walk step probability of the step `-e_i`. -/
theorem srwStep_neg_unit (i : Fin d) : srwStep d (-unit i) = 1 / (2 * d) := by
  unfold srwStep
  rw [Finset.sum_eq_single i]
  · simp [(unit_ne_neg_unit i).symm]
  · intro j _ hj
    have h1 : -unit i ≠ unit j := by
      intro h
      have := congrFun h i
      simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hj)] at this
    have h2 : -unit i ≠ -unit j := by
      intro h
      have := congrFun h i
      simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hj)] at this
    simp [h1, h2]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The simple random walk step probabilities vanish off the unit steps. -/
theorem srwStep_eq_zero {e : Site d} (he : e ∉ unitSteps d) : srwStep d e = 0 := by
  unfold srwStep
  apply Finset.sum_eq_zero
  intro i _
  have h1 : e ≠ unit i := fun h => he (mem_unitSteps.mpr ⟨i, Or.inl h⟩)
  have h2 : e ≠ -unit i := fun h => he (mem_unitSteps.mpr ⟨i, Or.inr h⟩)
  simp [h1, h2]

/-- The normalized coordinate of a site has absolute value at most one. -/
theorem abs_coord_div_euclidNorm_le_one (x : Site d) (i : Fin d) :
    |((x i : ℤ) : ℝ) / euclidNorm x| ≤ 1 := by
  by_cases hx : euclidNorm x = 0
  · rw [hx, div_zero, abs_zero]
    norm_num
  · have hpos : 0 < euclidNorm x := lt_of_le_of_ne (euclidNorm_nonneg x) (Ne.symm hx)
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    exact abs_coord_le_euclidNorm x i

/-- The first-departure probabilities are nonnegative when `0 ≤ ε < 1/d`. -/
theorem firstStep_nonneg {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ)) (x e : Site d) :
    0 ≤ firstStep d ε x e := by
  have hhalf : ε / 2 < 1 / (2 * d) := by
    have h := div_lt_div_of_pos_right hεd (show (0 : ℝ) < 2 by norm_num)
    rw [div_div] at h
    simpa [mul_comm] using h
  unfold firstStep
  apply Finset.sum_nonneg
  intro i _
  set r := ((x i : ℤ) : ℝ) / euclidNorm x with hr
  have hcabs : |ε / 2 * r| ≤ ε / 2 := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ε / 2)]
    calc ε / 2 * |r| ≤ ε / 2 * 1 :=
          mul_le_mul_of_nonneg_left (abs_coord_div_euclidNorm_le_one x i) (by linarith)
      _ = ε / 2 := mul_one _
  have hcle : ε / 2 * r ≤ ε / 2 := (abs_le.mp hcabs).2
  have hclo : -ε / 2 ≤ ε / 2 * r := by linarith [(abs_le.mp hcabs).1]
  apply add_nonneg
  · split_ifs with h
    · exact sub_nonneg.mpr (le_of_lt (lt_of_le_of_lt hcle hhalf))
    · exact le_refl 0
  · split_ifs with h
    · linarith
    · exact le_refl 0

/-- The simple random walk step probabilities are nonnegative. -/
theorem srwStep_nonneg (e : Site d) : 0 ≤ srwStep d e := by
  unfold srwStep
  apply Finset.sum_nonneg
  intro i _
  apply add_nonneg <;> split_ifs <;> positivity

/-- The first-departure probabilities sum to one. -/
theorem sum_firstStep (hd : 1 ≤ d) (ε : ℝ) (x : Site d) :
    ∑ e ∈ unitSteps d, firstStep d ε x e = 1 := by
  rw [sum_unitSteps]
  have hpair : ∀ i : Fin d,
      firstStep d ε x (unit i) + firstStep d ε x (-unit i) = 1 / (d : ℝ) := by
    intro i
    rw [firstStep_unit, firstStep_neg_unit]
    ring
  simp_rw [hpair]
  have hdne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]
  exact div_self hdne

/-- The simple random walk step probabilities sum to one. -/
theorem sum_srwStep (hd : 1 ≤ d) : ∑ e ∈ unitSteps d, srwStep d e = 1 := by
  rw [sum_unitSteps]
  have hpair : ∀ i : Fin d, srwStep d (unit i) + srwStep d (-unit i) = 1 / (d : ℝ) := by
    intro i
    rw [srwStep_unit, srwStep_neg_unit]
    ring
  simp_rw [hpair]
  have hdne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]
  exact div_self hdne

/-- The embedding of the negative of a site is the negative of its embedding. -/
theorem toSpace_neg (x : Site d) : toSpace (-x) = -toSpace x := by
  apply PiLp.ext
  intro i
  simp [toSpace_apply]

/-- The embedding of a site is the sum of its coordinates times the embedded unit vectors. -/
theorem toSpace_eq_sum_unit (x : Site d) :
    toSpace x = ∑ i : Fin d, ((x i : ℤ) : ℝ) • toSpace (unit i) := by
  apply PiLp.ext
  intro j
  rw [toSpace_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [PiLp.smul_apply, toSpace_apply]
  rw [Finset.sum_eq_single j]
  · simp [unit, Pi.single_eq_same]
  · intro i _ hi
    simp [unit, Pi.single_eq_of_ne (Ne.symm hi)]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- The mean of the first-departure step from `x` is `-ε u_x`. -/
theorem sum_firstStep_smul (ε : ℝ) (x : Site d) :
    ∑ e ∈ unitSteps d, firstStep d ε x e • toSpace e = -ε • unitDir (toSpace x) := by
  rw [sum_unitSteps]
  have hpair : ∀ i : Fin d,
      firstStep d ε x (unit i) • toSpace (unit i) +
        firstStep d ε x (-unit i) • toSpace (-unit i) =
      (-ε * (((x i : ℤ) : ℝ) / euclidNorm x)) • toSpace (unit i) := by
    intro i
    rw [firstStep_unit, firstStep_neg_unit, toSpace_neg, smul_neg, ← sub_eq_add_neg, ← sub_smul]
    congr 1
    ring
  simp_rw [hpair]
  calc ∑ i : Fin d, (-ε * (((x i : ℤ) : ℝ) / euclidNorm x)) • toSpace (unit i)
      = ∑ i : Fin d, ((-ε * (euclidNorm x)⁻¹) * ((x i : ℤ) : ℝ)) •
          toSpace (unit i) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        rw [div_eq_mul_inv]
        ring
    _ = ∑ i : Fin d, (-ε * (euclidNorm x)⁻¹) •
          (((x i : ℤ) : ℝ) • toSpace (unit i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_smul]
    _ = (-ε * (euclidNorm x)⁻¹) •
          ∑ i : Fin d, ((x i : ℤ) : ℝ) • toSpace (unit i) := by
        rw [Finset.smul_sum]
    _ = (-ε * (euclidNorm x)⁻¹) • toSpace x := by rw [← toSpace_eq_sum_unit]
    _ = -ε • ((euclidNorm x)⁻¹ • toSpace x) := by rw [mul_smul]
    _ = -ε • unitDir (toSpace x) := by rw [unitDir, norm_toSpace]

/-- The mean of a simple random walk step is zero. -/
theorem sum_srwStep_smul : ∑ e ∈ unitSteps d, srwStep d e • toSpace e = 0 := by
  rw [sum_unitSteps]
  apply Finset.sum_eq_zero
  intro i _
  rw [srwStep_unit, srwStep_neg_unit, toSpace_neg, smul_neg, add_neg_cancel]

/-- The one-step probabilities are nonnegative when `0 ≤ ε < 1/d`. -/
theorem stepProb_nonneg {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ)) (x : ℕ → Site d)
    (n : ℕ) (e : Site d) : 0 ≤ stepProb d ε x n e := by
  unfold stepProb
  split_ifs with h
  · exact firstStep_nonneg hε hεd (x n) e
  · exact srwStep_nonneg e

/-- The one-step probabilities vanish off the unit steps. -/
theorem stepProb_eq_zero (ε : ℝ) (x : ℕ → Site d) (n : ℕ) {e : Site d} (he : e ∉ unitSteps d) :
    stepProb d ε x n e = 0 := by
  unfold stepProb
  split_ifs with h
  · exact firstStep_eq_zero ε (x n) he
  · exact srwStep_eq_zero he

/-- The one-step probabilities sum to one. -/
theorem sum_stepProb (hd : 1 ≤ d) (ε : ℝ) (x : ℕ → Site d) (n : ℕ) :
    ∑ e ∈ unitSteps d, stepProb d ε x n e = 1 := by
  unfold stepProb
  split_ifs with h
  · exact sum_firstStep hd ε (x n)
  · exact sum_srwStep hd

end CERW.Support.Law
