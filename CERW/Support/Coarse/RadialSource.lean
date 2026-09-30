import CERW.Support.Coarse.RadialDrift
import CERW.Support.Law.Dynkin
import CERW.Support.Occupation.FreshSum

/-!
# The source inequality of the radial test

`eq:radial-source`, pathwise. Let `φ = (b - h)_+` with `b ≤ h` on `|x| ≤ r - 1`, `b ≥ h` on
`|x| ≥ r + 1`, `(P - I) b = 1_{0}`, the gradient asymptotics beyond `R ≤ r + 3`, and the one-step
bound `|b(x + e) - b(x)| ≤ C_g (1 + |x|)^{1-d}`. The Dynkin identity for `φ(X_j)` then reads
`φ(X_n) = Σ_{j<n} [(P - I)φ(X_j) - ε I_j u_{X_j} · Dφ(X_j)] + W_n`. The terms with `|X_j| ≤ r - 2`
vanish. On the shell `r - 2 < |X_j| ≤ r + 3` they are at most `(1 + ε√d) C_g (r - 1)^{1-d}`. Beyond
the shell `(P - I)φ = 0` and the drift is at least `ω_d⁻¹ |x|^{1-d}` at each first departure. Since
`φ ≥ 0`,
`ε ω_d⁻¹ Σ_{x ∈ A_n, |x| > r + 3} |x|^{1-d} ≤ (1 + ε√d) C_g (r - 1)^{1-d} · #shell visits + |W_n|`.
-/

namespace CERW.Support.Coarse

open LatticeProb Finset CERW CERW.Support.Law CERW.Support.Occupation

variable {d : ℕ}

/-- The gradient bound forces `Cg ≥ 0`: at the origin its right side is `Cg * 1`. -/
private lemma Cg_nonneg_of {b : Site d → ℝ} {Cg : ℝ} (hd : 1 ≤ d)
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) :
    0 ≤ Cg := by
  have hd0 : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have he : unit ⟨0, hd0⟩ ∈ unitSteps d := mem_unitSteps.mpr ⟨_, Or.inl rfl⟩
  have h := hgrad 0 (unit ⟨0, hd0⟩) he
  have h1 : (1 + euclidNorm (0 : Site d)) ^ (1 - (d : ℝ)) = 1 := by simp
  rw [h1, mul_one] at h
  exact (abs_nonneg _).trans h

/-- The radial power is antitone past the exponent `1 - d ≤ 0`. -/
private lemma rpow_one_sub_le_of_le {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hd : 1 ≤ d) : c ^ (1 - (d : ℝ)) ≤ a ^ (1 - (d : ℝ)) :=
  Real.rpow_le_rpow_of_nonpos ha hac (by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith)

/-- On the shell, a one-step increment of `(b - h)_+` is at most `Cg (r - 1)^(1 - d)`. -/
private lemma max_sub_increment_le {b : Site d → ℝ} {h Cg r : ℝ} (hd : 1 ≤ d) (hr : 2 ≤ r)
    (hCg : 0 ≤ Cg)
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {x : Site d} (hx : r - 2 < euclidNorm x) {e : Site d} (he : e ∈ unitSteps d) :
    |max (b (x + e) - h) 0 - max (b x - h) 0| ≤ Cg * (r - 1) ^ (1 - (d : ℝ)) := by
  have hr1 : 0 < r - 1 := by linarith
  have hx1 : r - 1 ≤ 1 + euclidNorm x := by linarith
  have hpow : (1 + euclidNorm x) ^ (1 - (d : ℝ)) ≤ (r - 1) ^ (1 - (d : ℝ)) :=
    rpow_one_sub_le_of_le hr1 hx1 hd
  calc |max (b (x + e) - h) 0 - max (b x - h) 0|
      ≤ |b (x + e) - b x| := abs_max_sub_add_sub_le b h x e
    _ ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)) := hgrad x e he
    _ ≤ Cg * (r - 1) ^ (1 - (d : ℝ)) := mul_le_mul_of_nonneg_left hpow hCg

/-- If every neighbour value of `f` at `x` agrees with `f x` within `c`, then the walk operator
applied at `x` is within `c` of `f x`. -/
private lemma abs_walkOp_sub_le {f : Site d → ℝ} {x : Site d} {c : ℝ} (hd : 1 ≤ d)
    (h : ∀ e ∈ unitSteps d, |f (x + e) - f x| ≤ c) : |walkOp f x - f x| ≤ c := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have h2d : (0 : ℝ) < 2 * d := by positivity
  have hrepr : walkOp f x - f x = walkOp (fun y => f y - f x) x := by
    rw [walkOp_sub, walkOp_const hd]
  rw [hrepr, walkOp, nbrSum, abs_div, abs_of_pos h2d, div_le_iff₀ h2d]
  calc |∑ i : Fin d, ((f (x + unit i) - f x) + (f (x - unit i) - f x))|
      ≤ ∑ i : Fin d, |(f (x + unit i) - f x) + (f (x - unit i) - f x)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (c + c) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (abs_add_le _ _).trans ?_
        exact add_le_add (h (unit i) (mem_unitSteps.mpr ⟨i, Or.inl rfl⟩))
          (h (-unit i) (mem_unitSteps.mpr ⟨i, Or.inr rfl⟩))
    _ = c * (2 * (d : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Each coordinate of the central difference is at most `c` when every one-step increment of
`f` is at most `c`. -/
private lemma abs_centralDiff_coord_le {f : Site d → ℝ} {x : Site d} {c : ℝ}
    (h : ∀ e ∈ unitSteps d, |f (x + e) - f x| ≤ c) (i : Fin d) :
    ‖(centralDiff f x) i‖ ≤ c := by
  have h1 : |f (x + unit i) - f x| ≤ c := h (unit i) (mem_unitSteps.mpr ⟨i, Or.inl rfl⟩)
  have h2 : |f (x - unit i) - f x| ≤ c := h (-unit i) (mem_unitSteps.mpr ⟨i, Or.inr rfl⟩)
  have htri : |(f (x + unit i) - f x) - (f (x - unit i) - f x)| ≤ 2 * c := by
    have h := abs_sub_le (f (x + unit i) - f x) 0 (f (x - unit i) - f x)
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith
  have hcoord : (centralDiff f x) i =
      ((f (x + unit i) - f x) - (f (x - unit i) - f x)) / 2 := by
    simp only [centralDiff, PiLp.toLp_apply]
    ring
  rw [hcoord, Real.norm_eq_abs, abs_div]
  have h2abs : |(2 : ℝ)| = 2 := by norm_num
  rw [h2abs]
  linarith

/-- The norm of the central difference is at most `√d c` when every coordinate is at most `c`. -/
private lemma norm_centralDiff_le {f : Site d → ℝ} {x : Site d} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i : Fin d, ‖(centralDiff f x) i‖ ≤ c) :
    ‖centralDiff f x‖ ≤ Real.sqrt d * c := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ i : Fin d, ‖(centralDiff f x) i‖ ^ 2)
      ≤ √(∑ _i : Fin d, c ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
    _ = √((d : ℝ) * c ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = Real.sqrt d * c := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hc]

/-- The first-departure drift term at a shell site is at most `ε √d c`. -/
private lemma abs_smul_inner_centralDiff_le {f : Site d → ℝ} {x : Site d} {c ε : ℝ}
    (hε : 0 ≤ ε) (hc : 0 ≤ c) (h : ∀ i : Fin d, ‖(centralDiff f x) i‖ ≤ c) :
    |ε * inner ℝ (unitDir (toSpace x)) (centralDiff f x)| ≤ ε * Real.sqrt d * c := by
  have hnorm := norm_centralDiff_le hc h
  have hinner : |inner ℝ (unitDir (toSpace x)) (centralDiff f x)| ≤ ‖centralDiff f x‖ := by
    calc |inner ℝ (unitDir (toSpace x)) (centralDiff f x)|
        ≤ ‖unitDir (toSpace x)‖ * ‖centralDiff f x‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * ‖centralDiff f x‖ := by
          exact mul_le_mul_of_nonneg_right (norm_unitDir_le _) (norm_nonneg _)
      _ = ‖centralDiff f x‖ := one_mul _
  calc |ε * inner ℝ (unitDir (toSpace x)) (centralDiff f x)|
      = ε * |inner ℝ (unitDir (toSpace x)) (centralDiff f x)| := by
        rw [abs_mul, abs_of_nonneg hε]
    _ ≤ ε * ‖centralDiff f x‖ := mul_le_mul_of_nonneg_left hinner hε
    _ ≤ ε * (Real.sqrt d * c) := mul_le_mul_of_nonneg_left hnorm hε
    _ = ε * Real.sqrt d * c := by ring

/-- An `if`-then-zero is bounded by the bound on the branch value. -/
private lemma abs_ite_le_of_abs_le {P : Prop} [Decidable P] {A B : ℝ} (hA : |A| ≤ B)
    (hB : 0 ≤ B) : |(if P then A else 0)| ≤ B := by
  split_ifs with h
  · exact hA
  · simpa using hB

/-- If all neighbours of a function vanish at `x`, its walk operator vanishes there. -/
private lemma walkOp_eq_zero_of_nbr_eq_zero {f : Site d → ℝ} {x : Site d}
    (h : ∀ i : Fin d, f (x + unit i) = 0 ∧ f (x - unit i) = 0) : walkOp f x = 0 := by
  rw [walkOp, nbrSum]
  have hsum : (∑ i : Fin d, (f (x + unit i) + f (x - unit i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [(h i).1, (h i).2, add_zero]
  rw [hsum, zero_div]

/-- If a function has equal one-step increment on the forward and backward neighbours of `x`,
its central difference vanishes there. -/
private lemma centralDiff_eq_zero_of_nbr {f : Site d → ℝ} {x : Site d}
    (h : ∀ i : Fin d, f (x + unit i) = f (x - unit i)) : centralDiff f x = 0 := by
  apply PiLp.ext
  intro i
  simp only [centralDiff, PiLp.toLp_apply]
  rw [h i, sub_self, zero_div]
  rfl

/-- `eq:radial-source`, pathwise, for a path from the origin. -/
theorem radial_source {b : Site d → ℝ} {h r R Ca Cg ε : ℝ} (hd : 1 ≤ d) (hr : 2 ≤ r)
    (hε : 0 ≤ ε) (hin : ∀ x, euclidNorm x ≤ r - 1 → b x ≤ h)
    (hout : ∀ x, r + 1 ≤ euclidNorm x → h ≤ b x)
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0)
    (hgradA : ∀ x, R ≤ euclidNorm x →
      ‖centralDiff b x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x‖ ≤
        Ca * euclidNorm x ^ (-(d : ℝ)))
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (hR : R ≤ r + 3) (hCa : Ca * unitBallVolume d ≤ r + 3) {Ω : Type*} (X : ℕ → Ω → Site d)
    (ω : Ω) (h0 : X 0 ω = 0) (n : ℕ) :
    ε * (unitBallVolume d)⁻¹ *
        ∑ z ∈ (departureRange (fun j => X j ω) n).filter (fun z => r + 3 < euclidNorm z),
          euclidNorm z ^ (1 - (d : ℝ)) ≤
      (1 + ε * Real.sqrt d) * Cg * (r - 1) ^ (1 - (d : ℝ)) *
          ∑ j ∈ range n,
            (if r - 2 < euclidNorm (X j ω) ∧ euclidNorm (X j ω) ≤ r + 3 then (1 : ℝ) else 0) +
        |dynkin ε (fun z => max (b z - h) 0) X n ω| := by
  let φ : Site d → ℝ := fun z => max (b z - h) 0
  let x : ℕ → Site d := fun j => X j ω
  let K : ℝ := (1 + ε * Real.sqrt d) * Cg * (r - 1) ^ (1 - (d : ℝ))
  let T : ℕ → ℝ := fun j => walkOp φ (x j) - φ (x j)
  let S : ℕ → ℝ := fun j => if x j ≠ 0 ∧ x j ∉ (range j).image x then
      ε * inner ℝ (unitDir (toSpace (x j))) (centralDiff φ (x j)) else 0
  let c : ℕ → ℝ := fun j => if r + 3 < euclidNorm (x j) ∧ x j ≠ 0 ∧
      x j ∉ (range j).image x then
      ε * (unitBallVolume d)⁻¹ * euclidNorm (x j) ^ (1 - (d : ℝ)) else 0
  let sh : ℕ → ℝ := fun j =>
    if r - 2 < euclidNorm (x j) ∧ euclidNorm (x j) ≤ r + 3 then (1 : ℝ) else 0
  change ε * (unitBallVolume d)⁻¹ *
      ∑ z ∈ (departureRange x n).filter (fun z => r + 3 < euclidNorm z),
        euclidNorm z ^ (1 - (d : ℝ)) ≤
      K * ∑ j ∈ range n, sh j + |dynkin ε φ X n ω|
  have hCg : 0 ≤ Cg := Cg_nonneg_of hd hgrad
  have hr0 : 0 ≤ r := by linarith
  have hnext : ∀ j, nextMean ε φ x j - φ (x j) = T j - S j := by
    intro j
    change (∑ e ∈ unitSteps d, stepProb d ε x j e * φ (x j + e)) - φ (x j) =
      (walkOp φ (x j) - φ (x j)) -
        (if x j ≠ 0 ∧ x j ∉ (range j).image x then
          ε * inner ℝ (unitDir (toSpace (x j))) (centralDiff φ (x j)) else 0)
    rw [sum_stepProb_mul]
    ring
  have hterm : ∀ j, c j - K * sh j ≤ S j - T j := by
    intro j
    by_cases hA : euclidNorm (x j) ≤ r - 2
    · -- inside: both terms vanish
      have hne : ∀ i : Fin d, φ (x j + unit i) = 0 ∧ φ (x j - unit i) = 0 := by
        intro i
        exact ⟨(max_sub_eq_zero_of_le hin hA (mem_unitSteps.mpr ⟨i, Or.inl rfl⟩)).1,
          (max_sub_eq_zero_of_le hin hA (mem_unitSteps.mpr ⟨i, Or.inr rfl⟩)).1⟩
      have hφx : φ (x j) = 0 :=
        max_eq_right (sub_nonpos.mpr (hin (x j) (by linarith)))
      have hwalk : walkOp φ (x j) = 0 := walkOp_eq_zero_of_nbr_eq_zero hne
      have hcd : centralDiff φ (x j) = 0 := by
        apply centralDiff_eq_zero_of_nbr
        intro i
        rw [(hne i).1, (hne i).2]
      have hT : T j = 0 := by
        change walkOp φ (x j) - φ (x j) = 0
        rw [hwalk, hφx, sub_zero]
      have hS : S j = 0 := by
        change (if x j ≠ 0 ∧ x j ∉ (range j).image x then
            ε * inner ℝ (unitDir (toSpace (x j))) (centralDiff φ (x j)) else 0) = 0
        rw [hcd, inner_zero_right, mul_zero]
        split_ifs <;> rfl
      have hlt3 : ¬ r + 3 < euclidNorm (x j) := by linarith
      have hc0 : c j = 0 := by
        change (if r + 3 < euclidNorm (x j) ∧ x j ≠ 0 ∧
            x j ∉ (range j).image x then
            ε * (unitBallVolume d)⁻¹ * euclidNorm (x j) ^ (1 - (d : ℝ)) else 0) = 0
        rw [if_neg (fun hh => hlt3 hh.1)]
      have hsh : sh j = 0 := by
        change (if r - 2 < euclidNorm (x j) ∧ euclidNorm (x j) ≤ r + 3 then
          (1 : ℝ) else 0) = 0
        rw [if_neg (fun hh => (not_lt_of_ge hA) hh.1)]
      rw [hc0, hsh, hT, hS]
      simp
    · rw [not_le] at hA
      by_cases hC : r + 3 < euclidNorm (x j)
      · -- beyond the shell
        have hrd := radial_drift (d := d) hd hr0 hout hb hgradA hC (by linarith) (by linarith)
        have hT : T j = 0 := by
          change walkOp φ (x j) - φ (x j) = 0
          exact hrd.1
        have hS_ge : c j ≤ S j := by
          by_cases hcond : x j ≠ 0 ∧ x j ∉ (range j).image x
          · have hc : c j =
                ε * (unitBallVolume d)⁻¹ * euclidNorm (x j) ^ (1 - (d : ℝ)) := by
              change (if r + 3 < euclidNorm (x j) ∧ x j ≠ 0 ∧
                  x j ∉ (range j).image x then
                  ε * (unitBallVolume d)⁻¹ * euclidNorm (x j) ^ (1 - (d : ℝ)) else 0) = _
              rw [if_pos ⟨hC, hcond⟩]
            have hS : S j =
                ε * inner ℝ (unitDir (toSpace (x j))) (centralDiff φ (x j)) := by
              change (if x j ≠ 0 ∧ x j ∉ (range j).image x then
                  ε * inner ℝ (unitDir (toSpace (x j))) (centralDiff φ (x j)) else 0) = _
              rw [if_pos hcond]
            rw [hc, hS]
            calc ε * (unitBallVolume d)⁻¹ * euclidNorm (x j) ^ (1 - (d : ℝ))
                = ε * ((unitBallVolume d)⁻¹ * euclidNorm (x j) ^ (1 - (d : ℝ))) := by ring
              _ ≤ ε * inner ℝ (unitDir (toSpace (x j))) (centralDiff φ (x j)) :=
                  mul_le_mul_of_nonneg_left hrd.2 hε
          · have hc : c j = 0 := by
              change (if r + 3 < euclidNorm (x j) ∧ x j ≠ 0 ∧
                  x j ∉ (range j).image x then
                  ε * (unitBallVolume d)⁻¹ * euclidNorm (x j) ^ (1 - (d : ℝ)) else 0) = 0
              rw [if_neg (fun hh => hcond ⟨hh.2.1, hh.2.2⟩)]
            have hS : S j = 0 := by
              change (if x j ≠ 0 ∧ x j ∉ (range j).image x then
                  ε * inner ℝ (unitDir (toSpace (x j))) (centralDiff φ (x j)) else 0) = 0
              rw [if_neg hcond]
            rw [hc, hS]
        have hsh : sh j = 0 := by
          change (if r - 2 < euclidNorm (x j) ∧ euclidNorm (x j) ≤ r + 3 then
            (1 : ℝ) else 0) = 0
          rw [if_neg (fun hh => not_lt_of_ge hh.2 hC)]
        rw [hsh, hT]
        simp only [mul_zero, sub_zero]
        exact hS_ge
      · -- on the shell
        rw [not_lt] at hC
        have hincr : ∀ e ∈ unitSteps d,
            |φ (x j + e) - φ (x j)| ≤ Cg * (r - 1) ^ (1 - (d : ℝ)) :=
          fun e he => max_sub_increment_le hd hr hCg hgrad hA he
        have hcc : 0 ≤ Cg * (r - 1) ^ (1 - (d : ℝ)) :=
          mul_nonneg hCg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ r - 1) _)
        have hTle : |T j| ≤ Cg * (r - 1) ^ (1 - (d : ℝ)) := by
          change |walkOp φ (x j) - φ (x j)| ≤ Cg * (r - 1) ^ (1 - (d : ℝ))
          exact abs_walkOp_sub_le hd hincr
        have hSle : |S j| ≤ ε * Real.sqrt d * (Cg * (r - 1) ^ (1 - (d : ℝ))) := by
          change |(if x j ≠ 0 ∧ x j ∉ (range j).image x then
              ε * inner ℝ (unitDir (toSpace (x j))) (centralDiff φ (x j)) else 0)| ≤ _
          apply abs_ite_le_of_abs_le
          · exact abs_smul_inner_centralDiff_le hε hcc
              (fun i => abs_centralDiff_coord_le hincr i)
          · positivity
        have hbound : |T j - S j| ≤ K := by
          have hTS : |T j - S j| ≤ |T j| + |S j| := by
            have hh := abs_sub_le (T j) 0 (S j)
            simpa only [sub_zero, zero_sub, abs_neg] using hh
          calc |T j - S j| ≤ |T j| + |S j| := hTS
            _ ≤ Cg * (r - 1) ^ (1 - (d : ℝ)) +
                  ε * Real.sqrt d * (Cg * (r - 1) ^ (1 - (d : ℝ))) :=
                add_le_add hTle hSle
            _ = K := by
                change Cg * (r - 1) ^ (1 - (d : ℝ)) +
                    ε * Real.sqrt d * (Cg * (r - 1) ^ (1 - (d : ℝ))) =
                  (1 + ε * Real.sqrt d) * Cg * (r - 1) ^ (1 - (d : ℝ))
                ring
        have hc0 : c j = 0 := by
          change (if r + 3 < euclidNorm (x j) ∧ x j ≠ 0 ∧
              x j ∉ (range j).image x then
              ε * (unitBallVolume d)⁻¹ * euclidNorm (x j) ^ (1 - (d : ℝ)) else 0) = 0
          rw [if_neg (fun hh => not_lt_of_ge hC hh.1)]
        have hsh1 : sh j = 1 := by
          change (if r - 2 < euclidNorm (x j) ∧ euclidNorm (x j) ≤ r + 3 then
            (1 : ℝ) else 0) = 1
          rw [if_pos ⟨hA, hC⟩]
        rw [hc0, hsh1, mul_one, zero_sub]
        have : T j - S j ≤ K := (le_abs_self _).trans hbound
        linarith
  have hdyn : dynkin ε φ X n ω = φ (x n) - φ (x 0) - ∑ j ∈ range n, (T j - S j) := by
    have hsum_eq : (∑ j ∈ range n,
        (nextMean ε φ (fun i => X i ω) j - φ (X j ω))) =
        ∑ j ∈ range n, (T j - S j) :=
      Finset.sum_congr rfl fun j _ => hnext j
    change φ (X n ω) - φ (X 0 ω) -
        (∑ j ∈ range n, (nextMean ε φ (fun i => X i ω) j - φ (X j ω))) =
      φ (x n) - φ (x 0) - ∑ j ∈ range n, (T j - S j)
    rw [hsum_eq]
  have hφ0 : φ (x 0) = 0 := by
    have hx0 : x 0 = 0 := h0
    change max (b (x 0) - h) 0 = 0
    rw [hx0]
    exact max_eq_right (sub_nonpos.mpr (hin 0 (by rw [euclidNorm_zero]; linarith)))
  have hST : ∑ j ∈ range n, (S j - T j) ≤ |dynkin ε φ X n ω| := by
    have hsum : ∑ j ∈ range n, (S j - T j) = -∑ j ∈ range n, (T j - S j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hdyn' : dynkin ε φ X n ω = φ (x n) - ∑ j ∈ range n, (T j - S j) := by
      rw [hdyn, hφ0, sub_zero]
    have hrew : -∑ j ∈ range n, (T j - S j) =
        dynkin ε φ X n ω - φ (x n) := by
      linarith
    rw [hsum, hrew]
    exact (sub_le_self _ (le_max_right _ _)).trans (le_abs_self _)
  have hsum_c : ∑ j ∈ range n, c j =
      ε * (unitBallVolume d)⁻¹ *
        ∑ z ∈ (departureRange x n).filter (fun z => r + 3 < euclidNorm z),
          euclidNorm z ^ (1 - (d : ℝ)) := by
    let g : Site d → ℝ := fun z => if r + 3 < euclidNorm z then
        ε * (unitBallVolume d)⁻¹ * euclidNorm z ^ (1 - (d : ℝ)) else 0
    have h1 : ∑ j ∈ range n, c j =
        ∑ j ∈ range n, (if x j ≠ 0 ∧ x j ∉ (range j).image x then g (x j) else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      change (if r + 3 < euclidNorm (x j) ∧ x j ≠ 0 ∧
          x j ∉ (range j).image x then
          ε * (unitBallVolume d)⁻¹ * euclidNorm (x j) ^ (1 - (d : ℝ)) else 0) =
        (if x j ≠ 0 ∧ x j ∉ (range j).image x then g (x j) else 0)
      by_cases hcond : x j ≠ 0 ∧ x j ∉ (range j).image x
      · rw [if_pos hcond]
        simp only [g]
        by_cases hlt : r + 3 < euclidNorm (x j)
        · rw [if_pos hlt, if_pos ⟨hlt, hcond⟩]
        · rw [if_neg hlt, if_neg (fun hh => hlt hh.1)]
      · rw [if_neg hcond, if_neg (fun hh => hcond ⟨hh.2.1, hh.2.2⟩)]
    rw [h1, sum_fresh_ne_zero_eq_sum_departureRange x n g,
      Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z = 0
    · subst z
      rw [if_neg (by simp), if_neg (by rw [euclidNorm_zero]; linarith)]
    · rw [if_pos hz]
  have hterm_sum : ∑ j ∈ range n, (c j - K * sh j) ≤ ∑ j ∈ range n, (S j - T j) :=
    Finset.sum_le_sum fun j _ => hterm j
  have hcsh : ∑ j ∈ range n, (c j - K * sh j) =
      ∑ j ∈ range n, c j - K * ∑ j ∈ range n, sh j := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  calc ε * (unitBallVolume d)⁻¹ *
        ∑ z ∈ (departureRange x n).filter (fun z => r + 3 < euclidNorm z),
          euclidNorm z ^ (1 - (d : ℝ))
      = ∑ j ∈ range n, c j := hsum_c.symm
    _ = (∑ j ∈ range n, (c j - K * sh j)) + K * ∑ j ∈ range n, sh j := by
        rw [hcsh]
        ring
    _ ≤ (∑ j ∈ range n, (S j - T j)) + K * ∑ j ∈ range n, sh j :=
        by linarith [hterm_sum]
    _ ≤ |dynkin ε φ X n ω| + K * ∑ j ∈ range n, sh j := by linarith [hST]
    _ = K * ∑ j ∈ range n, sh j + |dynkin ε φ X n ω| := by ring


end CERW.Support.Coarse
