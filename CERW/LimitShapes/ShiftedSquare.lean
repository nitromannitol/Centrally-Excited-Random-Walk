module

public import CERW.LimitShapes.Event
public import CERW.Support.LocalTime.LatticeKernelFacts

@[expose] public section

/-!
# Bounded increments of the shifted-square kernel

The gradient decay and logarithmic growth of the lattice kernel bound increments
of `(g - γ)²` by a constant times `1 + |γ|`. This gives the increment scale in
`sec:norm-event` without restricting the spatial target.
-/

open LatticeProb

namespace CERW.LimitShapes.ShiftedSquare

open CERW

/-- Gradient decay and logarithmic growth imply a global increment bound for
shifted squares of the kernel. -/
theorem square_sub_step_le {d : ℕ} (hd : 2 ≤ d) {b : Site d → ℝ}
    {Cb Cg : ℝ} (hCb : 0 ≤ Cb) (hCg : 0 ≤ Cg)
    (hgrowth : ∀ x, |b x| ≤ Cb * Real.log (euclidNorm x + 2))
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (γ : ℝ) (x e : Site d) (he : e ∈ unitSteps d) :
    |(b (x + e) - γ) ^ 2 - (b x - γ) ^ 2| ≤ 5 * Cb * Cg + 2 * Cg * |γ| := by
  let u := 1 + euclidNorm x
  have hu : 1 ≤ u := by dsimp [u]; linarith [euclidNorm_nonneg x]
  have hu0 : 0 < u := by linarith
  have hnorm : euclidNorm (x + e) ≤ euclidNorm x + 1 := by
    simpa only [CERW.Support.Law.euclidNorm_of_mem_unitSteps he] using
      CERW.Support.Occupation.euclidNorm_add_le x e
  have hx : |b x| ≤ 2 * Cb * u := by
    calc |b x| ≤ Cb * Real.log (euclidNorm x + 2) := hgrowth x
      _ ≤ Cb * (euclidNorm x + 2) :=
        mul_le_mul_of_nonneg_left
          (Real.log_le_self (by linarith [euclidNorm_nonneg x])) hCb
      _ ≤ 2 * Cb * u := by dsimp [u]; nlinarith [euclidNorm_nonneg x]
  have hxe : |b (x + e)| ≤ 3 * Cb * u := by
    calc |b (x + e)| ≤ Cb * Real.log (euclidNorm (x + e) + 2) := hgrowth (x + e)
      _ ≤ Cb * (euclidNorm (x + e) + 2) :=
        mul_le_mul_of_nonneg_left
          (Real.log_le_self (by linarith [euclidNorm_nonneg (x + e)])) hCb
      _ ≤ 3 * Cb * u := by dsimp [u]; nlinarith [euclidNorm_nonneg x]
  have hsum : |b (x + e) + b x - 2 * γ| ≤ 5 * Cb * u + 2 * |γ| := by
    calc |b (x + e) + b x - 2 * γ| ≤ |b (x + e) + b x| + |2 * γ| := abs_sub _ _
      _ ≤ |b (x + e)| + |b x| + 2 * |γ| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 5 * Cb * u + 2 * |γ| := by linarith
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hexp : (1 - (d : ℝ)) ≤ 0 := by linarith
  have hexp' : (2 - (d : ℝ)) ≤ 0 := by linarith
  have hp0 : 0 ≤ u ^ (1 - (d : ℝ)) := Real.rpow_nonneg hu0.le _
  have hp1 : u ^ (1 - (d : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu hexp
  have hup : u * u ^ (1 - (d : ℝ)) ≤ 1 := by
    calc u * u ^ (1 - (d : ℝ)) = u ^ (1 : ℝ) * u ^ (1 - (d : ℝ)) := by
            rw [Real.rpow_one]
      _ = u ^ (2 - (d : ℝ)) := by
        rw [← Real.rpow_add hu0]
        congr 1
        ring
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu hexp'
  have hfactor : (b (x + e) - γ) ^ 2 - (b x - γ) ^ 2 =
      (b (x + e) - b x) * (b (x + e) + b x - 2 * γ) := by ring
  rw [hfactor, abs_mul]
  calc |b (x + e) - b x| * |b (x + e) + b x - 2 * γ|
      ≤ (Cg * u ^ (1 - (d : ℝ))) * (5 * Cb * u + 2 * |γ|) :=
        mul_le_mul (hgrad x e he) hsum (abs_nonneg _) (mul_nonneg hCg hp0)
    _ = 5 * Cb * Cg * (u * u ^ (1 - (d : ℝ))) +
        2 * Cg * |γ| * u ^ (1 - (d : ℝ)) := by ring
    _ ≤ 5 * Cb * Cg + 2 * Cg * |γ| := by
      have hleft := mul_le_mul_of_nonneg_left hup (show 0 ≤ 5 * Cb * Cg by positivity)
      have hright := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ 2 * Cg * |γ| by positivity)
      linarith

/-- The lattice kernel admits a global shifted-square increment constant in every
dimension at least two. -/
theorem exists_square_sub_step_bound {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (x e : Site d), e ∈ unitSteps d →
      |(latticeKernel d (x + e) - γ) ^ 2 - (latticeKernel d x - γ) ^ 2| ≤ C * (1 + |γ|) := by
  obtain ⟨_, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  obtain ⟨Cb, hCb⟩ := hK.growth
  obtain ⟨Cg, hCg⟩ := hK.gradBound
  have hCg0 := CERW.Support.Law.cg_nonneg (by omega : 1 ≤ d) hCg
  have hCb' : ∀ x, |latticeKernel d x| ≤ |Cb| * Real.log (euclidNorm x + 2) := by
    intro x
    exact (hCb x).trans (mul_le_mul_of_nonneg_right (le_abs_self Cb)
      (Real.log_nonneg (by linarith [euclidNorm_nonneg x])))
  refine ⟨5 * |Cb| * Cg + 2 * Cg + 1, by positivity, ?_⟩
  intro γ x e he
  have h := square_sub_step_le hd (abs_nonneg Cb) hCg0 hCb' hCg γ x e he
  have hprod : 0 ≤ 5 * |Cb| * Cg * |γ| := by positivity
  nlinarith [abs_nonneg γ]


/-- The kernel centering is bounded by a fixed multiple of `log n`, uniformly in time. -/
theorem exists_kernelShift_le_log {d : ℕ} (hd : 1 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → |kernelShift d Ψ ε n| ≤ C * Real.log n := by
  let a := ((d : ℝ) + 1) / (2 * d * ε * normBallVolume Ψ)
  let β := (1 : ℝ) / (d + 1)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hV := CERW.Support.Norm.ContactAssembly.normBallVolume_pos' hd hΨ
  have ha : 0 < a := by dsimp [a]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  have hπ : 0 < 2 / Real.pi := div_pos two_pos Real.pi_pos
  refine ⟨(2 / Real.pi) * β * (2 * |Real.log a| + 1) + 1, by positivity, ?_⟩
  intro n hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 1 / 2 ≤ Real.log n := by
    have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    have hmono := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hnR
    norm_num at h2
    linarith
  by_cases hd2 : d = 2
  · have hscale : CERW.Support.Norm.ContactEvent.scale d Ψ ε n = (a * n) ^ β := by
      unfold CERW.Support.Norm.ContactEvent.scale
      dsimp [a, β]
      congr 1
      ring
    have hlogscale : Real.log (CERW.Support.Norm.ContactEvent.scale d Ψ ε n) =
        β * (Real.log a + Real.log n) := by
      rw [hscale, Real.log_rpow (mul_pos ha hn0), Real.log_mul ha.ne' hn0.ne']
    rw [kernelShift, if_pos hd2, abs_mul, abs_of_pos hπ, hlogscale, abs_mul, abs_of_pos hβ]
    have hsum : |Real.log a + Real.log n| ≤ (2 * |Real.log a| + 1) * Real.log n := by
      have htri := abs_add_le (Real.log a) (Real.log n)
      rw [abs_of_nonneg (by linarith : 0 ≤ Real.log n)] at htri
      nlinarith [abs_nonneg (Real.log a)]
    calc (2 / Real.pi) * (β * |Real.log a + Real.log n|)
        ≤ (2 / Real.pi) * (β * ((2 * |Real.log a| + 1) * Real.log n)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hβ.le) hπ.le
      _ ≤ ((2 / Real.pi) * β * (2 * |Real.log a| + 1) + 1) * Real.log n := by
        nlinarith
  · rw [kernelShift, if_neg hd2, abs_zero]
    positivity

/-- The shifted-square kernels have the increment scale stated at `sec:norm-event`:
`log n` in dimension two and `1` in higher dimensions. -/
theorem exists_squareKernel_step_bound {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ y x e : Site d, e ∈ unitSteps d →
      |squareKernel Ψ ε n y (x + e) - squareKernel Ψ ε n y x| ≤
        C * (if d = 2 then Real.log n else 1) := by
  obtain ⟨B, hB, hstep⟩ := exists_square_sub_step_bound hd
  obtain ⟨G, hG, hshift⟩ := exists_kernelShift_le_log (by omega : 1 ≤ d) hΨ hε
  refine ⟨B * (2 + G), by positivity, ?_⟩
  intro n hn y x e he
  have h := hstep (kernelShift d Ψ ε n) (x - y) e he
  rw [← add_sub_right_comm] at h
  change |(latticeKernel d (x + e - y) - kernelShift d Ψ ε n) ^ 2 -
      (latticeKernel d (x - y) - kernelShift d Ψ ε n) ^ 2| ≤ _
  refine h.trans ?_
  by_cases hd2 : d = 2
  · rw [if_pos hd2]
    have hlog : 1 / 2 ≤ Real.log n := by
      have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
      have hmono := Real.log_le_log (show (0 : ℝ) < 2 by norm_num)
        (show (2 : ℝ) ≤ n by exact_mod_cast hn)
      norm_num at h2
      linarith
    have hs := hshift n hn
    have hb := mul_le_mul_of_nonneg_left hs hB.le
    nlinarith
  · rw [if_neg hd2, kernelShift, if_neg hd2, abs_zero]
    nlinarith

end CERW.LimitShapes.ShiftedSquare
