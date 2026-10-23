import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Local potential error from square energy

Finite algebra for the local martingale estimate and Young absorption in Lemma `lem:contact`.
-/

namespace CERW.LimitShapes.Energy

/-- Abstract scale factors turn the square energy estimate into a local potential bound. -/
private theorem local_error_scales (A K C p q b δ L ell E V M U : ℝ)
    (hA : 0 < A) (hK : K = A ^ 2 + 2 * A + 1) (hC : C = K ^ 2 + 2 * K)
    (hL : 0 ≤ L) (hell : 0 ≤ ell) (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (hLδ : L ≤ δ) (hp : p * L = b ^ 2) (hq : q * L ≤ δ ^ 2)
    (hbδ : b ^ 2 ≤ δ) (hE : E ≤ A * (p * ell + q))
    (hV : V ≤ A * E) (hM : |M| ≤ A * (Real.sqrt (V * L) + L))
    (herr : |ell - U + M| ≤ A * L) :
    |ell - U| ≤ C * (δ + b * Real.sqrt ell) ∧
      ell / 2 - C * δ ≤ U ∧ (ell = 0 → |U| ≤ C * δ) := by
  have hK0 : 0 < K := by rw [hK]; positivity
  have hCK : K ≤ C := by rw [hC]; nlinarith [sq_nonneg K]
  have hs0 := Real.sqrt_nonneg ell
  have hs2 := Real.sq_sqrt hell
  have hx0 : 0 ≤ δ + b * Real.sqrt ell := by positivity
  have hv : V * L ≤ A ^ 2 * ((b * Real.sqrt ell) ^ 2 + δ ^ 2) := by
    have hvE := mul_le_mul_of_nonneg_right hV hL
    have heE := mul_le_mul_of_nonneg_left hE (le_of_lt hA)
    have heL := mul_le_mul_of_nonneg_right heE hL
    have hqA := mul_le_mul_of_nonneg_left hq (sq_nonneg A)
    have hid : A * (A * (p * ell + q)) * L =
        A ^ 2 * ((b * Real.sqrt ell) ^ 2 + q * L) := by
      rw [mul_pow, hs2, ← hp]
      ring
    rw [hid] at heL
    linarith
  have hroot : Real.sqrt (V * L) ≤ A * (b * Real.sqrt ell + δ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hcross : 0 ≤ (b * Real.sqrt ell) * δ := by positivity
      nlinarith [mul_nonneg (sq_nonneg A) hcross]
  have htri : |ell - U| ≤ |ell - U + M| + |M| := by
    have h := abs_add_le (ell - U + M) (-M)
    simpa only [add_neg_cancel_right, abs_neg] using h
  have hlocal : |ell - U| ≤ K * (δ + b * Real.sqrt ell) := by
    have hmroot := mul_le_mul_of_nonneg_left hroot hA.le
    have habs : 0 ≤ b * Real.sqrt ell := mul_nonneg hb hs0
    have hscale := mul_le_mul_of_nonneg_left hLδ (by positivity : 0 ≤ 2 * A)
    have hsurplus : 0 ≤ (2 * A + 1) * (b * Real.sqrt ell) := by positivity
    nlinarith
  have hyoung : K * (b * Real.sqrt ell) ≤ ell / 2 + K ^ 2 * δ / 2 := by
    have h := sq_nonneg (Real.sqrt ell - K * b)
    have hbK := mul_le_mul_of_nonneg_left hbδ (sq_nonneg K)
    nlinarith
  refine ⟨hlocal.trans (mul_le_mul_of_nonneg_right hCK hx0), ?_, ?_⟩
  · have hupper := (abs_le.mp hlocal).2
    have hδK := mul_le_mul_of_nonneg_right (sq_nonneg K) hδ
    rw [hC]
    nlinarith
  · intro heq
    subst ell
    simpa only [Real.sqrt_zero, mul_zero, add_zero, zero_sub, abs_neg] using
      hlocal.trans (mul_le_mul_of_nonneg_right hCK hx0)

/-- The local potential error and its one-sided consequence in Lemma `lem:contact`. -/
theorem exists_local_error_and_one_sided {d : ℕ} (hd : 2 ≤ d)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r L ell E V M U : ℝ),
      1 ≤ r → 1 ≤ L → L ^ 3 ≤ r → 0 ≤ ell → 0 ≤ E →
      E ≤ A * ((if d = 2 then L else 1) * ell + (if d = 2 then r else L)) →
      V ≤ A * E → |M| ≤ A * (Real.sqrt (V * L) + L) →
      |ell - U + M| ≤ A * L →
      let delta : ℝ := if d = 2 then Real.sqrt (r * L) else L
      |ell - U| ≤ C * (delta +
        (if d = 2 then L * Real.sqrt ell else Real.sqrt (ell * L))) ∧
      ell / 2 - C * delta ≤ U ∧ (ell = 0 → |U| ≤ C * delta) := by
  have _hd_used : 2 ≤ d := hd
  let K := A ^ 2 + 2 * A + 1
  let C := K ^ 2 + 2 * K
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro r L ell E V M U hr hL hcube hell _hE0 hE hV hM herr
  have hL0 : 0 ≤ L := by linarith
  have hr0 : 0 ≤ r := by linarith
  by_cases hd2 : d = 2
  · simp only [hd2, if_true] at hE ⊢
    have hδ0 := Real.sqrt_nonneg (r * L)
    have hδ2 := Real.sq_sqrt (mul_nonneg hr0 hL0)
    have hL2 : L ^ 2 ≤ Real.sqrt (r * L) := by
      have hc := mul_le_mul_of_nonneg_right hcube hL0
      nlinarith [sq_nonneg (L ^ 2 - Real.sqrt (r * L))]
    have hLδ : L ≤ Real.sqrt (r * L) := by nlinarith
    exact local_error_scales A K C L r L (Real.sqrt (r * L)) L ell E V M U
      hA rfl rfl hL0 hell hL0 hδ0 hLδ (by ring) (by rw [hδ2]) hL2
      hE hV hM herr
  · simp only [hd2, if_false, one_mul] at hE ⊢
    have hs2 := Real.sq_sqrt hL0
    have h := local_error_scales A K C 1 L (Real.sqrt L) L L ell E V M U
      hA rfl rfl hL0 hell (Real.sqrt_nonneg L) hL0 (le_refl L)
      (by simpa only [one_mul] using hs2.symm) (by nlinarith) (by rw [hs2])
      (by simpa only [one_mul] using hE) hV hM herr
    rw [Real.sqrt_mul hell, mul_comm (Real.sqrt ell) (Real.sqrt L)]
    exact h

end CERW.LimitShapes.Energy
