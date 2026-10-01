import CERW.Generic.Martingale.Lil.Statements

/-!
# The pathwise step

Along a path on which only finitely many blocks are hit, the truncation is eventually inactive
on the current block, so eventually `S_n ≤ (1 + δ) √(2 V_n log log V_n)`.
-/

universe u

namespace CERW.Generic.Martingale.Lil

open MeasureTheory ProbabilityTheory Filter Topology

/-- Below the gate the predictable stopping keeps every increment. -/
theorem predictableStop_eq_self_of_le {Ω : Type*} {S B : ℕ → Ω → ℝ} {b : ℝ} {n : ℕ} {ω : Ω}
    (h : ∀ j < n, B (j + 1) ω ≤ b) : predictableStop S B b n ω = S n ω - S 0 ω := by
  unfold predictableStop
  rw [← Finset.sum_range_sub (fun j => S j ω) n]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [bracketIndicator_of_le (h j (Finset.mem_range.mp hj)), one_mul]

/-- The truncation levels `b_k` tend to infinity. -/
theorem blockTrunc_eventually_ge {θ ε : ℝ} (hθ : 1 < θ) (hε : 0 < ε) (C : ℝ) :
    ∀ᶠ k in atTop, C ≤ blockTrunc θ ε k := by
  set M : ℝ := (C / ε) ^ 2 + 1 with hM
  have hMpos : 0 < M := by positivity
  have he : 1 < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog := Real.isLittleO_log_id_atTop.def (inv_pos.mpr hMpos)
  have hx : ∀ᶠ x : ℝ in atTop, Real.exp (Real.exp 1) < x ∧ Real.log x ≤ M⁻¹ * x :=
    (eventually_gt_atTop _).and (by
      filter_upwards [hlog, eventually_ge_atTop (0 : ℝ)] with x hx hx0
      simpa [Real.norm_eq_abs, abs_of_nonneg hx0] using (le_abs_self _).trans hx)
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt hθ).eventually hx] with k hk
  obtain ⟨hk1, hk2⟩ := hk
  have hxpos : 0 < θ ^ k := (Real.exp_pos _).trans hk1
  have hlog1 : 1 < Real.log (θ ^ k) := by
    rw [Real.lt_log_iff_exp_lt hxpos]
    exact (Real.exp_lt_exp.mpr he).trans hk1
  have hL0 : 0 < Real.log (Real.log (θ ^ k)) := Real.log_pos hlog1
  have hL1 : Real.log (Real.log (θ ^ k)) ≤ M⁻¹ * θ ^ k :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have h2 : M ≤ θ ^ k / Real.log (Real.log (θ ^ k)) := by
    rw [le_div_iff₀ hL0]
    have := mul_le_mul_of_nonneg_left hL1 hMpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hMpos.ne', one_mul] at this
    linarith
  have h3 : θ ^ k / Real.log (Real.log (θ ^ k)) ≤ θ ^ (k + 1) / Real.log (Real.log (θ ^ k)) := by
    refine div_le_div_of_nonneg_right ?_ hL0.le
    rw [pow_succ]
    exact le_mul_of_one_le_right hxpos.le hθ.le
  have h4 : |C / ε| ≤ Real.sqrt (θ ^ (k + 1) / Real.log (Real.log (θ ^ k))) :=
    Real.abs_le_sqrt (by linarith)
  unfold blockTrunc
  calc C = ε * (C / ε) := by field_simp
    _ ≤ ε * Real.sqrt (θ ^ (k + 1) / Real.log (Real.log (θ ^ k))) :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans h4) hε.le

/-- The gate `B ≤ ε √(V / log log (V ∨ e^e))` once the normalised ratio is below `ε`. -/
theorem le_mul_sqrt_of_lt {B V ε : ℝ} (hV : 0 < V)
    (hL : 0 < Real.log (Real.log (max V (Real.exp (Real.exp 1)))))
    (h : B * Real.sqrt (Real.log (Real.log (max V (Real.exp (Real.exp 1))))) / Real.sqrt V < ε) :
    B ≤ ε * Real.sqrt (V / Real.log (Real.log (max V (Real.exp (Real.exp 1))))) := by
  rw [Real.sqrt_div hV.le, ← mul_div_assoc]
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hsL : 0 < Real.sqrt (Real.log (Real.log (max V (Real.exp (Real.exp 1))))) :=
    Real.sqrt_pos.2 hL
  rw [div_lt_iff₀ hsV] at h
  rw [le_div_iff₀ hsL]
  linarith

/-- The pathwise step of the upper half. -/
theorem pathwiseUpper_of (hA : LilArith) : PathwiseUpper.{u} := by
  intro Ω S B V ω θ ε δ η hpar hS0 hVmono hV0 hV hB hblock
  obtain ⟨hθ, hε, hδ, _, _⟩ := hpar
  have hVm : Monotone (fun n => V n ω) := monotone_nat_of_le_succ hVmono
  have hVnn : ∀ n, 0 ≤ V n ω := fun n => hV0.symm.le.trans (hVm (Nat.zero_le n))
  have he : 1 < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hee : Real.exp 1 < Real.exp (Real.exp 1) := Real.exp_lt_exp.mpr he
  have hL1 : ∀ x : ℝ, Real.exp (Real.exp 1) ≤ x → 1 ≤ Real.log (Real.log x) := by
    intro x hx
    have h1 : Real.exp 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le hx)]
      exact hx
    have := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at this
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((hB.eventually_lt_const hε).and (hV.eventually_gt_atTop 0))
  have hBle : ∀ m ≥ N, B m ω ≤ ε * Real.sqrt (V m ω /
      Real.log (Real.log (max (V m ω) (Real.exp (Real.exp 1))))) := fun m hm =>
    le_mul_sqrt_of_lt (hN m hm).2 (lt_of_lt_of_le one_pos (hL1 _ (le_max_right _ _))) (hN m hm).1
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ m < N, B m ω ≤ C :=
    ⟨∑ m ∈ Finset.range N, |B m ω|, fun m hm => (le_abs_self _).trans
      (Finset.single_le_sum (f := fun m => |B m ω|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.2 hm))⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hblock.and ((blockTrunc_eventually_ge hθ hε C).and
    ((tendsto_pow_atTop_atTop_of_one_lt hθ).eventually_ge_atTop (Real.exp (Real.exp 1)))))
  filter_upwards [eventually_ge_atTop N, hV.eventually_ge_atTop (θ ^ K)] with n hnN hnV
  obtain ⟨-, -, hK3⟩ := hK K le_rfl
  have hVn1 : 1 ≤ V n ω :=
    le_trans (one_le_pow₀ hθ.le) hnV
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hVn1 hθ
  have hkK : K ≤ k := by
    by_contra hlt
    have hlt := not_le.mp hlt
    have : θ ^ (k + 1) ≤ θ ^ K := pow_le_pow_right₀ hθ.le hlt
    linarith
  obtain ⟨hk3, hk4, hk5⟩ := hK k hkK
  have hθk : Real.exp (Real.exp 1) ≤ θ ^ (k + 1) :=
    hk5.trans (pow_le_pow_right₀ hθ.le (Nat.le_succ k))
  have hLk : 0 < Real.log (Real.log (θ ^ k)) := lt_of_lt_of_le one_pos (hL1 _ hk5)
  have hxpos : 0 < θ ^ k := (Real.exp_pos _).trans_le hk5
  have hlogk : 0 < Real.log (θ ^ k) := Real.log_pos ((he.trans hee).trans_le hk5)
  have hLmono : Real.log (Real.log (θ ^ k)) ≤ Real.log (Real.log (θ ^ (k + 1))) :=
    Real.log_le_log hlogk (Real.log_le_log hxpos (pow_le_pow_right₀ hθ.le (Nat.le_succ k)))
  have hfk : (fun x : ℝ => x / Real.log (Real.log (max x (Real.exp (Real.exp 1)))))
      (θ ^ (k + 1)) ≤ θ ^ (k + 1) / Real.log (Real.log (θ ^ k)) := by
    simp only [max_eq_left hθk]
    exact div_le_div_of_nonneg_left (by positivity) hLk hLmono
  have hgate : ∀ j < n, B (j + 1) ω ≤ blockTrunc θ ε k := by
    intro j hj
    by_cases hm : j + 1 < N
    · exact (hC _ hm).trans hk4
    · have hm := not_lt.mp hm
      refine (hBle _ hm).trans ?_
      unfold blockTrunc
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hε.le
      have hVj : V (j + 1) ω ≤ θ ^ (k + 1) := ((hVm (Nat.succ_le_of_lt hj)).trans_lt hk2).le
      exact (hA.2.1 (Set.mem_Ici.2 (hVnn _)) (Set.mem_Ici.2 (hxpos.le.trans
        (pow_le_pow_right₀ hθ.le (Nat.le_succ k)))) hVj).trans hfk
  have hstop : predictableStop S B (blockTrunc θ ε k) n ω = S n ω := by
    rw [predictableStop_eq_self_of_le hgate, hS0, sub_zero]
  by_contra hcon
  have hcon := not_le.mp hcon
  apply hk3
  refine ⟨n, hk2.le, ?_⟩
  rw [hstop]
  unfold blockRadius
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by linarith)) hcon
  have hmono := hA.2.2 (Set.mem_Ici.2 (hee.le.trans hk5))
    (Set.mem_Ici.2 ((hee.le.trans hk5).trans hk1)) hk1
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left hmono (by norm_num)

end CERW.Generic.Martingale.Lil
