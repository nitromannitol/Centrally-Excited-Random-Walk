import CERW.Support.LocalTime.Bracket
import CERW.Generic.Martingale.Dyadic
import CERW.Generic.Martingale.Clamp
import CERW.Generic.Lattice.Centered

/-!
# The interval martingales of the local times

`eq:interval-mart`: for every `p > 0` there is `C` such that, for every `n ≥ 2`, with probability at
least `1 - Cn^{-p}`, simultaneously for all `0 ≤ s < t ≤ n` and all lattice targets `|y| ≤ 3n`,
`|𝓜^y_t - 𝓜^y_s| ≤ C e_n(M_{s,t})`. Here `e_n(m) = √m L + L` for `d = 2` and `√(mL) + L` for
`d ≥ 3`. Over `[s, t)` the bracket of `𝓜^y` is at most
`C_g² Σ_x ℓ_{s,t}(x) (1 + |x - y|)^{2-2d} ≤ C_g² M_{s,t} Σ_{x ∈ X[s,t)} (1 + |x - y|)^{2-2d}`.
The last sum is `O(L)` for `d = 2` (all sites within `4n` of `y`) and `O(1)` for `d ≥ 3`. Freedman's
inequality at dyadic brackets and a union bound over the `O(n^{d+2})` interval–target pairs finish.
-/

namespace CERW.Support.LocalTime

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law

variable {d : ℕ}

/-- The one-step bound forces `C_g ≥ 0`. -/
private lemma cg_nonneg (hd : 1 ≤ d) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) :
    0 ≤ Cg := by
  have h := hgrad 0 (unit ⟨0, by omega⟩) (mem_unitSteps.mpr ⟨⟨0, by omega⟩, Or.inl rfl⟩)
  have h' : |b (unit ⟨0, by omega⟩) - b 0| ≤ Cg := by simpa using h
  exact (abs_nonneg _).trans h'

/-- The Euclidean norm of a difference of lattice sites is at most the sum of the norms. -/
private lemma euclidNorm_sub_le (x y : Site d) :
    euclidNorm (x - y) ≤ euclidNorm x + euclidNorm y := by
  have h : toSpace (x - y) = toSpace x - toSpace y := by
    apply PiLp.ext
    intro i
    simp [toSpace_apply, Pi.sub_apply, Int.cast_sub]
  calc euclidNorm (x - y) = ‖toSpace (x - y)‖ := (norm_toSpace (x - y)).symm
    _ = ‖toSpace x - toSpace y‖ := by rw [h]
    _ ≤ ‖toSpace x‖ + ‖toSpace y‖ := norm_sub_le _ _
    _ = euclidNorm x + euclidNorm y := by rw [norm_toSpace, norm_toSpace]

/-- The predictable bracket `C_g² Σ_{j<t} (1 + |X_j - y|)^{2-2d}` of the translated Dynkin
martingale `𝓜^y`. -/
private noncomputable def bracket {Ω : Type*} (Cg : ℝ) (y : Site d) (X : ℕ → Ω → Site d)
    (t : ℕ) (ω : Ω) : ℝ :=
  Cg ^ 2 * ∑ j ∈ range t, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))

/-- A power of `1 + ρ` with nonpositive exponent is at most `1`. -/
private lemma rpow_one_add_le_one {ρ z : ℝ} (hρ : 0 ≤ ρ) (hz : z ≤ 0) : (1 + ρ) ^ z ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hz

/-- The bracket starts at `0`. -/
private lemma bracket_zero {Ω : Type*} (Cg : ℝ) (y : Site d) (X : ℕ → Ω → Site d) (ω : Ω) :
    bracket Cg y X 0 ω = 0 := by
  simp [bracket]

/-- The increment of the bracket is `C_g² (1 + |X_j - y|)^{2-2d}`. -/
private lemma bracket_succ_sub {Ω : Type*} (Cg : ℝ) (y : Site d) (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : bracket Cg y X (j + 1) ω - bracket Cg y X j ω =
      Cg ^ 2 * (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ)) := by
  simp only [bracket, sum_range_succ]
  ring

/-- The bracket is nondecreasing. -/
private lemma bracket_mono {Ω : Type*} (Cg : ℝ) (y : Site d) (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : bracket Cg y X j ω ≤ bracket Cg y X (j + 1) ω := by
  have h := bracket_succ_sub Cg y X j ω
  have h0 : 0 ≤ Cg ^ 2 * (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ)) :=
    mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (by linarith [euclidNorm_nonneg (X j ω - y)]) _)
  linarith

/-- The bracket increment over `[s, t)` is `C_g²` times the sum over `s ≤ j < t`. -/
private lemma bracket_sub {Ω : Type*} (Cg : ℝ) (y : Site d) (X : ℕ → Ω → Site d) {s t : ℕ}
    (hst : s ≤ t) (ω : Ω) : bracket Cg y X t ω - bracket Cg y X s ω =
      Cg ^ 2 * ∑ j ∈ Ico s t, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ)) := by
  rw [bracket, bracket, ← mul_sub, ← sum_Ico_eq_sub _ hst]

/-- The bracket increment over `s < t ≤ n` is at most `C_g² n`, as `1 ≤ d`. -/
private lemma bracket_sub_le (hd : 1 ≤ d) {Ω : Type*} (Cg : ℝ) (y : Site d)
    (X : ℕ → Ω → Site d) {s t n : ℕ} (hst : s ≤ t) (htn : t ≤ n) (ω : Ω) :
    bracket Cg y X t ω - bracket Cg y X s ω ≤ Cg ^ 2 * n := by
  rw [bracket_sub Cg y X hst]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  calc ∑ j ∈ Ico s t, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))
      ≤ ∑ _j ∈ Ico s t, (1 : ℝ) := by
        refine sum_le_sum fun j _ => rpow_one_add_le_one (euclidNorm_nonneg _) ?_
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
    _ = ((t - s : ℕ) : ℝ) := by simp
    _ ≤ n := by
        have : t - s ≤ n := by omega
        exact_mod_cast this

/-- The bracket at time `j + 1` is a function of the past path up to time `j`. -/
private lemma stronglyMeasurable_bracket_succ {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ n, Measurable (X n)) (Cg : ℝ) (y : Site d) (j : ℕ) :
    StronglyMeasurable[pathFiltration hX j] (bracket Cg y X (j + 1)) := by
  have h := stronglyMeasurable_comp_pastPath hX j
    (fun q => Cg ^ 2 * ∑ i ∈ range (j + 1),
      (1 + euclidNorm (extendPath q i - y)) ^ (2 - 2 * (d : ℝ)))
  have heq : bracket Cg y X (j + 1) = fun ω => Cg ^ 2 * ∑ i ∈ range (j + 1),
      (1 + euclidNorm (extendPath (pastPath X j ω) i - y)) ^ (2 - 2 * (d : ℝ)) := by
    funext ω
    simp only [bracket]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [extendPath_pastPath X (Nat.lt_succ_iff.mp (mem_range.mp hi)) ω]
  rw [heq]
  exact h

/-- The translated Dynkin martingale `𝓜^y` agrees almost surely with a martingale whose increments
are at most `2 C_g + 1` everywhere and whose conditional variances are at most the bracket
increments. -/
private lemma exists_clamped_translate (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (y : Site d) :
    ∃ M : ℕ → Ω → ℝ, Martingale M (pathFiltration hX.measurable) μ ∧
      (∀ i ω, |M (i + 1) ω - M i ω| ≤ 2 * Cg + 1) ∧
      (∀ j, μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | pathFiltration hX.measurable j] ≤ᵐ[μ]
        fun ω => bracket Cg y X (j + 1) ω - bracket Cg y X j ω) ∧
      ∀ᵐ ω ∂μ, ∀ i, M i ω = dynkin ε (fun z => b (z - y)) X i ω := by
  have hCg := cg_nonneg hd hgrad
  have hmart := martingale_dynkin hd hε hεd hX (fun z => b (z - y))
  have hinc : ∀ i, ∀ᵐ ω ∂μ, |dynkin ε (fun z => b (z - y)) X (i + 1) ω -
      dynkin ε (fun z => b (z - y)) X i ω| ≤ 2 * Cg + 1 := fun i =>
    (ae_abs_dynkin_translate_succ_sub_le hd hε hεd hX hgrad y).mono fun ω hω => by
      have h1 : (1 + euclidNorm (X i ω - y)) ^ (1 - (d : ℝ)) ≤ 1 :=
        rpow_one_add_le_one (euclidNorm_nonneg _) (by
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd
          linarith)
      have h2 := hω i
      nlinarith
  obtain ⟨M, hM, hbd, -, hae⟩ := CERW.Generic.Martingale.exists_martingale_clamp hmart
    (b := 2 * Cg + 1) (by linarith) hinc
  refine ⟨M, hM, hbd, fun j => ?_, hae⟩
  have hsq : (fun ω => (M (j + 1) ω - M j ω) ^ 2) =ᵐ[μ]
      fun ω => (dynkin ε (fun z => b (z - y)) X (j + 1) ω -
        dynkin ε (fun z => b (z - y)) X j ω) ^ 2 := by
    filter_upwards [hae] with ω hω
    rw [hω, hω]
  refine (condExp_congr_ae hsq).trans_le ?_
  filter_upwards [condExp_sq_dynkin_translate_le hd hε hεd hX hgrad y j] with ω hω
  rw [bracket_succ_sub]
  exact hω

/-- The interval maximum is at least one on a nonempty interval. -/
private lemma one_le_intervalMax (x : ℕ → Site d) {s t : ℕ} (hst : s < t) :
    1 ≤ intervalMax x s t := by
  have hs : s ∈ Ico s t := mem_Ico.mpr ⟨le_rfl, hst⟩
  have h1 : 1 ≤ intervalLocalTime x s t (x s) :=
    Finset.card_pos.mpr ⟨s, mem_filter.mpr ⟨hs, rfl⟩⟩
  exact h1.trans (Finset.le_sup (f := intervalLocalTime x s t) (mem_image_of_mem x hs))

/-- A sum over `s ≤ j < t` of a nonnegative function of the position is at most `M_{s,t}` times
the same function summed over the sites visited in `[s, t)`. -/
private lemma sum_Ico_le_intervalMax_mul (x : ℕ → Site d) (s t : ℕ) {g : Site d → ℝ}
    (hg : ∀ z, 0 ≤ g z) :
    ∑ j ∈ Ico s t, g (x j) ≤ (intervalMax x s t : ℝ) * ∑ z ∈ (Ico s t).image x, g z := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Ico s t) (t := (Ico s t).image x) (g := x)
    (f := fun i => g (x i)) (fun i hi => mem_image_of_mem x hi), Finset.mul_sum]
  refine sum_le_sum fun z _ => ?_
  have hinner : ∑ i ∈ (Ico s t).filter (fun i => x i = z), g (x i) =
      (intervalLocalTime x s t z : ℝ) * g z := by
    rw [sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2], sum_const, nsmul_eq_mul]
    rfl
  rw [hinner]
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast intervalLocalTime_le_intervalMax x s t z) (hg z)

/-- The sum of `(1 + |z - y|)^{2-2d}` over any set of sites within `4n` of `y` is `O(log n)`
for `d = 2` and `O(1)` for `d ≥ 3`. -/
private lemma exists_sum_image_le (hd : 2 ≤ d) :
    ∃ D : ℝ, 0 < D ∧ ∀ (x : ℕ → Site d) (n : ℕ), 1 ≤ n → (∀ j, euclidNorm (x j) ≤ j) →
      ∀ y : Site d, euclidNorm y ≤ 3 * n → ∀ s t : ℕ, t ≤ n →
        ∑ z ∈ (Ico s t).image x, (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)) ≤
          D * (if d = 2 then Real.log (n + 2) else 1) := by
  by_cases h2 : d = 2
  · obtain ⟨C, hC0, hC⟩ := CERW.Generic.Lattice.sum_finset_rpow_neg_le_log (d := d) (by omega)
    refine ⟨2 * C, by positivity, ?_⟩
    intro x n hn hx y hy s t htn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hR : ∀ z ∈ (Ico s t).image x, euclidNorm (z - y) ≤ 4 * n := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hz
      have hjn : (j : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hj).2.le.trans htn
      linarith [euclidNorm_sub_le (x j) y, hx j]
    have hexp : (2 - 2 * (d : ℝ)) = -(d : ℝ) := by subst h2; norm_num
    simp only [hexp]
    have h1 := hC ((Ico s t).image x) y (4 * n) (by linarith) hR
    have h3 : Real.log (4 * (n : ℝ) + 2) ≤ 2 * Real.log ((n : ℝ) + 2) := by
      have h4 := Real.log_le_log (by linarith : (0 : ℝ) < 4 * n + 2)
        (by nlinarith : 4 * (n : ℝ) + 2 ≤ ((n : ℝ) + 2) ^ 2)
      rw [Real.log_pow] at h4
      simpa using h4
    rw [if_pos h2]
    calc _ ≤ C * Real.log (4 * (n : ℝ) + 2) := h1
      _ ≤ C * (2 * Real.log ((n : ℝ) + 2)) := mul_le_mul_of_nonneg_left h3 hC0.le
      _ = 2 * C * Real.log ((n : ℝ) + 2) := by ring
  · obtain ⟨C, hC0, hC⟩ :=
      CERW.Generic.Lattice.sum_finset_rpow_two_sub_two_mul_le (d := d) (by omega)
    refine ⟨C, hC0, ?_⟩
    intro x n _ _ y _ s t _
    rw [if_neg h2, mul_one]
    exact hC _ y

/-- The error term `e_n(m) = √m L + L` for `d = 2` and `√(m L) + L` for `d ≥ 3`. -/
private noncomputable def errorBound (d : ℕ) (m L : ℝ) : ℝ :=
  if d = 2 then Real.sqrt m * L + L else Real.sqrt (m * L) + L

/-- The error term as `√(m Λ L) + L`, where `Λ = L` for `d = 2` and `Λ = 1` otherwise. -/
private lemma errorBound_eq {m L : ℝ} (hm : 0 ≤ m) (hL : 0 ≤ L) :
    errorBound d m L = Real.sqrt (m * (if d = 2 then L else 1) * L) + L := by
  unfold errorBound
  split_ifs with h
  · rw [show m * L * L = m * (L * L) by ring, Real.sqrt_mul hm, Real.sqrt_mul_self hL]
  · rw [mul_one]

/-- The deterministic step: on a path staying in the ball `|x_j| ≤ j`, the Freedman threshold
`c (√(max(V_t - V_s, 1) L) + B L)` is at most `C e_n(M_{s,t})`. -/
private lemma exists_det_bound (hd : 2 ≤ d) {Cg : ℝ} (hCg : 0 ≤ Cg) {c : ℝ} (hc : 1 ≤ c) :
    ∃ Cdet : ℝ, 0 < Cdet ∧ ∀ (x : ℕ → Site d) (n : ℕ), 2 ≤ n → (∀ j, euclidNorm (x j) ≤ j) →
      ∀ y : Site d, euclidNorm y ≤ 3 * n → ∀ s t : ℕ, s < t → t ≤ n →
        c * (Real.sqrt (max (Cg ^ 2 * ∑ j ∈ Ico s t,
              (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) 1 * Real.log (n + 2)) +
            (2 * Cg + 1) * Real.log (n + 2)) ≤
          Cdet * errorBound d (intervalMax x s t) (Real.log (n + 2)) := by
  obtain ⟨D, hD0, hD⟩ := exists_sum_image_le hd
  set A : ℝ := Cg ^ 2 * D with hA
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 < 2 * Cg + 1 := by linarith
  refine ⟨c * (Real.sqrt (A + 1) + (2 * Cg + 1)), by positivity, ?_⟩
  intro x n hn hx y hy s t hst htn
  set L : ℝ := Real.log (n + 2) with hLdef
  have hL1 : 1 ≤ L := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h4 : Real.log 4 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    have h5 : (1 : ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith [this]
    linarith
  have hL0 : 0 ≤ L := by linarith
  set m : ℝ := (intervalMax x s t : ℝ) with hm
  have hm1 : 1 ≤ m := by
    have h := one_le_intervalMax x hst
    rw [hm]
    exact_mod_cast h
  set Λ : ℝ := if d = 2 then L else 1 with hΛ
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ]
    split_ifs <;> linarith
  have hS : ∑ j ∈ Ico s t, (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ)) ≤ m * (D * Λ) :=
    (sum_Ico_le_intervalMax_mul x s t (g := fun z => (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)))
      (fun z => Real.rpow_nonneg (by linarith [euclidNorm_nonneg (z - y)]) _)).trans
      (mul_le_mul_of_nonneg_left (hD x n (by omega) hx y hy s t htn) (Nat.cast_nonneg _))
  have hmΛ : 1 ≤ m * Λ := by nlinarith
  have hmax : max (Cg ^ 2 * ∑ j ∈ Ico s t, (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) 1 ≤
      (A + 1) * (m * Λ) := by
    refine max_le ?_ (by nlinarith)
    calc Cg ^ 2 * ∑ j ∈ Ico s t, (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))
        ≤ Cg ^ 2 * (m * (D * Λ)) := mul_le_mul_of_nonneg_left hS (sq_nonneg _)
      _ = A * (m * Λ) := by rw [hA]; ring
      _ ≤ (A + 1) * (m * Λ) := by nlinarith
  set u : ℝ := Real.sqrt (m * Λ * L) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hsq : Real.sqrt (max (Cg ^ 2 * ∑ j ∈ Ico s t,
      (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) 1 * L) ≤ Real.sqrt (A + 1) * u := by
    rw [hu, ← Real.sqrt_mul (by linarith)]
    refine Real.sqrt_le_sqrt ?_
    calc _ ≤ (A + 1) * (m * Λ) * L := mul_le_mul_of_nonneg_right hmax hL0
      _ = (A + 1) * (m * Λ * L) := by ring
  rw [errorBound_eq (by linarith) hL0]
  have hsA : 0 ≤ Real.sqrt (A + 1) := Real.sqrt_nonneg _
  calc _ ≤ c * (Real.sqrt (A + 1) * u + (2 * Cg + 1) * L) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        linarith
    _ ≤ c * (Real.sqrt (A + 1) + (2 * Cg + 1)) * (u + L) := by
        have : Real.sqrt (A + 1) * u + (2 * Cg + 1) * L ≤
            (Real.sqrt (A + 1) + (2 * Cg + 1)) * (u + L) := by
          nlinarith [mul_nonneg hsA hL0, mul_nonneg hB0.le hu0]
        calc _ ≤ c * ((Real.sqrt (A + 1) + (2 * Cg + 1)) * (u + L)) :=
              mul_le_mul_of_nonneg_left this (by linarith)
          _ = _ := by ring

/-- One interval–target pair: Freedman's inequality at dyadic brackets, followed by the
deterministic step, bounds the probability that `𝓜^y_t - 𝓜^y_s` exceeds `C e_n(M_{s,t})`. -/
private lemma exists_event_bound (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ Cdet : ℝ, 0 < Cdet ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d}, IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        ∀ s t : ℕ, ∀ y : Site d, s < t → t ≤ n → euclidNorm y ≤ 3 * n →
          μ {ω | Cdet * errorBound d (intervalMax (fun j => X j ω) s t) (Real.log (n + 2)) <
              |dynkin ε (fun z => b (z - y)) X t ω - dynkin ε (fun z => b (z - y)) X s ω|} ≤
            ENNReal.ofReal (((Nat.clog 2 ⌈max (Cg ^ 2 * n) 1⌉₊ : ℕ) + 1) *
              (2 * Real.exp (-(K * Real.log (n + 2))))) := by
  have hd1 : 1 ≤ d := by omega
  have hCg := cg_nonneg hd1 hgrad
  obtain ⟨c, hc1, hc⟩ := CERW.Generic.Martingale.exists_dyadic_bound hK
  obtain ⟨Cdet, hCdet0, hCdet⟩ := exists_det_bound hd hCg hc1
  refine ⟨Cdet, hCdet0, ?_⟩
  intro Ω _ μ _ X hX n hn s t y hst htn hy
  obtain ⟨M, hM, hbd, hvar, hae⟩ := exists_clamped_translate hd1 hε hεd hX hgrad y
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst.le
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hL : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  have hW : (1 : ℝ) ≤ max (Cg ^ 2 * n) 1 := le_max_right _ _
  have hdy := hc hM (V := bracket Cg y X) (stronglyMeasurable_bracket_succ hX.measurable Cg y)
    (bracket_zero Cg y X) (bracket_mono Cg y X) hvar (b := 2 * Cg + 1) (by linarith) s k
    (fun i _ _ ω => hbd i ω) (W := max (Cg ^ 2 * n) 1) (L := Real.log ((n : ℝ) + 2)) hW hL
    (fun ω => (bracket_sub_le hd1 Cg y X (Nat.le_add_right s k) htn ω).trans (le_max_left _ _))
  refine le_trans (measure_mono_ae ?_) hdy
  filter_upwards [hae, ae_euclidNorm_le hd1 hε hεd hX] with ω hω hx hE
  change _ < _ at hE
  change _ < _
  rw [hω (s + k), hω s]
  refine lt_of_le_of_lt ?_ hE
  rw [bracket_sub Cg y X (Nat.le_add_right s k) ω]
  exact hCdet (fun j => X j ω) n hn hx y hy s (s + k) hst htn

/-- The error term is nonnegative. -/
private lemma errorBound_nonneg (m : ℝ) {L : ℝ} (hL : 0 ≤ L) : 0 ≤ errorBound d m L := by
  unfold errorBound
  split_ifs <;> positivity

/-- The base-two logarithm of `⌈W⌉₊`, plus one, is at most `(C_g² + 3)(n + 1)` when
`W = max (C_g² n) 1`. -/
private lemma clog_ceil_add_one_le (Cg : ℝ) (n : ℕ) :
    ((Nat.clog 2 ⌈max (Cg ^ 2 * n) 1⌉₊ : ℕ) : ℝ) + 1 ≤ (Cg ^ 2 + 3) * ((n : ℝ) + 1) := by
  have hclog : Nat.clog 2 ⌈max (Cg ^ 2 * n) 1⌉₊ ≤ ⌈max (Cg ^ 2 * n) 1⌉₊ :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have h1 : ((Nat.clog 2 ⌈max (Cg ^ 2 * n) 1⌉₊ : ℕ) : ℝ) ≤ (⌈max (Cg ^ 2 * n) 1⌉₊ : ℝ) := by
    exact_mod_cast hclog
  have h2 := Nat.ceil_lt_add_one (zero_le_one.trans (le_max_right (Cg ^ 2 * (n : ℝ)) 1))
  have h3 : max (Cg ^ 2 * (n : ℝ)) 1 ≤ Cg ^ 2 * n + 1 := max_le (by linarith) (by
    have := mul_nonneg (sq_nonneg Cg) (Nat.cast_nonneg (α := ℝ) n)
    linarith)
  have h4 : (0 : ℝ) ≤ Cg ^ 2 := sq_nonneg _
  have h5 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- The arithmetic of the union bound: `(n + 1)² (7 (n + 1))^D · G (n + 1) · 2 e^{-(p + D + 3) L}`
is at most `7^D G 2^{D+4} n^{-p}`. -/
private lemma union_bound_arith {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 1 ≤ n) (D : ℕ) {G : ℝ}
    (hG : 0 ≤ G) :
    (((n : ℝ) + 1) ^ 2 * (7 * ((n : ℝ) + 1)) ^ D) * ((G * ((n : ℝ) + 1)) *
      (2 * Real.exp (-((p + ((D + 3 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))) ≤
    (7 ^ D * G * 2 ^ (D + 4)) * (n : ℝ) ^ (-p) := by
  have h1 := CERW.Generic.Martingale.two_mul_exp_neg_mul_log_le
    (K := p + ((D + 3 : ℕ) : ℝ)) (by positivity) hn
  have h2 := CERW.Generic.Martingale.pow_mul_rpow_neg_le hn (D + 3) p
  have h3 : (0 : ℝ) ≤ 7 ^ D * G * ((n : ℝ) + 1) ^ (D + 3) := by positivity
  calc (((n : ℝ) + 1) ^ 2 * (7 * ((n : ℝ) + 1)) ^ D) * ((G * ((n : ℝ) + 1)) *
        (2 * Real.exp (-((p + ((D + 3 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))))
      = (7 ^ D * G * ((n : ℝ) + 1) ^ (D + 3)) *
          (2 * Real.exp (-((p + ((D + 3 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) := by
        rw [mul_pow]
        ring
    _ ≤ (7 ^ D * G * ((n : ℝ) + 1) ^ (D + 3)) * (2 * (n : ℝ) ^ (-(p + ((D + 3 : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left h1 h3
    _ = 2 * (7 ^ D * G) * (((n : ℝ) + 1) ^ (D + 3) * (n : ℝ) ^ (-(p + ((D + 3 : ℕ) : ℝ)))) := by
        ring
    _ ≤ 2 * (7 ^ D * G) * (2 ^ (D + 3) * (n : ℝ) ^ (-p)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (7 ^ D * G * 2 ^ (D + 4)) * (n : ℝ) ^ (-p) := by ring

/-- `eq:interval-mart`: under the one-step bound `|b(x + e) - b(x)| ≤ C_g (1 + |x|)^{1-d}`, with
probability at least `1 - Cn^{-p}`, `|𝓜^y_t - 𝓜^y_s| ≤ C e_n(M_{s,t})` for all `0 ≤ s < t ≤ n` and
all `|y| ≤ 3n`. -/
theorem exists_interval_mart (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      {X : ℕ → Ω → Site d}, IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ∃ s t : ℕ, ∃ y : Site d, s < t ∧ t ≤ n ∧ euclidNorm y ≤ 3 * n ∧
          C * (if d = 2 then
              Real.sqrt (intervalMax (fun j => X j ω) s t) * Real.log (n + 2) + Real.log (n + 2)
            else Real.sqrt (intervalMax (fun j => X j ω) s t * Real.log (n + 2)) +
              Real.log (n + 2)) <
            |dynkin ε (fun z => b (z - y)) X t ω - dynkin ε (fun z => b (z - y)) X s ω|} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  have hCg := cg_nonneg hd1 hgrad
  obtain ⟨Cdet, hCdet0, hCdet⟩ := exists_event_bound hd hε hεd hgrad
    (K := p + ((d + 3 : ℕ) : ℝ)) (by positivity)
  refine ⟨Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 4), by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hL0 : 0 ≤ Real.log ((n : ℝ) + 2) := (Real.log_pos (by linarith)).le
  set P : Finset (ℕ × ℕ) := ((range (n + 1)) ×ˢ (range (n + 1))).filter (fun q => q.1 < q.2)
    with hP
  set Y : Finset (Site d) := ballFinset d (3 * (n : ℝ)) with hY
  set B : ℕ × ℕ → Site d → Set Ω := fun q y =>
    {ω | Cdet * errorBound d (intervalMax (fun j => X j ω) q.1 q.2) (Real.log ((n : ℝ) + 2)) <
      |dynkin ε (fun z => b (z - y)) X q.2 ω - dynkin ε (fun z => b (z - y)) X q.1 ω|}
    with hB
  have hsub : {ω | ∃ s t : ℕ, ∃ y : Site d, s < t ∧ t ≤ n ∧ euclidNorm y ≤ 3 * n ∧
      (Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 4)) * (if d = 2 then
              Real.sqrt (intervalMax (fun j => X j ω) s t) * Real.log (n + 2) + Real.log (n + 2)
            else Real.sqrt (intervalMax (fun j => X j ω) s t * Real.log (n + 2)) +
              Real.log (n + 2)) <
            |dynkin ε (fun z => b (z - y)) X t ω - dynkin ε (fun z => b (z - y)) X s ω|} ⊆
      ⋃ q ∈ P, ⋃ y ∈ Y, B q y := by
    rintro ω ⟨s, t, y, hst, htn, hy, hlt⟩
    simp only [Set.mem_iUnion]
    refine ⟨(s, t), ?_, y, ?_, ?_⟩
    · simp only [hP, mem_filter, mem_product, mem_range]
      omega
    · rw [hY, mem_ballFinset_iff]
      exact hy
    · change Cdet * errorBound d _ _ < _
      have he := errorBound_nonneg (d := d) ((intervalMax (fun j => X j ω) s t : ℕ) : ℝ) hL0
      have hlt' : (Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 4)) *
          errorBound d (intervalMax (fun j => X j ω) s t) (Real.log ((n : ℝ) + 2)) <
            |dynkin ε (fun z => b (z - y)) X t ω - dynkin ε (fun z => b (z - y)) X s ω| := hlt
      have h7 : 0 ≤ 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 4) := by positivity
      nlinarith [mul_nonneg h7 he]
  have hbound : ∀ q ∈ P, ∀ y ∈ Y, μ (B q y) ≤ ENNReal.ofReal (((Cg ^ 2 + 3) * ((n : ℝ) + 1)) *
      (2 * Real.exp (-((p + ((d + 3 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))) := by
    intro q hq y hy
    have hq' := mem_filter.mp hq
    have h2 : q.2 ≤ n := by
      have := mem_range.mp (mem_product.mp hq'.1).2
      omega
    have hyn : euclidNorm y ≤ 3 * n := mem_ballFinset_iff.mp hy
    refine (hCdet hX n hn q.1 q.2 y hq'.2 h2 hyn).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (clog_ceil_add_one_le Cg n) (by positivity)
  have hPcard : (P.card : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have h1 : P.card ≤ (n + 1) * (n + 1) := by
      refine (card_filter_le _ _).trans ?_
      simp
    exact_mod_cast h1.trans_eq (by ring)
  have hYcard : (Y.card : ℝ) ≤ (7 * ((n : ℝ) + 1)) ^ d :=
    (card_ballFinset_le d (R := 3 * (n : ℝ)) (by positivity)).trans
      (pow_le_pow_left₀ (by positivity) (by linarith) d)
  set a : ℝ := ((Cg ^ 2 + 3) * ((n : ℝ) + 1)) *
    (2 * Real.exp (-((p + ((d + 3 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) with ha
  have ha0 : 0 ≤ a := by positivity
  refine (measure_mono hsub).trans ?_
  calc μ (⋃ q ∈ P, ⋃ y ∈ Y, B q y) ≤ ∑ q ∈ P, μ (⋃ y ∈ Y, B q y) := measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ P, ∑ y ∈ Y, μ (B q y) := sum_le_sum fun q _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ P, ∑ _y ∈ Y, ENNReal.ofReal a :=
        sum_le_sum fun q hq => sum_le_sum fun y hy => hbound q hq y hy
    _ = ENNReal.ofReal ((P.card : ℝ) * ((Y.card : ℝ) * a)) := by
        simp only [sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (p := (P.card : ℝ)) (Nat.cast_nonneg _),
          ENNReal.ofReal_mul (p := (Y.card : ℝ)) (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 4)) * (n : ℝ) ^ (-p)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (P.card : ℝ) * ((Y.card : ℝ) * a) ≤
            (((n : ℝ) + 1) ^ 2 * (7 * ((n : ℝ) + 1)) ^ d) * a := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hPcard hYcard (Nat.cast_nonneg _) (by positivity)) ha0
        have h2 := union_bound_arith hp.le (by omega : 1 ≤ n) d (G := Cg ^ 2 + 3) (by positivity)
        have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
        nlinarith [mul_nonneg hCdet0.le h3]

end CERW.Support.LocalTime
