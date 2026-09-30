import CERW.Support.Coarse.RadialDrift
import CERW.Support.Coarse.RadialBracket
import CERW.Support.LocalTime.Bracket
import CERW.Generic.Martingale.Dyadic
import CERW.Generic.Martingale.Clamp

/-!
# The radial martingales

`eq:radialbracket` and `eq:radialmart`. For an integer radius `r`, let `W^{(r)}` be the Dynkin
martingale of `φ_r = (b - h(r))_+`. The increments of `φ_r` vanish from `|x| ≤ r - 2`, and
elsewhere they are at most `C_g (1 + |x|)^{1-d} ≤ C_g (r - 1)^{1-d}`. So the bracket is at most
`C_g² Σ_{|x| > r - 2} ℓ_n(x) |x|^{2-2d} ≤ C r^{1-d} M_n F(r - b)`. The martingale
`r^{d-1} W^{(r)}` has bounded increments and bracket at most `C n`. Freedman's inequality at
dyadic brackets, and a union bound over the integers `r₀ ≤ r ≤ n`, give, with probability at least
`1 - Cn^{-p}`,
`|W^{(r)}_n| ≤ C [√(M_n r^{1-d} F(r - b) L) + r^{1-d} L]`.
-/

namespace CERW.Support.Coarse

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law

variable {d : ℕ}

/-- The one-step bound forces `C_g ≥ 0`. -/
private lemma cg_nonneg (hd : 1 ≤ d) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) :
    0 ≤ Cg := by
  have h := hgrad 0 (unit ⟨0, by omega⟩) (mem_unitSteps.mpr ⟨⟨0, by omega⟩, Or.inl rfl⟩)
  have h' : |b (unit ⟨0, by omega⟩) - b 0| ≤ Cg := by simpa using h
  exact (abs_nonneg _).trans h'

/-- The Dynkin martingale is linear: a constant factor passes through. -/
private lemma dynkin_const_mul {Ω : Type*} (ε c : ℝ) (g : Site d → ℝ) (X : ℕ → Ω → Site d)
    (t : ℕ) (ω : Ω) :
    dynkin ε (fun z => c * g z) X t ω = c * dynkin ε g X t ω := by
  have hnext : ∀ j, nextMean ε (fun z => c * g z) (fun i => X i ω) j =
      c * nextMean ε g (fun i => X i ω) j := by
    intro j
    simp only [nextMean, mul_sum]
    exact sum_congr rfl fun e _ => by ring
  have hsum : ∑ j ∈ range t, (nextMean ε (fun z => c * g z) (fun i => X i ω) j - c * g (X j ω)) =
      c * ∑ j ∈ range t, (nextMean ε g (fun i => X i ω) j - g (X j ω)) := by
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by rw [hnext j]; ring
  rw [dynkin, dynkin, hsum]
  ring

/-- The square root of a sum is at most the sum of the square roots. -/
private lemma sqrt_add_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- The increment of the scaled radial test at `x`: it vanishes for `|x| ≤ r - 2` and is at most
`c C_g (1 + |x|)^{1-d}` otherwise. -/
private lemma abs_osc_le {b : Site d → ℝ} {h r Cg c : ℝ} (hc : 0 ≤ c)
    (hin : ∀ x, euclidNorm x ≤ r - 1 → b x ≤ h)
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (x e : Site d) (he : e ∈ unitSteps d) :
    |c * max (b (x + e) - h) 0 - c * max (b x - h) 0| ≤
      if r - 2 < euclidNorm x then c * (Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) else 0 := by
  split_ifs with hx
  · rw [← mul_sub, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left
      ((abs_max_sub_add_sub_le b h x e).trans (hgrad x e he)) hc
  · obtain ⟨h1, h2⟩ := max_sub_eq_zero_of_le hin (not_lt.mp hx) he
    simp [h1, h2]

/-- The radial bracket term at a site: `(1 + |x|)^{2-2d}` when `|x| > r - 2` and `0` otherwise. -/
private noncomputable def radialTerm (d : ℕ) (r : ℝ) (x : Site d) : ℝ :=
  if r - 2 < euclidNorm x then (1 + euclidNorm x) ^ (2 - 2 * (d : ℝ)) else 0

/-- The radial bracket term is nonnegative. -/
private lemma radialTerm_nonneg (r : ℝ) (x : Site d) : 0 ≤ radialTerm d r x := by
  unfold radialTerm
  split_ifs
  · exact Real.rpow_nonneg (by linarith [euclidNorm_nonneg x]) _
  · exact le_rfl

/-- The square of `a^{1-d}` is `a^{2-2d}`. -/
private lemma rpow_one_sub_sq {a : ℝ} (ha : 0 ≤ a) :
    (a ^ (1 - (d : ℝ))) ^ 2 = a ^ (2 - 2 * (d : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  congr 1
  push_cast
  ring

/-- The squared increment of the scaled radial test is at most `c² C_g²` times the bracket term. -/
private lemma sq_osc_le {b : Site d → ℝ} {h r Cg c : ℝ} (hc : 0 ≤ c)
    (hin : ∀ x, euclidNorm x ≤ r - 1 → b x ≤ h)
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (x e : Site d) (he : e ∈ unitSteps d) :
    (c * max (b (x + e) - h) 0 - c * max (b x - h) 0) ^ 2 ≤
      c ^ 2 * Cg ^ 2 * radialTerm d r x := by
  have h1 := abs_osc_le hc hin hgrad x e he
  rw [← sq_abs]
  unfold radialTerm
  split_ifs at h1 ⊢ with hx
  · have h0 := abs_nonneg (c * max (b (x + e) - h) 0 - c * max (b x - h) 0)
    have hsq := pow_le_pow_left₀ h0 h1 2
    refine hsq.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, rpow_one_sub_sq (by linarith [euclidNorm_nonneg x])]
    ring
  · have h0 := abs_nonneg (c * max (b (x + e) - h) 0 - c * max (b x - h) 0)
    have : |c * max (b (x + e) - h) 0 - c * max (b x - h) 0| = 0 := le_antisymm h1 h0
    rw [this]
    simp

/-- The increment of the scaled radial test is at most `c C_g (r - 1)^{1-d}` at every site. -/
private lemma abs_osc_le_uniform {b : Site d → ℝ} {h r Cg c : ℝ} (hd : 1 ≤ d) (hc : 0 ≤ c)
    (hCg : 0 ≤ Cg) (hr : 1 < r) (hin : ∀ x, euclidNorm x ≤ r - 1 → b x ≤ h)
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (x e : Site d) (he : e ∈ unitSteps d) :
    |c * max (b (x + e) - h) 0 - c * max (b x - h) 0| ≤ c * (Cg * (r - 1) ^ (1 - (d : ℝ))) := by
  have h1 := abs_osc_le hc hin hgrad x e he
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine h1.trans ?_
  split_ifs with hx
  · refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hCg) hc
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  · exact mul_nonneg hc (mul_nonneg hCg (Real.rpow_nonneg (by linarith) _))

/-- The predictable bracket `c² C_g² Σ_{j<t} radialTerm (X_j)` of the scaled radial
martingale. -/
private noncomputable def radialBracket {Ω : Type*} (c Cg r : ℝ) (X : ℕ → Ω → Site d)
    (t : ℕ) (ω : Ω) : ℝ :=
  c ^ 2 * Cg ^ 2 * ∑ j ∈ range t, radialTerm d r (X j ω)

/-- The bracket starts at `0`. -/
private lemma radialBracket_zero {Ω : Type*} (c Cg r : ℝ) (X : ℕ → Ω → Site d) (ω : Ω) :
    radialBracket c Cg r X 0 ω = 0 := by
  simp [radialBracket]

/-- The increment of the bracket is `c² C_g²` times the bracket term at the current site. -/
private lemma radialBracket_succ_sub {Ω : Type*} (c Cg r : ℝ) (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : radialBracket c Cg r X (j + 1) ω - radialBracket c Cg r X j ω =
      c ^ 2 * Cg ^ 2 * radialTerm d r (X j ω) := by
  simp only [radialBracket, sum_range_succ]
  ring

/-- The bracket is nondecreasing. -/
private lemma radialBracket_mono {Ω : Type*} (c Cg r : ℝ) (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : radialBracket c Cg r X j ω ≤ radialBracket c Cg r X (j + 1) ω := by
  have h := radialBracket_succ_sub c Cg r X j ω
  have h0 : 0 ≤ c ^ 2 * Cg ^ 2 * radialTerm d r (X j ω) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (radialTerm_nonneg r _)
  linarith

/-- The bracket at time `j + 1` is a function of the past path up to time `j`. -/
private lemma stronglyMeasurable_radialBracket_succ {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ n, Measurable (X n)) (c Cg r : ℝ) (j : ℕ) :
    StronglyMeasurable[pathFiltration hX j] (radialBracket c Cg r X (j + 1)) := by
  have h := stronglyMeasurable_comp_pastPath hX j
    (fun q => c ^ 2 * Cg ^ 2 * ∑ i ∈ range (j + 1), radialTerm d r (extendPath q i))
  have heq : radialBracket c Cg r X (j + 1) = fun ω => c ^ 2 * Cg ^ 2 *
      ∑ i ∈ range (j + 1), radialTerm d r (extendPath (pastPath X j ω) i) := by
    funext ω
    simp only [radialBracket]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [extendPath_pastPath X (Nat.lt_succ_iff.mp (mem_range.mp hi)) ω]
  rw [heq]
  exact h

/-- Every bracket term is at most `((r - 1)^{1-d})²`. -/
private lemma radialTerm_le (hd : 1 ≤ d) {r : ℝ} (hr : 1 < r) (x : Site d) :
    radialTerm d r x ≤ ((r - 1) ^ (1 - (d : ℝ))) ^ 2 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [rpow_one_sub_sq (by linarith)]
  unfold radialTerm
  split_ifs with hx
  · exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  · exact Real.rpow_nonneg (by linarith) _

/-- Surely, the bracket at time `t` is at most `(C_g Q)² t`, where `c (r - 1)^{1-d} ≤ Q`. -/
private lemma radialBracket_le (hd : 1 ≤ d) {c Cg r Q : ℝ} (hc : 0 ≤ c) (hr : 1 < r)
    (hQ : c * (r - 1) ^ (1 - (d : ℝ)) ≤ Q) {Ω : Type*} (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) :
    radialBracket c Cg r X t ω ≤ (Cg * Q) ^ 2 * t := by
  have hsum : ∑ j ∈ range t, radialTerm d r (X j ω) ≤ t * ((r - 1) ^ (1 - (d : ℝ))) ^ 2 := by
    calc ∑ j ∈ range t, radialTerm d r (X j ω)
        ≤ ∑ _j ∈ range t, ((r - 1) ^ (1 - (d : ℝ))) ^ 2 :=
          sum_le_sum fun j _ => radialTerm_le hd hr _
      _ = t * ((r - 1) ^ (1 - (d : ℝ))) ^ 2 := by simp
  have h0 : 0 ≤ c * (r - 1) ^ (1 - (d : ℝ)) :=
    mul_nonneg hc (Real.rpow_nonneg (by linarith) _)
  have hsq := pow_le_pow_left₀ h0 hQ 2
  calc radialBracket c Cg r X t ω
      ≤ c ^ 2 * Cg ^ 2 * (t * ((r - 1) ^ (1 - (d : ℝ))) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = Cg ^ 2 * (c * (r - 1) ^ (1 - (d : ℝ))) ^ 2 * t := by ring
    _ ≤ Cg ^ 2 * Q ^ 2 * t := by
        gcongr
    _ = (Cg * Q) ^ 2 * t := by ring

/-- The scaled Dynkin martingale of the radial test agrees almost surely with a martingale whose
increments are at most `B` everywhere and whose conditional variances are at most the bracket
increments. -/
private lemma exists_clamped_radial (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) {b : Site d → ℝ} {h r Cg c Q B : ℝ}
    (hc : 0 ≤ c) (hCg : 0 ≤ Cg) (hr : 1 < r) (hin : ∀ x, euclidNorm x ≤ r - 1 → b x ≤ h)
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (hQ : c * (r - 1) ^ (1 - (d : ℝ)) ≤ Q) (hB : 2 * (Cg * Q) ≤ B) :
    ∃ M : ℕ → Ω → ℝ, Martingale M (pathFiltration hX.measurable) μ ∧
      (∀ i ω, |M (i + 1) ω - M i ω| ≤ B) ∧
      (∀ j, μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | pathFiltration hX.measurable j] ≤ᵐ[μ]
        fun ω => radialBracket c Cg r X (j + 1) ω - radialBracket c Cg r X j ω) ∧
      ∀ᵐ ω ∂μ, ∀ i, M i ω = c * dynkin ε (fun z => max (b z - h) 0) X i ω := by
  set f : Site d → ℝ := fun z => c * max (b z - h) 0 with hf
  have hmart := martingale_dynkin hd hε hεd hX f
  have hT0 : 0 ≤ c * (r - 1) ^ (1 - (d : ℝ)) :=
    mul_nonneg hc (Real.rpow_nonneg (by linarith) _)
  have hB0 : 0 ≤ B := by nlinarith
  have hinc : ∀ i, ∀ᵐ ω ∂μ, |dynkin ε f X (i + 1) ω - dynkin ε f X i ω| ≤ B := fun i =>
    (ae_abs_dynkin_succ_sub_le hd hε hεd hX f).mono fun ω hω => by
      refine (hω i (c * (Cg * (r - 1) ^ (1 - (d : ℝ)))) fun e he =>
        abs_osc_le_uniform hd hc hCg hr hin hgrad (X i ω) e he).trans ?_
      nlinarith [mul_le_mul_of_nonneg_left hQ hCg]
  obtain ⟨M, hM, hbd, -, hae⟩ := CERW.Generic.Martingale.exists_martingale_clamp hmart hB0 hinc
  refine ⟨M, hM, hbd, fun j => ?_, hae.mono fun ω hω i => ?_⟩
  · have hsq : (fun ω => (M (j + 1) ω - M j ω) ^ 2) =ᵐ[μ]
        fun ω => (dynkin ε f X (j + 1) ω - dynkin ε f X j ω) ^ 2 := by
      filter_upwards [hae] with ω hω
      rw [hω, hω]
    refine (condExp_congr_ae hsq).trans_le ?_
    filter_upwards [condExp_sq_dynkin_succ_sub_le hd hε hεd hX f j] with ω hω
    refine hω.trans ?_
    rw [radialBracket_succ_sub]
    calc ∑ e ∈ unitSteps d, stepProb d ε (fun i => X i ω) j e * (f (X j ω + e) - f (X j ω)) ^ 2
        ≤ ∑ e ∈ unitSteps d, stepProb d ε (fun i => X i ω) j e *
            (c ^ 2 * Cg ^ 2 * radialTerm d r (X j ω)) := by
          refine sum_le_sum fun e he => mul_le_mul_of_nonneg_left ?_
            (stepProb_nonneg hε hεd _ j e)
          exact sq_osc_le hc hin hgrad (X j ω) e he
      _ = c ^ 2 * Cg ^ 2 * radialTerm d r (X j ω) := by
          rw [← sum_mul, sum_stepProb hd ε _ j, one_mul]
  · rw [hω i]
    exact dynkin_const_mul ε c (fun z => max (b z - h) 0) X i ω

/-- If `r / a ≤ s`, `c ≥ 0` and `c r^z = 1` with `z ≤ 0`, then `c s^z ≤ (a^z)⁻¹`. -/
private lemma mul_rpow_le_inv_rpow {r s a c z : ℝ} (hz : z ≤ 0) (hr : 0 < r) (ha : 0 < a)
    (hc : 0 ≤ c) (hs : r / a ≤ s) (hcr : c * r ^ z = 1) : c * s ^ z ≤ (a ^ z)⁻¹ := by
  have h1 : s ^ z ≤ (r / a) ^ z := Real.rpow_le_rpow_of_nonpos (div_pos hr ha) hs hz
  rw [Real.div_rpow hr.le ha.le] at h1
  calc c * s ^ z ≤ c * (r ^ z / a ^ z) := mul_le_mul_of_nonneg_left h1 hc
    _ = (c * r ^ z) / a ^ z := by ring
    _ = (a ^ z)⁻¹ := by rw [hcr, one_div]

/-- The sum of the bracket terms along a path is at most the tail bound of the radial bracket. -/
private lemma sum_radialTerm_le (hd : 1 ≤ d) (x : ℕ → Site d) (n : ℕ) {r bd : ℝ}
    (hbd : 2 + Real.sqrt d / 2 < bd) (hrb : bd < r) (hr : Real.sqrt d + 2 ≤ r) :
    ∑ j ∈ range n, radialTerm d r (x j) ≤
      2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) * (r - 2) ^ (1 - (d : ℝ)) *
        maxLocalTime x n * tail d (cellSet x n) (r - bd) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1
  rw [CERW.Support.LocalTime.sum_range_eq_sum_localTime x n (radialTerm d r)]
  refine le_trans ?_ (sum_localTime_rpow_le_tail hd x n hbd hrb hr)
  rw [sum_filter]
  refine sum_le_sum fun z _ => ?_
  unfold radialTerm
  split_ifs with hz
  · have hpos : 0 < euclidNorm z := by linarith
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)) (Nat.cast_nonneg _)
  · simp

/-- The scaled bracket at time `n` is at most `C c M_n F(r - b_d)` when `c r^{1-d} = 1`. -/
private lemma radialBracket_le_tail (hd : 1 ≤ d) {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω)
    (n : ℕ) {r bd c Cg : ℝ} (hbd : 2 + Real.sqrt d / 2 < bd) (hrb : bd < r)
    (hr : Real.sqrt d + 2 ≤ r) (hc0 : 0 ≤ c) (hcr : c * r ^ (1 - (d : ℝ)) = 1) :
    radialBracket c Cg r X n ω ≤
      (Cg ^ 2 * (2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) * ((3 : ℝ) ^ (1 - (d : ℝ)))⁻¹)) *
        c * (maxLocalTime (fun j => X j ω) n *
          tail d (cellSet (fun j => X j ω) n) (r - bd)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1
  have hr3 : 3 ≤ r := by linarith
  have hS := sum_radialTerm_le hd (fun j => X j ω) n hbd hrb hr
  have hkey : c * (r - 2) ^ (1 - (d : ℝ)) ≤ ((3 : ℝ) ^ (1 - (d : ℝ)))⁻¹ :=
    mul_rpow_le_inv_rpow (by linarith) (by linarith) (by norm_num) hc0 (by linarith) hcr
  have hF := CERW.Support.Geometry.tail_nonneg (d := d) (cellSet (fun j => X j ω) n) (r - bd)
  have hMF : 0 ≤ (maxLocalTime (fun j => X j ω) n : ℝ) *
      tail d (cellSet (fun j => X j ω) n) (r - bd) := mul_nonneg (Nat.cast_nonneg _) hF
  have hcoef : 0 ≤ Cg ^ 2 * (2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d)) := by
    have := unitBallVolume_pos d
    positivity
  calc radialBracket c Cg r X n ω
      ≤ c ^ 2 * Cg ^ 2 * (2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) * (r - 2) ^ (1 - (d : ℝ)) *
        maxLocalTime (fun j => X j ω) n * tail d (cellSet (fun j => X j ω) n) (r - bd)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (Cg ^ 2 * (2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d))) * (c * (r - 2) ^ (1 - (d : ℝ))) *
        (c * ((maxLocalTime (fun j => X j ω) n : ℝ) *
          tail d (cellSet (fun j => X j ω) n) (r - bd))) := by ring
    _ ≤ (Cg ^ 2 * (2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d))) *
          ((3 : ℝ) ^ (1 - (d : ℝ)))⁻¹ *
        (c * ((maxLocalTime (fun j => X j ω) n : ℝ) *
          tail d (cellSet (fun j => X j ω) n) (r - bd))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hcoef)
          (mul_nonneg hc0 hMF)
    _ = _ := by ring

/-- The arithmetic of the deterministic step: on the good event, the rescaled Freedman threshold
gives the claimed bound for `W_n = c⁻¹ M_n`. -/
private lemma final_arith {cd c ρ V C₁ B L m F Wn : ℝ} (hcd : 1 ≤ cd) (hc : 0 < c)
    (hρ : c * ρ = 1) (hC₁ : 0 ≤ C₁) (hV0 : 0 ≤ V) (hV : V ≤ C₁ * c * (m * F)) (hL : 1 ≤ L)
    (hB : 0 < B) (hW : c * |Wn| ≤ cd * (Real.sqrt (max V 1 * L) + B * L)) :
    |Wn| ≤ cd * (Real.sqrt C₁ + 1 + B) * (Real.sqrt (m * ρ * F * L) + ρ * L) := by
  have hρ0 : 0 < ρ := lt_of_not_ge fun h => by nlinarith [mul_nonneg hc.le (neg_nonneg.mpr h)]
  have hL0 : 0 ≤ L := by linarith
  have hWn : |Wn| = ρ * (c * |Wn|) := by rw [← mul_assoc, mul_comm ρ c, hρ, one_mul]
  set a : ℝ := C₁ * c * (m * F) with ha
  have ha0 : 0 ≤ a := hV0.trans hV
  have hmax : max V 1 ≤ a + 1 := max_le (by linarith) (by linarith)
  have hsq1 : Real.sqrt (max V 1 * L) ≤ Real.sqrt (a * L) + Real.sqrt L := by
    calc Real.sqrt (max V 1 * L) ≤ Real.sqrt ((a + 1) * L) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hmax hL0)
      _ = Real.sqrt (a * L + L) := by rw [add_mul, one_mul]
      _ ≤ Real.sqrt (a * L) + Real.sqrt L := sqrt_add_le_add (mul_nonneg ha0 hL0) hL0
  have hsqL : Real.sqrt L ≤ L := by
    rw [Real.sqrt_le_left hL0]
    nlinarith
  have hkey : ρ * Real.sqrt (a * L) = Real.sqrt C₁ * Real.sqrt (m * ρ * F * L) := by
    have h1 : ρ * Real.sqrt (a * L) = Real.sqrt (ρ ^ 2 * (a * L)) := by
      rw [Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ0.le]
    have h2 : ρ ^ 2 * (a * L) = C₁ * (m * ρ * F * L) := by
      have : ρ ^ 2 * (C₁ * c * (m * F) * L) = C₁ * (m * ρ * F * L) * (c * ρ) := by ring
      rw [ha, this, hρ, mul_one]
    rw [h1, h2, Real.sqrt_mul hC₁]
  have hS0 := Real.sqrt_nonneg (m * ρ * F * L)
  have hC0 := Real.sqrt_nonneg C₁
  have hT0 : 0 ≤ ρ * L := mul_nonneg hρ0.le hL0
  calc |Wn| = ρ * (c * |Wn|) := hWn
    _ ≤ ρ * (cd * (Real.sqrt (a * L) + L + B * L)) := by
        refine mul_le_mul_of_nonneg_left (hW.trans ?_) hρ0.le
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        linarith
    _ = cd * (Real.sqrt C₁ * Real.sqrt (m * ρ * F * L) + (1 + B) * (ρ * L)) := by
        rw [← hkey]
        ring
    _ ≤ cd * ((Real.sqrt C₁ + 1 + B) * (Real.sqrt (m * ρ * F * L) + ρ * L)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        nlinarith [mul_nonneg hC0 hT0, mul_nonneg hB.le hS0, hS0, hT0]
    _ = _ := by ring

/-- One radius: Freedman's inequality at dyadic brackets, followed by the deterministic step,
bounds the probability that `|W^{(r)}_n|` exceeds the threshold, for every `r ≥ r₀`. -/
private lemma exists_radius_bound (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    {b : Site d → ℝ} {h : ℝ → ℝ} {Cg r₀ bd : ℝ} (hbd : 2 + Real.sqrt d / 2 < bd)
    (hr₀ : bd < r₀) (hr₀' : Real.sqrt d + 2 ≤ r₀)
    (hin : ∀ r : ℝ, r₀ ≤ r → ∀ x, euclidNorm x ≤ r - 1 → b x ≤ h r)
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ Cdet : ℝ, 0 < Cdet ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d}, IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        ∀ r : ℕ, r₀ ≤ r →
          μ {ω | Cdet * (Real.sqrt (maxLocalTime (fun j => X j ω) n * (r : ℝ) ^ (1 - (d : ℝ)) *
                tail d (cellSet (fun j => X j ω) n) (r - bd) * Real.log (n + 2)) +
              (r : ℝ) ^ (1 - (d : ℝ)) * Real.log (n + 2)) <
            |dynkin ε (fun z => max (b z - h r) 0) X n ω|} ≤
          ENNReal.ofReal (((Nat.clog 2 ⌈max ((Cg * ((2 : ℝ) ^ (1 - (d : ℝ)))⁻¹) ^ 2 * n) 1⌉₊ : ℕ)
            + 1) * (2 * Real.exp (-(K * Real.log (n + 2))))) := by
  have hd1 : 1 ≤ d := by omega
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hsq : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1'
  have hCg := cg_nonneg hd1 hgrad
  obtain ⟨cd, hcd1, hcd⟩ := CERW.Generic.Martingale.exists_dyadic_bound hK
  set Q : ℝ := ((2 : ℝ) ^ (1 - (d : ℝ)))⁻¹ with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set B : ℝ := 2 * (Cg * Q) + 1 with hBdef
  have hB : 0 < B := by
    have := mul_nonneg hCg hQ0
    linarith
  set C₁ : ℝ := Cg ^ 2 * (2 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
    ((3 : ℝ) ^ (1 - (d : ℝ)))⁻¹) with hC₁
  have hC₁0 : 0 ≤ C₁ := by
    have := unitBallVolume_pos d
    positivity
  refine ⟨cd * (Real.sqrt C₁ + 1 + B), by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn r hr
  have hrR : (3 : ℝ) ≤ r := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  set c : ℝ := ((r : ℝ) ^ (1 - (d : ℝ)))⁻¹ with hc
  have hc0 : 0 < c := by positivity
  have hcr : c * (r : ℝ) ^ (1 - (d : ℝ)) = 1 := inv_mul_cancel₀ (by positivity)
  have hQc : c * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) ≤ Q :=
    mul_rpow_le_inv_rpow (by linarith) hrpos (by norm_num) hc0.le (by linarith) hcr
  obtain ⟨M, hM, hbdM, hvar, hae⟩ := exists_clamped_radial hd1 hε hεd hX (h := h r)
    (r := (r : ℝ)) (B := B) hc0.le hCg (by linarith) (hin r hr) hgrad hQc (by linarith)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  have hL1 : 1 ≤ Real.log ((n : ℝ) + 2) := by
    have h4 : Real.log 4 ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith)
    have h5 : (1 : ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith [this]
    linarith
  have hW : (1 : ℝ) ≤ max ((Cg * Q) ^ 2 * n) 1 := le_max_right _ _
  have hdy := hcd hM (V := radialBracket c Cg r X)
    (stronglyMeasurable_radialBracket_succ hX.measurable c Cg r)
    (radialBracket_zero c Cg r X) (radialBracket_mono c Cg r X) hvar (b := B) hB 0 n
    (fun i _ _ ω => hbdM i ω) (W := max ((Cg * Q) ^ 2 * n) 1) (L := Real.log ((n : ℝ) + 2)) hW hL
    (fun ω => by
      rw [zero_add, radialBracket_zero, sub_zero]
      exact (radialBracket_le hd1 hc0.le (by linarith) hQc X n ω).trans (le_max_left _ _))
  refine le_trans (measure_mono_ae ?_) hdy
  filter_upwards [hae] with ω hω hE
  change _ < _ at hE
  change _ < _
  rw [zero_add, radialBracket_zero, sub_zero, hω n, hω 0, dynkin_zero, mul_zero, sub_zero]
  refine lt_of_not_ge fun hle => ?_
  have hV0 : 0 ≤ radialBracket c Cg r X n ω :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (sum_nonneg fun j _ => radialTerm_nonneg _ _)
  have hV := radialBracket_le_tail hd1 X ω n (Cg := Cg) hbd (hr₀.trans_le hr) (hr₀'.trans hr)
    hc0.le hcr
  have hW' : c * |dynkin ε (fun z => max (b z - h r) 0) X n ω| ≤
      cd * (Real.sqrt (max (radialBracket c Cg r X n ω) 1 * Real.log ((n : ℝ) + 2)) +
        B * Real.log ((n : ℝ) + 2)) := by
    rw [← abs_of_pos hc0, ← abs_mul, abs_of_pos hc0]
    exact hle
  have hfin := final_arith hcd1 hc0 hcr hC₁0 hV0 hV hL1 hB hW'
  exact absurd hE (not_lt.mpr hfin)

/-- The base-two logarithm of `⌈W⌉₊`, plus one, is at most `(G + 3)(n + 1)` when
`W = max (G n) 1`, with `G = C²`. -/
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

/-- The arithmetic of the union bound: `(n + 1) · (G + 3)(n + 1) · 2 e^{-(p + 2) L}` is at most
`8 (G + 3) n^{-p}`. -/
private lemma union_bound_arith {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 1 ≤ n) {G : ℝ} (hG : 0 ≤ G) :
    ((n : ℝ) + 1) * (((G + 3) * ((n : ℝ) + 1)) *
      (2 * Real.exp (-((p + ((2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))) ≤
    (8 * (G + 3)) * (n : ℝ) ^ (-p) := by
  have h1 := CERW.Generic.Martingale.two_mul_exp_neg_mul_log_le
    (K := p + ((2 : ℕ) : ℝ)) (by positivity) hn
  have h2 := CERW.Generic.Martingale.pow_mul_rpow_neg_le hn 2 p
  have h3 : (0 : ℝ) ≤ (G + 3) * ((n : ℝ) + 1) ^ 2 := by positivity
  calc ((n : ℝ) + 1) * (((G + 3) * ((n : ℝ) + 1)) *
        (2 * Real.exp (-((p + ((2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))))
      = ((G + 3) * ((n : ℝ) + 1) ^ 2) *
          (2 * Real.exp (-((p + ((2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) := by ring
    _ ≤ ((G + 3) * ((n : ℝ) + 1) ^ 2) * (2 * (n : ℝ) ^ (-(p + ((2 : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left h1 h3
    _ = 2 * (G + 3) * (((n : ℝ) + 1) ^ 2 * (n : ℝ) ^ (-(p + ((2 : ℕ) : ℝ)))) := by ring
    _ ≤ 2 * (G + 3) * (2 ^ 2 * (n : ℝ) ^ (-p)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (8 * (G + 3)) * (n : ℝ) ^ (-p) := by ring

/-- `eq:radialmart`: if `b ≤ h(r)` on `|x| ≤ r - 1` for every `r ≥ r₀`, and `b` has the one-step
bound, then with probability at least `1 - Cn^{-p}`, simultaneously for all integers
`r₀ ≤ r ≤ n`, `|W^{(r)}_n| ≤ C [√(M_n r^{1-d} F(r - b_d) L) + r^{1-d} L]`. -/
theorem exists_radial_mart (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    {b : Site d → ℝ} {h : ℝ → ℝ} {Cg r₀ bd : ℝ} (hbd : 2 + Real.sqrt d / 2 < bd)
    (hr₀ : bd < r₀) (hr₀' : Real.sqrt d + 2 ≤ r₀)
    (hin : ∀ r : ℝ, r₀ ≤ r → ∀ x, euclidNorm x ≤ r - 1 → b x ≤ h r)
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      {X : ℕ → Ω → Site d}, IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ∃ r : ℕ, r₀ ≤ r ∧ r ≤ n ∧
          C * (Real.sqrt (maxLocalTime (fun j => X j ω) n * (r : ℝ) ^ (1 - (d : ℝ)) *
                tail d (cellSet (fun j => X j ω) n) (r - bd) * Real.log (n + 2)) +
              (r : ℝ) ^ (1 - (d : ℝ)) * Real.log (n + 2)) <
            |dynkin ε (fun z => max (b z - h r) 0) X n ω|} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cdet, hCdet0, hCdet⟩ := exists_radius_bound hd hε hεd hbd hr₀ hr₀' hin hgrad
    (K := p + ((2 : ℕ) : ℝ)) (by positivity)
  set G : ℝ := (Cg * ((2 : ℝ) ^ (1 - (d : ℝ)))⁻¹) ^ 2 with hG
  have hG0 : 0 ≤ G := sq_nonneg _
  refine ⟨Cdet + 8 * (G + 3), by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hL0 : 0 ≤ Real.log ((n : ℝ) + 2) := (Real.log_pos (by linarith)).le
  set R : Finset ℕ := (range (n + 1)).filter (fun r => r₀ ≤ (r : ℝ)) with hR
  set B : ℕ → Set Ω := fun r =>
    {ω | Cdet * (Real.sqrt (maxLocalTime (fun j => X j ω) n * (r : ℝ) ^ (1 - (d : ℝ)) *
        tail d (cellSet (fun j => X j ω) n) (r - bd) * Real.log (n + 2)) +
      (r : ℝ) ^ (1 - (d : ℝ)) * Real.log (n + 2)) <
        |dynkin ε (fun z => max (b z - h r) 0) X n ω|} with hB
  have hbound : ∀ r ∈ R, μ (B r) ≤ ENNReal.ofReal (((G + 3) * ((n : ℝ) + 1)) *
      (2 * Real.exp (-((p + ((2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))) := by
    intro r hr
    refine (hCdet hX n hn r (mem_filter.mp hr).2).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (clog_ceil_add_one_le (Cg * ((2 : ℝ) ^ (1 - (d : ℝ)))⁻¹) n)
      (by positivity)
  have hRcard : (R.card : ℝ) ≤ (n : ℝ) + 1 := by
    have h1 : R.card ≤ n + 1 := (card_filter_le _ _).trans (by simp)
    exact_mod_cast h1
  set a : ℝ := ((G + 3) * ((n : ℝ) + 1)) *
    (2 * Real.exp (-((p + ((2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) with ha
  have ha0 : 0 ≤ a := by positivity
  refine (measure_mono (t := ⋃ r ∈ R, B r) ?_).trans ?_
  · rintro ω ⟨r, hr, hrn, hlt⟩
    simp only [Set.mem_iUnion]
    refine ⟨r, ?_, ?_⟩
    · simp only [hR, mem_filter, mem_range]
      exact ⟨by omega, hr⟩
    · have he : 0 ≤ Real.sqrt (maxLocalTime (fun j => X j ω) n * (r : ℝ) ^ (1 - (d : ℝ)) *
          tail d (cellSet (fun j => X j ω) n) (r - bd) * Real.log (n + 2)) +
          (r : ℝ) ^ (1 - (d : ℝ)) * Real.log (n + 2) :=
        add_nonneg (Real.sqrt_nonneg _)
          (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hL0)
      refine lt_of_le_of_lt ?_ hlt
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * (G + 3)) he]
  · calc μ (⋃ r ∈ R, B r) ≤ ∑ r ∈ R, μ (B r) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _r ∈ R, ENNReal.ofReal a := sum_le_sum hbound
      _ = ENNReal.ofReal ((R.card : ℝ) * a) := by
          simp only [sum_const, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul (p := (R.card : ℝ)) (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((Cdet + 8 * (G + 3)) * (n : ℝ) ^ (-p)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (R.card : ℝ) * a ≤ ((n : ℝ) + 1) * a :=
            mul_le_mul_of_nonneg_right hRcard ha0
          have h2 := union_bound_arith hp.le (by omega : 1 ≤ n) hG0
          have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
          nlinarith [mul_nonneg hCdet0.le h3]

end CERW.Support.Coarse
