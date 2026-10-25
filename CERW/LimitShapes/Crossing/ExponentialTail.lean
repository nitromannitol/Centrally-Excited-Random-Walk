module

public import CERW.LimitShapes.Crossing.ExponentialStopping
public import CERW.LimitShapes.Crossing.ExponentialExit
public import CERW.LimitShapes.Crossing.ExponentialDrift
public import CERW.Support.Norm.ContactPotential

@[expose] public section

/-!
# Fixed-level exponential distance tails

The stopped exponential estimate gives the fixed-level part of the paper's
 equation `eq:distance-crossing`, uniformly over admissible fields and laws.
-/

namespace CERW.LimitShapes.Crossing.ExponentialTail

open MeasureTheory Filter LatticeProb CERW CERW.Support.Law
open CERW.LimitShapes.Crossing.ExponentialExit

open private CERW.Support.Norm.toSpace_add from CERW.Support.Norm.OuterCrossing

/-- Coordinate ellipticity bounds the inward drift scale by one half. -/
theorem drift_normMin_le_half {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) :
    ε * normMin Ψ ≤ 1 / 2 := by
  let i : Fin d := ⟨0, by omega⟩
  have hm := (CERW.Generic.Norm.normMin_pos_mul_le hΨ (by omega)).2 (coordVec i)
  have hn : ‖(coordVec i : EuclideanSpace ℝ (Fin d))‖ = 1 := by simp [coordVec]
  rw [hn, mul_one] at hm
  have he := (mul_le_mul_of_nonneg_left hm hε.le).trans (hell i).le
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact he.trans (one_div_le_one_div_of_le (by norm_num) hd')

/-- The distance crossing event at a fixed norm level has an exponential tail. -/
theorem measure_distance_crossing_le_exp {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (hsub : ∀ x, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (hzero : ξ 0 = 0)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X)
    (N L : ℕ) {a s : ℝ} (ha : 0 ≤ a) (_hs : 0 < s) :
    μ {ω | ∃ t ≤ N, exteriorLocalTime Ψ (X · ω) t a ≤ L ∧
      ∃ j ≤ t, s ≤ Metric.infDist (toSpace (X j ω)) {v | Ψ v ≤ a}} ≤
      ENNReal.ofReal ((1 + Real.exp 1 * N) *
        Real.exp (-(ε * normMin Ψ / (2 * (L + 1 : ℝ))) * s)) := by
  have hd1 : 1 ≤ d := by omega
  have hc := CERW.Support.Norm.ContactAssembly.drift_coord_le hΨ hε hell hsub hzero
  let κ := ε * normMin Ψ
  have hk : 0 < κ := mul_pos hε
    (CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1).1
  have hkh : κ ≤ 1 / 2 := drift_normMin_le_half hd hΨ hε hell
  let θ := κ / (2 * (L + 1 : ℝ))
  let R := (L + 1 : ℝ) / κ
  have hLpos : 0 < (L + 1 : ℝ) := by positivity
  have ht : 0 < θ := div_pos hk (by positivity)
  have hth : θ ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (L + 1 : ℝ))).2
    have : (1 : ℝ) ≤ L + 1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg L)
    nlinarith
  have hr : 1 ≤ R := (le_div_iff₀ hk).2 (by
    have : (1 : ℝ) ≤ L + 1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg L)
    linarith)
  have htr : θ * R ≤ 1 / 2 := by
    dsimp [θ, R]
    field_simp
    norm_num
  have hl : (L + 1 : ℝ) * (θ + 1 / (2 * R)) ≤ κ := by
    dsimp [θ, R]
    apply le_of_eq
    field_simp
    ring
  let δ := fun x : Site d => Metric.infDist (toSpace x) {v | Ψ v ≤ a}
  have hzΨ : Ψ 0 = 0 := (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).1
  have hz : δ 0 = 0 := by
    apply Metric.infDist_zero_of_mem
    change Ψ (toSpace 0) ≤ a
    have hemb : toSpace (0 : Site d) = 0 := by ext i; simp [toSpace]
    rw [hemb, hzΨ]
    exact ha
  have hlip : ∀ x e, e ∈ unitSteps d → δ (x + e) ≤ δ x + 1 := by
    intro x e he
    have hn : ‖toSpace e‖ = 1 := by
      rw [norm_toSpace, euclidNorm_of_mem_unitSteps he]
    have hh := (Metric.lipschitz_infDist_pt {v | Ψ v ≤ a}).dist_le_mul
      (toSpace (x + e)) (toSpace x)
    have hh' : |δ (x + e) - δ x| ≤ 1 := by
      simpa only [δ, Real.dist_eq, Real.norm_eq_abs, CERW.Support.Norm.toSpace_add,
        dist_eq_norm, add_sub_cancel_left,
        hn, NNReal.coe_one, one_mul] using hh
    linarith [(abs_le.mp hh').2]
  let τ := fun ω => crossingStop Ψ a L s N (X · ω)
  have hτ := isStoppingTime_crossingStop Ψ a L s hX.measurable N
  have hb : ∀ ω, τ ω ≤ N := fun ω => (crossingStop_spec Ψ a L s N (X · ω)).1
  have hcount : ∀ᵐ ω ∂μ, ∀ x, R ≤ δ x → localTime (X · ω) (τ ω) x ≤ L + 1 := by
    apply ae_of_all
    intro ω x hx
    have hout : a ≤ Ψ (toSpace x) := by
      by_contra h
      have hm : toSpace x ∈ {v | Ψ v ≤ a} := (not_le.mp h).le
      have hz' : δ x = 0 := Metric.infDist_zero_of_mem hm
      rw [hz'] at hx
      linarith
    exact (localTime_le_exterior Ψ a (X · ω) (τ ω) x hout).trans
      (exteriorLocalTime_crossingStop_le Ψ a L s N (X · ω))
  have hf : ∀ j < N, ∀ᵐ ω ∂μ, j < τ ω → R ≤ δ (X j ω) →
      (∑ e ∈ unitSteps d, driftStepProb d ε ξ (X · ω) j e *
        (Real.exp (θ * δ (X j ω + e)) - Real.exp (θ * δ (X j ω)))) ≤
      θ * Real.exp (θ * δ (X j ω)) * (θ + 1 / (2 * δ (X j ω)) -
        if X j ω ∉ departureRange (X · ω) j then κ else 0) := by
    intro j _
    apply ae_of_all
    intro ω _ hx
    exact ExponentialDrift.sum_driftStepProb_exp_distance_le hd1 hΨ ha hε.le ξ
      hsub hzero hc (X · ω) j ht (by linarith) (hr.trans hx)
  have hi := ExponentialStopping.integrable_stopped_site_function hd1 hε.le hc hX
    (fun x => Real.exp (θ * δ x)) hτ hb
  have he := ExponentialStopping.integral_exp_stopped_le hd1 hε.le hc hX N L δ
    (fun _ => Metric.infDist_nonneg) hz θ R κ ht hth hr htr hk hl hlip τ hτ hb
    hcount hf
  have hi' := hi.const_mul (Real.exp (-θ * s))
  have hm := hi'.measure_le_integral (ae_of_all μ (fun ω => by positivity))
    (s := {ω | ∃ t ≤ N, exteriorLocalTime Ψ (X · ω) t a ≤ L ∧
      ∃ j ≤ t, s ≤ δ (X j ω)}) (fun ω h => by
        have hh := distance_le_at_crossingStop Ψ a L s N (X · ω) h
        have hh' : 0 ≤ -θ * s + θ * δ (X (τ ω) ω) := by
          nlinarith
        rw [← Real.exp_add]
        exact Real.one_le_exp hh')
  apply hm.trans
  rw [integral_const_mul]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.exp (-θ * s) * (1 + Real.exp 1 * N) :=
      mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- A fixed level has a polynomial distance tail, uniformly over fields and laws. -/
theorem exists_measure_distance_crossing_le {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ N : ℕ, 2 ≤ N →
        ∀ L : ℕ, ∀ a : ℝ, 0 ≤ a →
          μ {ω | ∃ t ≤ N, exteriorLocalTime Ψ (X · ω) t a ≤ L ∧
            ∃ j ≤ t, C * (L + 1 : ℝ) * Real.log N ≤
              Metric.infDist (toSpace (X j ω)) {v | Ψ v ≤ a}} ≤
            ENNReal.ofReal (C * (N : ℝ) ^ (-p - 2)) := by
  let κ := ε * normMin Ψ
  have hk : 0 < κ := mul_pos hε
    (CERW.Generic.Norm.normMin_pos_mul_le hΨ (by omega)).1
  let C := 2 * (p + 3) / κ + (1 + Real.exp 1)
  have hc : 0 < C := by dsimp [C]; positivity
  have hc1 : 1 + Real.exp 1 ≤ C := by
    dsimp [C]
    linarith [le_of_lt (div_pos (by linarith : 0 < 2 * (p + 3)) hk)]
  have hck : p + 3 ≤ κ * C / 2 := by
    have hh : 2 * (p + 3) / κ ≤ C := by
      dsimp [C]
      linarith [Real.exp_pos (1 : ℝ)]
    have hh' := (div_le_iff₀ hk).mp hh
    nlinarith
  refine ⟨C, hc, ?_⟩
  intro ξ hsub hzero Ω _ μ _ X hX N hN L a ha
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hn0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hs : 0 < C * (L + 1 : ℝ) * Real.log N := by positivity
  apply (measure_distance_crossing_le_exp hd hΨ hε hell ξ hsub hzero μ X hX
    N L ha hs).trans
  apply ENNReal.ofReal_le_ofReal
  have he : Real.exp (-(κ / (2 * (L + 1 : ℝ))) *
      (C * (L + 1 : ℝ) * Real.log N)) ≤ (N : ℝ) ^ (-(p + 3)) := by
    rw [Real.rpow_def_of_pos hn0]
    apply Real.exp_le_exp.mpr
    have heq : -(κ / (2 * (L + 1 : ℝ))) *
        (C * (L + 1 : ℝ) * Real.log N) = -(κ * C / 2) * Real.log N := by
      field_simp
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right hck hlog.le]
  have hf : 1 + Real.exp 1 * N ≤ C * N := by
    have hh := mul_le_mul_of_nonneg_right hc1 hn0.le
    nlinarith
  calc
    _ ≤ (C * N) * (N : ℝ) ^ (-(p + 3)) :=
      mul_le_mul hf he (Real.exp_pos _).le (by positivity)
    _ = C * (N : ℝ) ^ (-p - 2) := by
      rw [mul_assoc]
      conv_lhs => arg 2; arg 1; rw [← Real.rpow_one (N : ℝ)]
      rw [← Real.rpow_add hn0]
      congr 2
      ring

end CERW.LimitShapes.Crossing.ExponentialTail
