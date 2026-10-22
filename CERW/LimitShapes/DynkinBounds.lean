import CERW.LimitShapes.DynkinFreedman
import CERW.Support.Lower.SharpBulk

/-!
# Freedman bounds for the Dynkin martingales through a fixed horizon

The logarithm and the failure probability can use a terminal horizon even when
the martingale is evaluated at an earlier time. This is the form needed for the
simultaneous distance crossing estimate `eq:distance-crossing`.
-/

universe u

open MeasureTheory ProbabilityTheory Filter
open LatticeProb (Site)

namespace CERW.LimitShapes.DynkinBounds

open CERW CERW.Support.Law CERW.Support.Drift
open private exists_bracket_version dyadic_threshold_le dyadic_failure_le
  from CERW.Support.Norm.Freedman
open private maxDynkin_predBracket_smul from CERW.Support.Lower.SharpBulk

/-- The dyadic Freedman argument at any time before the horizon, using the
horizon's logarithm and polynomial exceptional probability. -/
private theorem freedman_prefix_bound :
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ n : ℕ, n ≤ N →
      ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ), Martingale Z ℱ μ →
        (∀ᵐ ω ∂μ, ∀ t, |Z (t + 1) ω - Z t ω| ≤ 1) →
        μ {ω | ¬ |Z n ω - Z 0 ω|
            ≤ C * (Real.sqrt (CERW.predBracket μ ℱ Z Z n ω * Real.log N) + Real.log N)}
          ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-p)) := by
  intro p hp
  obtain ⟨c, hc1, hc⟩ :=
    CERW.Generic.Martingale.exists_dyadic_bound.{u} (K := p + 1) (by linarith)
  refine ⟨3 * c + 4, by linarith, ?_⟩
  intro N hN n hnN Ω m0 μ hμ ℱ Z hZ hinc
  obtain ⟨M, hM, hMb, -, hMae⟩ :=
    CERW.Generic.Martingale.exists_martingale_clamp hZ zero_le_one (ae_all_iff.mp hinc)
  obtain ⟨V, hVpred, hV0, hVmono, hVn, hVdom, hVae⟩ := exists_bracket_version hM hMb hMae
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hL4 : 1 / 4 ≤ Real.log N := by
    have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog : 1 - (2 : ℝ)⁻¹ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos zero_lt_two
    have hmono : Real.log 2 ≤ Real.log N := Real.log_le_log zero_lt_two h2
    norm_num at hlog
    linarith
  have hdy := hc hM hVpred hV0 hVmono hVdom (b := 1) one_pos 0 n
    (fun i _ _ ω => hMb i ω) (W := (N : ℝ)) (L := Real.log N) hN1 hL (fun ω => by
      rw [zero_add, hV0 ω, sub_zero]
      exact (hVn n ω).trans (Nat.cast_le.mpr hnN))
  have hfail := dyadic_failure_le (p := p) hN
  have hcast : ⌈(N : ℝ)⌉₊ = N := Nat.ceil_natCast N
  have hsub : {ω | ¬ |Z n ω - Z 0 ω|
        ≤ (3 * c + 4) * (Real.sqrt (CERW.predBracket μ ℱ Z Z n ω * Real.log N) + Real.log N)}
      ≤ᵐ[μ] {ω | c * (Real.sqrt (max (V (0 + n) ω - V 0 ω) 1 * Real.log N) + 1 * Real.log N)
        < |M (0 + n) ω - M 0 ω|} := by
    filter_upwards [hMae, hVae] with ω h1 h2 hω
    have hω' : (3 * c + 4) * (Real.sqrt (CERW.predBracket μ ℱ Z Z n ω * Real.log N)
        + Real.log N) < |Z n ω - Z 0 ω| := not_le.mp hω
    have hVnn : 0 ≤ V n ω := by
      have hmono : Monotone fun k => V k ω :=
        monotone_nat_of_le_succ fun k => hVmono k ω
      calc (0 : ℝ) = V 0 ω := (hV0 ω).symm
        _ ≤ V n ω := hmono (Nat.zero_le n)
    rw [← h2 n] at hω'
    show c * (Real.sqrt (max (V (0 + n) ω - V 0 ω) 1 * Real.log N) + 1 * Real.log N)
      < |M (0 + n) ω - M 0 ω|
    rw [zero_add, hV0 ω, sub_zero, h1 n, h1 0]
    exact lt_of_le_of_lt (dyadic_threshold_le (by linarith) hVnn hL4) hω'
  refine le_trans (measure_mono_ae hsub) (le_trans hdy ?_)
  apply ENNReal.ofReal_le_ofReal
  rw [hcast] at hfail ⊢
  have hrpow : 0 ≤ (N : ℝ) ^ (-p) := Real.rpow_nonneg hNpos.le _
  calc ((Nat.clog 2 N : ℝ) + 1) * (2 * Real.exp (-((p + 1) * Real.log N)))
      ≤ 4 * (N : ℝ) ^ (-p) := hfail
    _ ≤ (3 * c + 4) * (N : ℝ) ^ (-p) :=
        mul_le_mul_of_nonneg_right (by linarith) hrpow


/-- A uniform bound for a Dynkin martingale with test-function increments bounded by `B`.
The logarithm and failure probability are measured at the horizon `N`. -/
theorem exists_dynkin_freedman_bound (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ n : ℕ, n ≤ N →
      ∀ {d : ℕ}, 1 ≤ d → ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
        [IsProbabilityMeasure μ] (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)),
        0 ≤ ε → (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
      ∀ (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X →
      ∀ (f : Site d → ℝ) (B : ℝ), 0 < B →
        (∀ x e, e ∈ unitSteps d → |f (x + e) - f x| ≤ B) →
        μ {ω | ¬ |dynkinMart (driftStepProb d ε ξ) f (X · ω) n| ≤
            C * (Real.sqrt (dynkinBracket (driftStepProb d ε ξ) f f (X · ω) n *
              Real.log N) + B * Real.log N)} ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-p)) := by
  obtain ⟨A, hA, hF⟩ := freedman_prefix_bound.{u} p hp
  refine ⟨2 * A, by positivity, ?_⟩
  intro N hN n hn d hd Ω _ μ _ ε ξ hε hξ X hX f B hB hf
  let M := driftDynkin ε ξ f X
  let c := (2 * B)⁻¹
  have hc : 0 < c := inv_pos.mpr (by positivity)
  have hcB : c * (2 * B) = 1 := inv_mul_cancel₀ (by positivity)
  have hM : Martingale M (pathFiltration hX.measurable) μ :=
    martingale_driftDynkin hd hε hξ hX f
  have hinc : ∀ᵐ ω ∂μ, ∀ t,
      |(c • M) (t + 1) ω - (c • M) t ω| ≤ 1 := by
    filter_upwards [ae_abs_driftDynkin_succ_sub_le hd hε hξ hX f] with ω hω t
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, abs_mul, abs_of_pos hc]
    exact (mul_le_mul_of_nonneg_left (hω t B (hf (X t ω))) hc.le).trans hcB.le
  have htail := hF N hN n hn μ (pathFiltration hX.measurable) (c • M) (hM.smul c) hinc
  have hsub : {ω | ¬ |dynkinMart (driftStepProb d ε ξ) f (X · ω) n| ≤
      2 * A * (Real.sqrt (dynkinBracket (driftStepProb d ε ξ) f f (X · ω) n *
        Real.log N) + B * Real.log N)} ≤ᵐ[μ]
      {ω | ¬ |(c • M) n ω - (c • M) 0 ω| ≤
        A * (Real.sqrt (predBracket μ (pathFiltration hX.measurable)
          (c • M) (c • M) n ω * Real.log N) + Real.log N)} := by
    filter_upwards [maxDynkin_predBracket_smul μ (pathFiltration hX.measurable) M M c n,
      ae_predBracket_driftDynkin hd hε hξ hX f] with ω hscale hbr hbad hgood
    have hbr' := hbr n
    change predBracket μ (pathFiltration hX.measurable) M M n ω = _ at hbr'
    rw [hscale, hbr'] at hgood
    have hsqrt : Real.sqrt (c ^ 2 * dynkinBracket (driftStepProb d ε ξ) f f
        (X · ω) n * Real.log N) =
        c * Real.sqrt (dynkinBracket (driftStepProb d ε ξ) f f (X · ω) n * Real.log N) := by
      rw [mul_assoc, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
    rw [hsqrt] at hgood
    have hzero : M 0 ω = 0 := driftDynkin_zero ε ξ f X ω
    simp only [Pi.smul_apply, smul_eq_mul, hzero, mul_zero, sub_zero, abs_mul,
      abs_of_pos hc] at hgood
    have hMval : M n ω = dynkinMart (driftStepProb d ε ξ) f (X · ω) n :=
      (dynkinMart_driftStepProb_eq_driftDynkin hd ε ξ f X n ω).symm
    rw [hMval] at hgood
    apply hbad
    let S := Real.sqrt (dynkinBracket (driftStepProb d ε ξ) f f (X · ω) n * Real.log N)
    have hcancel : 2 * B * c = 1 := by rw [mul_comm, hcB]
    calc |dynkinMart (driftStepProb d ε ξ) f (X · ω) n|
        = 2 * B * (c * |dynkinMart (driftStepProb d ε ξ) f (X · ω) n|) := by
            rw [← mul_assoc, hcancel, one_mul]
      _ ≤ 2 * B * (A * (c * S + Real.log N)) :=
        mul_le_mul_of_nonneg_left hgood (by positivity)
      _ = A * S + 2 * A * B * Real.log N := by
        calc 2 * B * (A * (c * S + Real.log N))
            = (2 * B * c) * A * S + 2 * A * B * Real.log N := by ring
          _ = A * S + 2 * A * B * Real.log N := by rw [hcancel, one_mul]
      _ ≤ 2 * A * (S + B * Real.log N) := by
        nlinarith [mul_nonneg hA.le (Real.sqrt_nonneg
          (dynkinBracket (driftStepProb d ε ξ) f f (X · ω) n * Real.log N))]

  refine (measure_mono_ae hsub).trans (htail.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg N) _)

end CERW.LimitShapes.DynkinBounds
