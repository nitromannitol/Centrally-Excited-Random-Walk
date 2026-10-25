module

public import CERW.LimitShapes.Event
public import CERW.Support.Norm.Section5Localization

@[expose] public section

/-!
# The inner radius from the approximation and quadratic estimates

The deterministic inner-radius argument uses only the coarse bounds, the
potential approximation, the quadratic estimate, and the contact bound.
-/

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes.InnerApproximation

open CERW CERW.Support.Statements CERW.Support.Norm.ContactEvent
  CERW.Support.Norm.Section5Localization

open private inner_core_inputs
  from CERW.Support.Norm.Section5Localization

variable {d : ℕ}

/-- The deterministic inner-radius conclusion from the estimates it consumes. -/
theorem inner_of_approximation_inputs (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (K : CERW.Support.Norm.ContactEvent.EventConstants) {Cc : ℝ}
    (hCc : 0 < Cc) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (x : ℕ → Site d) (n : ℕ),
        n₀ ≤ n → PathTyping d x →
        (CoarseBounds d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε K.c_co K.C_co x n ∧
          CERW.LimitShapes.LocalApproximation (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε K.C_loc
              x n ∧
          QuadraticEstimate d ε ξ K.C_quad x n) →
        ContactBound d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε Cc x n →
        InnerConclusion d ε C x n := by
  have hd1 : 1 ≤ d := by omega
  have hΨ : IsNorm (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) := isNorm_euclidean
  have hpball : ∀ ρ : ℝ, 0 < ρ → ∀ y : EuclideanSpace ℝ (Fin d),
      potential d ε (Metric.ball 0 ρ) y = 2 * d * ε * max (ρ - ‖y‖) 0 := by
    intro ρ hρ y
    have h := CERW.Support.Norm.norm_ball_potential hd hΨ ε hρ y
    have hset : {v : EuclideanSpace ℝ (Fin d) | ‖v‖ < ρ} = Metric.ball 0 ρ := by
      ext v
      simp
    rw [hset, normPotential_norm_eq hd1] at h
    exact h
  obtain ⟨Cg, hCg, hg⟩ := CERW.Support.Norm.norm_potential_geometry hd
    (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) hΨ
  have hpbound : ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
      ∀ y, |potential d ε D y| ≤ Cg * ε * (volume D).toReal ^ ((1 : ℝ) / d) := by
    intro D hDm hDb y
    obtain ⟨h1, -, -⟩ := hg ε hε D hDm hDb
    have h := h1 y
    rw [normPotential_norm_eq hd1] at h
    exact h
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hbase : 0 < ((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d) := by positivity
  set a : ℝ := (((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1)) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hbase _
  set Cco : ℝ := max K.C_co 0 with hCco_def
  set Cl : ℝ := max K.C_loc 0 with hCl_def
  set Cq : ℝ := max K.C_quad 0 with hCq_def
  have hCco : 0 ≤ Cco := le_max_right _ _
  have hCl0 : 0 ≤ Cl := le_max_right _ _
  have hCq : 0 ≤ Cq := le_max_right _ _
  set C₀ : ℝ := Cco * (a ^ d + a) + 1 with hC₀_def
  have hC₀ : 0 < C₀ := by
    have : 0 ≤ Cco * (a ^ d + a) := mul_nonneg hCco (by positivity)
    linarith
  set C₁ : ℝ := Cl + Cq * (C₀ + 1) + 1 with hC₁_def
  have hC₁ : 0 < C₁ := by
    have : 0 ≤ Cq * (C₀ + 1) := mul_nonneg hCq (by linarith)
    linarith
  obtain ⟨Cin, hCin, nin, hcore⟩ := inner_core_inputs.{0} hd hε hC₀ hC₁ hCc hCg.le hpball hpbound
  refine ⟨Cin, hCin, max nin 2, fun ξ hξ hξ0 x n hn hlegal hE hcont => ?_⟩
  have hnin : nin ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < n := by linarith
  set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1)) with hN_def
  have hN1 : 1 ≤ N := Real.one_le_rpow hn1R (by positivity)
  set L : ℝ := Real.log (n + 2) with hL_def
  have hlogL : Real.log n ≤ L := Real.log_le_log hnpos (by linarith)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1R
  have hL0 : 0 ≤ L := hlog0.trans hlogL
  -- the scale and the rate in the notation of the core
  have hr : scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n =
      ((d + 1) * n / (2 * d * ε * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal))
        ^ ((1 : ℝ) / (d + 1)) := by
    unfold scale
    rw [normBallVolume_norm]
    rfl
  have hscale : scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n = a * N := by
    unfold scale
    rw [normBallVolume_norm, ha_def, hN_def,
      show ((d : ℝ) + 1) * n / (2 * d * ε * unitBallVolume d) =
        (((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d)) * n by ring]
    exact Real.mul_rpow hbase.le (Nat.cast_nonneg n)
  have hq : contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n =
      (if d = 2 then Real.sqrt (Real.log n / ((d + 1) * n / (2 * d * ε *
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^
            ((1 : ℝ) / (d + 1)))
        else Real.log n / ((d + 1) * n / (2 * d * ε *
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^
            ((1 : ℝ) / (d + 1))) := by
    unfold contactRate
    rw [hr]
  obtain ⟨hcoarse, hglob, hquad⟩ := hE
  obtain ⟨-, hcard, -, hM, -, hH⟩ := hcoarse
  rw [hscale] at hcard hM hH
  have hNd : 0 ≤ N ^ d := pow_nonneg (by linarith) d
  have haN : 0 ≤ a * N := mul_nonneg ha.le (by linarith)
  have had : 0 ≤ a ^ d := by positivity
  have hcard' : ((departureRange x n).card : ℝ) ≤ C₀ * N ^ d := by
    refine hcard.trans ?_
    refine (mul_le_mul_of_nonneg_right (le_max_left K.C_co 0)
      (pow_nonneg haN d)).trans ?_
    rw [mul_pow, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hNd
    have : Cco * a ^ d ≤ Cco * (a ^ d + a) :=
      mul_le_mul_of_nonneg_left (by linarith) hCco
    linarith
  have hM' : (maxLocalTime x n : ℝ) ≤ C₀ * N := by
    refine hM.trans ?_
    refine (mul_le_mul_of_nonneg_right (le_max_left K.C_co 0) haN).trans ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    have : Cco * a ≤ Cco * (a ^ d + a) :=
      mul_le_mul_of_nonneg_left (by linarith) hCco
    linarith
  have hH' : maxRadius x n ≤ C₀ * N := by
    refine hH.trans ?_
    refine (mul_le_mul_of_nonneg_right (le_max_left K.C_co 0) haN).trans ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    have : Cco * a ≤ Cco * (a ^ d + a) :=
      mul_le_mul_of_nonneg_left (by linarith) hCco
    linarith
  have hM0 : (0 : ℝ) ≤ (maxLocalTime x n : ℝ) := Nat.cast_nonneg _
  have hglob' : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
      |cellLocalTime x n y - potential d ε (cellSet x n) y| ≤
        C₁ * (if d = 2 then Real.sqrt (maxLocalTime x n : ℝ) * L + L
          else Real.sqrt ((maxLocalTime x n : ℝ) * L) + L) := by
    intro y hy
    have h := hglob y hy
    rw [normPotential_norm_eq hd1] at h
    refine h.trans ?_
    have hCl : Cl ≤ C₁ := by
      have : 0 ≤ Cq * (C₀ + 1) := mul_nonneg hCq (by linarith)
      linarith
    have hKl : K.C_loc ≤ Cl := le_max_left _ _
    by_cases h2 : d = 2
    · simp only [h2, if_true] at h ⊢
      have hs : 0 ≤ Real.sqrt (maxLocalTime x n : ℝ) := Real.sqrt_nonneg _
      calc K.C_loc * Real.log n + K.C_loc * (Real.sqrt (maxLocalTime x n : ℝ) * Real.log n)
          ≤ Cl * L + Cl * (Real.sqrt (maxLocalTime x n : ℝ) * L) := by
            have e1 : K.C_loc * Real.log n ≤ Cl * L :=
              mul_le_mul hKl hlogL hlog0 hCl0
            have e2 : K.C_loc * (Real.sqrt (maxLocalTime x n : ℝ) * Real.log n) ≤
                Cl * (Real.sqrt (maxLocalTime x n : ℝ) * L) :=
              mul_le_mul hKl (mul_le_mul_of_nonneg_left hlogL hs) (by positivity) hCl0
            linarith
        _ = Cl * (Real.sqrt (maxLocalTime x n : ℝ) * L + L) := by ring
        _ ≤ C₁ * (Real.sqrt (maxLocalTime x n : ℝ) * L + L) :=
            mul_le_mul_of_nonneg_right hCl (by positivity)
    · simp only [h2, if_false] at h ⊢
      calc K.C_loc * Real.log n + K.C_loc * Real.sqrt ((maxLocalTime x n : ℝ) * Real.log n)
          ≤ Cl * L + Cl * Real.sqrt ((maxLocalTime x n : ℝ) * L) := by
            have e1 : K.C_loc * Real.log n ≤ Cl * L :=
              mul_le_mul hKl hlogL hlog0 hCl0
            have e2 : K.C_loc * Real.sqrt ((maxLocalTime x n : ℝ) * Real.log n) ≤
                Cl * Real.sqrt ((maxLocalTime x n : ℝ) * L) :=
              mul_le_mul hKl (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlogL hM0))
                (Real.sqrt_nonneg _) hCl0
            linarith
        _ = Cl * (Real.sqrt ((maxLocalTime x n : ℝ) * L) + L) := by ring
        _ ≤ C₁ * (Real.sqrt ((maxLocalTime x n : ℝ) * L) + L) :=
            mul_le_mul_of_nonneg_right hCl (by positivity)
  have hξE := field_eq_unitDir hξ hξ0
  have hquad' : |CERW.Support.Law.dynkin ε (fun z : Site d => euclidNorm z ^ 2)
      (fun j (_ : PUnit.{1}) => x j) n PUnit.unit| ≤ C₁ * (N * Real.sqrt (n * L) + N * L) := by
    rw [dynkin_sq_eq_quadraticMartingale hd1 ε x hlegal n, ← hξE]
    refine hquad.trans ?_
    have hsq : Real.sqrt ((n : ℝ) * Real.log n) ≤ Real.sqrt ((n : ℝ) * L) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlogL hnpos.le)
    have hH1 : maxRadius x n + 1 ≤ (C₀ + 1) * N := by nlinarith
    have hsqrt0 : 0 ≤ Real.sqrt ((n : ℝ) * L) := Real.sqrt_nonneg _
    have hNL : 0 ≤ N * L := mul_nonneg (by linarith) hL0
    have hKq : K.C_quad ≤ Cq := le_max_left _ _
    have hH0 : 0 ≤ maxRadius x n + 1 := by
      have : 0 ≤ maxRadius x n :=
        (LatticeProb.euclidNorm_nonneg _).trans (euclidNorm_le_maxRadius x (Nat.zero_le n))
      linarith
    have hsq0 : 0 ≤ Real.sqrt ((n : ℝ) * Real.log n) := Real.sqrt_nonneg _
    calc K.C_quad * (maxRadius x n + 1) * Real.sqrt ((n : ℝ) * Real.log n)
        ≤ Cq * (maxRadius x n + 1) * Real.sqrt ((n : ℝ) * Real.log n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKq hH0) hsq0
      _ ≤ Cq * ((C₀ + 1) * N) * Real.sqrt ((n : ℝ) * L) := by
          gcongr
      _ = Cq * (C₀ + 1) * (N * Real.sqrt (n * L)) := by ring
      _ ≤ C₁ * (N * Real.sqrt (n * L)) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith) hsqrt0)
          linarith
      _ ≤ C₁ * (N * Real.sqrt (n * L) + N * L) := by
          refine mul_le_mul_of_nonneg_left ?_ hC₁.le
          linarith
  have hcont' : ∀ y₀ : EuclideanSpace ℝ (Fin d),
      ‖y₀‖ = innerRadius (fun j => x j) n → y₀ ∈ closure (cellSet (fun j => x j) n)ᶜ →
        potential d ε (cellSet (fun j => x j) n) y₀ ≤
          Cc * ((d + 1) * n / (2 * d * ε *
              (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^
            ((1 : ℝ) / (d + 1)) *
            (if d = 2 then Real.sqrt (Real.log n / ((d + 1) * n / (2 * d * ε *
                (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^
                  ((1 : ℝ) / (d + 1)))
              else Real.log n / ((d + 1) * n / (2 * d * ε *
                (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^
                  ((1 : ℝ) / (d + 1))) := by
    intro y₀ h1 h2
    have h := hcont y₀ h1 h2
    rw [normPotential_norm_eq hd1, hq, hr] at h
    exact h
  have hmain := hcore (fun j (_ : PUnit.{1}) => x j) PUnit.unit n hnin hlegal.1 hcard' hM' hH'
    hglob' hquad' hcont'
  unfold InnerConclusion
  rw [hq, hr]
  exact hmain


end CERW.LimitShapes.InnerApproximation
