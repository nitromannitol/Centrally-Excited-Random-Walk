import CERW.Support.Geometry.Newton
import CERW.Support.Geometry.Bound
import CERW.Support.Occupation.Cells
import CERW.Support.Occupation.CellSetVolume

/-!
# The local-time profile

`eq:profile-rate`, deterministically. On `B(0, KN)` suppose `|ℓ̃_n - U_{D_n}| ≤ δ₀`, and
suppose `D_n ⊆ B(0, (K - 1)N)` with `K ≥ a + 1`, `B(0, b) ⊆ D_n`, `|b - aN| ≤ C₁ N Q`,
`|D_n \ B(0, b)| ≤ C₁ N^d Q` and `δ₀ ≤ C₁ N Q^{1/d}`, where `0 ≤ Q ≤ 1`. Then
`|ℓ_n(x)/N - 2dε (a - |x|/N)_+| ≤ C Q^{1/d}` for every site `x`. Inside, `U_{D_n}` is the ball
potential `2dε (b - |x|)_+` plus `O(ε m^{1/d})`. Outside, both sides vanish.
-/

namespace CERW.Support.Contact

open MeasureTheory LatticeProb CERW CERW.Support.Geometry CERW.Support.Occupation

variable {d : ℕ}

/-- `(N ^ d) ^ (1 / d) = N` for `N ≥ 0` and `d > 0`. -/
private lemma rpow_natCast_inv_self {N : ℝ} (hN : 0 ≤ N) (hd : 0 < d) :
    (N ^ d) ^ ((1 : ℝ) / d) = N := by
  have hdR : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact this.ne'
  rw [← Real.rpow_natCast N d, ← Real.rpow_mul hN]
  have hmul : (d : ℝ) * ((1 : ℝ) / (d : ℝ)) = 1 := by field_simp
  rw [hmul, Real.rpow_one]

/-- The scaling identity `max (u * N - v) 0 = N * max (u - v / N) 0` for `N > 0`. -/
private lemma max_mul_sub_div {N : ℝ} (hN : 0 < N) (u v : ℝ) :
    max (u * N - v) 0 = N * max (u - v / N) 0 := by
  rw [mul_max_of_nonneg _ _ hN.le, mul_zero]
  congr 1
  field_simp

/-- Raising the excess-volume bound to the power `1 / d`. -/
private lemma volume_rpow_inv_le {m C₁ N Q : ℝ} (hm0 : 0 ≤ m) (hC₁ : 0 ≤ C₁)
    (hN : 0 ≤ N) (hQ : 0 ≤ Q) (hm : m ≤ C₁ * N ^ d * Q) (hd : 0 < d) :
    m ^ ((1 : ℝ) / d) ≤ C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp : 0 ≤ (1 : ℝ) / d := le_of_lt (div_pos one_pos hdR)
  calc m ^ ((1 : ℝ) / d) ≤ (C₁ * N ^ d * Q) ^ ((1 : ℝ) / d) :=
        Real.rpow_le_rpow hm0 hm hp
    _ = C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d) := by
        rw [Real.mul_rpow (mul_nonneg hC₁ (pow_nonneg hN d)) hQ,
            Real.mul_rpow hC₁ (pow_nonneg hN d)]
        rw [rpow_natCast_inv_self hN hd]

/-- Splitting the potential over a measurable subset. -/
private lemma potential_sdiff_eq (hd : 1 ≤ d) {ε : ℝ}
    {A D : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (hAD : A ⊆ D) (y : EuclideanSpace ℝ (Fin d)) :
    potential d ε D y = potential d ε A y + potential d ε (D \ A) y := by
  have hF : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) D :=
    integrableOn_potentialIntegrand hd hD hDfin y
  have hFA : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) A := hF.mono_set hAD
  have hFE : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) (D \ A) := hF.mono_set Set.sdiff_subset
  have hunion : A ∪ (D \ A) = D := Set.union_sdiff_cancel hAD
  have hsplit : ∫ v in D, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d =
      (∫ v in A, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) +
      (∫ v in D \ A, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) := by
    conv_lhs => rw [← hunion]
    exact setIntegral_union Set.disjoint_sdiff_right (hD.diff hA) hFA hFE
  unfold potential
  rw [hsplit]
  ring

/-- `eq:profile-rate`: `|ℓ_n(x)/N - 2dε (a - |x|/N)_+| ≤ C Q^{1/d}` for every site, under the
displayed approximation, containment, inradius, excess-volume and error bounds. -/
theorem exists_abs_localTime_div_sub_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {a C₁ K : ℝ}
    (hC₁ : 0 ≤ C₁) (hK : a + 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ → Site d) (n : ℕ) (b δ₀ N Q : ℝ), 0 < N → 0 ≤ Q → Q ≤ 1 →
      0 < b → Metric.ball 0 b ⊆ cellSet X n → cellSet X n ⊆ Metric.ball 0 ((K - 1) * N) →
      |b - a * N| ≤ C₁ * N * Q →
      (volume (cellSet X n \ Metric.ball 0 b)).toReal ≤ C₁ * N ^ d * Q →
      δ₀ ≤ C₁ * N * Q ^ ((1 : ℝ) / d) →
      (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ < K * N →
        |cellLocalTime X n y - potential d ε (cellSet X n) y| ≤ δ₀) →
      ∀ x : Site d, |(localTime X n x : ℝ) / N - 2 * d * ε * max (a - euclidNorm x / N) 0| ≤
        C * Q ^ ((1 : ℝ) / d) := by
  have hdpos : 0 < d := by omega
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hdR1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hp_le_one : (1 : ℝ) / (d : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hdR]
    simpa using hdR1
  let Cd : ℝ := 2 * d * ε * unitBallVolume d ^ (-(1 : ℝ) / d)
  have hCd0 : 0 ≤ Cd := by
    have hω : 0 < unitBallVolume d := unitBallVolume_pos d
    have hr : 0 < unitBallVolume d ^ (-(1 : ℝ) / d) := Real.rpow_pos_of_pos hω _
    have : 0 < 2 * (d : ℝ) * ε * unitBallVolume d ^ (-(1 : ℝ) / d) := by positivity
    exact this.le
  have hCpos : 0 < C₁ + Cd * C₁ ^ ((1 : ℝ) / d) + 2 * (d : ℝ) * ε * C₁ + 1 := by
    have h1 : 0 ≤ Cd * C₁ ^ ((1 : ℝ) / d) := mul_nonneg hCd0 (Real.rpow_nonneg hC₁ _)
    have h2 : 0 ≤ 2 * (d : ℝ) * ε * C₁ := by positivity
    linarith
  refine ⟨C₁ + Cd * C₁ ^ ((1 : ℝ) / d) + 2 * (d : ℝ) * ε * C₁ + 1, hCpos, ?_⟩
  intro X n b δ₀ N Q hN hQ0 hQle hb hball hDsub hba hvol hδ hall x
  have hNpos : 0 < N := hN
  have hQp0 : 0 ≤ Q ^ ((1 : ℝ) / d) := Real.rpow_nonneg hQ0 _
  have hQleQp : Q ≤ Q ^ ((1 : ℝ) / d) := Real.self_le_rpow_of_le_one hQ0 hQle hp_le_one
  by_cases hx : euclidNorm x < K * N
  · have hlocal : |(localTime X n x : ℝ) -
        potential d ε (cellSet X n) (toSpace x)| ≤ δ₀ := by
      have h1 := hall (toSpace x) (by rw [norm_toSpace]; exact hx)
      rwa [cellLocalTime_of_mem_cell X n (toSpace_mem_cell x)] at h1
    have hDmeas : MeasurableSet (cellSet X n) := measurableSet_cellSet X n
    have hEmeas : MeasurableSet (cellSet X n \ Metric.ball 0 b) :=
      hDmeas.diff measurableSet_ball
    have hDfin : volume (cellSet X n) ≠ ⊤ :=
      (lt_of_le_of_lt (measure_mono hDsub) measure_ball_lt_top).ne
    have hEfin : volume (cellSet X n \ Metric.ball 0 b) ≠ ⊤ :=
      (lt_of_le_of_lt (measure_mono (Set.sdiff_subset.trans hDsub)) measure_ball_lt_top).ne
    have hsplit : potential d ε (cellSet X n) (toSpace x) =
        potential d ε (Metric.ball 0 b) (toSpace x) +
        potential d ε (cellSet X n \ Metric.ball 0 b) (toSpace x) :=
      potential_sdiff_eq hd1 measurableSet_ball hDmeas hDfin hball (toSpace x)
    have hUB : potential d ε (Metric.ball 0 b) (toSpace x) =
        2 * (d : ℝ) * ε * max (b - euclidNorm x) 0 := by
      rw [potential_ball hd ε hb (toSpace x), norm_toSpace]
    have hmle : (volume (cellSet X n \ Metric.ball 0 b)).toReal ^ ((1 : ℝ) / d) ≤
        C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d) :=
      volume_rpow_inv_le ENNReal.toReal_nonneg hC₁ hN.le hQ0 hvol hdpos
    have hUE : |potential d ε (cellSet X n \ Metric.ball 0 b) (toSpace x)| ≤
        Cd * (C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d)) := by
      calc |potential d ε (cellSet X n \ Metric.ball 0 b) (toSpace x)|
          ≤ Cd * (volume (cellSet X n \ Metric.ball 0 b)).toReal ^ ((1 : ℝ) / d) :=
            abs_potential_le hd1 hε.le hEmeas hEfin (toSpace x)
        _ ≤ Cd * (C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d)) :=
            mul_le_mul_of_nonneg_left hmle hCd0
    have hUBdiff : |potential d ε (Metric.ball 0 b) (toSpace x) -
        2 * (d : ℝ) * ε * max (a * N - euclidNorm x) 0| ≤
        2 * (d : ℝ) * ε * C₁ * N * Q ^ ((1 : ℝ) / d) := by
      rw [hUB]
      have hcoef : 0 ≤ 2 * (d : ℝ) * ε := by positivity
      rw [← mul_sub, abs_mul, abs_of_nonneg hcoef]
      have hmaxle : |max (b - euclidNorm x) 0 - max (a * N - euclidNorm x) 0| ≤
          C₁ * N * Q := by
        have h1 := abs_max_sub_max_le_abs (b - euclidNorm x) (a * N - euclidNorm x) 0
        have h2 : (b - euclidNorm x) - (a * N - euclidNorm x) = b - a * N := by ring
        rw [h2] at h1
        exact h1.trans hba
      calc 2 * (d : ℝ) * ε *
            |max (b - euclidNorm x) 0 - max (a * N - euclidNorm x) 0|
          ≤ 2 * (d : ℝ) * ε * (C₁ * N * Q) := mul_le_mul_of_nonneg_left hmaxle hcoef
        _ = 2 * (d : ℝ) * ε * C₁ * N * Q := by ring
        _ ≤ 2 * (d : ℝ) * ε * C₁ * N * Q ^ ((1 : ℝ) / d) := by
            have hQstep : C₁ * N * Q ≤ C₁ * N * Q ^ ((1 : ℝ) / d) :=
              mul_le_mul_of_nonneg_left hQleQp (mul_nonneg hC₁ hN.le)
            calc 2 * (d : ℝ) * ε * C₁ * N * Q
                = 2 * (d : ℝ) * ε * (C₁ * N * Q) := by ring
              _ ≤ 2 * (d : ℝ) * ε * (C₁ * N * Q ^ ((1 : ℝ) / d)) :=
                  mul_le_mul_of_nonneg_left hQstep hcoef
              _ = 2 * (d : ℝ) * ε * C₁ * N * Q ^ ((1 : ℝ) / d) := by ring
    have hA : |(localTime X n x : ℝ) - 2 * (d : ℝ) * ε * max (a * N - euclidNorm x) 0| ≤
        (C₁ + Cd * C₁ ^ ((1 : ℝ) / d) + 2 * (d : ℝ) * ε * C₁) *
          (N * Q ^ ((1 : ℝ) / d)) := by
      have hsum1 : |(localTime X n x : ℝ) -
            potential d ε (cellSet X n) (toSpace x)| +
            |potential d ε (cellSet X n \ Metric.ball 0 b) (toSpace x)| ≤
            C₁ * N * Q ^ ((1 : ℝ) / d) +
              Cd * (C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d)) :=
        add_le_add (hlocal.trans hδ) hUE
      have htri : |((localTime X n x : ℝ) - potential d ε (cellSet X n) (toSpace x)) +
            potential d ε (cellSet X n \ Metric.ball 0 b) (toSpace x) +
            (potential d ε (Metric.ball 0 b) (toSpace x) -
              2 * (d : ℝ) * ε * max (a * N - euclidNorm x) 0)| ≤
          |(localTime X n x : ℝ) - potential d ε (cellSet X n) (toSpace x)| +
            |potential d ε (cellSet X n \ Metric.ball 0 b) (toSpace x)| +
            |potential d ε (Metric.ball 0 b) (toSpace x) -
              2 * (d : ℝ) * ε * max (a * N - euclidNorm x) 0| := by
        have h1 := abs_add_le ((localTime X n x : ℝ) -
            potential d ε (cellSet X n) (toSpace x))
            (potential d ε (cellSet X n \ Metric.ball 0 b) (toSpace x))
        have h2 := abs_add_le
            (((localTime X n x : ℝ) - potential d ε (cellSet X n) (toSpace x)) +
              potential d ε (cellSet X n \ Metric.ball 0 b) (toSpace x))
            (potential d ε (Metric.ball 0 b) (toSpace x) -
              2 * (d : ℝ) * ε * max (a * N - euclidNorm x) 0)
        linarith
      have hdecomp : (localTime X n x : ℝ) -
          2 * (d : ℝ) * ε * max (a * N - euclidNorm x) 0 =
          ((localTime X n x : ℝ) - potential d ε (cellSet X n) (toSpace x)) +
            potential d ε (cellSet X n \ Metric.ball 0 b) (toSpace x) +
            (potential d ε (Metric.ball 0 b) (toSpace x) -
              2 * (d : ℝ) * ε * max (a * N - euclidNorm x) 0) := by
        rw [hsplit]
        ring
      calc |(localTime X n x : ℝ) - 2 * (d : ℝ) * ε * max (a * N - euclidNorm x) 0|
          = |((localTime X n x : ℝ) - potential d ε (cellSet X n) (toSpace x)) +
              potential d ε (cellSet X n \ Metric.ball 0 b) (toSpace x) +
              (potential d ε (Metric.ball 0 b) (toSpace x) -
                2 * (d : ℝ) * ε * max (a * N - euclidNorm x) 0)| := by rw [hdecomp]
        _ ≤ |(localTime X n x : ℝ) - potential d ε (cellSet X n) (toSpace x)| +
            |potential d ε (cellSet X n \ Metric.ball 0 b) (toSpace x)| +
            |potential d ε (Metric.ball 0 b) (toSpace x) -
              2 * (d : ℝ) * ε * max (a * N - euclidNorm x) 0| := htri
        _ ≤ C₁ * N * Q ^ ((1 : ℝ) / d) +
            Cd * (C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d)) +
            2 * (d : ℝ) * ε * C₁ * N * Q ^ ((1 : ℝ) / d) :=
            add_le_add hsum1 hUBdiff
        _ = (C₁ + Cd * C₁ ^ ((1 : ℝ) / d) + 2 * (d : ℝ) * ε * C₁) *
              (N * Q ^ ((1 : ℝ) / d)) := by ring
    have hmaxid : max (a * N - euclidNorm x) 0 =
        N * max (a - euclidNorm x / N) 0 := max_mul_sub_div hNpos a (euclidNorm x)
    have hnormeq : (localTime X n x : ℝ) / N -
        2 * (d : ℝ) * ε * max (a - euclidNorm x / N) 0 =
        ((localTime X n x : ℝ) - 2 * (d : ℝ) * ε * max (a * N - euclidNorm x) 0) / N := by
      rw [hmaxid]
      field_simp
    rw [hnormeq, abs_div, abs_of_pos hNpos]
    calc |(localTime X n x : ℝ) - 2 * (d : ℝ) * ε * max (a * N - euclidNorm x) 0| / N
        ≤ ((C₁ + Cd * C₁ ^ ((1 : ℝ) / d) + 2 * (d : ℝ) * ε * C₁) *
            (N * Q ^ ((1 : ℝ) / d))) / N := div_le_div_of_nonneg_right hA hNpos.le
      _ = (C₁ + Cd * C₁ ^ ((1 : ℝ) / d) + 2 * (d : ℝ) * ε * C₁) *
            Q ^ ((1 : ℝ) / d) := by field_simp
      _ ≤ (C₁ + Cd * C₁ ^ ((1 : ℝ) / d) + 2 * (d : ℝ) * ε * C₁ + 1) *
            Q ^ ((1 : ℝ) / d) := by
          apply mul_le_mul_of_nonneg_right _ hQp0
          linarith
  · have hKN : K * N ≤ euclidNorm x := le_of_not_gt hx
    have hxnot : x ∉ departureRange X n := by
      intro hxmem
      have hmem : toSpace x ∈ cellSet X n :=
        Set.mem_iUnion₂.mpr ⟨x, hxmem, toSpace_mem_cell x⟩
      have hlt := Metric.mem_ball.mp (hDsub hmem)
      rw [dist_zero_right, norm_toSpace] at hlt
      have hle : (K - 1) * N ≤ K * N :=
        mul_le_mul_of_nonneg_right (by linarith) hN.le
      linarith
    have hlt0 : localTime X n x = 0 := by
      rw [mem_departureRange_iff] at hxnot
      omega
    have hmax0 : max (a - euclidNorm x / N) 0 = 0 := by
      apply max_eq_right
      have hRdiv : K ≤ euclidNorm x / N := by
        rw [le_div_iff₀ hNpos]
        exact hKN
      have haK : a < K := by linarith
      linarith
    have hloc0 : (localTime X n x : ℝ) = 0 := by rw [hlt0]; norm_num
    rw [hloc0, hmax0]
    simp only [zero_div, mul_zero, sub_zero, abs_zero]
    exact mul_nonneg hCpos.le hQp0

end CERW.Support.Contact
