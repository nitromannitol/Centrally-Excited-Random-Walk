import CERW.Support.Statements
import CERW.Support.Geometry.Assembly
import CERW.Support.Contact.NormReplace
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellSetVolume
import CERW.Generic.Kernel.RadialPower
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The potential at a fixed site

`lem:fixed-site-centering`: for the Euclidean norm, every fixed site `y` and `0 < ε < 1/d`,
almost surely and for all large `n`,
`U_{D_n}(y) - 2dε(r_n - |y|) - Q_n / (ω_d r_n^d)` is bounded by `C (log n)^3` if `d = 2` and by
`C` if `d ≥ 3`, where `Q` is the quadratic martingale.

The statement follows from the fluctuation bounds of `fluctuation_rates` (Theorem 1.2 (i), (ii)):
the cell set `D_n` differs from `B(0, r_n)` only on the annulus `||v| - r_n| ≤ W_n` with
`|D_n ∆ B(0, r_n)| ≤ r_n^d m_n`. The potential is split as `U_{B(0, r_n)} + U_μ` with
`μ = 1_{D_n} - 1_{B(0, r_n)}`, the kernel of `U_μ` at `y` is compared with its value at the
origin and then with `r_n^{-d} |v|`, and `Σ_{A_n} |x|` replaces `∫_{D_n} |v|` at the cost of the
cell size.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Limit

open CERW.Support.Statements

section

variable {d : ℕ}

/-- The direction of `v` paired with `v` is the norm of `v`. -/
private lemma inner_unitDir_self (v : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (unitDir v) v = ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    rw [unitDir, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp

/-- Near the radius `r`, `s / s ^ d` is within `d 3^d |s - r| / r ^ d` of `s / r ^ d`. -/
private lemma abs_div_pow_sub_le (hd : 1 ≤ d) {r s : ℝ} (hr : 0 < r) (hs : |s - r| ≤ r / 2) :
    |s / s ^ d - s / r ^ d| ≤ d * 3 ^ d * |s - r| / r ^ d := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  have hs' := abs_le.mp hs
  have hs0 : 0 < s := by linarith [hs'.1]
  have hsr : s ≤ 3 * s ∧ r ≤ 2 * s := ⟨by linarith, by linarith [hs'.1]⟩
  have hsd : 0 < s ^ (k + 1) := pow_pos hs0 _
  have hrd : 0 < r ^ (k + 1) := pow_pos hr _
  have hdiff : |r ^ (k + 1) - s ^ (k + 1)| ≤ |r - s| * (k + 1) * (3 * s) ^ k := by
    have h := abs_pow_sub_pow_le (a := r) (b := s) (n := k + 1)
    rw [Nat.add_sub_cancel] at h
    refine h.trans ?_
    have hmax : max |r| |s| ≤ 3 * s := by
      rw [abs_of_pos hr, abs_of_pos hs0]
      exact max_le (by linarith [hs'.2]) (by linarith)
    have := pow_le_pow_left₀ (le_max_of_le_right (abs_nonneg s)) hmax k
    push_cast
    gcongr
  have heq : s / s ^ (k + 1) - s / r ^ (k + 1) = s * (r ^ (k + 1) - s ^ (k + 1)) /
      (s ^ (k + 1) * r ^ (k + 1)) := by
    field_simp
  rw [heq, abs_div, abs_mul, abs_of_pos hs0, abs_of_pos (mul_pos hsd hrd), abs_sub_comm s r]
  rw [div_le_div_iff₀ (mul_pos hsd hrd) hrd]
  have h3 : (3 * s) ^ k = 3 ^ k * s ^ k := mul_pow _ _ _
  calc s * |r ^ (k + 1) - s ^ (k + 1)| * r ^ (k + 1)
      ≤ s * (|r - s| * (k + 1) * (3 * s) ^ k) * r ^ (k + 1) := by gcongr
    _ = (k + 1 : ℕ) * 3 ^ k * |r - s| * (s ^ (k + 1) * r ^ (k + 1)) := by
        rw [h3, pow_succ s k]; push_cast; ring
    _ ≤ (k + 1 : ℕ) * 3 ^ (k + 1) * |r - s| * (s ^ (k + 1) * r ^ (k + 1)) := by
        have h31 : (3 : ℝ) ^ k ≤ 3 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
        gcongr

/-- The integrand of the potential at `y` differs from its value at the origin by at most
`(d 3^d + 1) |y| / |v|^d` when `|y| ≤ |v| / 2`. -/
private lemma abs_potentialIntegrand_sub_le (hd : 1 ≤ d) {v y : EuclideanSpace ℝ (Fin d)}
    (hv : v ≠ 0) (hy : ‖y‖ ≤ ‖v‖ / 2) :
    |inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d - ‖v‖ / ‖v‖ ^ d| ≤
      (d * 3 ^ d + 1) * ‖y‖ / ‖v‖ ^ d := by
  have ha : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hba : |‖v - y‖ - ‖v‖| ≤ ‖y‖ := by
    have h := abs_norm_sub_norm_le (v - y) v
    rwa [sub_sub_cancel_left, norm_neg] at h
  have hb2 : |‖v - y‖ - ‖v‖| ≤ ‖v‖ / 2 := hba.trans hy
  have hb0 : 0 < ‖v - y‖ := by linarith [abs_le.mp hb2]
  have hP : |inner ℝ (unitDir v) (v - y)| ≤ ‖v - y‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_unitDir_le v))
  have hQ : |inner ℝ (unitDir v) y| ≤ ‖y‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_unitDir_le v))
  have hinner : inner ℝ (unitDir v) (v - y) = ‖v‖ - inner ℝ (unitDir v) y := by
    rw [inner_sub_right, inner_unitDir_self]
  have hadp : 0 < ‖v‖ ^ d := pow_pos ha d
  have hbdp : 0 < ‖v - y‖ ^ d := pow_pos hb0 d
  have hdec : inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d - ‖v‖ / ‖v‖ ^ d =
      inner ℝ (unitDir v) (v - y) * (1 / ‖v - y‖ ^ d - 1 / ‖v‖ ^ d) -
        inner ℝ (unitDir v) y / ‖v‖ ^ d := by
    rw [hinner]
    field_simp
    ring
  have hfirst : |inner ℝ (unitDir v) (v - y) * (1 / ‖v - y‖ ^ d - 1 / ‖v‖ ^ d)| ≤
      d * 3 ^ d * ‖y‖ / ‖v‖ ^ d := by
    have hz : ‖v - y‖ * (1 / ‖v - y‖ ^ d - 1 / ‖v‖ ^ d) =
        ‖v - y‖ / ‖v - y‖ ^ d - ‖v - y‖ / ‖v‖ ^ d := by ring
    calc |inner ℝ (unitDir v) (v - y) * (1 / ‖v - y‖ ^ d - 1 / ‖v‖ ^ d)|
        = |inner ℝ (unitDir v) (v - y)| * |1 / ‖v - y‖ ^ d - 1 / ‖v‖ ^ d| := abs_mul _ _
      _ ≤ ‖v - y‖ * |1 / ‖v - y‖ ^ d - 1 / ‖v‖ ^ d| := by gcongr
      _ = |‖v - y‖ / ‖v - y‖ ^ d - ‖v - y‖ / ‖v‖ ^ d| := by
          rw [← hz, abs_mul, abs_of_pos hb0]
      _ ≤ d * 3 ^ d * |‖v - y‖ - ‖v‖| / ‖v‖ ^ d := abs_div_pow_sub_le hd ha hb2
      _ ≤ d * 3 ^ d * ‖y‖ / ‖v‖ ^ d := by gcongr
  have hsecond : |inner ℝ (unitDir v) y / ‖v‖ ^ d| ≤ ‖y‖ / ‖v‖ ^ d := by
    rw [abs_div, abs_of_pos hadp]
    gcongr
  rw [hdec]
  calc |inner ℝ (unitDir v) (v - y) * (1 / ‖v - y‖ ^ d - 1 / ‖v‖ ^ d) -
        inner ℝ (unitDir v) y / ‖v‖ ^ d|
      ≤ |inner ℝ (unitDir v) (v - y) * (1 / ‖v - y‖ ^ d - 1 / ‖v‖ ^ d)| +
        |inner ℝ (unitDir v) y / ‖v‖ ^ d| := abs_sub _ _
    _ ≤ d * 3 ^ d * ‖y‖ / ‖v‖ ^ d + ‖y‖ / ‖v‖ ^ d := add_le_add hfirst hsecond
    _ = (d * 3 ^ d + 1) * ‖y‖ / ‖v‖ ^ d := by ring

/-- Where `|‖v‖ - r| ≤ W ≤ r / 2` and `‖y‖ ≤ r / 4`, the integrand of `U_D(y)` is within
`(d 3^d + 1) 2^d (‖y‖ + W) / r^d` of `‖v‖ / r^d`. -/
private lemma abs_potentialIntegrand_sub_norm_le (hd : 1 ≤ d) {r W : ℝ} (hr : 0 < r)
    {v y : EuclideanSpace ℝ (Fin d)} (hv : |‖v‖ - r| ≤ W) (hW : W ≤ r / 2)
    (hy : ‖y‖ ≤ r / 4) :
    |inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d - ‖v‖ / r ^ d| ≤
      (d * 3 ^ d + 1) * 2 ^ d * (‖y‖ + W) / r ^ d := by
  have hvr : |‖v‖ - r| ≤ r / 2 := hv.trans hW
  have hhalf : r / 2 ≤ ‖v‖ := by linarith [abs_le.mp hvr]
  have hvpos : 0 < ‖v‖ := by linarith
  have hv0 : v ≠ 0 := norm_pos_iff.mp hvpos
  have hy2 : ‖y‖ ≤ ‖v‖ / 2 := by linarith
  have hW0 : 0 ≤ W := (abs_nonneg _).trans hv
  have h1 := abs_potentialIntegrand_sub_le hd hv0 hy2
  have h2 := abs_div_pow_sub_le hd hr hvr
  have hrd : 0 < r ^ d := pow_pos hr d
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hpow : (r / 2) ^ d ≤ ‖v‖ ^ d := pow_le_pow_left₀ (by linarith) hhalf d
  have hpow' : r ^ d / 2 ^ d ≤ ‖v‖ ^ d := by rwa [← div_pow]
  have hK0 : 0 ≤ (d * 3 ^ d + 1 : ℝ) * ‖y‖ := by positivity
  have h3 : (d * 3 ^ d + 1) * ‖y‖ / ‖v‖ ^ d ≤ (d * 3 ^ d + 1) * ‖y‖ * 2 ^ d / r ^ d := by
    calc (d * 3 ^ d + 1) * ‖y‖ / ‖v‖ ^ d
        ≤ (d * 3 ^ d + 1) * ‖y‖ / (r ^ d / 2 ^ d) :=
          div_le_div_of_nonneg_left hK0 (by positivity) hpow'
      _ = (d * 3 ^ d + 1) * ‖y‖ * 2 ^ d / r ^ d := by field_simp
  have h2' : |‖v‖ / ‖v‖ ^ d - ‖v‖ / r ^ d| ≤ d * 3 ^ d * W / r ^ d :=
    h2.trans (by gcongr)
  have hX : (d * 3 ^ d : ℝ) ≤ (d * 3 ^ d + 1) * 2 ^ d :=
    calc (d * 3 ^ d : ℝ) ≤ d * 3 ^ d + 1 := by linarith
      _ ≤ (d * 3 ^ d + 1) * 2 ^ d := le_mul_of_one_le_right (by positivity) h2d
  have hnum : (d * 3 ^ d + 1) * ‖y‖ * 2 ^ d + d * 3 ^ d * W ≤
      (d * 3 ^ d + 1) * 2 ^ d * (‖y‖ + W) := by
    have := mul_le_mul_of_nonneg_right hX hW0
    nlinarith
  calc |inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d - ‖v‖ / r ^ d|
      ≤ |inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d - ‖v‖ / ‖v‖ ^ d| +
        |‖v‖ / ‖v‖ ^ d - ‖v‖ / r ^ d| := abs_sub_le _ _ _
    _ ≤ (d * 3 ^ d + 1) * ‖y‖ * 2 ^ d / r ^ d + d * 3 ^ d * W / r ^ d :=
        add_le_add (h1.trans h3) h2'
    _ = ((d * 3 ^ d + 1) * ‖y‖ * 2 ^ d + d * 3 ^ d * W) / r ^ d := by rw [add_div]
    _ ≤ (d * 3 ^ d + 1) * 2 ^ d * (‖y‖ + W) / r ^ d :=
        div_le_div_of_nonneg_right hnum hrd.le

/-- For measurable sets of finite volume and a function integrable on both, the difference of
the integrals over `D` and over `B` is at most `M |D ∆ B|` if `|g| ≤ M` on `D ∆ B`. -/
private lemma abs_setIntegral_sub_le {g : EuclideanSpace ℝ (Fin d) → ℝ}
    {D B : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hB : MeasurableSet B)
    (hDfin : volume D ≠ ⊤) (hBfin : volume B ≠ ⊤)
    (hgD : IntegrableOn g D) (hgB : IntegrableOn g B) {M : ℝ} (hM : ∀ v ∈ D ∆ B, |g v| ≤ M) :
    |(∫ v in D, g v) - ∫ v in B, g v| ≤ M * (volume (D ∆ B)).toReal := by
  have h1 := integral_inter_add_sdiff hB hgD
  have h2 := integral_inter_add_sdiff hD hgB
  rw [Set.inter_comm B D] at h2
  have hdiff : (∫ v in D, g v) - ∫ v in B, g v =
      (∫ v in D \ B, g v) - ∫ v in B \ D, g v := by linarith
  have hfin1 : volume (D \ B) < ⊤ := (measure_mono Set.sdiff_subset).trans_lt hDfin.lt_top
  have hfin2 : volume (B \ D) < ⊤ := (measure_mono Set.sdiff_subset).trans_lt hBfin.lt_top
  have hb1 := norm_setIntegral_le_of_norm_le_const (f := g) (C := M) hfin1
    (fun v hv => by rw [Real.norm_eq_abs]; exact hM v (Or.inl hv))
  have hb2 := norm_setIntegral_le_of_norm_le_const (f := g) (C := M) hfin2
    (fun v hv => by rw [Real.norm_eq_abs]; exact hM v (Or.inr hv))
  rw [Real.norm_eq_abs] at hb1 hb2
  have hsd : (volume (D ∆ B)).toReal = (volume (D \ B)).toReal + (volume (B \ D)).toReal := by
    rw [measure_symmDiff_eq hD.nullMeasurableSet hB.nullMeasurableSet,
      ENNReal.toReal_add hfin1.ne hfin2.ne]
  rw [hdiff, hsd]
  calc |(∫ v in D \ B, g v) - ∫ v in B \ D, g v|
      ≤ |∫ v in D \ B, g v| + |∫ v in B \ D, g v| := abs_sub _ _
    _ ≤ M * (volume (D \ B)).toReal + M * (volume (B \ D)).toReal := add_le_add hb1 hb2
    _ = M * ((volume (D \ B)).toReal + (volume (B \ D)).toReal) := by ring

/-- A continuous function is integrable on a bounded set. -/
private lemma integrableOn_norm_of_isBounded {S : Set (EuclideanSpace ℝ (Fin d))}
    (hS : Bornology.IsBounded S) : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) S :=
  (continuous_norm.continuousOn.integrableOn_compact hS.isCompact_closure).mono_set
    subset_closure

/-- The potential of a bounded measurable set `D` whose symmetric difference with `B(0, r)` lies
in the annulus `||v| - r| ≤ W` is `2dε(r - |y|)` plus `(2ε / (ω_d r^d))` times the difference of
the first moments of `D` and `B(0, r)`, up to an error proportional to
`(|y| + W) |D ∆ B(0, r)| / r^d`. -/
private theorem abs_potential_sub_le (hd : 2 ≤ d) {ε r W : ℝ} (hε : 0 < ε) (hr : 0 < r)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    {y : EuclideanSpace ℝ (Fin d)} (hy : ‖y‖ ≤ r / 4) (hW : W ≤ r / 2)
    (hann : ∀ v ∈ D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, |‖v‖ - r| ≤ W) :
    |potential d ε D y - 2 * d * ε * (r - ‖y‖) -
        2 * ε / unitBallVolume d / r ^ d *
          ((∫ v in D, ‖v‖) - ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖)| ≤
      2 * ε / unitBallVolume d * ((d * 3 ^ d + 1) * 2 ^ d * (‖y‖ + W) / r ^ d *
        (volume (D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)).toReal) := by
  have hω := unitBallVolume_pos d
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hBb : Bornology.IsBounded (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) :=
    Metric.isBounded_ball
  have hBm : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) :=
    Metric.isOpen_ball.measurableSet
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hBfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hfD := Geometry.integrableOn_potentialIntegrand (d := d) (by omega) hD hDfin y
  have hfB := Geometry.integrableOn_potentialIntegrand (d := d) (by omega) hBm hBfin y
  have hnD := (integrableOn_norm_of_isBounded hDb).div_const (r ^ d)
  have hnB := (integrableOn_norm_of_isBounded hBb).div_const (r ^ d)
  have hM : ∀ v ∈ D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
      |inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d - ‖v‖ / r ^ d| ≤
        (d * 3 ^ d + 1) * 2 ^ d * (‖y‖ + W) / r ^ d := fun v hv =>
    abs_potentialIntegrand_sub_norm_le (by omega) hr (hann v hv) hW hy
  have key := abs_setIntegral_sub_le
    (g := fun v => inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d - ‖v‖ / r ^ d)
    hD hBm hDfin hBfin (hfD.sub hnD) (hfB.sub hnB) hM
  rw [integral_sub hfD hnD, integral_sub hfB hnB, integral_div, integral_div] at key
  have hpotB : potential d ε (Metric.ball 0 r) y = 2 * d * ε * (r - ‖y‖) := by
    rw [Geometry.potential_ball hd ε hr y, max_eq_left (by linarith)]
  have hpotD : potential d ε D y =
      2 * ε / unitBallVolume d * ∫ v in D, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d := rfl
  have hpotB' : potential d ε (Metric.ball 0 r) y = 2 * ε / unitBallVolume d *
      ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
        inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d := rfl
  have hLHS : potential d ε D y - 2 * d * ε * (r - ‖y‖) -
        2 * ε / unitBallVolume d / r ^ d *
          ((∫ v in D, ‖v‖) - ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖) =
      2 * ε / unitBallVolume d *
        (((∫ v in D, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) -
            (∫ v in D, ‖v‖) / r ^ d) -
          ((∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
              inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) -
            (∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖) / r ^ d)) := by
    rw [← hpotB, hpotD, hpotB']
    ring
  rw [hLHS, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left key hc

/-- Scaling by `r` carries `(r⁻¹ • S) ∆ B(0, 1)` to `S ∆ B(0, r)`, so the volumes differ by
`r^d`. -/
private lemma volume_symmDiff_ball {r : ℝ} (hr : 0 < r) (S : Set (EuclideanSpace ℝ (Fin d))) :
    volume (S ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) =
      ENNReal.ofReal (r ^ d) *
        volume ((r⁻¹ • S) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  have h : S ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r =
      r • ((r⁻¹ • S) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    rw [Set.smul_set_symmDiff₀ hr.ne', smul_inv_smul₀ hr.ne', smul_ball hr.ne', smul_zero,
      Real.norm_eq_abs, abs_of_pos hr, mul_one]
  rw [h, Measure.addHaar_smul, finrank_euclideanSpace_fin, abs_of_pos (pow_pos hr d)]

/-- The first moment of the ball: `∫_{B(0,r)} |v| dv = d ω_d r^{d+1} / (d + 1)`. -/
private lemma integral_ball_norm (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖ =
      d * unitBallVolume d * r ^ (d + 1) / (d + 1) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h := (Generic.Kernel.integrableOn_ball_rpow_neg_and_integral_eq (d := d) hd
    (s := -1) (ρ := r) (by linarith) hr).2
  simp only [neg_neg, Real.rpow_one] at h
  rw [h]
  have hexp : ((d : ℝ) - -1) = ((d + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hexp, Real.rpow_natCast]
  push_cast
  ring

/-- The first moments of the cell set and of the range differ by at most `(√d/2) |D_n|`, and
`|D_n| = |A_n|`. -/
private lemma abs_sum_sub_integral_le (X : ℕ → Site d) (n : ℕ) :
    |∑ x ∈ departureRange X n, euclidNorm x - ∫ v in cellSet X n, ‖v‖| ≤
      Real.sqrt d / 2 * (volume (cellSet X n)).toReal := by
  have h := Contact.abs_sum_euclidNorm_sub_integral_le X n
  rwa [Occupation.volume_cellSet, ENNReal.toReal_natCast]

/-- The volume of a set is at most that of `B(0, r)` plus that of its symmetric difference with
`B(0, r)`. -/
private lemma toReal_volume_le_add_symmDiff {r : ℝ} (hr : 0 < r)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hDfin : volume D ≠ ⊤) :
    (volume D).toReal ≤ r ^ d * unitBallVolume d +
      (volume (D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)).toReal := by
  have hBfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hsub : D ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r ∪
      D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r := by
    intro v hv
    by_cases hvB : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r
    · exact Or.inl hvB
    · exact Or.inr (Or.inl ⟨hv, hvB⟩)
  have hsdfin : volume (D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) ≠ ⊤ :=
    ((measure_mono (symmDiff_le_sup (a := D)
      (b := Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r))).trans_lt
        (measure_union_lt_top hDfin.lt_top hBfin.lt_top)).ne
  have h1 : volume D ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) +
      volume (D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) :=
    (measure_mono hsub).trans (measure_union_le _ _)
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hBfin, hsdfin⟩) h1
  rw [ENNReal.toReal_add hBfin hsdfin, Measure.addHaar_ball_of_pos volume 0 hr,
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_pos hr d).le] at h2
  exact h2

/-- The deterministic centering estimate at a fixed site. If `B(0, r)` and `D_n` differ only on
the annulus of width `A + B + √d/2` about the sphere of radius `r`, with `r^{d+1}` the radius
of the model, then the potential `U_{D_n}(y)` is centered by `2dε(r - |y|)` and
`Q_n / (ω_d r^d)` up to an error in terms of the width and of the volume parameter `m`. -/
private theorem abs_centering_le (hd : 2 ≤ d) {ε r A B m m₀ : ℝ} (hε : 0 < ε) (hr : 1 ≤ r)
    (X : ℕ → Site d) (n : ℕ) (y : Site d)
    (hrn : r ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d))
    (hy : euclidNorm y ≤ r / 4) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hAB : A + B + Real.sqrt d / 2 ≤ r / 2)
    (hA : r - A ≤ innerRadius X n) (hB : maxRadius X n ≤ r + B)
    (hmm : m ≤ m₀)
    (hm : (volume (cellSet X n ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)).toReal ≤
      r ^ d * m) :
    |potential d ε (cellSet X n) (toSpace y) - 2 * d * ε * (r - euclidNorm y) -
        quadraticMart ε X n / (unitBallVolume d * r ^ d)| ≤
      2 * ε / unitBallVolume d * ((d * 3 ^ d + 1) * 2 ^ d *
        (euclidNorm y + (A + B + Real.sqrt d / 2)) * m) +
      (ε * Real.sqrt d * (unitBallVolume d + m₀) + 4) / unitBallVolume d := by
  have hω := unitBallVolume_pos d
  have hr0 : 0 < r := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsq : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hrd : 0 < r ^ d := pow_pos hr0 d
  have hD := Occupation.measurableSet_cellSet X n
  have hDb : Bornology.IsBounded (cellSet X n) :=
    Metric.isBounded_ball.subset (Occupation.cellSet_subset_ball (by omega) X n)
  have hDfin : volume (cellSet X n) ≠ ⊤ := hDb.measure_lt_top.ne
  have hy' : ‖toSpace y‖ ≤ r / 4 := by rwa [norm_toSpace]
  have hann : ∀ v ∈ cellSet X n ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
      |‖v‖ - r| ≤ A + B + Real.sqrt d / 2 := by
    intro v hv
    rcases Set.mem_symmDiff.mp hv with ⟨hvD, hvB⟩ | ⟨hvB, hvD⟩
    · have h1 : r ≤ ‖v‖ := not_lt.mp (fun h => hvB (mem_ball_zero_iff.mpr h))
      have h2 := Occupation.norm_le_of_mem_cellSet X n hvD
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have h1 : ‖v‖ < r := mem_ball_zero_iff.mp hvB
      have h2 : innerRadius X n ≤ ‖v‖ :=
        csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact norm_nonneg w⟩ ⟨v, hvD, rfl⟩
      rw [abs_of_nonpos (by linarith)]
      linarith
  have hcore := abs_potential_sub_le hd hε hr0 hD hDb hy' hAB hann
  rw [norm_toSpace] at hcore
  have hKd : 0 ≤ (d * 3 ^ d + 1 : ℝ) * 2 ^ d * (euclidNorm y + (A + B + Real.sqrt d / 2)) / r ^ d :=
    by have := LatticeProb.euclidNorm_nonneg y; positivity
  have hstep : (d * 3 ^ d + 1 : ℝ) * 2 ^ d * (euclidNorm y + (A + B + Real.sqrt d / 2)) / r ^ d *
      (volume (cellSet X n ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)).toReal ≤
      (d * 3 ^ d + 1) * 2 ^ d * (euclidNorm y + (A + B + Real.sqrt d / 2)) * m := by
    calc _ ≤ (d * 3 ^ d + 1 : ℝ) * 2 ^ d * (euclidNorm y + (A + B + Real.sqrt d / 2)) / r ^ d *
          (r ^ d * m) := mul_le_mul_of_nonneg_left hm hKd
      _ = _ := by field_simp
  have hfirst := hcore.trans (mul_le_mul_of_nonneg_left hstep (by positivity))
  -- the second piece
  have hIB : ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖ = n / (2 * ε) := by
    rw [integral_ball_norm (by omega) hr0, hrn]
    field_simp
  have hvolD : (volume (cellSet X n)).toReal ≤ r ^ d * (unitBallVolume d + m₀) := by
    have h1 := toReal_volume_le_add_symmDiff hr0 hDfin
    calc (volume (cellSet X n)).toReal
        ≤ r ^ d * unitBallVolume d + r ^ d * m₀ := by
          refine h1.trans (add_le_add le_rfl (hm.trans ?_))
          exact mul_le_mul_of_nonneg_left hmm hrd.le
      _ = r ^ d * (unitBallVolume d + m₀) := by ring
  have hXn : euclidNorm (X n) ^ 2 ≤ 4 * r ^ d := by
    have h1 : euclidNorm (X n) ≤ maxRadius X n := euclidNorm_le_maxRadius X le_rfl
    have h2 : euclidNorm (X n) ≤ 2 * r := by linarith
    calc euclidNorm (X n) ^ 2 ≤ (2 * r) ^ 2 :=
          pow_le_pow_left₀ (LatticeProb.euclidNorm_nonneg _) h2 2
      _ = 4 * r ^ 2 := by ring
      _ ≤ 4 * r ^ d := by gcongr
  have hS := abs_sum_sub_integral_le X n
  set I := ∫ v in cellSet X n, ‖v‖ with hI
  set S := ∑ x ∈ departureRange X n, euclidNorm x with hSdef
  have hexpr : 2 * ε / unitBallVolume d / r ^ d *
      (I - ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖) -
        quadraticMart ε X n / (unitBallVolume d * r ^ d) =
      (2 * ε * (I - S) - euclidNorm (X n) ^ 2) / (unitBallVolume d * r ^ d) := by
    rw [hIB, quadraticMart]
    field_simp
    ring
  have hsecond : |2 * ε / unitBallVolume d / r ^ d *
      (I - ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖) -
        quadraticMart ε X n / (unitBallVolume d * r ^ d)| ≤
      (ε * Real.sqrt d * (unitBallVolume d + m₀) + 4) / unitBallVolume d := by
    rw [hexpr, abs_div, abs_of_pos (mul_pos hω hrd)]
    have hnum : |2 * ε * (I - S) - euclidNorm (X n) ^ 2| ≤
        (ε * Real.sqrt d * (unitBallVolume d + m₀) + 4) * r ^ d := by
      have h1 : |2 * ε * (I - S)| ≤ ε * Real.sqrt d * (unitBallVolume d + m₀) * r ^ d := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * ε), abs_sub_comm]
        calc 2 * ε * |S - I| ≤ 2 * ε * (Real.sqrt d / 2 * (volume (cellSet X n)).toReal) :=
              mul_le_mul_of_nonneg_left hS (by positivity)
          _ ≤ 2 * ε * (Real.sqrt d / 2 * (r ^ d * (unitBallVolume d + m₀))) := by gcongr
          _ = _ := by ring
      calc |2 * ε * (I - S) - euclidNorm (X n) ^ 2|
          ≤ |2 * ε * (I - S)| + |euclidNorm (X n) ^ 2| := abs_sub _ _
        _ ≤ ε * Real.sqrt d * (unitBallVolume d + m₀) * r ^ d + 4 * r ^ d := by
            rw [abs_of_nonneg (sq_nonneg (euclidNorm (X n)))]
            exact add_le_add h1 hXn
        _ = _ := by ring
    calc |2 * ε * (I - S) - euclidNorm (X n) ^ 2| / (unitBallVolume d * r ^ d)
        ≤ (ε * Real.sqrt d * (unitBallVolume d + m₀) + 4) * r ^ d /
            (unitBallVolume d * r ^ d) := div_le_div_of_nonneg_right hnum (by positivity)
      _ = _ := by field_simp
  calc |potential d ε (cellSet X n) (toSpace y) - 2 * d * ε * (r - euclidNorm y) -
        quadraticMart ε X n / (unitBallVolume d * r ^ d)|
      = |(potential d ε (cellSet X n) (toSpace y) - 2 * d * ε * (r - euclidNorm y) -
          2 * ε / unitBallVolume d / r ^ d *
            (I - ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖)) +
        (2 * ε / unitBallVolume d / r ^ d *
            (I - ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖v‖) -
          quadraticMart ε X n / (unitBallVolume d * r ^ d))| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hfirst hsecond)

/-- The volume of `S ∆ B(0, r)` is at most `r^d m` when that of `(r⁻¹ • S) ∆ B(0, 1)` is at
most `m`. -/
private lemma toReal_volume_symmDiff_le {r m : ℝ} (hr : 0 < r) (hm0 : 0 ≤ m)
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hm : volume ((r⁻¹ • S) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      ENNReal.ofReal m) :
    (volume (S ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)).toReal ≤ r ^ d * m := by
  rw [volume_symmDiff_ball hr S]
  have h : ENNReal.ofReal (r ^ d) *
      volume ((r⁻¹ • S) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      ENNReal.ofReal (r ^ d) * ENNReal.ofReal m := by gcongr
  rw [← ENNReal.ofReal_mul (pow_pos hr d).le] at h
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

/-- The `d + 1`-st power of `x ^ (1 / (d + 1))` is `x`. -/
private lemma rpow_inv_succ_pow (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / (d + 1))) ^ (d + 1) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have h : (1 : ℝ) / (d + 1) * ((d + 1 : ℕ) : ℝ) = 1 := by
    push_cast
    field_simp
  rw [h, Real.rpow_one]

/-- `L ^ (5/2) = (√L)^5`. -/
private lemma rpow_five_halves {L : ℝ} (hL : 0 ≤ L) :
    L ^ ((5 : ℝ) / 2) = Real.sqrt L ^ 5 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hL]
  norm_num

/-- Every fixed power of `log n` is eventually a small multiple of `(κ n)^{1/(d+1)}`. -/
private lemma eventually_mul_log_pow_le (d k : ℕ) {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, c * Real.log n ^ k ≤ (κ * n) ^ ((1 : ℝ) / (d + 1)) := by
  have hs : (0 : ℝ) < 1 / (d + 1) := by positivity
  have hO := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hs).def
    (c := κ ^ ((1 : ℝ) / (d + 1)) / c) (by positivity)
  have h' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hO
  filter_upwards [h'] with n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn0 _)] at hn
  rw [Real.mul_rpow hκ.le hn0]
  calc c * Real.log n ^ k = c * Real.log n ^ (k : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ c * |Real.log n ^ (k : ℝ)| := mul_le_mul_of_nonneg_left (le_abs_self _) hc.le
    _ ≤ c * (κ ^ ((1 : ℝ) / (d + 1)) / c * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) :=
        mul_le_mul_of_nonneg_left hn hc.le
    _ = κ ^ ((1 : ℝ) / (d + 1)) * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by field_simp

/-- The planar arithmetic: with `t = √r` and `u = √(log n)`, the width of the annulus times the
volume parameter is at most a multiple of `u^6 = (log n)^3`. -/
private lemma planar_arith {t u C p : ℝ} (ht : 1 ≤ t) (hu : 1 ≤ u) (hC : 0 < C) (hp : 0 ≤ p) :
    (p + C * (t * u) + C * t * u ^ 5) * (C * (u / t)) ≤ (2 * C ^ 2 + p * C) * u ^ 6 := by
  have ht0 : 0 < t := by linarith
  have h1 : u / t ≤ u ^ 6 :=
    (div_le_self (by linarith) ht).trans (le_self_pow₀ hu (by norm_num))
  have h3 : u ^ 2 ≤ u ^ 6 := pow_le_pow_right₀ hu (by norm_num)
  have e1 : C * (t * u) * (C * (u / t)) = C ^ 2 * u ^ 2 := by field_simp
  have e2 : C * t * u ^ 5 * (C * (u / t)) = C ^ 2 * u ^ 6 := by field_simp
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  calc (p + C * (t * u) + C * t * u ^ 5) * (C * (u / t))
      = p * (C * (u / t)) + C * (t * u) * (C * (u / t)) + C * t * u ^ 5 * (C * (u / t)) := by
        ring
    _ = p * (C * (u / t)) + C ^ 2 * u ^ 2 + C ^ 2 * u ^ 6 := by rw [e1, e2]
    _ ≤ p * (C * u ^ 6) + C ^ 2 * u ^ 6 + C ^ 2 * u ^ 6 := by
        gcongr
    _ = (2 * C ^ 2 + p * C) * u ^ 6 := by ring

/-- The planar case of the centering estimate, for a path whose range satisfies the planar
fluctuation bounds with constant `C₁` eventually. -/
private theorem centering_planar (hd2 : d = 2) {ε : ℝ} (hε : 0 < ε) (y : Site d) {C₁ : ℝ}
    (hC₁ : 0 < C₁) (r : ℕ → ℝ)
    (hr : ∀ n : ℕ, r n = ((d + 1) * n / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ → Site d,
      (∀ᶠ n : ℕ in atTop,
        (|innerRadius Y n - r n| ≤ C₁ * Real.sqrt (r n * Real.log n) ∧
          maxRadius Y n - r n ≤ C₁ * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)) ∧
        volume (((r n)⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
          ENNReal.ofReal (C₁ * Real.sqrt (Real.log n / r n))) →
      ∀ᶠ n : ℕ in atTop,
        |potential d ε (cellSet Y n) (toSpace y) - 2 * d * ε * (r n - euclidNorm y) -
            quadraticMart ε Y n / (unitBallVolume d * r n ^ d)| ≤ C * Real.log n ^ 3 := by
  have hd : 2 ≤ d := hd2.ge
  have hω := unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hy0 := LatticeProb.euclidNorm_nonneg y
  have hsq : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = euclidNorm y + Real.sqrt d / 2 := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  obtain ⟨Kd, hKd⟩ : ∃ Kd : ℝ, Kd = (d * 3 ^ d + 1) * 2 ^ d := ⟨_, rfl⟩
  have hKd0 : 0 ≤ Kd := by rw [hKd]; positivity
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ,
      K2 = (ε * Real.sqrt d * (unitBallVolume d + C₁) + 4) / unitBallVolume d := ⟨_, rfl⟩
  have hK20 : 0 ≤ K2 := by rw [hK2]; positivity
  have hc0 : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  refine ⟨2 * ε / unitBallVolume d * Kd * (2 * C₁ ^ 2 + p * C₁) + K2 + 1, by positivity,
    fun Y hY => ?_⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = (d + 1) / (2 * d * ε * unitBallVolume d) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have hrκ : ∀ n : ℕ, r n = (κ * n) ^ ((1 : ℝ) / (d + 1)) := fun n => by
    rw [hr n, hκdef]
    congr 1
    ring
  have hev : ∀ (k : ℕ) (c' : ℝ), 0 < c' → ∀ᶠ n : ℕ in atTop, c' * Real.log n ^ k ≤ r n := by
    intro k c' hc'
    filter_upwards [eventually_mul_log_pow_le d k hκ hc'] with n hn
    rwa [hrκ n]
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hY, hlog, hev 0 1 one_pos, hev 0 (4 * euclidNorm y + 1) (by positivity),
    hev 0 (2 * Real.sqrt d + 1) (by positivity), hev 6 (64 * C₁ ^ 2) (by positivity),
    hev 1 1 one_pos] with n hn hL hr1 hry hrs hr6 hrL
  simp only [pow_zero, mul_one, one_mul, pow_one] at hr1 hry hrs hrL
  have hrn : r n ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d) := by
    rw [hr n]
    exact rpow_inv_succ_pow d (by positivity)
  obtain ⟨⟨hin, hout⟩, hvol⟩ := hn
  have hr0 : 0 < r n := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.sqrt (r n) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.sqrt (Real.log n) := ⟨_, rfl⟩
  have ht1 : 1 ≤ t := by rw [ht]; exact Real.one_le_sqrt.mpr hr1
  have hu1 : 1 ≤ u := by rw [hu]; exact Real.one_le_sqrt.mpr hL
  have ht2 : t ^ 2 = r n := by rw [ht]; exact Real.sq_sqrt hr0.le
  have hu2 : u ^ 2 = Real.log n := by rw [hu]; exact Real.sq_sqrt (by linarith)
  have hut : u ≤ t := by rw [hu, ht]; exact Real.sqrt_le_sqrt hrL
  have ht0 : 0 < t := by linarith
  rw [Real.sqrt_mul hr0.le, ← ht, ← hu] at hin
  rw [rpow_five_halves (by linarith), ← ht, ← hu] at hout
  rw [Real.sqrt_div (by linarith), ← ht, ← hu] at hvol
  have hL3 : u ^ 6 = Real.log n ^ 3 := by rw [← hu2]; ring
  have ht8 : 8 * C₁ * Real.log n ^ 3 ≤ t := by
    rw [ht]
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    calc (8 * C₁ * Real.log n ^ 3) ^ 2 = 64 * C₁ ^ 2 * Real.log n ^ 6 := by ring
      _ ≤ r n := hr6
  have hu5 : u ^ 5 ≤ Real.log n ^ 3 := by
    rw [← hL3]
    exact pow_le_pow_right₀ hu1 (by norm_num)
  have hu5' : u ≤ u ^ 5 := le_self_pow₀ hu1 (by norm_num)
  have hA0 : 0 ≤ C₁ * (t * u) := by positivity
  have hB0 : 0 ≤ C₁ * t * u ^ 5 := by positivity
  have hAB : C₁ * (t * u) + C₁ * t * u ^ 5 + Real.sqrt d / 2 ≤ r n / 2 := by
    have h1 : C₁ * (t * u) ≤ C₁ * t * u ^ 5 := by
      calc C₁ * (t * u) = C₁ * t * u := by ring
        _ ≤ C₁ * t * u ^ 5 := by gcongr
    have h2 : C₁ * t * u ^ 5 ≤ C₁ * t * Real.log n ^ 3 := by gcongr
    have h3 : C₁ * t * Real.log n ^ 3 ≤ t * (t / 8) := by
      have : C₁ * Real.log n ^ 3 ≤ t / 8 := by linarith
      calc C₁ * t * Real.log n ^ 3 = t * (C₁ * Real.log n ^ 3) := by ring
        _ ≤ t * (t / 8) := by gcongr
    have h4 : t * (t / 8) = r n / 8 := by rw [← ht2]; ring
    linarith
  have hm := toReal_volume_symmDiff_le hr0 (by positivity) (cellSet Y n) hvol
  have hmm : C₁ * (u / t) ≤ C₁ := by
    have : u / t ≤ 1 := (div_le_one ht0).mpr hut
    calc C₁ * (u / t) ≤ C₁ * 1 := by gcongr
      _ = C₁ := mul_one _
  have hG := abs_centering_le hd hε hr1 Y n y hrn (by linarith) hA0 hB0 hAB
    (by linarith [(abs_le.mp hin).1]) (by linarith) hmm hm
  have harith := planar_arith ht1 hu1 hC₁ hp0
  have hinner : euclidNorm y + (C₁ * (t * u) + C₁ * t * u ^ 5 + Real.sqrt d / 2) =
      p + C₁ * (t * u) + C₁ * t * u ^ 5 := by rw [hp]; ring
  rw [hinner, ← hKd, ← hK2] at hG
  have h1 : Kd * (p + C₁ * (t * u) + C₁ * t * u ^ 5) * (C₁ * (u / t)) ≤
      Kd * ((2 * C₁ ^ 2 + p * C₁) * Real.log n ^ 3) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (by rw [← hL3]; exact harith) hKd0
  have hL31 : 1 ≤ Real.log n ^ 3 := one_le_pow₀ hL
  have h2 : K2 ≤ (K2 + 1) * Real.log n ^ 3 :=
    calc K2 = K2 * 1 := (mul_one _).symm
      _ ≤ K2 * Real.log n ^ 3 := mul_le_mul_of_nonneg_left hL31 hK20
      _ ≤ (K2 + 1) * Real.log n ^ 3 :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)
  calc _ ≤ 2 * ε / unitBallVolume d * (Kd * ((2 * C₁ ^ 2 + p * C₁) * Real.log n ^ 3)) + K2 :=
        hG.trans (add_le_add (mul_le_mul_of_nonneg_left h1 hc0) le_rfl)
    _ ≤ 2 * ε / unitBallVolume d * (Kd * ((2 * C₁ ^ 2 + p * C₁) * Real.log n ^ 3)) +
          (K2 + 1) * Real.log n ^ 3 := add_le_add le_rfl h2
    _ = _ := by ring

/-- The arithmetic of dimension at least three: if `L^(k+1) ≤ R` then the width times the
volume parameter is bounded. -/
private lemma high_arith {L R C p : ℝ} {k : ℕ} (hL : 1 ≤ L) (hR : 0 < R) (hC : 0 < C)
    (hp : 0 ≤ p) (hk : 1 ≤ k) (hLR : L ≤ R) (hLk : L ^ (k + 1) ≤ R) :
    (p + C * L + C * L ^ k) * (C * (L / R)) ≤ p * C + 2 * C ^ 2 := by
  have h1 : L / R ≤ 1 := (div_le_one hR).mpr hLR
  have h2 : L ^ (k + 1) / R ≤ 1 := (div_le_one hR).mpr hLk
  have h3 : L ^ 2 / R ≤ L ^ (k + 1) / R :=
    div_le_div_of_nonneg_right (pow_le_pow_right₀ hL (by omega)) hR.le
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  calc (p + C * L + C * L ^ k) * (C * (L / R))
      = p * (C * (L / R)) + C ^ 2 * (L ^ 2 / R) + C ^ 2 * (L ^ (k + 1) / R) := by ring
    _ ≤ p * (C * 1) + C ^ 2 * 1 + C ^ 2 * 1 := by
        gcongr
        exact h3.trans h2
    _ = p * C + 2 * C ^ 2 := by ring

/-- The case `d ≥ 3` of the centering estimate, for a path whose range satisfies the
fluctuation bounds with constant `C₁` eventually. -/
private theorem centering_high (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (y : Site d) {C₁ : ℝ}
    (hC₁ : 0 < C₁) (r : ℕ → ℝ)
    (hr : ∀ n : ℕ, r n = ((d + 1) * n / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ → Site d,
      (∀ᶠ n : ℕ in atTop,
        (|innerRadius Y n - r n| ≤ C₁ * Real.log n ∧
          maxRadius Y n - r n ≤ C₁ * Real.log n ^ ((d : ℝ) + 1)) ∧
        volume (((r n)⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
          ENNReal.ofReal (C₁ * (Real.log n / r n))) →
      ∀ᶠ n : ℕ in atTop,
        |potential d ε (cellSet Y n) (toSpace y) - 2 * d * ε * (r n - euclidNorm y) -
            quadraticMart ε Y n / (unitBallVolume d * r n ^ d)| ≤ C := by
  have hω := unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hy0 := LatticeProb.euclidNorm_nonneg y
  have hsq : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = euclidNorm y + Real.sqrt d / 2 := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  obtain ⟨Kd, hKd⟩ : ∃ Kd : ℝ, Kd = (d * 3 ^ d + 1) * 2 ^ d := ⟨_, rfl⟩
  have hKd0 : 0 ≤ Kd := by rw [hKd]; positivity
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ,
      K2 = (ε * Real.sqrt d * (unitBallVolume d + C₁) + 4) / unitBallVolume d := ⟨_, rfl⟩
  have hK20 : 0 ≤ K2 := by rw [hK2]; positivity
  have hc0 : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  refine ⟨2 * ε / unitBallVolume d * (Kd * (p * C₁ + 2 * C₁ ^ 2)) + K2 + 1, by positivity,
    fun Y hY => ?_⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = (d + 1) / (2 * d * ε * unitBallVolume d) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have hrκ : ∀ n : ℕ, r n = (κ * n) ^ ((1 : ℝ) / (d + 1)) := fun n => by
    rw [hr n, hκdef]
    congr 1
    ring
  have hev : ∀ (k : ℕ) (c' : ℝ), 0 < c' → ∀ᶠ n : ℕ in atTop, c' * Real.log n ^ k ≤ r n := by
    intro k c' hc'
    filter_upwards [eventually_mul_log_pow_le d k hκ hc'] with n hn
    rwa [hrκ n]
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hY, hlog, hev 0 1 one_pos, hev 0 (4 * euclidNorm y + 1) (by positivity),
    hev 0 (2 * Real.sqrt d + 1) (by positivity), hev (d + 1) (8 * C₁) (by positivity),
    hev (d + 1 + 1) 1 one_pos, hev 1 1 one_pos] with n hn hL hr1 hry hrs hr8 hrk hrL
  simp only [pow_zero, mul_one, one_mul, pow_one] at hr1 hry hrs hrL hrk
  have hrn : r n ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d) := by
    rw [hr n]
    exact rpow_inv_succ_pow d (by positivity)
  obtain ⟨⟨hin, hout⟩, hvol⟩ := hn
  have hr0 : 0 < r n := by linarith
  have hpow : Real.log n ^ ((d : ℝ) + 1) = Real.log n ^ (d + 1) := by
    rw [← Real.rpow_natCast]
    norm_num
  rw [hpow] at hout
  have hu5 : Real.log n ≤ Real.log n ^ (d + 1) := le_self_pow₀ hL (by omega)
  have hA0 : 0 ≤ C₁ * Real.log n := by positivity
  have hB0 : 0 ≤ C₁ * Real.log n ^ (d + 1) := by positivity
  have hAB : C₁ * Real.log n + C₁ * Real.log n ^ (d + 1) + Real.sqrt d / 2 ≤ r n / 2 := by
    have h1 : C₁ * Real.log n ≤ C₁ * Real.log n ^ (d + 1) := by gcongr
    have h2 : 8 * C₁ * Real.log n ^ (d + 1) ≤ r n := hr8
    linarith
  have hm := toReal_volume_symmDiff_le hr0 (by positivity) (cellSet Y n) hvol
  have hmm : C₁ * (Real.log n / r n) ≤ C₁ := by
    have : Real.log n / r n ≤ 1 := (div_le_one hr0).mpr hrL
    calc C₁ * (Real.log n / r n) ≤ C₁ * 1 := by gcongr
      _ = C₁ := mul_one _
  have hG := abs_centering_le hd hε hr1 Y n y hrn (by linarith) hA0 hB0 hAB
    (by linarith [(abs_le.mp hin).1]) (by linarith) hmm hm
  have harith := high_arith (k := d + 1) (C := C₁) (p := p) hL hr0 hC₁ hp0 (by omega) hrL hrk
  have hinner : euclidNorm y + (C₁ * Real.log n + C₁ * Real.log n ^ (d + 1) +
      Real.sqrt d / 2) = p + C₁ * Real.log n + C₁ * Real.log n ^ (d + 1) := by
    rw [hp]; ring
  rw [hinner, ← hKd, ← hK2] at hG
  have h1 : Kd * (p + C₁ * Real.log n + C₁ * Real.log n ^ (d + 1)) *
      (C₁ * (Real.log n / r n)) ≤ Kd * (p * C₁ + 2 * C₁ ^ 2) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left harith hKd0
  calc _ ≤ 2 * ε / unitBallVolume d * (Kd * (p * C₁ + 2 * C₁ ^ 2)) + K2 :=
        hG.trans (add_le_add (mul_le_mul_of_nonneg_left h1 hc0) le_rfl)
    _ ≤ _ := by linarith

end

/-- `lem:fixed-site-centering`: the potential of the cell set at a fixed site is centered by
`2dε(r_n - |y|) + Q_n / (ω_d r_n^d)`, up to `C (log n)^3` if `d = 2` and `C` if `d ≥ 3`. -/
theorem fixed_site_centering_of (hfluct : fluctuation_rates.{u}) : fixed_site_centering.{u} := by
  intro d hd ωd ε hε0 hε1 r y
  obtain ⟨C₁, hC₁, -, hae⟩ := hfluct hd ε hε0 hε1 1 one_pos
  by_cases hd2 : d = 2
  · obtain ⟨C, hC0, hC⟩ := centering_planar hd2 hε0 y hC₁ r (fun n => rfl)
    refine ⟨C, hC0, ?_⟩
    intro Ω _ μ _ X hX
    filter_upwards [hae μ X hX] with ω hω
    refine (hC (fun x => X x ω) (hω.mono fun n hn => ?_)).mono fun n hn => ?_
    · simp only [if_pos hd2] at hn
      exact ⟨hn.1, hn.2.1⟩
    · rw [if_pos hd2]
      exact hn
  · obtain ⟨C, hC0, hC⟩ := centering_high hd hε0 y hC₁ r (fun n => rfl)
    refine ⟨C, hC0, ?_⟩
    intro Ω _ μ _ X hX
    filter_upwards [hae μ X hX] with ω hω
    refine (hC (fun x => X x ω) (hω.mono fun n hn => ?_)).mono fun n hn => ?_
    · simp only [if_neg hd2] at hn
      exact ⟨hn.1, hn.2.1⟩
    · rw [if_neg hd2, mul_one]
      exact hn

end CERW.Support.Limit
