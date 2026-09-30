import CERW.Support.Contact.ContactMass
import CERW.Support.Contact.Envelope
import CERW.Support.Contact.PlanarBracket

/-!
# The planar contact variance

`eq:massplanar` and `eq:envelopeplanar`, deterministically, for `d = 2`. Let `m = |D_n \ B(0, b)|`
and `S = (K - 1) N`. Suppose the global approximation
`|ℓ̃_n - U_{D_n}| ≤ δ₀ ≤ C₀ √N L` holds on
`B(0, K N)`. Suppose also that the unvisited contact site `z` has the sharp decomposition
`0 = ℓ_n(z) = U(z) + ρ - M` with `|ρ| + |M| ≤ C₁ (√(B_z L) + L)`.
1. The contact inequality with the global approximation at `z` gives `m ≤ C N^{3/2} L`.
2. The envelope gives `ℓ_n ≤ 4ε (b - |·|)_+ + A` at departure sites, with
   `A = C N^{3/4} L^{1/2} + C₀ √N L`.
3. The planar hole bracket gives `B_z ≤ C N`, since `L^6 ≤ N`.
4. The contact inequality with the sharp decomposition gives `m ≤ C N^{3/2} √L = C N² Q`.
5. The envelope once more gives `ℓ_n ≤ 4ε (b - |·|)_+ + C N^{3/4} L^{1/4}`, and
   `N^{3/4} L^{1/4} = N Q^{1/2} = W`.
-/

namespace CERW.Support.Contact

open MeasureTheory LatticeProb CERW CERW.Support.Occupation

/-- The two-dimensional contact inequality: with `S = (K - 1) N`, the excess volume is at most
`(ω₂/(2ε)) · 2 · (K - 1) · N · (|ρ| + |M| + Δ)`. -/
private theorem contact_mass_planar {ε K N b : ℝ} (hε : 0 < ε) (hK : 2 ≤ K)
    (hN : 0 < N) (X : ℕ → Site 2) (n : ℕ) (hb : 0 ≤ b)
    (hball : Metric.ball 0 b ⊆ cellSet X n)
    (hDS : cellSet X n ⊆ Metric.closedBall 0 ((K - 1) * N))
    {y₀ : EuclideanSpace ℝ (Fin 2)} (hy₀ : ‖y₀‖ = b)
    {z : Site 2} (hz0 : localTime X n z = 0) {Δ ρ M : ℝ}
    (hpt : (localTime X n z : ℝ) = potential 2 ε (cellSet X n) (toSpace z) + ρ - M)
    (hmod : |potential 2 ε (cellSet X n) y₀ - potential 2 ε (cellSet X n) (toSpace z)| ≤ Δ) :
    (volume (cellSet X n \ Metric.ball 0 b)).toReal ≤
      unitBallVolume 2 / (2 * ε) * 2 * (K - 1) * N * (|ρ| + |M| + Δ) := by
  have hS : 0 < (K - 1) * N := by nlinarith
  have h := volume_sdiff_le_contact (d := 2) (by norm_num) hε X n hb hS hball hDS hy₀ hz0 hpt
    hmod
  have h2e : (2 : ℝ) ^ ((((2 : ℕ) : ℝ)) - 1) = 2 := by
    rw [show ((((2 : ℕ) : ℝ)) - 1) = 1 by norm_num, Real.rpow_one]
  have hSe : ((K - 1) * N) ^ ((((2 : ℕ) : ℝ)) - 1) = (K - 1) * N := by
    rw [show ((((2 : ℕ) : ℝ)) - 1) = 1 by norm_num, Real.rpow_one]
  rw [h2e, hSe] at h
  calc (volume (cellSet X n \ Metric.ball 0 b)).toReal
      ≤ unitBallVolume 2 / (2 * ε) * 2 * ((K - 1) * N) * (|ρ| + |M| + Δ) := h
    _ = unitBallVolume 2 / (2 * ε) * 2 * (K - 1) * N * (|ρ| + |M| + Δ) := by ring

/-- The local-time envelope at departure sites, from the global approximation: at every departure
site `x`, `ℓ_n(x) ≤ 4ε (b - |x|)_+ + 4ε ω₂^{-1/2} M^{1/2} + δ₀`, whenever `m ≤ M`. -/
private theorem localTime_le_envelope_departure {ε K N b δ₀ Mb : ℝ} (hε : 0 < ε)
    (hN : 0 < N) (hb : 0 < b) (X : ℕ → Site 2) (n : ℕ)
    (hball : Metric.ball 0 b ⊆ cellSet X n)
    (hDsub : cellSet X n ⊆ Metric.ball 0 ((K - 1) * N))
    (happrox : ∀ y : EuclideanSpace ℝ (Fin 2), ‖y‖ < K * N →
      |cellLocalTime X n y - potential 2 ε (cellSet X n) y| ≤ δ₀)
    (hmb : (volume (cellSet X n \ Metric.ball 0 b)).toReal ≤ Mb) :
    ∀ x ∈ departureRange X n, (localTime X n x : ℝ) ≤
      4 * ε * max (b - euclidNorm x) 0 +
        4 * ε * unitBallVolume 2 ^ (-(1 : ℝ) / 2) * Mb ^ ((1 : ℝ) / 2) + δ₀ := by
  intro x hx
  have hxmem : toSpace x ∈ cellSet X n := (toSpace_mem_cellSet_iff X n x).mpr hx
  have hxD : toSpace x ∈ Metric.ball 0 ((K - 1) * N) := hDsub hxmem
  have hxlt1 : euclidNorm x < (K - 1) * N := by
    rw [Metric.mem_ball, dist_zero_right, norm_toSpace] at hxD
    exact hxD
  have hxlt : ‖toSpace x‖ < K * N := by
    rw [norm_toSpace]
    nlinarith
  have happ : |cellLocalTime X n (toSpace x) -
      potential 2 ε (cellSet X n) (toSpace x)| ≤ δ₀ :=
    happrox (toSpace x) hxlt
  have hclt : cellLocalTime X n (toSpace x) = (localTime X n x : ℝ) :=
    cellLocalTime_of_mem_cell X n (toSpace_mem_cell x)
  have hpt : (localTime X n x : ℝ) = potential 2 ε (cellSet X n) (toSpace x) +
      (cellLocalTime X n (toSpace x) - potential 2 ε (cellSet X n) (toSpace x)) - 0 := by
    rw [hclt]; ring
  have henv := localTime_le_envelope (d := 2) (by norm_num) (le_of_lt hε) X n hb hball x hpt
  simp only [abs_zero] at henv
  have hmnn : 0 ≤ (volume (cellSet X n \ Metric.ball 0 b)).toReal := ENNReal.toReal_nonneg
  have hpow : (volume (cellSet X n \ Metric.ball 0 b)).toReal ^ ((1 : ℝ) / 2) ≤
      Mb ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow hmnn hmb (by norm_num)
  have hω : 0 ≤ unitBallVolume 2 ^ (-(1 : ℝ) / 2) :=
    Real.rpow_nonneg (le_of_lt (unitBallVolume_pos 2)) _
  have hstep1 : 4 * ε * unitBallVolume 2 ^ (-(1 : ℝ) / 2) *
      (volume (cellSet X n \ Metric.ball 0 b)).toReal ^ ((1 : ℝ) / 2) ≤
      4 * ε * unitBallVolume 2 ^ (-(1 : ℝ) / 2) * Mb ^ ((1 : ℝ) / 2) := by
    have hc : 0 ≤ 4 * ε * unitBallVolume 2 ^ (-(1 : ℝ) / 2) :=
      mul_nonneg (by positivity) hω
    exact mul_le_mul_of_nonneg_left hpow hc
  linarith [henv, hstep1, happ]

/-- The logarithmic bound `log (2 K N + 2) ≤ 8 (2 K + 2)^{1/8} N^{1/8}` for `K > 0`, `N ≥ 1`. -/
private theorem planar_log_bound {K N : ℝ} (hK : 0 < K) (hN : 1 ≤ N) :
    Real.log (2 * K * N + 2) ≤ 8 * (2 * K + 2) ^ ((1 : ℝ) / 8) * N ^ ((1 : ℝ) / 8) := by
  have hKN : 0 < 2 * K * N + 2 := by positivity
  have hlog := Real.log_le_rpow_div (le_of_lt hKN) (by norm_num : (0 : ℝ) < 1 / 8)
  have hlog' : Real.log (2 * K * N + 2) ≤ 8 * (2 * K * N + 2) ^ ((1 : ℝ) / 8) := by
    calc Real.log (2 * K * N + 2) ≤ (2 * K * N + 2) ^ ((1 : ℝ) / 8) / ((1 : ℝ) / 8) := hlog
      _ = 8 * (2 * K * N + 2) ^ ((1 : ℝ) / 8) := by
          rw [div_eq_mul_inv, show ((1 : ℝ) / 8)⁻¹ = 8 by norm_num]; ring
  have hbase : 0 ≤ 2 * K + 2 := by positivity
  have hNn : 0 ≤ N := le_trans (by norm_num) hN
  have hle : 2 * K * N + 2 ≤ (2 * K + 2) * N := by nlinarith
  have hrpow : (2 * K * N + 2) ^ ((1 : ℝ) / 8) ≤ ((2 * K + 2) * N) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow (le_of_lt hKN) hle (by norm_num)
  rw [Real.mul_rpow hbase hNn] at hrpow
  calc Real.log (2 * K * N + 2) ≤ 8 * (2 * K * N + 2) ^ ((1 : ℝ) / 8) := hlog'
    _ ≤ 8 * ((2 * K + 2) ^ ((1 : ℝ) / 8) * N ^ ((1 : ℝ) / 8)) := by gcongr
    _ = 8 * (2 * K + 2) ^ ((1 : ℝ) / 8) * N ^ ((1 : ℝ) / 8) := by ring

/-- `L^{1/2} ≤ N^{1/8}` when `L ≥ 1` and `L^6 ≤ N`. -/
private theorem rpow_half_le_eighth {N L : ℝ} (hL : 1 ≤ L) (hLN : L ^ 6 ≤ N) :
    L ^ ((1 : ℝ) / 2) ≤ N ^ ((1 : ℝ) / 8) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have h4 : L ^ 4 ≤ N := le_trans (pow_le_pow_right₀ hL (by norm_num : 4 ≤ 6)) hLN
  have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ L ^ 4) h4
    (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hconv : (L ^ 4) ^ ((1 : ℝ) / 8) = L ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast_mul (le_of_lt hLpos) 4 (1 / 8)]
    norm_num
  rwa [hconv] at h

/-- `L^{3/4} ≤ N^{1/4}` when `L ≥ 1` and `L^6 ≤ N`. -/
private theorem rpow_three_quarters_le {N L : ℝ} (hL : 1 ≤ L) (hLN : L ^ 6 ≤ N) :
    L ^ ((3 : ℝ) / 4) ≤ N ^ ((1 : ℝ) / 4) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have h3 : L ^ 3 ≤ N := le_trans (pow_le_pow_right₀ hL (by norm_num : 3 ≤ 6)) hLN
  have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ L ^ 3) h3
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hconv : (L ^ 3) ^ ((1 : ℝ) / 4) = L ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_natCast_mul (le_of_lt hLpos) 3 (1 / 4)]
    norm_num
  rwa [hconv] at h

/-- `N^{3/4} L^{1/2} N^{1/8} ≤ N` when `L ≥ 1` and `L^6 ≤ N`. -/
private theorem pow_term_A_le {N L : ℝ} (hN : 1 ≤ N) (hL : 1 ≤ L) (hLN : L ^ 6 ≤ N) :
    N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 8) ≤ N := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hLhalf : L ^ ((1 : ℝ) / 2) ≤ N ^ ((1 : ℝ) / 8) := rpow_half_le_eighth hL hLN
  have h78 : N ^ ((3 : ℝ) / 4) * N ^ ((1 : ℝ) / 8) = N ^ ((7 : ℝ) / 8) := by
    rw [← Real.rpow_add hNpos]; congr 1; norm_num
  calc N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 8)
      = N ^ ((3 : ℝ) / 4) * N ^ ((1 : ℝ) / 8) * L ^ ((1 : ℝ) / 2) := by ring
    _ = N ^ ((7 : ℝ) / 8) * L ^ ((1 : ℝ) / 2) := by rw [h78]
    _ ≤ N ^ ((7 : ℝ) / 8) * N ^ ((1 : ℝ) / 8) := by
        have : 0 ≤ N ^ ((7 : ℝ) / 8) := Real.rpow_nonneg (le_of_lt hNpos) _
        exact mul_le_mul_of_nonneg_left hLhalf this
    _ = N ^ ((7 : ℝ) / 8 + (1 : ℝ) / 8) := (Real.rpow_add hNpos _ _).symm
    _ = N := by rw [show (7 : ℝ) / 8 + 1 / 8 = 1 by norm_num, Real.rpow_one]

/-- `N^{1/2} L N^{1/8} ≤ N` when `L ≥ 1` and `L^6 ≤ N`. -/
private theorem pow_term_B_le {N L : ℝ} (hN : 1 ≤ N) (hL : 1 ≤ L) (hLN : L ^ 6 ≤ N) :
    N ^ ((1 : ℝ) / 2) * L * N ^ ((1 : ℝ) / 8) ≤ N := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hL6 : L ≤ N ^ ((1 : ℝ) / 6) := by
    have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ L ^ 6) hLN
      (by norm_num : (0 : ℝ) ≤ 1 / 6)
    have hconv : (L ^ 6) ^ ((1 : ℝ) / 6) = L := by
      rw [← Real.rpow_natCast_mul (le_of_lt hLpos) 6 (1 / 6)]
      norm_num
    rwa [hconv] at h
  calc N ^ ((1 : ℝ) / 2) * L * N ^ ((1 : ℝ) / 8)
      = N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 8) * L := by ring
    _ ≤ N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 8) * N ^ ((1 : ℝ) / 6) := by
        have : 0 ≤ N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 8) :=
          mul_nonneg (Real.rpow_nonneg (le_of_lt hNpos) _) (Real.rpow_nonneg (le_of_lt hNpos) _)
        exact mul_le_mul_of_nonneg_left hL6 this
    _ = N ^ ((1 : ℝ) / 2 + 1 / 8 + 1 / 6) := by
        rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    _ ≤ N := by
        have h := Real.rpow_le_rpow_of_exponent_le hN
          (show (1 : ℝ) / 2 + 1 / 8 + 1 / 6 ≤ (1 : ℝ) by norm_num)
        rwa [Real.rpow_one] at h

/-- `√N · L ≤ N^{3/4} L^{1/4}` when `L ≥ 1` and `L^6 ≤ N`. -/
private theorem sqrt_mul_le {N L : ℝ} (hN : 1 ≤ N) (hL : 1 ≤ L) (hLN : L ^ 6 ≤ N) :
    Real.sqrt N * L ≤ N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hsq : Real.sqrt N = N ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow N
  have hLsplit : L = L ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hLpos]; norm_num
  have h34 : L ^ ((3 : ℝ) / 4) ≤ N ^ ((1 : ℝ) / 4) := rpow_three_quarters_le hL hLN
  have hN12 : 0 ≤ N ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hNpos) _
  have hstep : N ^ ((1 : ℝ) / 2) * L ^ ((3 : ℝ) / 4) ≤
      N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_left h34 hN12
  have hNpow : N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 4) = N ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hNpos]; norm_num
  rw [hsq]
  conv_lhs => rw [hLsplit]
  calc N ^ ((1 : ℝ) / 2) * (L ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4))
      = (N ^ ((1 : ℝ) / 2) * L ^ ((3 : ℝ) / 4)) * L ^ ((1 : ℝ) / 4) := by ring
    _ ≤ (N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 4)) * L ^ ((1 : ℝ) / 4) := by
        have : 0 ≤ L ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (le_of_lt hLpos) _
        exact mul_le_mul_of_nonneg_right hstep this
    _ = N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) := by rw [hNpow]

/-- `(a (N^{3/2} L))^{1/2} = a^{1/2} N^{3/4} L^{1/2}`. -/
private theorem rpow_half_of_mul_l {a N L : ℝ} (ha : 0 ≤ a) (hN : 0 ≤ N) (hL : 0 ≤ L) :
    (a * (N ^ ((3 : ℝ) / 2) * L)) ^ ((1 : ℝ) / 2) =
      a ^ ((1 : ℝ) / 2) * N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 2) := by
  rw [Real.mul_rpow ha (mul_nonneg (Real.rpow_nonneg hN _) hL)]
  rw [Real.mul_rpow (Real.rpow_nonneg hN _) hL]
  rw [← Real.rpow_mul hN (3 / 2) (1 / 2)]
  norm_num
  ring

/-- `(a (N^{3/2} L^{1/2}))^{1/2} = a^{1/2} N^{3/4} L^{1/4}`. -/
private theorem rpow_half_of_mul {a N L : ℝ} (ha : 0 ≤ a) (hN : 0 ≤ N) (hL : 0 ≤ L) :
    (a * (N ^ ((3 : ℝ) / 2) * L ^ ((1 : ℝ) / 2))) ^ ((1 : ℝ) / 2) =
      a ^ ((1 : ℝ) / 2) * N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) := by
  rw [Real.mul_rpow ha (mul_nonneg (Real.rpow_nonneg hN _) (Real.rpow_nonneg hL _))]
  rw [Real.mul_rpow (Real.rpow_nonneg hN _) (Real.rpow_nonneg hL _)]
  rw [← Real.rpow_mul hN (3 / 2) (1 / 2), ← Real.rpow_mul hL (1 / 2) (1 / 2)]
  norm_num
  ring

/-- `N² (L/N)^{1/2} = N^{3/2} L^{1/2}` for `N > 0`, `L ≥ 0`. -/
private theorem sq_mul_div_rpow_half {N L : ℝ} (hN : 0 < N) (hL : 0 ≤ L) :
    N ^ 2 * (L / N) ^ ((1 : ℝ) / 2) = N ^ ((3 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) := by
  have hNn : 0 ≤ N := le_of_lt hN
  have h1 : (L / N) ^ ((1 : ℝ) / 2) = L ^ ((1 : ℝ) / 2) / N ^ ((1 : ℝ) / 2) :=
    Real.div_rpow hL hNn ((1 : ℝ) / 2)
  have hN32 : N ^ ((3 : ℝ) / 2) = N ^ ((2 : ℝ)) * N ^ (-((1 : ℝ) / 2)) := by
    rw [← Real.rpow_add hN]; congr 1; ring
  have hN2 : (N : ℝ) ^ 2 = N ^ ((2 : ℝ)) := (Real.rpow_natCast N 2).symm
  rw [h1]
  rw [hN2]
  rw [hN32]
  rw [Real.rpow_neg hNn]
  field_simp

/-- `N ((L/N)^{1/2})^{1/2} = N^{3/4} L^{1/4}` for `N > 0`, `L ≥ 0`. -/
private theorem rpow_half_half {N L : ℝ} (hN : 0 < N) (hL : 0 ≤ L) :
    N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) =
      N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) := by
  have hNn : 0 ≤ N := le_of_lt hN
  have hLN : 0 ≤ L / N := div_nonneg hL hNn
  have h1 : ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) = (L / N) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_mul hLN (1 / 2) (1 / 2)]; norm_num
  have h2 : (L / N) ^ ((1 : ℝ) / 4) = L ^ ((1 : ℝ) / 4) / N ^ ((1 : ℝ) / 4) :=
    Real.div_rpow hL hNn ((1 : ℝ) / 4)
  have hN34 : N ^ ((3 : ℝ) / 4) = N ^ ((1 : ℝ)) * N ^ (-((1 : ℝ) / 4)) := by
    rw [← Real.rpow_add hN]; congr 1; ring
  rw [h1]
  rw [h2]
  rw [hN34]
  rw [Real.rpow_one]
  rw [Real.rpow_neg hNn]
  field_simp

/-- If `a ≤ c x L`, `d ≤ c x`, `0 ≤ c x` and `1 ≤ L`, then `a + d ≤ 2 c x L`. -/
private theorem add_le_two_mul_of_le_mul {a d c x L : ℝ} (ha : a ≤ c * x * L)
    (hd : d ≤ c * x) (hcx : 0 ≤ c * x) (hL : 1 ≤ L) : a + d ≤ 2 * c * x * L := by
  nlinarith

/-- `eq:massplanar` and `eq:envelopeplanar`: in the plane, the global approximation and the sharp
decomposition at the unvisited contact site give `m ≤ C N² Q` and
`ℓ_n ≤ 4ε (b - |·|)_+ + C W`,
where `Q = (L/N)^{1/2}` and `W = N Q^{1/2}`. -/
theorem exists_mass_planar {ε K C₀ C₁ : ℝ} (hε : 0 < ε) (hK : 2 ≤ K) (hC₀ : 0 ≤ C₀)
    (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ → Site 2) (n : ℕ) (b N L δ₀ Δ ρ M : ℝ) (z : Site 2)
      (y₀ : EuclideanSpace ℝ (Fin 2)), 1 ≤ L → L ^ 6 ≤ N → 0 < b →
      Metric.ball 0 b ⊆ cellSet X n → cellSet X n ⊆ Metric.ball 0 ((K - 1) * N) →
      δ₀ ≤ C₀ * Real.sqrt N * L →
      (∀ y : EuclideanSpace ℝ (Fin 2), ‖y‖ < K * N →
        |cellLocalTime X n y - potential 2 ε (cellSet X n) y| ≤ δ₀) →
      ‖y₀‖ = b → localTime X n z = 0 → b ≤ euclidNorm z → euclidNorm z < K * N →
      |potential 2 ε (cellSet X n) y₀ - potential 2 ε (cellSet X n) (toSpace z)| ≤ Δ →
      Δ ≤ C₀ * Real.sqrt N →
      (localTime X n z : ℝ) = potential 2 ε (cellSet X n) (toSpace z) + ρ - M →
      |ρ| + |M| ≤ C₁ * (Real.sqrt ((∑ x ∈ departureRange X n,
          (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (-2 : ℝ)) * L) + L) →
      (volume (cellSet X n \ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) b)).toReal
          ≤ C * N ^ 2 * (L / N) ^ ((1 : ℝ) / 2) ∧
      ∀ y : Site 2, (localTime X n y : ℝ) ≤
        4 * ε * max (b - euclidNorm y) 0 + C * N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) := by
  obtain ⟨Cb, hCbpos, hbracket⟩ := exists_planar_bracket_le
  let cU : ℝ := unitBallVolume 2 / (2 * ε) * 2
  let cN : ℝ := cU * (K - 1)
  let LK : ℝ := 8 * (2 * K + 2) ^ ((1 : ℝ) / 8)
  let K1 : ℝ := (2 * cN * C₀) ^ ((1 : ℝ) / 2)
  let A1c : ℝ := 4 * ε * unitBallVolume 2 ^ (-(1 : ℝ) / 2) * K1
  let Cz : ℝ := Cb * (4 * ε * (2 * K + 1) + A1c * LK + C₀ * LK)
  let M0 : ℝ := cN * (C₁ * Real.sqrt Cz + C₁ + C₀)
  let C : ℝ := M0 + 4 * ε * unitBallVolume 2 ^ (-(1 : ℝ) / 2) * Real.sqrt M0 + C₀ + 1
  have hωpos : 0 < unitBallVolume 2 := unitBallVolume_pos 2
  have hKpos : 0 < K := by linarith
  have hKm1pos : 0 < K - 1 := by linarith
  have hcUpos : 0 < cU := by simp only [cU]; positivity
  have hcNpos : 0 < cN := by simp only [cN]; exact mul_pos hcUpos hKm1pos
  have hLKpos : 0 < LK := by simp only [LK]; positivity
  have hK1nn : 0 ≤ K1 := by simp only [K1]; positivity
  have hA1cnn : 0 ≤ A1c := by simp only [A1c]; positivity
  have hCzpos : 0 < Cz := by simp only [Cz]; positivity
  have hM0nn : 0 ≤ M0 := by simp only [M0]; positivity
  have hCpos : 0 < C := by simp only [C]; positivity
  refine ⟨C, hCpos, ?_⟩
  intro X n b N L δ₀ Δ ρ M z y₀ hL hLN hb hball hDsub hδ happrox hy₀ hz0 hbz hzN hmod
    hΔ hpt hρM
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have hN1 : 1 ≤ N := le_trans (one_le_pow₀ hL) hLN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hNnn : 0 ≤ N := le_of_lt hNpos
  have hδ0 : 0 ≤ δ₀ := by
    have h0 : ‖(0 : EuclideanSpace ℝ (Fin 2))‖ < K * N := by
      simpa using mul_pos hKpos hNpos
    exact le_trans (abs_nonneg _) (happrox 0 h0)
  set m : ℝ := (volume (cellSet X n \ Metric.ball 0 b)).toReal with hmdef
  set Bz : ℝ := ∑ x ∈ departureRange X n,
      (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (-2 : ℝ) with hBzdef
  have hDS1 : cellSet X n ⊆ Metric.closedBall 0 ((K - 1) * N) :=
    fun v hv => Metric.ball_subset_closedBall (hDsub hv)
  have hN32 : N * N ^ ((1 : ℝ) / 2) = N ^ ((3 : ℝ) / 2) := by
    nth_rewrite 1 [← Real.rpow_one N]
    rw [← Real.rpow_add hNpos]
    norm_num
  -- Step 1: the global approximation gives m ≤ 2 cN C₀ N^{3/2} L.
  have hUle : |potential 2 ε (cellSet X n) (toSpace z)| ≤ δ₀ := by
    have hzlt : ‖toSpace z‖ < K * N := by rw [norm_toSpace]; exact hzN
    have h := happrox (toSpace z) hzlt
    have hclt : cellLocalTime X n (toSpace z) = (localTime X n z : ℝ) :=
      cellLocalTime_of_mem_cell X n (toSpace_mem_cell z)
    rw [hclt, hz0] at h
    simpa using h
  have hpt1 : (localTime X n z : ℝ) = potential 2 ε (cellSet X n) (toSpace z) +
      (-potential 2 ε (cellSet X n) (toSpace z)) - 0 := by
    rw [hz0]; ring
  have hcontact1 := contact_mass_planar hε hK hNpos X n hb.le hball hDS1 hy₀ hz0 hpt1 hmod
  rw [← hmdef] at hcontact1
  have hm1 : m ≤ 2 * cN * C₀ * (N ^ ((3 : ℝ) / 2) * L) := by
    rw [abs_neg, abs_zero] at hcontact1
    have hsum : |potential 2 ε (cellSet X n) (toSpace z)| + Δ ≤
        2 * C₀ * N ^ ((1 : ℝ) / 2) * L := by
      have h1 : |potential 2 ε (cellSet X n) (toSpace z)| ≤ C₀ * N ^ ((1 : ℝ) / 2) * L := by
        rw [Real.sqrt_eq_rpow] at hδ
        exact le_trans hUle hδ
      have h2 : Δ ≤ C₀ * N ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow] at hΔ
        exact hΔ
      have h3 : 0 ≤ C₀ * N ^ ((1 : ℝ) / 2) := mul_nonneg hC₀ (Real.rpow_nonneg hNnn _)
      exact add_le_two_mul_of_le_mul h1 h2 h3 hL
    have hcoef : 0 ≤ unitBallVolume 2 / (2 * ε) * 2 * (K - 1) * N := by
      have h1 : 0 ≤ unitBallVolume 2 / (2 * ε) :=
        div_nonneg (le_of_lt hωpos) (by linarith [hε])
      have h2 : 0 ≤ unitBallVolume 2 / (2 * ε) * 2 * (K - 1) :=
        mul_nonneg (mul_nonneg h1 (by norm_num)) (le_of_lt hKm1pos)
      exact mul_nonneg h2 (le_of_lt hNpos)
    have hmid : |potential 2 ε (cellSet X n) (toSpace z)| + 0 + Δ ≤
        2 * C₀ * N ^ ((1 : ℝ) / 2) * L := by simpa using hsum
    have hstep : m ≤ unitBallVolume 2 / (2 * ε) * 2 * (K - 1) * N *
        (2 * C₀ * N ^ ((1 : ℝ) / 2) * L) := by
      calc m ≤ unitBallVolume 2 / (2 * ε) * 2 * (K - 1) * N *
            (|potential 2 ε (cellSet X n) (toSpace z)| + 0 + Δ) := hcontact1
        _ ≤ unitBallVolume 2 / (2 * ε) * 2 * (K - 1) * N *
            (2 * C₀ * N ^ ((1 : ℝ) / 2) * L) :=
            mul_le_mul_of_nonneg_left hmid hcoef
    calc m ≤ unitBallVolume 2 / (2 * ε) * 2 * (K - 1) * N *
          (2 * C₀ * N ^ ((1 : ℝ) / 2) * L) := hstep
      _ = 2 * cN * C₀ * (N ^ ((3 : ℝ) / 2) * L) := by
          simp only [cN, cU]
          rw [← hN32]; ring
  -- Steps 2 and 5: the envelope at departure sites.
  let A1 : ℝ := A1c * N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 2) + C₀ * Real.sqrt N * L
  have hA1nn : 0 ≤ A1 := by
    have h1 : 0 ≤ A1c * N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 2) :=
      mul_nonneg (mul_nonneg hA1cnn (Real.rpow_nonneg hNnn _)) (Real.rpow_nonneg hLnn _)
    have h2 : 0 ≤ C₀ * Real.sqrt N * L :=
      mul_nonneg (mul_nonneg hC₀ (Real.sqrt_nonneg N)) hLnn
    simp only [A1]
    exact add_nonneg h1 h2
  have hA1dep : ∀ x ∈ departureRange X n, (localTime X n x : ℝ) ≤
      4 * ε * max (b - euclidNorm x) 0 + A1 := by
    intro x hx
    rw [hmdef] at hm1
    have henv := localTime_le_envelope_departure hε hNpos hb X n hball hDsub happrox hm1 x hx
    have hMb1 : (2 * cN * C₀ * (N ^ ((3 : ℝ) / 2) * L)) ^ ((1 : ℝ) / 2) =
        K1 * (N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 2)) := by
      simp only [K1]
      rw [rpow_half_of_mul_l (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hcNpos)) hC₀)
        hNnn hLnn]
      ring
    have hcoefnn : 0 ≤ 4 * ε * unitBallVolume 2 ^ (-(1 : ℝ) / 2) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hε))
        (Real.rpow_nonneg (le_of_lt hωpos) _)
    calc (localTime X n x : ℝ)
        ≤ 4 * ε * max (b - euclidNorm x) 0 +
            4 * ε * unitBallVolume 2 ^ (-(1 : ℝ) / 2) *
              (2 * cN * C₀ * (N ^ ((3 : ℝ) / 2) * L)) ^ ((1 : ℝ) / 2) + δ₀ := henv
      _ ≤ 4 * ε * max (b - euclidNorm x) 0 + A1 := by
          rw [hMb1]
          simp only [A1, A1c]
          linarith [hδ]
  -- Step 4: the contact inequality with the sharp decomposition.
  have hdist : ∀ x ∈ departureRange X n, euclidNorm (x - z) ≤ 2 * K * N := by
    intro x hx
    have hxmem : toSpace x ∈ cellSet X n := (toSpace_mem_cellSet_iff X n x).mpr hx
    have hxD : toSpace x ∈ Metric.ball 0 ((K - 1) * N) := hDsub hxmem
    have hxnorm : euclidNorm x < (K - 1) * N := by
      rw [Metric.mem_ball, dist_zero_right, norm_toSpace] at hxD
      exact hxD
    have hxz : euclidNorm (x - z) ≤ euclidNorm x + euclidNorm z := by
      have h := CERW.Support.Occupation.euclidNorm_add_le x (-z)
      rwa [show x + (-z) = x - z by abel, CERW.Generic.Lattice.euclidNorm_neg] at h
    linarith
  have hbzN : Bz ≤ Cz * N := by
    have hR : 1 ≤ 2 * K * N := by
      have h2K : (1 : ℝ) ≤ 2 * K := by linarith
      have hml := mul_le_mul h2K hN1 (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : (0 : ℝ) ≤ 2 * K)
      simpa using hml
    have hb := hbracket X n (4 * ε) b A1 (2 * K * N) z hR (by linarith [hε]) hA1nn hbz
      hdist hA1dep
    rw [← hBzdef] at hb
    have hlogb := planar_log_bound hKpos hN1
    have hAlog : A1 * Real.log (2 * K * N + 2) ≤ (A1c * LK + C₀ * LK) * N := by
      have hstep : A1 * Real.log (2 * K * N + 2) ≤ A1 * (LK * N ^ ((1 : ℝ) / 8)) :=
        mul_le_mul_of_nonneg_left hlogb hA1nn
      have hA : N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 8) ≤ N :=
        pow_term_A_le hN1 hL hLN
      have hB : Real.sqrt N * L * N ^ ((1 : ℝ) / 8) ≤ N := by
        rw [Real.sqrt_eq_rpow]
        exact pow_term_B_le hN1 hL hLN
      have hcoef1 : 0 ≤ A1c * LK := mul_nonneg hA1cnn (le_of_lt hLKpos)
      have hcoef2 : 0 ≤ C₀ * LK := mul_nonneg hC₀ (le_of_lt hLKpos)
      have hdist : A1 * (LK * N ^ ((1 : ℝ) / 8)) ≤ (A1c * LK + C₀ * LK) * N := by
        have hA1expand : A1 * (LK * N ^ ((1 : ℝ) / 8)) =
            A1c * LK * (N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 8)) +
              C₀ * LK * (Real.sqrt N * L * N ^ ((1 : ℝ) / 8)) := by
          simp only [A1]
          ring
        rw [hA1expand]
        calc A1c * LK * (N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 8)) +
              C₀ * LK * (Real.sqrt N * L * N ^ ((1 : ℝ) / 8))
            ≤ A1c * LK * N + C₀ * LK * N :=
              add_le_add (mul_le_mul_of_nonneg_left hA hcoef1)
                (mul_le_mul_of_nonneg_left hB hcoef2)
          _ = (A1c * LK + C₀ * LK) * N := by ring
      exact le_trans hstep hdist
    have hsumR : 4 * ε * (2 * K * N + 1) + A1 * Real.log (2 * K * N + 2) ≤
        (4 * ε * (2 * K + 1) + A1c * LK + C₀ * LK) * N := by
      have h2KN1 : 2 * K * N + 1 ≤ (2 * K + 1) * N := by
        have he : (2 * K + 1) * N = 2 * K * N + N := by ring
        rw [he]; linarith [hN1]
      have h1 : 4 * ε * (2 * K * N + 1) ≤ 4 * ε * (2 * K + 1) * N := by
        have h4 : 0 ≤ 4 * ε := by linarith [hε]
        calc 4 * ε * (2 * K * N + 1) ≤ 4 * ε * ((2 * K + 1) * N) :=
              mul_le_mul_of_nonneg_left h2KN1 h4
          _ = 4 * ε * (2 * K + 1) * N := by ring
      have hRHS : (4 * ε * (2 * K + 1) + A1c * LK + C₀ * LK) * N =
          4 * ε * (2 * K + 1) * N + (A1c * LK + C₀ * LK) * N := by ring
      rw [hRHS]
      linarith [h1, hAlog]
    calc Bz ≤ Cb * (4 * ε * (2 * K * N + 1) + A1 * Real.log (2 * K * N + 2)) := hb
      _ ≤ Cb * ((4 * ε * (2 * K + 1) + A1c * LK + C₀ * LK) * N) :=
          mul_le_mul_of_nonneg_left hsumR (le_of_lt hCbpos)
      _ = Cz * N := by simp only [Cz]; ring
  have hm4 : m ≤ M0 * (N ^ ((3 : ℝ) / 2) * L ^ ((1 : ℝ) / 2)) := by
    have hcontact4 := contact_mass_planar hε hK hNpos X n hb.le hball hDS1 hy₀ hz0 hpt hmod
    rw [← hmdef] at hcontact4
    have hcontact4' : m ≤ cN * N * (|ρ| + |M| + Δ) := by
      calc m ≤ unitBallVolume 2 / (2 * ε) * 2 * (K - 1) * N * (|ρ| + |M| + Δ) := hcontact4
        _ = cN * N * (|ρ| + |M| + Δ) := by simp only [cN, cU]
    have hsqB : Real.sqrt (Bz * L) ≤ Real.sqrt Cz * (Real.sqrt N * Real.sqrt L) := by
      have hBL : Bz * L ≤ Cz * N * L := mul_le_mul_of_nonneg_right hbzN hLnn
      calc Real.sqrt (Bz * L) ≤ Real.sqrt (Cz * N * L) := Real.sqrt_le_sqrt hBL
        _ = Real.sqrt (Cz * (N * L)) := by ring_nf
        _ = Real.sqrt Cz * Real.sqrt (N * L) := Real.sqrt_mul (le_of_lt hCzpos) (N * L)
        _ = Real.sqrt Cz * (Real.sqrt N * Real.sqrt L) := by rw [Real.sqrt_mul hNnn L]
    have h1 : |ρ| + |M| + Δ ≤
        C₁ * Real.sqrt Cz * (Real.sqrt N * Real.sqrt L) + C₁ * L + C₀ * Real.sqrt N := by
      have hAB : |ρ| + |M| ≤ C₁ * Real.sqrt (Bz * L) + C₁ * L := by linarith [hρM]
      have hAB' : C₁ * Real.sqrt (Bz * L) ≤
          C₁ * (Real.sqrt Cz * (Real.sqrt N * Real.sqrt L)) :=
        mul_le_mul_of_nonneg_left hsqB hC₁
      linarith [hAB, hAB', hΔ]
    have hLleL6 : L ≤ L ^ 6 := by simpa using pow_le_pow_right₀ hL (by norm_num : 1 ≤ 6)
    have hLleN : L ≤ N := le_trans hLleL6 hLN
    have hsL_le_sN : Real.sqrt L ≤ Real.sqrt N := Real.sqrt_le_sqrt hLleN
    have h1_le_sL : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hL
    have hsqL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLnn
    have hprod1 : L ≤ Real.sqrt N * Real.sqrt L := by
      nth_rewrite 1 [← hsqL]
      exact mul_le_mul_of_nonneg_right hsL_le_sN (Real.sqrt_nonneg L)
    have hprod2 : Real.sqrt N ≤ Real.sqrt N * Real.sqrt L := by
      calc Real.sqrt N = Real.sqrt N * 1 := (mul_one _).symm
        _ ≤ Real.sqrt N * Real.sqrt L := mul_le_mul_of_nonneg_left h1_le_sL (Real.sqrt_nonneg N)
    have hinner :
        C₁ * Real.sqrt Cz * (Real.sqrt N * Real.sqrt L) + C₁ * L + C₀ * Real.sqrt N ≤
        (C₁ * Real.sqrt Cz + C₁ + C₀) * (Real.sqrt N * Real.sqrt L) := by
      have e1 : C₁ * L ≤ C₁ * (Real.sqrt N * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hprod1 hC₁
      have e2 : C₀ * Real.sqrt N ≤ C₀ * (Real.sqrt N * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hprod2 hC₀
      calc C₁ * Real.sqrt Cz * (Real.sqrt N * Real.sqrt L) + C₁ * L + C₀ * Real.sqrt N
          ≤ C₁ * Real.sqrt Cz * (Real.sqrt N * Real.sqrt L) +
            C₁ * (Real.sqrt N * Real.sqrt L) + C₀ * (Real.sqrt N * Real.sqrt L) :=
            by linarith [e1, e2]
        _ = (C₁ * Real.sqrt Cz + C₁ + C₀) * (Real.sqrt N * Real.sqrt L) := by ring
    have hstep := mul_le_mul_of_nonneg_left (le_trans h1 hinner)
      (mul_nonneg (le_of_lt hcNpos) hNnn)
    have hM0eq : cN * N * ((C₁ * Real.sqrt Cz + C₁ + C₀) * (Real.sqrt N * Real.sqrt L)) =
        M0 * (N ^ ((3 : ℝ) / 2) * L ^ ((1 : ℝ) / 2)) := by
      simp only [M0]
      rw [Real.sqrt_eq_rpow N, Real.sqrt_eq_rpow L]
      have hNN : N * (N ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2)) =
          N ^ ((3 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) := by
        rw [show N * (N ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2)) =
            N * N ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) by ring, hN32]
      rw [show cN * N *
            ((C₁ * Real.sqrt Cz + C₁ + C₀) * (N ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2))) =
          cN * (C₁ * Real.sqrt Cz + C₁ + C₀) *
            (N * (N ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2))) by ring, hNN]
    calc m ≤ cN * N * (|ρ| + |M| + Δ) := hcontact4'
      _ ≤ cN * N * ((C₁ * Real.sqrt Cz + C₁ + C₀) * (Real.sqrt N * Real.sqrt L)) := hstep
      _ = M0 * (N ^ ((3 : ℝ) / 2) * L ^ ((1 : ℝ) / 2)) := hM0eq
  -- Step 5: the final envelope.
  have hM0half : (M0 * (N ^ ((3 : ℝ) / 2) * L ^ ((1 : ℝ) / 2))) ^ ((1 : ℝ) / 2) =
      Real.sqrt M0 * (N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4)) := by
    rw [rpow_half_of_mul hM0nn hNnn hLnn]
    rw [Real.sqrt_eq_rpow]
    ring
  have hA2dep : ∀ x ∈ departureRange X n, (localTime X n x : ℝ) ≤
      4 * ε * max (b - euclidNorm x) 0 +
        (4 * ε * unitBallVolume 2 ^ (-(1 : ℝ) / 2) * Real.sqrt M0 + C₀) *
          (N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4)) := by
    intro x hx
    have henv := localTime_le_envelope_departure hε hNpos hb X n hball hDsub happrox hm4 x hx
    have hδA : δ₀ ≤ C₀ * Real.sqrt N * L := hδ
    have hδ5 : δ₀ ≤ C₀ * (N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4)) := by
      have hsm := sqrt_mul_le hN1 hL hLN
      calc δ₀ ≤ C₀ * Real.sqrt N * L := hδA
        _ = C₀ * (Real.sqrt N * L) := by ring
        _ ≤ C₀ * (N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4)) :=
            mul_le_mul_of_nonneg_left hsm hC₀
    calc (localTime X n x : ℝ)
        ≤ 4 * ε * max (b - euclidNorm x) 0 +
            4 * ε * unitBallVolume 2 ^ (-(1 : ℝ) / 2) *
              (M0 * (N ^ ((3 : ℝ) / 2) * L ^ ((1 : ℝ) / 2))) ^ ((1 : ℝ) / 2) + δ₀ := henv
      _ ≤ 4 * ε * max (b - euclidNorm x) 0 +
            (4 * ε * unitBallVolume 2 ^ (-(1 : ℝ) / 2) * Real.sqrt M0 + C₀) *
              (N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4)) := by
          rw [hM0half]
          ring_nf
          linarith [hδ5]
  have hE0nn : 0 ≤ 4 * ε * unitBallVolume 2 ^ (-(1 : ℝ) / 2) * Real.sqrt M0 + C₀ := by
    have hc : 0 ≤ 4 * ε * unitBallVolume 2 ^ (-(1 : ℝ) / 2) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hε))
        (Real.rpow_nonneg (le_of_lt hωpos) _)
    exact add_nonneg (mul_nonneg hc (Real.sqrt_nonneg M0)) hC₀
  have hE0leC : 4 * ε * unitBallVolume 2 ^ (-(1 : ℝ) / 2) * Real.sqrt M0 + C₀ ≤ C := by
    simp only [C]; linarith [hM0nn]
  have hM0leC : M0 ≤ C := by simp only [C]; linarith [hE0nn]
  constructor
  · have hvol : m ≤ M0 * N ^ 2 * (L / N) ^ ((1 : ℝ) / 2) := by
      rw [mul_assoc, sq_mul_div_rpow_half hNpos hLnn]
      exact hm4
    calc m ≤ M0 * N ^ 2 * (L / N) ^ ((1 : ℝ) / 2) := hvol
      _ ≤ C * N ^ 2 * (L / N) ^ ((1 : ℝ) / 2) := by
          have hX : 0 ≤ N ^ 2 * (L / N) ^ ((1 : ℝ) / 2) :=
            mul_nonneg (pow_nonneg hNnn 2) (Real.rpow_nonneg (div_nonneg hLnn hNnn) _)
          have hmul : M0 * (N ^ 2 * (L / N) ^ ((1 : ℝ) / 2)) ≤
              C * (N ^ 2 * (L / N) ^ ((1 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_right hM0leC hX
          have e1 : M0 * N ^ 2 * (L / N) ^ ((1 : ℝ) / 2) =
              M0 * (N ^ 2 * (L / N) ^ ((1 : ℝ) / 2)) := by ring
          have e2 : C * N ^ 2 * (L / N) ^ ((1 : ℝ) / 2) =
              C * (N ^ 2 * (L / N) ^ ((1 : ℝ) / 2)) := by ring
          rw [e1, e2]
          exact hmul
  · intro y
    by_cases hy : y ∈ departureRange X n
    · have h := hA2dep y hy
      have hNpow : N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) =
          N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) := rpow_half_half hNpos hLnn
      calc (localTime X n y : ℝ)
          ≤ 4 * ε * max (b - euclidNorm y) 0 +
              (4 * ε * unitBallVolume 2 ^ (-(1 : ℝ) / 2) * Real.sqrt M0 + C₀) *
                (N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4)) := h
        _ ≤ 4 * ε * max (b - euclidNorm y) 0 +
              C * (N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4)) := by
            have hc : 0 ≤ N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) :=
              mul_nonneg (Real.rpow_nonneg hNnn _) (Real.rpow_nonneg hLnn _)
            have := mul_le_mul_of_nonneg_right hE0leC hc
            linarith
        _ = 4 * ε * max (b - euclidNorm y) 0 +
              C * N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) := by
            rw [← hNpow]
            ring
    · have hzero : localTime X n y = 0 := by
        rw [mem_departureRange_iff, not_lt, Nat.le_zero] at hy
        exact hy
      rw [hzero, Nat.cast_zero]
      have hnonneg : 0 ≤ 4 * ε * max (b - euclidNorm y) 0 +
          C * N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) := by
        have hCnn : 0 ≤ C := le_of_lt hCpos
        have hfirst : 0 ≤ 4 * ε * max (b - euclidNorm y) 0 :=
          mul_nonneg (by linarith [hε]) (le_max_right _ _)
        have hsecond : 0 ≤ C * N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) :=
          mul_nonneg (mul_nonneg hCnn hNnn)
            (Real.rpow_nonneg (Real.rpow_nonneg (div_nonneg hLnn hNnn) _) _)
        exact add_nonneg hfirst hsecond
      exact hnonneg

end CERW.Support.Contact
