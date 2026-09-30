import CERW.Support.Contact.ContactMass
import CERW.Support.Contact.Envelope
import CERW.Support.Contact.EnvelopeHigh
import CERW.Generic.Young.Contact

/-!
# The contact variance in dimensions three and higher

`eq:masshigh` and the high-dimensional envelope with rate `W = N Q^{1/d}`, deterministically, for
`d ≥ 3`. Let `m = |D_n \ B(0, b)|`, `V = m^{1/d}` and `S = (K - 1) N`. Suppose that at every
site of norm at most `n` the decomposition `ℓ_n = U + ρ - M` holds with `|ρ| ≤ C₁ L` and
`|M(y)| ≤ C₁ (√(B_y L) + L)`, and that the contact modulus satisfies `Δ ≤ C₀ L`.
1. The envelope gives `ℓ_n ≤ 2dε (b - |·|)_+ + C V + C₁ L + C₁ √(B_y L)` at departure sites.
2. `exists_envelope_high` gives `ℓ_n ≤ C ((b - |·|)_+ + V + L)` and `B_z ≤ C (V + L)`.
3. The contact inequality gives `m ≤ C N^{d-1} (m^{1/(2d)} √L + L)`. By
   `le_of_le_mul_rpow_mul_sqrt_add`, `m ≤ C (N^d Q + N^{d-1} L) ≤ C N^d Q`, since `L ≤ N`.
4. Hence `V ≤ C N Q^{1/d}` and `L ≤ N Q^{1/d}`.
-/

namespace CERW.Support.Contact

open MeasureTheory LatticeProb CERW

variable {d : ℕ}

/-- The denominator `2d - 1` is positive for `d ≥ 1`. -/
private lemma two_mul_sub_one_pos (d : ℕ) (hd : 1 ≤ d) : (0 : ℝ) < 2 * (d : ℝ) - 1 := by
  have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  linarith

/-- For `0 < x ≤ 1` and `a ≤ 1`, `x ≤ x ^ a`. -/
private lemma self_le_rpow_of_le_one {x a : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (ha1 : a ≤ 1) : x ≤ x ^ a := by
  have := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 ha1
  simpa using this

/-- `1 / x ≤ 1` for `1 ≤ x`. -/
private lemma one_div_le_one_of_one_le {x : ℝ} (hx : 0 < x) (h : 1 ≤ x) : 1 / x ≤ 1 := by
  rw [div_le_iff₀ hx, one_mul]
  exact h

/-- `sqrt (a + b) ≤ sqrt a + sqrt b` for nonnegative `a`, `b`. -/
private lemma sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have h2 : 0 ≤ Real.sqrt a * Real.sqrt b :=
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = Real.sqrt a + Real.sqrt b := by
        rw [Real.sqrt_sq (by positivity)]

/-- The exponent identity `N^{2d(d-1)/(2d-1)} L^{d/(2d-1)} = N^d (L/N)^{d/(2d-1)}`. -/
private lemma rpow_exp_identity (d : ℕ) (hd : 1 ≤ d) {N L : ℝ} (hL : 0 < L) (hLN : L ≤ N) :
    N ^ ((2 * (d : ℝ) * ((d : ℝ) - 1)) / (2 * (d : ℝ) - 1)) *
      L ^ ((d : ℝ) / (2 * (d : ℝ) - 1)) =
      N ^ d * (L / N) ^ ((d : ℝ) / (2 * (d : ℝ) - 1)) := by
  have hN : 0 < N := lt_of_lt_of_le hL hLN
  have hden : (0 : ℝ) < 2 * (d : ℝ) - 1 := two_mul_sub_one_pos d hd
  set a : ℝ := (d : ℝ) / (2 * (d : ℝ) - 1) with ha
  have hbda : (2 * (d : ℝ) * ((d : ℝ) - 1)) / (2 * (d : ℝ) - 1) = (d : ℝ) - a := by
    rw [ha]; field_simp; ring
  rw [hbda, Real.rpow_sub hN, Real.rpow_natCast]
  rw [show (L / N) ^ a = L ^ a / N ^ a from Real.div_rpow (le_of_lt hL) (le_of_lt hN) a]
  ring

/-- `N^{d-1} L ≤ N^d (L/N)^{d/(2d-1)}`. -/
private lemma pow_sub_one_mul_le (d : ℕ) (hd : 1 ≤ d) {N L : ℝ} (hL : 0 < L) (hLN : L ≤ N) :
    N ^ (d - 1) * L ≤ N ^ d * (L / N) ^ ((d : ℝ) / (2 * (d : ℝ) - 1)) := by
  have hN : 0 < N := lt_of_lt_of_le hL hLN
  have hden : (0 : ℝ) < 2 * (d : ℝ) - 1 := two_mul_sub_one_pos d hd
  have ha1 : (d : ℝ) / (2 * (d : ℝ) - 1) ≤ 1 := by
    rw [div_le_one hden]
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hx : L / N ≤ (L / N) ^ ((d : ℝ) / (2 * (d : ℝ) - 1)) :=
    self_le_rpow_of_le_one (div_pos hL hN) (by rw [div_le_one hN]; exact hLN) ha1
  have hbase : N ^ (d - 1) * L = N ^ d * (L / N) := by
    have h1 : N ^ (d - 1) * L * N = N ^ d * L := by
      calc N ^ (d - 1) * L * N = (N ^ (d - 1) * N) * L := by ring
        _ = N ^ ((d - 1) + 1) * L := by rw [pow_succ]
        _ = N ^ d * L := by rw [show (d - 1) + 1 = d by omega]
    rw [← mul_div_assoc, eq_div_iff hN.ne']
    exact h1
  rw [hbase]
  exact mul_le_mul_of_nonneg_left hx (by positivity)

/-- The real-power form `N^{d-1} L ≤ N^d (L/N)^{d/(2d-1)}`. -/
private lemma rpow_sub_one_mul_le (d : ℕ) (hd : 1 ≤ d) {N L : ℝ} (hL : 0 < L) (hLN : L ≤ N) :
    N ^ ((d : ℝ) - 1) * L ≤ N ^ d * (L / N) ^ ((d : ℝ) / (2 * (d : ℝ) - 1)) := by
  have hnat : N ^ ((d : ℝ) - 1) = N ^ (d - 1) := by
    have hc : (d : ℝ) - 1 = ((d - 1 : ℕ) : ℝ) := by
      rw [← Nat.cast_one, ← Nat.cast_sub hd]
    rw [hc, Real.rpow_natCast]
  rw [hnat]
  exact pow_sub_one_mul_le d hd hL hLN

/-- `L ≤ N ((L/N)^{d/(2d-1)})^{1/d}`. -/
private lemma le_mul_rpow_div (d : ℕ) (hd : 1 ≤ d) {N L : ℝ} (hL : 0 < L) (hLN : L ≤ N) :
    L ≤ N * ((L / N) ^ ((d : ℝ) / (2 * (d : ℝ) - 1))) ^ ((1 : ℝ) / d) := by
  have hN : 0 < N := lt_of_lt_of_le hL hLN
  have hden : (0 : ℝ) < 2 * (d : ℝ) - 1 := two_mul_sub_one_pos d hd
  have hx0 : 0 ≤ L / N := le_of_lt (div_pos hL hN)
  have hxd : ((L / N) ^ ((d : ℝ) / (2 * (d : ℝ) - 1))) ^ ((1 : ℝ) / d)
      = (L / N) ^ ((1 : ℝ) / (2 * (d : ℝ) - 1)) := by
    rw [← Real.rpow_mul hx0]
    congr 1
    field_simp
  rw [hxd]
  have hone : (1 : ℝ) / (2 * (d : ℝ) - 1) ≤ 1 :=
    one_div_le_one_of_one_le hden (by linarith [show (1 : ℝ) ≤ (d : ℝ) by exact_mod_cast hd])
  have hxle : L / N ≤ (L / N) ^ ((1 : ℝ) / (2 * (d : ℝ) - 1)) :=
    self_le_rpow_of_le_one (div_pos hL hN) (by rw [div_le_one hN]; exact hLN) hone
  calc L = N * (L / N) := by field_simp
    _ ≤ N * (L / N) ^ ((1 : ℝ) / (2 * (d : ℝ) - 1)) := mul_le_mul_of_nonneg_left hxle hN.le

/-- `(N^d Q)^{1/d} = N Q^{1/d}`. -/
private lemma rpow_div_eq (d : ℕ) (hd : 1 ≤ d) {N Q : ℝ} (hN : 0 ≤ N) (hQ : 0 ≤ Q) :
    (N ^ d * Q) ^ ((1 : ℝ) / d) = N * Q ^ ((1 : ℝ) / d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  rw [Real.mul_rpow (by positivity) hQ]
  congr 1
  rw [← Real.rpow_natCast N d, ← Real.rpow_mul hN]
  rw [show (d : ℝ) * (1 / (d : ℝ)) = 1 by field_simp]
  rw [Real.rpow_one]

/-- `sqrt (m^{1/d}) = m^{1/(2d)}`. -/
private lemma sqrt_rpow_inv (d : ℕ) (hd : 1 ≤ d) {m : ℝ} (hm : 0 ≤ m) :
    Real.sqrt (m ^ ((1 : ℝ) / d)) = m ^ ((1 : ℝ) / (2 * (d : ℝ))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hm]
  congr 1
  field_simp

/-- At a departure site, the envelope together with the two decomposition bounds gives
`ℓ_n(y) ≤ c₀ (b - |y|)_+ + A₁ + C₁ √(B_y L)`. -/
private lemma dep_le (d : ℕ) (hd2 : 2 ≤ d) {ε C₁ b L : ℝ} (hε : 0 < ε)
    {X : ℕ → Site d} {n : ℕ} {M : Site d → ℝ} {c0 ca A1 mvol : ℝ}
    (hb : 0 < b) (hball : Metric.ball 0 b ⊆ cellSet X n)
    (hXn : ∀ j < n, euclidNorm (X j) ≤ n)
    (hc0 : c0 = 2 * (d : ℝ) * ε)
    (hca : ca = c0 * unitBallVolume d ^ (-(1 : ℝ) / (d : ℝ)))
    (hmvol : mvol = (volume (cellSet X n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal)
    (hA1 : A1 = ca * mvol ^ ((1 : ℝ) / (d : ℝ)) + 2 * C₁ * L)
    (hpt : ∀ y : Site d, euclidNorm y ≤ n →
        |(localTime X n y : ℝ) - potential d ε (cellSet X n) (toSpace y) + M y| ≤ C₁ * L)
    (hM : ∀ y : Site d, euclidNorm y ≤ n →
        |M y| ≤ C₁ * (Real.sqrt ((∑ x ∈ departureRange X n,
          (localTime X n x : ℝ) * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ))) * L) + L)) :
    ∀ y ∈ departureRange X n,
      (localTime X n y : ℝ) ≤ c0 * max (b - euclidNorm y) 0 + A1 +
        C₁ * Real.sqrt ((∑ x ∈ departureRange X n,
          (localTime X n x : ℝ) * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ))) * L) := by
  intro y hy
  have hyn : euclidNorm y ≤ n := by
    obtain ⟨j, hj, hjy⟩ := Finset.mem_image.mp hy
    rw [← hjy]
    exact hXn j (Finset.mem_range.mp hj)
  have hρ : |(localTime X n y : ℝ) - potential d ε (cellSet X n) (toSpace y) + M y| ≤
      C₁ * L := hpt y hyn
  have hMy : |M y| ≤ C₁ * (Real.sqrt ((∑ x ∈ departureRange X n,
        (localTime X n x : ℝ) * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ))) * L) + L) :=
    hM y hyn
  have henv := localTime_le_envelope (d := d) hd2 (le_of_lt hε) X n hb hball y
    (ρ := (localTime X n y : ℝ) - potential d ε (cellSet X n) (toSpace y) + M y) (M := M y)
    (by ring)
  have hMsplit : |M y| ≤ C₁ * Real.sqrt ((∑ x ∈ departureRange X n,
        (localTime X n x : ℝ) * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ))) * L) +
        C₁ * L := by
    rw [mul_add] at hMy
    exact hMy
  calc (localTime X n y : ℝ)
      ≤ 2 * (d : ℝ) * ε * max (b - euclidNorm y) 0 +
          2 * (d : ℝ) * ε * unitBallVolume d ^ (-(1 : ℝ) / (d : ℝ)) *
            mvol ^ ((1 : ℝ) / (d : ℝ)) +
          |(localTime X n y : ℝ) - potential d ε (cellSet X n) (toSpace y) + M y| + |M y| := by
        simpa only [hmvol] using henv
    _ ≤ c0 * max (b - euclidNorm y) 0 + A1 +
          C₁ * Real.sqrt ((∑ x ∈ departureRange X n,
            (localTime X n x : ℝ) * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ))) * L) := by
        have h1 : 2 * (d : ℝ) * ε * max (b - euclidNorm y) 0 +
              2 * (d : ℝ) * ε * unitBallVolume d ^ (-(1 : ℝ) / (d : ℝ)) *
                mvol ^ ((1 : ℝ) / (d : ℝ)) =
            c0 * max (b - euclidNorm y) 0 + ca * mvol ^ ((1 : ℝ) / (d : ℝ)) := by
          rw [hca, hc0]
        rw [h1, hA1]
        linarith only [hρ, hMsplit]

/-- The contact inequality rewritten with `S = (K - 1) N`, in the form used downstream. -/
private lemma contact_bound (d : ℕ) (hd2 : 2 ≤ d) {ε b N Δ K Kc : ℝ} (hε : 0 < ε)
    {X : ℕ → Site d} {n : ℕ} {M : Site d → ℝ} {z : Site d}
    {y₀ : EuclideanSpace ℝ (Fin d)} {mvol : ℝ}
    (hK : 2 ≤ K) (hNpos : 0 < N) (hb : 0 < b)
    (hball : Metric.ball 0 b ⊆ cellSet X n)
    (hDS : cellSet X n ⊆ Metric.ball 0 ((K - 1) * N))
    (hy0 : ‖y₀‖ = b) (hz0 : localTime X n z = 0)
    (hmod : |potential d ε (cellSet X n) y₀ - potential d ε (cellSet X n) (toSpace z)| ≤ Δ)
    (hmvol : mvol = (volume (cellSet X n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal)
    (hKc : Kc = unitBallVolume d / (2 * ε) * (2 : ℝ) ^ ((d : ℝ) - 1) *
      (K - 1) ^ ((d : ℝ) - 1)) :
    mvol ≤ Kc * N ^ ((d : ℝ) - 1) *
      (|(localTime X n z : ℝ) - potential d ε (cellSet X n) (toSpace z) + M z| + |M z| +
        Δ) := by
  have hSpos : 0 < (K - 1) * N := by
    have hK1 : 0 < K - 1 := by linarith only [hK]
    exact mul_pos hK1 hNpos
  have hDS' : cellSet X n ⊆ Metric.closedBall 0 ((K - 1) * N) :=
    fun v hv => Metric.ball_subset_closedBall (hDS hv)
  have hSsplit : ((K - 1) * N) ^ ((d : ℝ) - 1) =
      (K - 1) ^ ((d : ℝ) - 1) * N ^ ((d : ℝ) - 1) := by
    rw [Real.mul_rpow (by linarith only [hK] : (0 : ℝ) ≤ K - 1) hNpos.le]
  have hcontact := volume_sdiff_le_contact (d := d) hd2 hε X n (b := b) (S := (K - 1) * N)
    (Δ := Δ) (ρ := (localTime X n z : ℝ) - potential d ε (cellSet X n) (toSpace z) + M z)
    (M := M z) (le_of_lt hb) hSpos hball hDS' hy0 hz0 (by ring) hmod
  rw [← hmvol, hSsplit] at hcontact
  calc mvol ≤ unitBallVolume d / (2 * ε) * (2 : ℝ) ^ ((d : ℝ) - 1) *
        ((K - 1) ^ ((d : ℝ) - 1) * N ^ ((d : ℝ) - 1)) *
        (|(localTime X n z : ℝ) - potential d ε (cellSet X n) (toSpace z) + M z| + |M z| +
          Δ) := hcontact
    _ = Kc * N ^ ((d : ℝ) - 1) *
        (|(localTime X n z : ℝ) - potential d ε (cellSet X n) (toSpace z) + M z| + |M z| +
          Δ) := by
          rw [hKc]; ring

/-- A square-root estimate turning `B_z ≤ Ce (ca m^{1/d} + D₁ L)` into the explicit bound
`√(B_z L) ≤ √(Ce ca) m^{1/(2d)} √L + √(Ce D₁) L`. -/
private lemma sqrt_bound (d : ℕ) (hd1 : 1 ≤ d) {Ce ca D1 Bz mvol L : ℝ}
    (hmvol_nonneg : 0 ≤ mvol) (hLpos : 0 < L)
    (hcanonneg : 0 ≤ ca) (hD1nonneg : 0 ≤ D1) (hCepos : 0 < Ce)
    (hBz_le : Bz ≤ Ce * (ca * mvol ^ ((1 : ℝ) / (d : ℝ)) + D1 * L)) :
    Real.sqrt (Bz * L) ≤
      Real.sqrt (Ce * ca) * mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L +
        Real.sqrt (Ce * D1) * L := by
  have h1 : Real.sqrt (Bz * L) ≤
      Real.sqrt (Ce * (ca * mvol ^ ((1 : ℝ) / (d : ℝ)) + D1 * L) * L) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right hBz_le hLpos.le
  have h2 : Ce * (ca * mvol ^ ((1 : ℝ) / (d : ℝ)) + D1 * L) * L =
      Ce * ca * mvol ^ ((1 : ℝ) / (d : ℝ)) * L + Ce * D1 * L * L := by ring
  have h3 : Real.sqrt (Ce * ca * mvol ^ ((1 : ℝ) / (d : ℝ)) * L + Ce * D1 * L * L) ≤
      Real.sqrt (Ce * ca * mvol ^ ((1 : ℝ) / (d : ℝ)) * L) +
        Real.sqrt (Ce * D1 * L * L) :=
    sqrt_add_le _ _ (mul_nonneg (mul_nonneg (mul_nonneg hCepos.le hcanonneg)
      (Real.rpow_nonneg hmvol_nonneg _)) hLpos.le)
      (mul_nonneg (mul_nonneg (mul_nonneg hCepos.le hD1nonneg) hLpos.le) hLpos.le)
  have h4 : Real.sqrt (Ce * ca * mvol ^ ((1 : ℝ) / (d : ℝ)) * L) =
      Real.sqrt (Ce * ca) * mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L := by
    rw [show Ce * ca * mvol ^ ((1 : ℝ) / (d : ℝ)) * L =
      (Ce * ca) * (mvol ^ ((1 : ℝ) / (d : ℝ)) * L) by ring]
    rw [Real.sqrt_mul (mul_nonneg hCepos.le hcanonneg)
      (mvol ^ ((1 : ℝ) / (d : ℝ)) * L)]
    rw [Real.sqrt_mul (Real.rpow_nonneg hmvol_nonneg _) L]
    rw [sqrt_rpow_inv d hd1 hmvol_nonneg]
    ring
  have h5 : Real.sqrt (Ce * D1 * L * L) = Real.sqrt (Ce * D1) * L := by
    rw [show Ce * D1 * L * L = (Ce * D1) * (L * L) by ring]
    rw [Real.sqrt_mul (mul_nonneg hCepos.le hD1nonneg) (L * L)]
    rw [Real.sqrt_mul_self hLpos.le]
  calc Real.sqrt (Bz * L) ≤
        Real.sqrt (Ce * (ca * mvol ^ ((1 : ℝ) / (d : ℝ)) + D1 * L) * L) := h1
    _ = Real.sqrt (Ce * ca * mvol ^ ((1 : ℝ) / (d : ℝ)) * L + Ce * D1 * L * L) := by
          rw [h2]
    _ ≤ Real.sqrt (Ce * ca * mvol ^ ((1 : ℝ) / (d : ℝ)) * L) +
          Real.sqrt (Ce * D1 * L * L) := h3
    _ = Real.sqrt (Ce * ca) * mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L +
          Real.sqrt (Ce * D1) * L := by rw [h4, h5]

/-- The Young-inequality step absorbing the bracket: from
`m ≤ Kc N^{d-1} (C₁ √(B_z L) + (2C₁ + C₀) L)` produce
`m ≤ c N^{d-1} (m^{1/(2d)} √L + L)` with `c = Kc · cabs`. -/
private lemma mass_young (d : ℕ) {C₀ C₁ Ce ca D1 Kc cabs c Bz mvol N L : ℝ}
    (hmvol_nonneg : 0 ≤ mvol) (hLpos : 0 < L) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hKcN_nonneg : 0 ≤ Kc * N ^ ((d : ℝ) - 1))
    (hcabs : cabs = C₁ * Real.sqrt (Ce * ca) + (2 * C₁ + C₀) + C₁ * Real.sqrt (Ce * D1) + 1)
    (hc : c = Kc * cabs)
    (hsqrt_bound : Real.sqrt (Bz * L) ≤
      Real.sqrt (Ce * ca) * mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L +
        Real.sqrt (Ce * D1) * L)
    (hm1 : mvol ≤ Kc * N ^ ((d : ℝ) - 1) *
      (C₁ * Real.sqrt (Bz * L) + (2 * C₁ + C₀) * L)) :
    mvol ≤ c * N ^ ((d : ℝ) - 1) *
      (mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L + L) := by
  have hmn_nonneg : 0 ≤ mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L :=
    mul_nonneg (Real.rpow_nonneg hmvol_nonneg _) (Real.sqrt_nonneg L)
  have hA_le : C₁ * Real.sqrt (Ce * ca) ≤ cabs := by
    have h1 : 0 ≤ C₁ * Real.sqrt (Ce * D1) := mul_nonneg hC₁ (Real.sqrt_nonneg _)
    have h2 : 0 ≤ 2 * C₁ + C₀ := by linarith only [hC₁, hC₀]
    rw [hcabs]
    linarith only [h1, h2]
  have hB_le : C₁ * Real.sqrt (Ce * D1) + (2 * C₁ + C₀) ≤ cabs := by
    have h1 : 0 ≤ C₁ * Real.sqrt (Ce * ca) := mul_nonneg hC₁ (Real.sqrt_nonneg _)
    rw [hcabs]
    linarith only [h1]
  have hbracket2 : C₁ * Real.sqrt (Bz * L) + (2 * C₁ + C₀) * L ≤
      cabs * (mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L + L) := by
    have hC1sqrt : C₁ * Real.sqrt (Bz * L) ≤
        C₁ * Real.sqrt (Ce * ca) * mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L +
          C₁ * Real.sqrt (Ce * D1) * L := by
      have h := mul_le_mul_of_nonneg_left hsqrt_bound hC₁
      calc C₁ * Real.sqrt (Bz * L) ≤
            C₁ * (Real.sqrt (Ce * ca) * mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L +
              Real.sqrt (Ce * D1) * L) := h
        _ = C₁ * Real.sqrt (Ce * ca) * mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L +
              C₁ * Real.sqrt (Ce * D1) * L := by ring
    have hA : C₁ * Real.sqrt (Ce * ca) * mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L ≤
        cabs * (mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L) := by
      calc C₁ * Real.sqrt (Ce * ca) * mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L =
            (C₁ * Real.sqrt (Ce * ca)) *
              (mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L) := by ring
        _ ≤ cabs * (mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L) :=
              mul_le_mul_of_nonneg_right hA_le hmn_nonneg
    have hB : (C₁ * Real.sqrt (Ce * D1) + (2 * C₁ + C₀)) * L ≤ cabs * L :=
      mul_le_mul_of_nonneg_right hB_le hLpos.le
    have hcombine : C₁ * Real.sqrt (Bz * L) + (2 * C₁ + C₀) * L ≤
        C₁ * Real.sqrt (Ce * ca) * mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L +
          (C₁ * Real.sqrt (Ce * D1) + (2 * C₁ + C₀)) * L := by
      linarith only [hC1sqrt]
    rw [show cabs * (mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L + L) =
      cabs * (mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L) + cabs * L by ring]
    linarith only [hcombine, hA, hB]
  calc mvol ≤ Kc * N ^ ((d : ℝ) - 1) *
        (C₁ * Real.sqrt (Bz * L) + (2 * C₁ + C₀) * L) := hm1
    _ ≤ Kc * N ^ ((d : ℝ) - 1) *
          (cabs * (mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L + L)) :=
          mul_le_mul_of_nonneg_left hbracket2 hKcN_nonneg
    _ = c * N ^ ((d : ℝ) - 1) *
          (mvol ^ ((1 : ℝ) / (2 * (d : ℝ))) * Real.sqrt L + L) := by
          rw [hc]; ring

/-- The Young-inequality output `m ≤ 2 C (N^d Q)` with `Q = (L/N)^{d/(2d-1)}`. -/
private lemma young_key (d : ℕ) (hd1 : 1 ≤ d) {Cy N L Q mvol : ℝ}
    (hLpos : 0 < L) (hLN : L ≤ N) (hCypos : 0 < Cy)
    (hQdef : Q = (L / N) ^ ((d : ℝ) / (2 * d - 1)))
    (hkey : mvol ≤ Cy * (N ^ ((2 * (d : ℝ) * ((d : ℝ) - 1)) / (2 * (d : ℝ) - 1)) *
          L ^ ((d : ℝ) / (2 * (d : ℝ) - 1)) + N ^ ((d : ℝ) - 1) * L)) :
    mvol ≤ 2 * Cy * (N ^ d * Q) := by
  have hid : N ^ ((2 * (d : ℝ) * ((d : ℝ) - 1)) / (2 * (d : ℝ) - 1)) *
      L ^ ((d : ℝ) / (2 * (d : ℝ) - 1)) = N ^ d * Q := by
    rw [hQdef]
    exact rpow_exp_identity d hd1 hLpos hLN
  have hid2 : N ^ ((d : ℝ) - 1) * L ≤ N ^ d * Q := by
    rw [hQdef]
    exact rpow_sub_one_mul_le d hd1 hLpos hLN
  calc mvol ≤ Cy * (N ^ ((2 * (d : ℝ) * ((d : ℝ) - 1)) / (2 * (d : ℝ) - 1)) *
        L ^ ((d : ℝ) / (2 * (d : ℝ) - 1)) + N ^ ((d : ℝ) - 1) * L) := hkey
    _ = Cy * (N ^ d * Q + N ^ ((d : ℝ) - 1) * L) := by rw [hid]
    _ ≤ Cy * (N ^ d * Q + N ^ d * Q) := by gcongr
    _ = 2 * Cy * (N ^ d * Q) := by ring

/-- The root of the Young bound: `m^{1/d} ≤ (2C)^{1/d} N Q^{1/d}`. -/
private lemma root_bound (d : ℕ) (hd1 : 1 ≤ d) {N Q mvol Cy : ℝ}
    (hmvol_nonneg : 0 ≤ mvol) (hNpos : 0 < N) (hQnonneg : 0 ≤ Q) (hCypos : 0 < Cy)
    (key2 : mvol ≤ 2 * Cy * (N ^ d * Q)) :
    mvol ^ ((1 : ℝ) / (d : ℝ)) ≤
      (2 * Cy) ^ ((1 : ℝ) / (d : ℝ)) * N * Q ^ ((1 : ℝ) / (d : ℝ)) := by
  have hNQ : 0 ≤ N ^ d * Q := mul_nonneg (pow_nonneg hNpos.le d) hQnonneg
  have h := Real.rpow_le_rpow hmvol_nonneg key2
    (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (d : ℝ))
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * Cy) hNQ] at h
  rw [rpow_div_eq d hd1 hNpos.le hQnonneg] at h
  rw [← mul_assoc] at h
  exact h

/-- The bound `A₁ + C₁² L + c₀ L ≤ (ca (2C)^{1/d} + D₁) (N Q^{1/d})`. -/
private lemma env_bound (d : ℕ) {C₁ ca D1 Cy N Q A1 c0 L mvol : ℝ}
    (hcanonneg : 0 ≤ ca) (hD1nonneg : 0 ≤ D1)
    (hEz : A1 + C₁ ^ 2 * L + c0 * L = ca * mvol ^ ((1 : ℝ) / (d : ℝ)) + D1 * L)
    (hmroot : mvol ^ ((1 : ℝ) / (d : ℝ)) ≤
      (2 * Cy) ^ ((1 : ℝ) / (d : ℝ)) * N * Q ^ ((1 : ℝ) / (d : ℝ)))
    (hLle : L ≤ N * Q ^ ((1 : ℝ) / (d : ℝ))) :
    A1 + C₁ ^ 2 * L + c0 * L ≤
      (ca * (2 * Cy) ^ ((1 : ℝ) / (d : ℝ)) + D1) * (N * Q ^ ((1 : ℝ) / (d : ℝ))) := by
  have h1 : ca * mvol ^ ((1 : ℝ) / (d : ℝ)) ≤
      ca * (2 * Cy) ^ ((1 : ℝ) / (d : ℝ)) * (N * Q ^ ((1 : ℝ) / (d : ℝ))) := by
    calc ca * mvol ^ ((1 : ℝ) / (d : ℝ)) ≤
          ca * ((2 * Cy) ^ ((1 : ℝ) / (d : ℝ)) * N * Q ^ ((1 : ℝ) / (d : ℝ))) :=
            mul_le_mul_of_nonneg_left hmroot hcanonneg
      _ = ca * (2 * Cy) ^ ((1 : ℝ) / (d : ℝ)) * (N * Q ^ ((1 : ℝ) / (d : ℝ))) := by ring
  have h2 : D1 * L ≤ D1 * (N * Q ^ ((1 : ℝ) / (d : ℝ))) :=
    mul_le_mul_of_nonneg_left hLle hD1nonneg
  rw [hEz]
  calc ca * mvol ^ ((1 : ℝ) / (d : ℝ)) + D1 * L
      ≤ ca * (2 * Cy) ^ ((1 : ℝ) / (d : ℝ)) * (N * Q ^ ((1 : ℝ) / (d : ℝ))) +
          D1 * (N * Q ^ ((1 : ℝ) / (d : ℝ))) :=
        add_le_add h1 h2
    _ = (ca * (2 * Cy) ^ ((1 : ℝ) / (d : ℝ)) + D1) *
          (N * Q ^ ((1 : ℝ) / (d : ℝ))) := by ring

/-- The local-time envelope with the constant `Cfin`. -/
private lemma envelope_bound (d : ℕ) {X : ℕ → Site d} {n : ℕ}
    {b Ce c0 C₁ Cfin ca D1 Cy N Q A1 L : ℝ}
    (hCepos : 0 < Ce)
    (hCfin : Cfin = max (2 * Cy)
      (max (Ce * c0) (Ce * (ca * (2 * Cy) ^ ((1 : ℝ) / (d : ℝ)) + D1))))
    (hEbound : A1 + C₁ ^ 2 * L + c0 * L ≤
      (ca * (2 * Cy) ^ ((1 : ℝ) / (d : ℝ)) + D1) * (N * Q ^ ((1 : ℝ) / (d : ℝ))))
    (hNpos : 0 < N) (hQnonneg : 0 ≤ Q)
    (henv_all : ∀ y : Site d, (localTime X n y : ℝ) ≤
      Ce * (c0 * max (b - euclidNorm y) 0 + A1 + C₁ ^ 2 * L + c0 * L)) :
    ∀ y : Site d, (localTime X n y : ℝ) ≤
      Cfin * max (b - euclidNorm y) 0 + Cfin * N * Q ^ ((1 : ℝ) / (d : ℝ)) := by
  intro y
  have hy := henv_all y
  have hs_nonneg : 0 ≤ max (b - euclidNorm y) 0 := le_max_right _ _
  have hCe_c0_le : Ce * c0 ≤ Cfin := by
    rw [hCfin]
    exact le_trans (le_max_left _ _) (le_max_right (2 * Cy) _)
  have hCe_E_le : Ce * (ca * (2 * Cy) ^ ((1 : ℝ) / (d : ℝ)) + D1) ≤ Cfin := by
    rw [hCfin]
    exact le_trans (le_max_right _ _) (le_max_right (2 * Cy) _)
  have h1 : Ce * (c0 * max (b - euclidNorm y) 0 + (A1 + C₁ ^ 2 * L + c0 * L)) ≤
      Cfin * max (b - euclidNorm y) 0 + Cfin * (N * Q ^ ((1 : ℝ) / (d : ℝ))) := by
    have ha : Ce * c0 * max (b - euclidNorm y) 0 ≤ Cfin * max (b - euclidNorm y) 0 :=
      mul_le_mul_of_nonneg_right hCe_c0_le hs_nonneg
    have hb : Ce * (A1 + C₁ ^ 2 * L + c0 * L) ≤ Cfin * (N * Q ^ ((1 : ℝ) / (d : ℝ))) := by
      have h2 := mul_le_mul_of_nonneg_left hEbound hCepos.le
      have h3 : Ce * ((ca * (2 * Cy) ^ ((1 : ℝ) / (d : ℝ)) + D1) *
            (N * Q ^ ((1 : ℝ) / (d : ℝ)))) =
          (Ce * (ca * (2 * Cy) ^ ((1 : ℝ) / (d : ℝ)) + D1)) *
            (N * Q ^ ((1 : ℝ) / (d : ℝ))) := by ring
      rw [h3] at h2
      exact le_trans h2 (mul_le_mul_of_nonneg_right hCe_E_le
        (mul_nonneg hNpos.le (Real.rpow_nonneg hQnonneg _)))
    calc Ce * (c0 * max (b - euclidNorm y) 0 + (A1 + C₁ ^ 2 * L + c0 * L)) =
          Ce * c0 * max (b - euclidNorm y) 0 + Ce * (A1 + C₁ ^ 2 * L + c0 * L) := by ring
      _ ≤ Cfin * max (b - euclidNorm y) 0 + Cfin * (N * Q ^ ((1 : ℝ) / (d : ℝ))) :=
            add_le_add ha hb
  calc (localTime X n y : ℝ) ≤
        Ce * (c0 * max (b - euclidNorm y) 0 + A1 + C₁ ^ 2 * L + c0 * L) := hy
    _ = Ce * (c0 * max (b - euclidNorm y) 0 + (A1 + C₁ ^ 2 * L + c0 * L)) := by ring
    _ ≤ Cfin * max (b - euclidNorm y) 0 + Cfin * (N * Q ^ ((1 : ℝ) / (d : ℝ))) := h1
    _ = Cfin * max (b - euclidNorm y) 0 + Cfin * N * Q ^ ((1 : ℝ) / (d : ℝ)) := by ring

/-- `eq:masshigh` and the envelope: for `d ≥ 3`, the decomposition at sites of norm at most `n`
and the contact site give `m ≤ C N^d Q` and `ℓ_n ≤ C (b - |·|)_+ + C N Q^{1/d}`, where
`Q = (L/N)^{d/(2d-1)}`. -/
theorem exists_mass_high (hd : 3 ≤ d) {ε K C₀ C₁ : ℝ} (hε : 0 < ε) (hK : 2 ≤ K) (hC₀ : 0 ≤ C₀)
    (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ → Site d) (n : ℕ) (b N Δ : ℝ) (M : Site d → ℝ) (z : Site d)
      (y₀ : EuclideanSpace ℝ (Fin d)),
      let L : ℝ := Real.log (n + 2)
      let Q : ℝ := (L / N) ^ ((d : ℝ) / (2 * d - 1))
      1 ≤ n → (∀ j < n, euclidNorm (X j) ≤ n) → L ≤ N → 0 < b →
      Metric.ball 0 b ⊆ cellSet X n → cellSet X n ⊆ Metric.ball 0 ((K - 1) * N) →
      ‖y₀‖ = b → localTime X n z = 0 → b ≤ euclidNorm z → euclidNorm z ≤ n →
      |potential d ε (cellSet X n) y₀ - potential d ε (cellSet X n) (toSpace z)| ≤ Δ →
      Δ ≤ C₀ * L →
      (∀ y : Site d, euclidNorm y ≤ n →
        |(localTime X n y : ℝ) - potential d ε (cellSet X n) (toSpace y) + M y| ≤ C₁ * L) →
      (∀ y : Site d, euclidNorm y ≤ n →
        |M y| ≤ C₁ * (Real.sqrt ((∑ x ∈ departureRange X n,
          (localTime X n x : ℝ) * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ))) * L) + L)) →
      (volume (cellSet X n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal
          ≤ C * N ^ d * Q ∧
      ∀ y : Site d, (localTime X n y : ℝ) ≤
        C * max (b - euclidNorm y) 0 + C * N * Q ^ ((1 : ℝ) / d) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  obtain ⟨Ce, hCepos, hCe⟩ := exists_envelope_high hd
  have hwpos : 0 < unitBallVolume d := unitBallVolume_pos d
  let c0 : ℝ := 2 * (d : ℝ) * ε
  have hc0nonneg : 0 ≤ c0 := by dsimp only [c0]; positivity
  let ca : ℝ := c0 * unitBallVolume d ^ (-(1 : ℝ) / (d : ℝ))
  have hcanonneg : 0 ≤ ca := by dsimp only [ca, c0]; positivity
  let D1 : ℝ := 2 * C₁ + C₁ ^ 2 + c0
  have hD1nonneg : 0 ≤ D1 := by dsimp only [D1]; positivity
  let Kc : ℝ := unitBallVolume d / (2 * ε) * (2 : ℝ) ^ ((d : ℝ) - 1) *
    (K - 1) ^ ((d : ℝ) - 1)
  have hKcpos : 0 < Kc := by
    dsimp only [Kc]
    have hK1 : 0 < K - 1 := by linarith
    positivity
  let cabs : ℝ := C₁ * Real.sqrt (Ce * ca) + (2 * C₁ + C₀) + C₁ * Real.sqrt (Ce * D1) + 1
  have hcabspos : 0 < cabs := by dsimp only [cabs]; positivity
  let c : ℝ := Kc * cabs
  have hcpos : 0 < c := by dsimp only [c]; positivity
  obtain ⟨Cy, hCypos, hCy⟩ := CERW.Generic.Young.le_of_le_mul_rpow_mul_sqrt_add (d := d) hd1 hcpos
  let Cfin : ℝ := max (2 * Cy) (max (Ce * c0) (Ce * (ca * (2 * Cy) ^ ((1 : ℝ) / (d : ℝ)) +
    D1)))
  have hCfinpos : 0 < Cfin := by dsimp only [Cfin]; positivity
  refine ⟨Cfin, hCfinpos, ?_⟩
  intro X n b N Δ M z y₀
  dsimp only
  set L : ℝ := Real.log (n + 2) with hLdef
  set Q : ℝ := (L / N) ^ ((d : ℝ) / (2 * d - 1)) with hQdef
  intro hn hXn hLN hb hball hDS hy0 hz0 hbz hzn hmod hΔL hpt hM
  have hLpos : 0 < L := by
    rw [hLdef]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact Real.log_pos (by linarith)
  have hNpos : 0 < N := lt_of_lt_of_le hLpos hLN
  set mvol : ℝ := (volume (cellSet X n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal
    with hmvol
  have hmvol_nonneg : 0 ≤ mvol := by
    rw [hmvol]
    exact ENNReal.toReal_nonneg
  let A1 : ℝ := ca * mvol ^ ((1 : ℝ) / (d : ℝ)) + 2 * C₁ * L
  have hA1nonneg : 0 ≤ A1 := by
    dsimp only [A1]
    exact add_nonneg (mul_nonneg hcanonneg (Real.rpow_nonneg hmvol_nonneg _))
      (by positivity)
  have hpt_dep : ∀ y ∈ departureRange X n,
      (localTime X n y : ℝ) ≤ c0 * max (b - euclidNorm y) 0 + A1 +
        C₁ * Real.sqrt ((∑ x ∈ departureRange X n,
          (localTime X n x : ℝ) * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ))) * L) :=
    dep_le (d := d) (ca := ca) hd2 hε hb hball hXn rfl rfl hmvol rfl hpt hM
  have henv_all := (hCe X n c0 b A1 C₁ hn hc0nonneg hA1nonneg hC₁ hXn hpt_dep).1
  have hbracket_all := (hCe X n c0 b A1 C₁ hn hc0nonneg hA1nonneg hC₁ hXn hpt_dep).2
  have hcontact' : mvol ≤ Kc * N ^ ((d : ℝ) - 1) *
      (|(localTime X n z : ℝ) - potential d ε (cellSet X n) (toSpace z) + M z| + |M z| + Δ) :=
    contact_bound (d := d) hd2 hε hK hNpos hb hball hDS hy0 hz0 hmod hmvol rfl
  have hρz : |(localTime X n z : ℝ) - potential d ε (cellSet X n) (toSpace z) + M z| ≤
      C₁ * L := hpt z hzn
  have hMz : |M z| ≤ C₁ * (Real.sqrt ((∑ x ∈ departureRange X n,
        (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (2 - 2 * (d : ℝ))) * L) + L) :=
    hM z hzn
  set Bz : ℝ := ∑ x ∈ departureRange X n,
    (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (2 - 2 * (d : ℝ))
  have hBz_nonneg : 0 ≤ Bz := by
    dsimp only [Bz]
    refine Finset.sum_nonneg fun x hx => ?_
    exact mul_nonneg (by positivity)
      (Real.rpow_nonneg (by linarith [euclidNorm_nonneg (x - z)]) _)
  have hbracket_z : Bz ≤ Ce * (A1 + C₁ ^ 2 * L + c0 * L) := hbracket_all z hbz hzn
  have hEz : A1 + C₁ ^ 2 * L + c0 * L = ca * mvol ^ ((1 : ℝ) / (d : ℝ)) + D1 * L := by
    dsimp only [A1, D1]; ring
  have hBz_le : Bz ≤ Ce * (ca * mvol ^ ((1 : ℝ) / (d : ℝ)) + D1 * L) := by
    rw [hEz] at hbracket_z
    exact hbracket_z
  have hsum_le : |(localTime X n z : ℝ) - potential d ε (cellSet X n) (toSpace z) + M z| +
      |M z| + Δ ≤ C₁ * Real.sqrt (Bz * L) + (2 * C₁ + C₀) * L := by
    have hMsplit : |M z| ≤ C₁ * Real.sqrt (Bz * L) + C₁ * L := by
      rw [mul_add] at hMz
      exact hMz
    linarith only [hρz, hΔL, hMsplit]
  have hKcN_nonneg : 0 ≤ Kc * N ^ ((d : ℝ) - 1) :=
    mul_nonneg hKcpos.le (Real.rpow_nonneg hNpos.le _)
  have hm1 : mvol ≤ Kc * N ^ ((d : ℝ) - 1) *
      (C₁ * Real.sqrt (Bz * L) + (2 * C₁ + C₀) * L) := by
    calc mvol ≤ Kc * N ^ ((d : ℝ) - 1) *
          (|(localTime X n z : ℝ) - potential d ε (cellSet X n) (toSpace z) + M z| + |M z| +
            Δ) := hcontact'
      _ ≤ Kc * N ^ ((d : ℝ) - 1) * (C₁ * Real.sqrt (Bz * L) + (2 * C₁ + C₀) * L) :=
            mul_le_mul_of_nonneg_left hsum_le hKcN_nonneg
  have hsqrt_bound := sqrt_bound (d := d) hd1 hmvol_nonneg hLpos hcanonneg hD1nonneg hCepos hBz_le
  have hm_young := mass_young (d := d) hmvol_nonneg hLpos hC₀ hC₁ hKcN_nonneg rfl rfl
    hsqrt_bound hm1
  have hkey := hCy mvol N L hmvol_nonneg hNpos.le hLpos.le hm_young
  have hQnonneg : 0 ≤ Q := by
    rw [hQdef]
    exact Real.rpow_nonneg (div_nonneg hLpos.le hNpos.le) _
  have key2 := young_key (d := d) hd1 hLpos hLN hCypos hQdef hkey
  have hmass : mvol ≤ Cfin * N ^ d * Q := by
    have h2Cy_le : 2 * Cy ≤ Cfin := le_max_left _ _
    have hNQ_nonneg : 0 ≤ N ^ d * Q := by positivity
    calc mvol ≤ 2 * Cy * (N ^ d * Q) := key2
      _ ≤ Cfin * (N ^ d * Q) := mul_le_mul_of_nonneg_right h2Cy_le hNQ_nonneg
      _ = Cfin * N ^ d * Q := by ring
  have hmroot := root_bound (d := d) hd1 hmvol_nonneg hNpos hQnonneg hCypos key2
  have hLle : L ≤ N * Q ^ ((1 : ℝ) / (d : ℝ)) := by
    rw [hQdef]
    exact le_mul_rpow_div d hd1 hLpos hLN
  have hEbound := env_bound (d := d) hcanonneg hD1nonneg hEz hmroot hLle
  have henv_y := envelope_bound (d := d) hCepos rfl hEbound hNpos hQnonneg henv_all
  exact ⟨hmass, henv_y⟩

end CERW.Support.Contact
