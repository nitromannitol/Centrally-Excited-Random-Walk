import CERW.Support.Contact.InradiusArith
import CERW.Support.Contact.BallExcess
import CERW.Support.Contact.NormReplace
import CERW.Support.Contact.Quadratic
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Main.ScaleLimits

/-!
# The inradius

`eq:inradius`, deterministically. Divide the quadratic identity
`|X_n|² = n - 2ε Σ_{x ∈ A_n} |x| + 𝒬_n` by `n = N^{d+1}`. The cell replacement
`|Σ_{A_n} |x| - ∫_D |v|| ≤ (√d/2) |A_n|` and the ball decomposition
`∫_D |v| = d ω_d b^{d+1}/(d+1) + ∫_E |v|` with `0 ≤ ∫_E |v| ≤ K N m` hold.
Combined with the quadratic error `|𝒬_n| ≤ C₁ (N √(nL) + N L)` and the excess
volume `m ≤ C₁ N^d Q`, they give
`|b/N - a| ≤ C Q` through `exists_abs_div_sub_le`, for all large `n`.
-/

namespace CERW.Support.Contact

open MeasureTheory LatticeProb CERW CERW.Support.Law

variable {d : ℕ}

/-- The exponent of the rate `Q`: `1/2` in the plane, `d/(2d - 1)` otherwise. -/
private noncomputable def rateExp (d : ℕ) : ℝ :=
  if d = 2 then (1 : ℝ) / 2 else (d : ℝ) / (2 * d - 1)

/-- `log(n + 2) ≥ 1` for `n ≥ 1`. -/
private lemma log_nat_add_two_ge_one {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) ≤ Real.log (n + 2) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h3 : (3 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  linarith [Real.exp_one_lt_three]

/-- The exponent of the rate is positive. -/
private lemma rateExp_pos {d : ℕ} (hd : 2 ≤ d) : 0 < rateExp d := by
  rw [rateExp]
  split_ifs with h2
  · norm_num
  · have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have h2d : (0 : ℝ) < 2 * d - 1 := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
      linarith
    exact div_pos hd' h2d

/-- The exponent of the rate is at most one. -/
private lemma rateExp_le_one {d : ℕ} (hd : 2 ≤ d) : rateExp d ≤ 1 := by
  rw [rateExp]
  split_ifs with h2
  · norm_num
  · have h2d : (0 : ℝ) < 2 * d - 1 := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
      linarith
    rw [div_le_one h2d]
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith

/-- The exponent of the rate is at most `d - 1` for `d ≥ 2`. -/
private lemma rateExp_le_d_sub_one {d : ℕ} (hd : 2 ≤ d) : rateExp d ≤ (d : ℝ) - 1 := by
  have h1 : rateExp d ≤ 1 := rateExp_le_one hd
  have h2 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  linarith

/-- The exponent of the rate is at least `1/2`. -/
private lemma half_le_rateExp {d : ℕ} (hd : 2 ≤ d) : (1 : ℝ) / 2 ≤ rateExp d := by
  rw [rateExp]
  split_ifs with h2
  · norm_num
  · have h2d : (0 : ℝ) < 2 * d - 1 := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
      linarith
    rw [le_div_iff₀ h2d]
    linarith

/-- The exponent inequality behind `N √(nL) ≤ n Q`. -/
private lemma scaleExp {d : ℕ} (hd : 2 ≤ d) :
    (1 : ℝ) / (d + 1) + 1 / 2 ≤ 1 - ((1 : ℝ) / (d + 1)) * rateExp d := by
  rw [rateExp]
  split_ifs with h2
  · rw [h2]; norm_num
  · have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
    have h2d : (0 : ℝ) < 2 * (d : ℝ) - 1 := by linarith
    have hmid : (d : ℝ) / (2 * (d : ℝ) - 1) ≤ ((d : ℝ) - 1) / 2 := by
      rw [div_le_iff₀ h2d]
      have hfac : (0 : ℝ) ≤ ((d : ℝ) - 3) * (2 * (d : ℝ) + 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hfac]
    have hkey : (1 + (d : ℝ) / (2 * (d : ℝ) - 1)) / ((d : ℝ) + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < (d : ℝ) + 1)]
      nlinarith [hmid]
    have hstep : (1 : ℝ) / ((d : ℝ) + 1) +
        ((d : ℝ) / (2 * (d : ℝ) - 1)) / ((d : ℝ) + 1) ≤ 1 / 2 := by
      have := hkey
      rw [add_div] at this
      exact this
    have hgoal : (1 : ℝ) / ((d : ℝ) + 1) + 1 / 2 ≤
        1 - ((1 : ℝ) / ((d : ℝ) + 1)) * ((d : ℝ) / (2 * (d : ℝ) - 1)) := by
      rw [show ((1 : ℝ) / ((d : ℝ) + 1)) * ((d : ℝ) / (2 * (d : ℝ) - 1)) =
          ((d : ℝ) / (2 * (d : ℝ) - 1)) / ((d : ℝ) + 1) by ring]
      linarith [hstep]
    exact hgoal

/-- The exponent `1 - (1 + e)/(d + 1)` is positive. -/
private lemma quadExp_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < 1 - (1 + rateExp d) / (d + 1) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < d + 1 := by linarith
  rw [sub_pos, div_lt_one hd1]
  have h1 : rateExp d ≤ 1 := rateExp_le_one hd
  linarith

/-- The basic rate identity `n (L/n^a)^e = n^{1-ae} L^e`. -/
private lemma mul_rate_eq {n L e a : ℝ} (hn : 0 < n) (hL : 0 ≤ L) :
    n * (L / n ^ a) ^ e = n ^ (1 - a * e) * L ^ e := by
  rw [Real.div_rpow hL (Real.rpow_nonneg hn.le a), ← Real.rpow_mul hn.le]
  have h2 : n * n ^ (-(a * e)) = n ^ (1 - a * e) := by
    nth_rewrite 1 [← Real.rpow_one n]
    rw [← Real.rpow_add hn]
    rw [show (1 : ℝ) + -(a * e) = 1 - a * e by ring]
  calc n * (L ^ e / n ^ (a * e))
      = (n * n ^ (-(a * e))) * L ^ e := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hn.le]
        ring
    _ = n ^ (1 - a * e) * L ^ e := by rw [h2]

/-- The scale times `√(nL)` as a single product of powers. -/
private lemma scale_mul_sqrt_eq {d : ℕ} {n L : ℝ} (hn : 0 < n) (hL : 0 ≤ L) :
    n ^ ((1 : ℝ) / (d + 1)) * Real.sqrt (n * L) =
      n ^ ((1 : ℝ) / (d + 1) + 1 / 2) * L ^ ((1 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, Real.mul_rpow hn.le hL]
  have h1 : n ^ ((1 : ℝ) / (d + 1)) * (n ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2)) =
      (n ^ ((1 : ℝ) / (d + 1)) * n ^ ((1 : ℝ) / 2)) * L ^ ((1 : ℝ) / 2) := by
    ring
  rw [h1, ← Real.rpow_add hn]

/-- `N^σ ≤ Q` whenever `σ ≤ -e` and `n ≥ 1`, `e ≥ 0`. -/
private lemma rpow_scale_le_rate {d : ℕ} {n : ℕ} {e σ : ℝ} (hn : 1 ≤ n) (he0 : 0 ≤ e)
    (hσ : σ ≤ -e) :
    ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ σ ≤
      (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ e := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (n + 2) := log_nat_add_two_ge_one hn
  have hL0 : (0 : ℝ) ≤ Real.log (n + 2) := le_trans zero_le_one hL1
  have hN0 : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos hnpos _
  rw [← Real.rpow_mul hn0, Real.div_rpow hL0 hN0.le, ← Real.rpow_mul hn0]
  have hLe : (1 : ℝ) ≤ Real.log (n + 2) ^ e := Real.one_le_rpow hL1 he0
  have hden : (0 : ℝ) < (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * e) :=
    Real.rpow_pos_of_pos hnpos _
  have hfrac : (1 : ℝ) / (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * e) ≤
      Real.log (n + 2) ^ e / (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * e) :=
    div_le_div_of_nonneg_right hLe hden.le
  have hone : (1 : ℝ) / (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * e) =
      (n : ℝ) ^ (-(((1 : ℝ) / (d + 1)) * e)) := by
    rw [Real.rpow_neg hn0, inv_eq_one_div]
  have hmono : (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * σ) ≤
      (n : ℝ) ^ (-(((1 : ℝ) / (d + 1)) * e)) := by
    refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    have h2 : ((1 : ℝ) / (d + 1)) * σ ≤ ((1 : ℝ) / (d + 1)) * (-e) :=
      mul_le_mul_of_nonneg_left hσ (by positivity)
    linarith
  rw [hone] at hfrac
  linarith

/-- `N √(nL) ≤ n Q` for `n ≥ 1`. -/
private lemma scale_mul_sqrt_le_n_rate {d : ℕ} {n : ℕ} {e : ℝ} (hn : 1 ≤ n)
    (he : (1 : ℝ) / 2 ≤ e)
    (hexp : (1 : ℝ) / (d + 1) + 1 / 2 ≤ 1 - ((1 : ℝ) / (d + 1)) * e) :
    ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) * Real.sqrt (n * Real.log (n + 2)) ≤
      (n : ℝ) * (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ e := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (n + 2) := log_nat_add_two_ge_one hn
  have hL0 : (0 : ℝ) ≤ Real.log (n + 2) := le_trans zero_le_one hL1
  rw [scale_mul_sqrt_eq hnpos hL0, mul_rate_eq hnpos hL0]
  refine mul_le_mul ?_ ?_ (Real.rpow_nonneg hL0 _) (Real.rpow_nonneg hn0 _)
  · refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    linarith [hexp]
  · exact Real.rpow_le_rpow_of_exponent_le hL1 he

/-- `N L ≤ n Q` for `n ≥ 1` once `L ≤ n^c` with `1/(d+1) + c = 1 - e/(d+1)`. -/
private lemma scale_mul_log_le_n_rate {d : ℕ} {n : ℕ} {e c : ℝ} (hn : 1 ≤ n) (he0 : 0 ≤ e)
    (hc : (1 : ℝ) / (d + 1) + c = 1 - ((1 : ℝ) / (d + 1)) * e)
    (hLc : Real.log (n + 2) ≤ (n : ℝ) ^ c) :
    ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) * Real.log (n + 2) ≤
      (n : ℝ) * (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ e := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (n + 2) := log_nat_add_two_ge_one hn
  have hL0 : (0 : ℝ) ≤ Real.log (n + 2) := le_trans zero_le_one hL1
  rw [mul_rate_eq hnpos hL0]
  have hLe : (1 : ℝ) ≤ Real.log (n + 2) ^ e := Real.one_le_rpow hL1 he0
  have hbase : (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * Real.log (n + 2) ≤
      (n : ℝ) ^ (1 - ((1 : ℝ) / (d + 1)) * e) := by
    have h1 : (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * Real.log (n + 2) ≤
        (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * (n : ℝ) ^ c :=
      mul_le_mul_of_nonneg_left hLc (Real.rpow_nonneg hn0 _)
    have h2 : (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * (n : ℝ) ^ c =
        (n : ℝ) ^ (1 - ((1 : ℝ) / (d + 1)) * e) := by
      rw [← Real.rpow_add hnpos]
      rw [hc]
    rwa [h2] at h1
  calc (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * Real.log (n + 2)
      ≤ (n : ℝ) ^ (1 - ((1 : ℝ) / (d + 1)) * e) := hbase
    _ ≤ (n : ℝ) ^ (1 - ((1 : ℝ) / (d + 1)) * e) * Real.log (n + 2) ^ e := by
        rw [le_mul_iff_one_le_right (Real.rpow_pos_of_pos hnpos _)]
        exact hLe

/-- `eq:inradius`: there are `C` and `n₀` such that, for `n ≥ n₀`, a path from the origin with
`B(0, b) ⊆ D_n ⊆ B̄(0, K N)`, `|X_n| ≤ K N`, `|A_n| ≤ K N^d`, excess volume at most
`C₁ N^d Q`, and quadratic martingale at most `C₁ (N √(nL) + N L)` has `|b/N - a| ≤ C Q`. -/
theorem exists_inradius (hd : 2 ≤ d) {ε K C₁ : ℝ} (hε : 0 < ε) (hK : 0 < K) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ) (b : ℝ),
      n₀ ≤ n →
      let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
      let L : ℝ := Real.log (n + 2)
      let Q : ℝ := if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
      X 0 ω = 0 → 0 ≤ b →
      Metric.ball 0 b ⊆ cellSet (fun j => X j ω) n →
      cellSet (fun j => X j ω) n ⊆ Metric.closedBall 0 (K * N) →
      euclidNorm (X n ω) ≤ K * N →
      ((departureRange (fun j => X j ω) n).card : ℝ) ≤ K * N ^ d →
      (volume (cellSet (fun j => X j ω) n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal
        ≤ C₁ * N ^ d * Q →
      |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω|
        ≤ C₁ * (N * Real.sqrt (n * L) + N * L) →
        |b / N - ((d + 1) / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))| ≤ C * Q := by
  let C₁' : ℝ := K ^ 2 + (Real.sqrt d / 2 * K) + K * C₁ + 2 * C₁ + 1
  have hC₁'val : C₁' = K ^ 2 + (Real.sqrt d / 2 * K) + K * C₁ + 2 * C₁ + 1 := rfl
  have hC₁' : 0 ≤ C₁' := by
    rw [hC₁'val]
    have h1 : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
    have h2 : (0 : ℝ) ≤ K * C₁ := mul_nonneg hK.le hC₁
    have h3 : (0 : ℝ) ≤ Real.sqrt d / 2 * K := by positivity
    linarith
  obtain ⟨C, hCpos, hC⟩ := exists_abs_div_sub_le hd hε (C₁ := C₁') hC₁'
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1
    ((CERW.Support.Main.tendsto_log_rpow_div_rpow 1 (quadExp_pos hd)).eventually_lt_const
      one_pos)
  refine ⟨C, hCpos, max n₁ 1, ?_⟩
  intro Ω X ω n b hmn N L Q hX0 hb hball hDsub hXn hA hEvol hQn
  have hn : 1 ≤ n := le_trans (le_max_right n₁ 1) hmn
  have hn₁' : n₁ ≤ n := le_trans (le_max_left n₁ 1) hmn
  have hNpos : 0 < N := by
    dsimp only [N]
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
  have hNnonneg : 0 ≤ N := le_of_lt hNpos
  have hL1 : 1 ≤ L := by
    dsimp only [L]
    exact log_nat_add_two_ge_one hn
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have hQeq : Q = (L / N) ^ rateExp d := by
    by_cases h2 : d = 2
    · dsimp only [Q, L, N, rateExp]
      rw [if_pos h2, if_pos h2]
    · dsimp only [Q, L, N, rateExp]
      rw [if_neg h2, if_neg h2]
  have hQnonneg : 0 ≤ Q := by
    rw [hQeq]
    exact Real.rpow_nonneg (div_nonneg hL0 hNnonneg) _
  have hNpow : N ^ (d + 1) = (n : ℝ) := by
    dsimp only [N]
    have hx : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [show (1 : ℝ) / (d + 1) = (((d + 1 : ℕ) : ℝ))⁻¹ by
      rw [one_div, Nat.cast_add, Nat.cast_one]]
    exact Real.rpow_inv_natCast_pow hx (by omega)
  let S : ℝ := ∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x
  let I : ℝ := ∫ v in cellSet (fun j => X j ω) n, ‖v‖
  let IE : ℝ :=
    ∫ v in cellSet (fun j => X j ω) n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b, ‖v‖
  let Qn : ℝ := dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω
  let Xsq : ℝ := euclidNorm (X n ω) ^ 2
  have hX : Xsq = (n : ℝ) - 2 * ε * S + Qn := by
    dsimp only [Xsq, S, Qn]
    exact sq_euclidNorm_eq (by omega : 1 ≤ d) ε X ω hX0 n
  have hX_nonneg : 0 ≤ Xsq := by
    dsimp only [Xsq]
    positivity
  have hK2 : K ^ 2 ≤ C₁' := by
    rw [hC₁'val]
    have h2 : (0 : ℝ) ≤ K * C₁ := mul_nonneg hK.le hC₁
    have h3 : (0 : ℝ) ≤ Real.sqrt d / 2 * K := by positivity
    have h4 : (0 : ℝ) ≤ 2 * C₁ := by linarith
    linarith
  have hXub : Xsq ≤ C₁' * N ^ 2 := by
    dsimp only [Xsq]
    calc euclidNorm (X n ω) ^ 2 ≤ (K * N) ^ 2 :=
          pow_le_pow_left₀ (euclidNorm_nonneg _) hXn 2
      _ = K ^ 2 * N ^ 2 := by ring
      _ ≤ C₁' * N ^ 2 := mul_le_mul_of_nonneg_right hK2 (sq_nonneg N)
  have hsqrtK : Real.sqrt d / 2 * K ≤ C₁' := by
    rw [hC₁'val]
    have h1 : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
    have h2 : (0 : ℝ) ≤ K * C₁ := mul_nonneg hK.le hC₁
    have h4 : (0 : ℝ) ≤ 2 * C₁ := by linarith
    linarith
  have hSI : |S - I| ≤ C₁' * N ^ d := by
    have h := abs_sum_euclidNorm_sub_integral_le (fun j => X j ω) n
    dsimp only [S, I]
    calc |∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x -
          ∫ v in cellSet (fun j => X j ω) n, ‖v‖|
        ≤ Real.sqrt d / 2 * ((departureRange (fun j => X j ω) n).card : ℝ) := h
      _ ≤ Real.sqrt d / 2 * (K * N ^ d) := mul_le_mul_of_nonneg_left hA (by positivity)
      _ = (Real.sqrt d / 2 * K) * N ^ d := by ring
      _ ≤ C₁' * N ^ d := mul_le_mul_of_nonneg_right hsqrtK (by positivity)
  have hballadd := integral_norm_eq_ball_add (d := d) (by omega : 1 ≤ d)
      (CERW.Support.Occupation.measurableSet_cellSet (fun j => X j ω) n) hb hball hDsub
  have hI : I = d * unitBallVolume d * b ^ (d + 1) / (d + 1) + IE := by
    dsimp only [I, IE]
    exact hballadd.1
  have hIE0 : 0 ≤ IE := by
    dsimp only [IE]
    exact hballadd.2.1
  have hKC₁ : K * C₁ ≤ C₁' := by
    rw [hC₁'val]
    have h1 : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
    have h3 : (0 : ℝ) ≤ Real.sqrt d / 2 * K := by positivity
    have h4 : (0 : ℝ) ≤ 2 * C₁ := by linarith
    linarith
  have hIEub : IE ≤ C₁' * n * Q := by
    have h3 := hballadd.2.2
    dsimp only [IE] at h3 ⊢
    have hKN : (0 : ℝ) ≤ K * N := mul_nonneg hK.le hNnonneg
    have hnQ : (0 : ℝ) ≤ (n : ℝ) * Q := mul_nonneg (Nat.cast_nonneg n) hQnonneg
    have hstep : (K * N) * (volume (cellSet (fun j => X j ω) n \
        Metric.ball 0 b)).toReal ≤ (K * N) * (C₁ * N ^ d * Q) :=
      mul_le_mul_of_nonneg_left hEvol hKN
    calc ∫ v in cellSet (fun j => X j ω) n \ Metric.ball 0 b, ‖v‖
        ≤ (K * N) * (volume (cellSet (fun j => X j ω) n \
            Metric.ball 0 b)).toReal := h3
      _ ≤ (K * N) * (C₁ * N ^ d * Q) := hstep
      _ = K * C₁ * (N * N ^ d) * Q := by ring
      _ = K * C₁ * N ^ (d + 1) * Q := by rw [← pow_succ']
      _ = K * C₁ * (n : ℝ) * Q := by rw [hNpow]
      _ = (K * C₁) * ((n : ℝ) * Q) := by ring
      _ ≤ C₁' * ((n : ℝ) * Q) := mul_le_mul_of_nonneg_right hKC₁ hnQ
      _ = C₁' * (n : ℝ) * Q := by ring
  have hexp : (1 : ℝ) / (d + 1) + 1 / 2 ≤ 1 - ((1 : ℝ) / (d + 1)) * rateExp d :=
    scaleExp hd
  have hc : (1 : ℝ) / (d + 1) + (1 - (1 + rateExp d) / (d + 1)) =
      1 - ((1 : ℝ) / (d + 1)) * rateExp d := by
    field_simp
    ring
  have hLc : L ≤ (n : ℝ) ^ (1 - (1 + rateExp d) / (d + 1)) := by
    have hlt := hn₁ n hn₁'
    dsimp only [L] at hlt ⊢
    rw [Real.rpow_one] at hlt
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hcp : (0 : ℝ) < (n : ℝ) ^ (1 - (1 + rateExp d) / (d + 1)) :=
      Real.rpow_pos_of_pos hnpos _
    rw [div_lt_one hcp] at hlt
    exact le_of_lt hlt
  have hQn_ev : N * Real.sqrt (n * L) ≤ (n : ℝ) * Q ∧ N * L ≤ (n : ℝ) * Q := by
    constructor
    · rw [hQeq]
      exact scale_mul_sqrt_le_n_rate hn (half_le_rateExp hd) hexp
    · rw [hQeq]
      exact scale_mul_log_le_n_rate hn (rateExp_pos hd).le hc hLc
  have h2C₁ : 2 * C₁ ≤ C₁' := by
    rw [hC₁'val]
    have h1 : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
    have h2 : (0 : ℝ) ≤ K * C₁ := mul_nonneg hK.le hC₁
    have h3 : (0 : ℝ) ≤ Real.sqrt d / 2 * K := by positivity
    linarith
  have hQnub : |Qn| ≤ C₁' * n * Q := by
    dsimp only [Qn]
    have hsum : N * Real.sqrt (n * L) + N * L ≤ 2 * ((n : ℝ) * Q) := by
      linarith [hQn_ev.1, hQn_ev.2]
    have hnQ : (0 : ℝ) ≤ (n : ℝ) * Q := mul_nonneg (Nat.cast_nonneg n) hQnonneg
    calc |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω|
        ≤ C₁ * (N * Real.sqrt (n * L) + N * L) := hQn
      _ ≤ C₁ * (2 * ((n : ℝ) * Q)) := mul_le_mul_of_nonneg_left hsum hC₁
      _ = (2 * C₁) * ((n : ℝ) * Q) := by ring
      _ ≤ C₁' * ((n : ℝ) * Q) := mul_le_mul_of_nonneg_right h2C₁ hnQ
      _ = C₁' * (n : ℝ) * Q := by ring
  have hNQ1 : N ^ (1 - (d : ℝ)) ≤ Q := by
    rw [hQeq]
    refine rpow_scale_le_rate hn (rateExp_pos hd).le ?_
    linarith [rateExp_le_d_sub_one hd]
  have hNQ2 : N⁻¹ ≤ Q := by
    rw [hQeq]
    have h := rpow_scale_le_rate (d := d) (n := n) (e := rateExp d) (σ := -1) hn
      (rateExp_pos hd).le (by linarith [rateExp_le_one hd])
    simpa only [Real.rpow_neg_one] using h
  exact hC n b S I IE Qn Xsq Q hn hb hQnonneg hX hX_nonneg hXub hSI hI hIE0 hIEub
    hQnub hNQ1 hNQ2

end CERW.Support.Contact
