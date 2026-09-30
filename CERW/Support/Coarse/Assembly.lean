import CERW.Support.LocalTime.LocalAssembly
import CERW.Support.Coarse.RadialAssembly
import CERW.Support.Coarse.Vector
import CERW.Support.Coarse.Sstar
import CERW.Support.Coarse.Shell
import CERW.Support.Coarse.Tail
import CERW.Support.Coarse.OuterRadius
import CERW.Support.Coarse.MassError
import CERW.Support.Coarse.RadiusArith
import CERW.Support.Geometry.MassIdentity
import CERW.Generic.Kernel.RadialPacking
import CERW.Support.Law.Dynkin
import CERW.Support.Occupation.Facts
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Geometry.TailBasic
import CERW.Support.Main.ScaleLimits
import CERW.Support.Law.ScaleArith

/-!
# The occupation and radius bounds

`prop:coarse`, assembled from the kernel facts. Intersect the events of `lem:local`,
`lem:radial` and `eq:vector`. Then deterministically:
1. `eq:sstar-lower` gives `s = R_n^{1/d} ≥ cN`, and with it the preconditions.
2. `eq:shell` and the dyadic halving give the coarse tail.
3. The crossing contradiction gives `H_n ≤ (B₀ + 1) s`.
4. The mass identity, the mass error and the radial packing inequality give `s ≤ CN`.
5. The lower bounds follow from `n ≤ M_n R_n` and `R_n ≤ (2H_n + 1)^d`.
-/

universe u

namespace CERW.Support.Coarse

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law CERW.Support.LocalTime

/-- The scale `λ_n` of `eq:M` is at most `L²` once `L ≥ 1`. -/
private lemma lam_le_sq {L : ℝ} (hL : 1 ≤ L) (d : ℕ) :
    (if d = 2 then L ^ 2 else L) ≤ L ^ 2 := by
  split_ifs
  · exact le_rfl
  · nlinarith

/-- The error scale `e_n(m)` of `eq:approx` is at most `√m L + L` once `L ≥ 1`. -/
private lemma error_scale_le {L m : ℝ} (hL : 1 ≤ L) (hm : 0 ≤ m) (d : ℕ) :
    (if d = 2 then Real.sqrt m * L + L else Real.sqrt (m * L) + L) ≤ Real.sqrt m * L + L := by
  split_ifs
  · exact le_rfl
  · rw [Real.sqrt_mul hm]
    have h1 : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hL
    have h2 := Real.mul_self_sqrt (by linarith : 0 ≤ L)
    have h3 : Real.sqrt L ≤ L := by nlinarith
    have := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg m)
    linarith

/-- The `(d+1)`-st power of `n^{1/(d+1)}` is `n`. -/
private lemma rpow_frac_pow {x : ℝ} (hx : 0 ≤ x) (d : ℕ) :
    (x ^ ((1 : ℝ) / (d + 1))) ^ (d + 1) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have hexp : ((1 : ℝ) / (d + 1)) * (((d + 1 : ℕ) : ℝ)) = 1 := by
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  rw [hexp, Real.rpow_one]

/-- A bound on every local time in the shell `||x| - r| ≤ 3` bounds the shell maximum. -/
private lemma shellMax_le_of_forall {d : ℕ} (x : ℕ → Site d) (n r : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ z : Site d, |euclidNorm z - r| ≤ 3 → (localTime x n z : ℝ) ≤ K) :
    (shellMax x n r : ℝ) ≤ K := by
  have h1 : shellMax x n r ≤ ⌊K⌋₊ := by
    unfold shellMax
    apply Finset.sup_le
    intro z hz
    exact Nat.le_floor (h z (Finset.mem_filter.mp hz).2)
  exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hK)

/-- The real-variable form of the last step: the six bounds follow from the scale bounds
`c_s N ≤ s ≤ C_m N`, `M ≤ C_s s`, `H ≤ (B₀ + 1) s`, `n ≤ M R`, `R = s^d` and `s ≤ 2H + 1`. -/
private lemma exists_final_constants {d : ℕ} {cs Cs Cm B₀ : ℝ} (hcs : 0 < cs)
    (hCs : 0 < Cs) (hCm : 0 < Cm) (hB₀ : 0 ≤ B₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N s R M H nn : ℝ, 0 < N → nn = N ^ (d + 1) → R = s ^ d →
      0 ≤ M → 2 ≤ cs * N → cs * N ≤ s → s ≤ Cm * N → M ≤ Cs * s → H ≤ (B₀ + 1) * s →
      nn ≤ M * R → s ≤ 2 * H + 1 →
      c * N ^ d ≤ R ∧ R ≤ C * N ^ d ∧ c * N ≤ M ∧ M ≤ C * N ∧ c * N ≤ H ∧ H ≤ C * N := by
  have hCmd : 0 < Cm ^ d := pow_pos hCm d
  have hcsd : 0 < cs ^ d := pow_pos hcs d
  refine ⟨min (min (cs ^ d) (Cm ^ d)⁻¹) (cs / 4),
    max (max (Cm ^ d) (Cs * Cm)) ((B₀ + 1) * Cm), ?_, ?_, ?_⟩
  · exact lt_min (lt_min hcsd (inv_pos.mpr hCmd)) (by linarith)
  · exact lt_max_of_lt_left (lt_max_of_lt_left hCmd)
  intro N s R M H nn hN hnn hR hM0 h2 hcsN hsCm hMs hHs hnM hsH
  have hc1 : min (min (cs ^ d) (Cm ^ d)⁻¹) (cs / 4) ≤ cs ^ d :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : min (min (cs ^ d) (Cm ^ d)⁻¹) (cs / 4) ≤ (Cm ^ d)⁻¹ :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : min (min (cs ^ d) (Cm ^ d)⁻¹) (cs / 4) ≤ cs / 4 := min_le_right _ _
  have hC1 : Cm ^ d ≤ max (max (Cm ^ d) (Cs * Cm)) ((B₀ + 1) * Cm) :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hC2 : Cs * Cm ≤ max (max (Cm ^ d) (Cs * Cm)) ((B₀ + 1) * Cm) :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hC3 : (B₀ + 1) * Cm ≤ max (max (Cm ^ d) (Cs * Cm)) ((B₀ + 1) * Cm) := le_max_right _ _
  set c := min (min (cs ^ d) (Cm ^ d)⁻¹) (cs / 4) with hc
  set C := max (max (Cm ^ d) (Cs * Cm)) ((B₀ + 1) * Cm) with hC
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact le_min (le_min hcsd.le (inv_pos.mpr hCmd).le) (by linarith)
  have hNd : 0 < N ^ d := pow_pos hN d
  have hcsN0 : 0 < cs * N := mul_pos hcs hN
  have hs0 : 0 < s := lt_of_lt_of_le hcsN0 hcsN
  have hRlow : cs ^ d * N ^ d ≤ R := by
    rw [hR, ← mul_pow]
    exact pow_le_pow_left₀ hcsN0.le hcsN d
  have hRup : R ≤ Cm ^ d * N ^ d := by
    rw [hR, ← mul_pow]
    exact pow_le_pow_left₀ hs0.le hsCm d
  have hR0 : 0 ≤ R := by rw [hR]; exact pow_nonneg hs0.le d
  have hN1 : N ^ (d + 1) = N ^ d * N := pow_succ N d
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right hc1 hNd.le).trans hRlow
  · exact hRup.trans (mul_le_mul_of_nonneg_right hC1 hNd.le)
  · have h1 : N ^ d * N ≤ M * (Cm ^ d * N ^ d) := by
      calc N ^ d * N = nn := by rw [hnn, hN1]
        _ ≤ M * R := hnM
        _ ≤ M * (Cm ^ d * N ^ d) := mul_le_mul_of_nonneg_left hRup hM0
    have h2 : N ≤ M * Cm ^ d := by
      have h3 : N ^ d * N ≤ N ^ d * (M * Cm ^ d) := by
        calc N ^ d * N ≤ M * (Cm ^ d * N ^ d) := h1
          _ = N ^ d * (M * Cm ^ d) := by ring
      exact le_of_mul_le_mul_left h3 hNd
    have h4 : (Cm ^ d)⁻¹ * N ≤ M := by
      rw [inv_mul_le_iff₀ hCmd]
      linarith
    exact (mul_le_mul_of_nonneg_right hc2 hN.le).trans h4
  · calc M ≤ Cs * s := hMs
      _ ≤ Cs * (Cm * N) := mul_le_mul_of_nonneg_left hsCm hCs.le
      _ = (Cs * Cm) * N := by ring
      _ ≤ C * N := mul_le_mul_of_nonneg_right hC2 hN.le
  · have h1 : cs * N / 4 ≤ H := by linarith
    calc c * N ≤ cs / 4 * N := mul_le_mul_of_nonneg_right hc3 hN.le
      _ = cs * N / 4 := by ring
      _ ≤ H := h1
  · calc H ≤ (B₀ + 1) * s := hHs
      _ ≤ (B₀ + 1) * (Cm * N) := mul_le_mul_of_nonneg_left hsCm (by linarith)
      _ = ((B₀ + 1) * Cm) * N := by ring
      _ ≤ C * N := mul_le_mul_of_nonneg_right hC3 hN.le

/-- The mass inequality: the mass identity, the mass error and the radial packing inequality give
`2ε (d/(d+1)) ω_d^{-1/d} s^{d+1} ≤ n + ω_d S^d δ` for `s = R_n^{1/d}`. -/
private lemma mass_inequality {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (x : ℕ → Site d)
    (n : ℕ) {S δ s : ℝ} (hs : s = ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d)) (hspos : 0 < s)
    (hS : 0 < S) (hDS : cellSet x n ⊆ Metric.ball 0 S)
    (happrox : ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
      |cellLocalTime x n y - potential d ε (cellSet x n) y| ≤ δ) :
    2 * ε * ((d : ℝ) / (d + 1) * unitBallVolume d ^ (-(1 : ℝ) / d)) * s ^ (d + 1) ≤
      n + unitBallVolume d * S ^ d * δ := by
  have hd1 : 1 ≤ d := by omega
  have hD : MeasurableSet (cellSet x n) := CERW.Support.Occupation.measurableSet_cellSet x n
  have hDb : Bornology.IsBounded (cellSet x n) := Metric.isBounded_ball.subset hDS
  have hsd : s ^ d = ((departureRange x n).card : ℝ) := by
    rw [hs]
    exact CERW.Generic.Kernel.rpow_one_div_natCast_pow (Nat.cast_nonneg _) hd1
  have hpack := CERW.Generic.Kernel.le_setIntegral_norm hd1 hD hDb
  have hRpos : 0 < ((departureRange x n).card : ℝ) := by
    rw [← hsd]
    exact pow_pos hspos d
  rw [CERW.Support.Occupation.volume_cellSet, ENNReal.toReal_natCast] at hpack
  have hRpow : ((departureRange x n).card : ℝ) ^ (1 + (1 : ℝ) / d) = s ^ (d + 1) := by
    rw [Real.rpow_add hRpos, Real.rpow_one, ← hs, ← hsd, pow_succ]
  rw [hRpow] at hpack
  have hid := CERW.Support.Geometry.integral_ball_potential hd ε hD hDS
  have herr := CERW.Support.Coarse.abs_sub_integral_potential_le hd hε.le x n hS hDS happrox
  rw [hid] at herr
  have h1 := (abs_le.mp herr).1
  have h2 := mul_le_mul_of_nonneg_left hpack (by positivity : 0 ≤ 2 * ε)
  linarith

/-- If `s² ≤ n` and `t² ≤ n` for a real `n ≥ 0`, then `t s ≤ n`. -/
private lemma mul_le_of_sq_le_sq {s t n : ℝ} (hn : 0 ≤ n)
    (h1 : s ^ 2 ≤ n) (h2 : t ^ 2 ≤ n) : t * s ≤ n := by
  by_contra hcon
  rw [not_le] at hcon
  nlinarith [mul_self_lt_mul_self hn hcon, mul_le_mul h2 h1 (sq_nonneg s) hn]

/-- The deterministic core of `prop:coarse`: for kernel constants `K, C_r, C_v` there are
constants `c, C` and a threshold `n₀` such that, on a path satisfying the interval bound, the
approximation bound, the radial test and the vector bound, the six bounds of `eq:coarse` hold. -/
private lemma coarse_deterministic {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) {K Cr Cv : ℝ} (hK : 0 < K) (hCr : 0 < Cr) (hCv : 0 ≤ Cv)
    {bd r₀ : ℕ} (hbd : 3 ≤ bd) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ {Ω : Type u} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ), n₀ ≤ n → X 0 ω = 0 →
        (∀ j, X (j + 1) ω - X j ω ∈ unitSteps d) →
        (maxLocalTime (fun j => X j ω) n : ℝ) ≤
          K * ε * ((departureRange (fun j => X j ω) n).card : ℝ) ^ ((1 : ℝ) / d) +
            K * Real.log (n + 2) ^ 2 →
        (∀ s t : ℕ, s < t → t ≤ n →
          (intervalMax (fun j => X j ω) s t : ℝ) ≤
            K * ε * (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) +
              K * Real.log (n + 2) ^ 2) →
        (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
          |cellLocalTime (fun j => X j ω) n y -
              potential d ε (cellSet (fun j => X j ω) n) y| ≤
            K * (Real.sqrt (maxLocalTime (fun j => X j ω) n) * Real.log (n + 2) +
              Real.log (n + 2))) →
        (∀ r : ℕ, r₀ ≤ r → r ≤ n →
          tail d (cellSet (fun j => X j ω) n) ((r : ℝ) + bd) ≤
            Cr * shellMax (fun j => X j ω) n r *
              (tail d (cellSet (fun j => X j ω) n) ((r : ℝ) - bd) -
                tail d (cellSet (fun j => X j ω) n) ((r : ℝ) + bd)) +
            Cr * (Real.sqrt ((maxLocalTime (fun j => X j ω) n : ℝ) * (r : ℝ) ^ (1 - (d : ℝ)) *
                tail d (cellSet (fun j => X j ω) n) ((r : ℝ) - bd) * Real.log (n + 2)) +
              (r : ℝ) ^ (1 - (d : ℝ)) * Real.log (n + 2))) →
        (∀ s t : ℕ, s < t → t ≤ n →
          ‖compensated ε X t ω - compensated ε X s ω‖ ≤
            Cv * Real.sqrt (((t : ℝ) - s) * Real.log (n + 2))) →
        c * ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ d ≤
            ((departureRange (fun j => X j ω) n).card : ℝ) ∧
          ((departureRange (fun j => X j ω) n).card : ℝ) ≤
            C * ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ d ∧
          c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ≤ (maxLocalTime (fun j => X j ω) n : ℝ) ∧
          (maxLocalTime (fun j => X j ω) n : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ∧
          c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ≤ maxRadius (fun j => X j ω) n ∧
          maxRadius (fun j => X j ω) n ≤ C * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hbd1 : (1 : ℝ) ≤ (bd : ℝ) := by exact_mod_cast (by omega : 1 ≤ bd)
  have hbd3 : (3 : ℝ) ≤ (bd : ℝ) := by exact_mod_cast hbd
  obtain ⟨cs, Cs, hcs, hCs, hsst⟩ :=
    exists_sstar_bounds hd1 (Cd := K * ε) (C := K) (mul_pos hK hε).le hK.le
  set C₁ : ℝ := K * Cs + Cs with hC₁
  have hC₁pos : 0 < C₁ := add_pos (mul_pos hK hCs) hCs
  obtain ⟨Csh, hCsh, hshell⟩ := exists_shell_bound hd
  obtain ⟨B₀, Ct, hB₀, hCt, n₁, htail⟩ := exists_coarse_tail hd (Crad := Cr) (C₁ := C₁)
    (Csh := Csh) (c := cs) (bd := (bd : ℝ)) (r₀ := (r₀ : ℝ)) hCr hC₁pos hCsh hcs hbd1
  obtain ⟨n₂, hH⟩ := exists_maxRadius_le.{u} hd hε (Cv := Cv) (CI := K) (Ct := Ct) (B₀ := B₀)
    (c := cs) hCv hK.le hCt.le hB₀ hcs
  have hwd : 0 < unitBallVolume d := unitBallVolume_pos d
  have hB₀pos : 0 < B₀ := by linarith only [hB₀]
  set cp : ℝ := 2 * ε * ((d : ℝ) / (d + 1) * unitBallVolume d ^ (-(1 : ℝ) / d)) with hcp
  have hcp0 : 0 < cp :=
    mul_pos (mul_pos two_pos hε)
      (mul_pos (div_pos hdR (by linarith only [hdR])) (Real.rpow_pos_of_pos hwd _))
  set Cq : ℝ := unitBallVolume d * (B₀ + 2) ^ d * (K * Cs) with hCq
  have hCq0 : 0 ≤ Cq :=
    (mul_pos (mul_pos hwd (pow_pos (by linarith only [hB₀]) d)) (mul_pos hK hCs)).le
  obtain ⟨Cm, hCm, hmass⟩ := exists_le_of_mass (d := d) hcp0 hcs hCq0
  obtain ⟨c, C, hc, hC, hfin⟩ := exists_final_constants (d := d) hcs hCs hCm hB₀pos.le
  have hdp1 : (0 : ℝ) < 1 / (d + 1) := div_pos one_pos (by linarith only [hdR])
  have hNtend : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (d + 1))) Filter.atTop
      Filter.atTop :=
    (tendsto_rpow_atTop hdp1).comp tendsto_natCast_atTop_atTop
  have hNlarge : ∀ᶠ n : ℕ in Filter.atTop, (d : ℝ) + 6 ≤ cs * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    filter_upwards [hNtend.eventually_ge_atTop (((d : ℝ) + 6) / cs)] with n hn
    rw [div_le_iff₀ hcs] at hn
    linarith only [hn]
  have hθ : 0 < cs / (K * Cs) ^ 2 := div_pos hcs (pow_pos (mul_pos hK hCs) 2)
  have hlim := CERW.Support.Main.tendsto_log_rpow_div_rpow (2 : ℝ)
    (c := (1 : ℝ) / (d + 1)) hdp1
  have hLsmall : ∀ᶠ n : ℕ in Filter.atTop,
      Real.log (n + 2) ^ 2 ≤ cs / (K * Cs) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    filter_upwards [hlim.eventually_le_const hθ, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hNpos : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos hnpos _
    rw [Real.rpow_two, div_le_iff₀ hNpos] at hn
    exact hn
  have hBlarge : ∀ᶠ n : ℕ in Filter.atTop, (B₀ + 2) ^ 2 ≤ (n : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop ⌈(B₀ + 2) ^ 2⌉₊] with n hn
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
    (hsst.and (hmass.and (hNlarge.and (hLsmall.and (hBlarge.and (
      (Filter.eventually_ge_atTop n₁).and ((Filter.eventually_ge_atTop n₂).and
        (Filter.eventually_ge_atTop 2))))))))
  refine ⟨c, C, hc, hC, max n₀ 2, le_max_right _ _, ?_⟩
  intro Ω X ω n hn h0 hstep hM hint happ hrad hvec
  obtain ⟨hsstn, hmassn, hN6, hLn, hen, hn1, hn2, hn3⟩ := hn₀ n ((le_max_left _ _).trans hn)
  set x : ℕ → Site d := fun j => X j ω with hx
  set R : ℕ := (departureRange x n).card with hRdef
  set s : ℝ := (R : ℝ) ^ ((1 : ℝ) / d) with hs
  set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1)) with hN
  set L : ℝ := Real.log (n + 2) with hLdef
  have hn2' : 2 ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN0 : 0 < N := Real.rpow_pos_of_pos hnpos _
  have hL1 : 1 ≤ L := one_le_log_add_two hn2'
  have hsd : s ^ d = (R : ℝ) :=
    CERW.Generic.Kernel.rpow_one_div_natCast_pow (Nat.cast_nonneg _) hd1
  have hnMR : (n : ℝ) ≤ (maxLocalTime x n : ℝ) * (R : ℝ) := by
    exact_mod_cast CERW.Support.Occupation.le_maxLocalTime_mul_card x n
  obtain ⟨hcsN, hMs, hsqrt⟩ := hsstn (maxLocalTime x n : ℝ) s (Nat.cast_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by rw [hsd]; exact hnMR) hM
  have hd6 : (d : ℝ) + 6 ≤ cs * N := hN6
  have hcsN0 : 0 < cs * N := mul_pos hcs hN0
  have hs0 : 0 < s := lt_of_lt_of_le hcsN0 hcsN
  have hs6 : 6 ≤ s := by linarith only [hd6, hcsN, hdR]
  have hsd' : Real.sqrt d ≤ s := by
    have h1 : Real.sqrt d ≤ (d : ℝ) + 6 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith only [hdR], by nlinarith only [hdR]⟩
    linarith only [h1, hd6, hcsN]
  set δ : ℝ := K * Cs * Real.sqrt s * L with hδ
  have hδ0 : 0 ≤ δ :=
    mul_nonneg (mul_nonneg (mul_pos hK hCs).le (Real.sqrt_nonneg s)) (by linarith only [hL1])
  have hδC : δ ≤ C₁ * Real.sqrt s * L := by
    have h1 : K * Cs ≤ C₁ := by linarith only [hC₁, hCs]
    have h2 : 0 ≤ Real.sqrt s * L := mul_nonneg (Real.sqrt_nonneg s) (by linarith only [hL1])
    calc δ = (K * Cs) * (Real.sqrt s * L) := by rw [hδ]; ring
      _ ≤ C₁ * (Real.sqrt s * L) := mul_le_mul_of_nonneg_right h1 h2
      _ = C₁ * Real.sqrt s * L := by ring
  have hδs : δ ≤ s := by
    have h1 : K * Cs * L ≤ Real.sqrt s := by
      apply Real.le_sqrt_of_sq_le
      have h2 : (K * Cs) ^ 2 * L ^ 2 ≤ (K * Cs) ^ 2 * (cs / (K * Cs) ^ 2 * N) :=
        mul_le_mul_of_nonneg_left hLn (sq_nonneg _)
      have h3 : (K * Cs) ^ 2 * (cs / (K * Cs) ^ 2 * N) = cs * N := by
        field_simp
      calc (K * Cs * L) ^ 2 = (K * Cs) ^ 2 * L ^ 2 := by ring
        _ ≤ cs * N := h2.trans_eq h3
        _ ≤ s := hcsN
    have h2 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
    calc δ = (K * Cs * L) * Real.sqrt s := by rw [hδ]; ring
      _ ≤ Real.sqrt s * Real.sqrt s := mul_le_mul_of_nonneg_right h1 h2
      _ = s := Real.mul_self_sqrt hs0.le
  have hlocal : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
      |cellLocalTime x n y - potential d ε (cellSet x n) y| ≤ δ := by
    intro y hy
    refine (happ y hy).trans ?_
    calc K * (Real.sqrt (maxLocalTime x n) * L + L) ≤ K * (Cs * Real.sqrt s * L) := by
          exact mul_le_mul_of_nonneg_left hsqrt hK.le
      _ = δ := by rw [hδ]; ring
  have hRn : (R : ℝ) ≤ n := by exact_mod_cast CERW.Support.Occupation.card_departureRange_le x n
  have hBs : (B₀ + 2) * s ≤ n := by
    have h1 : s ^ 2 ≤ n := by
      calc s ^ 2 ≤ s ^ d := pow_le_pow_right₀ (by linarith only [hs6]) hd
        _ = R := hsd
        _ ≤ n := hRn
    exact mul_le_of_sq_le_sq hnpos.le h1 hen
  have hBs4 : B₀ * s + 4 ≤ 2 * n := by linarith only [hBs, hs6, hnpos]
  have hB₀2 : (2 : ℝ) ≤ B₀ := by linarith only [hB₀]
  have hMC₁ : (maxLocalTime x n : ℝ) ≤ C₁ * s :=
    hMs.trans (mul_le_mul_of_nonneg_right (by linarith [mul_pos hK hCs]) hs0.le)
  have hradC : ∀ r : ℕ, (r₀ : ℝ) ≤ r → r ≤ n →
      tail d (cellSet x n) ((r : ℝ) + bd) ≤
        Cr * shellMax x n r * (tail d (cellSet x n) ((r : ℝ) - bd) -
          tail d (cellSet x n) ((r : ℝ) + bd)) +
        Cr * (Real.sqrt ((maxLocalTime x n : ℝ) * (r : ℝ) ^ (1 - (d : ℝ)) *
            tail d (cellSet x n) ((r : ℝ) - bd) * L) + (r : ℝ) ^ (1 - (d : ℝ)) * L) :=
    fun r hr hrn => hrad r (by exact_mod_cast hr) hrn
  have hshellC : ∀ r : ℕ, s ≤ r → (r : ℝ) ≤ B₀ * s →
      (shellMax x n r : ℝ) ≤ Csh * B₀ ^ (((d : ℝ) - 1) / (2 * d - 1)) *
        s ^ (1 - 1 / (2 * (d : ℝ) - 1)) *
        (tail d (cellSet x n) ((r : ℝ) - bd) + δ) ^ (1 / (2 * (d : ℝ) - 1)) := by
    intro r hsr hrB
    apply shellMax_le_of_forall x n r
    · exact mul_nonneg (mul_nonneg (mul_nonneg hCsh.le (Real.rpow_nonneg hB₀pos.le _))
        (Real.rpow_nonneg hs0.le _))
        (Real.rpow_nonneg (add_nonneg (CERW.Support.Geometry.tail_nonneg _ _) hδ0) _)
    · intro z hz
      exact hshell ε hε hεd x n δ s B₀ r bd hs hs6 hδ0 hδs hB₀2 hsr hrB hbd3
        (fun y hy => hlocal y (hy.trans hBs4)) z hz
  have hFt := htail x n δ hn1 hcsN hMC₁ hδ0 hδC hradC hshellC
  have hHle : maxRadius x n ≤ (B₀ + 1) * s := hH X ω n hn2 h0 hstep hvec hint hcsN hFt
  have hHnn : 0 ≤ maxRadius x n :=
    (euclidNorm_nonneg (x 0)).trans (CERW.euclidNorm_le_maxRadius x (Nat.zero_le n))
  set S : ℝ := (B₀ + 1) * s + Real.sqrt d with hSdef
  have hS0 : 0 < S :=
    add_pos_of_pos_of_nonneg (mul_pos (by linarith only [hB₀pos]) hs0) (Real.sqrt_nonneg _)
  have hSs : S ≤ (B₀ + 2) * s := by linarith only [hSdef, hsd']
  have hDS : cellSet x n ⊆ Metric.ball 0 S :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 x n).trans
      (Metric.ball_subset_ball (by linarith only [hHle, hSdef]))
  have hball : ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
      |cellLocalTime x n y - potential d ε (cellSet x n) y| ≤ δ := by
    intro y hy
    apply hlocal y
    have h1 : ‖y‖ < S := mem_ball_zero_iff.mp hy
    linarith only [h1, hSs, hBs, hnpos]
  have hmi := mass_inequality hd hε x n hs hs0 hS0 hDS hball
  have herr : unitBallVolume d * S ^ d * δ ≤ Cq * s ^ ((d : ℝ) + 1 / 2) * L := by
    have h1 : S ^ d ≤ ((B₀ + 2) * s) ^ d := pow_le_pow_left₀ hS0.le hSs d
    have h2 : s ^ ((d : ℝ) + 1 / 2) = s ^ d * Real.sqrt s := by
      rw [Real.rpow_add hs0, Real.rpow_natCast, Real.sqrt_eq_rpow]
    have h3 : unitBallVolume d * S ^ d * δ ≤ unitBallVolume d * ((B₀ + 2) * s) ^ d * δ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hwd.le) hδ0
    calc unitBallVolume d * S ^ d * δ ≤ unitBallVolume d * ((B₀ + 2) * s) ^ d * δ := h3
      _ = Cq * s ^ ((d : ℝ) + 1 / 2) * L := by
          rw [h2, hδ, hCq, mul_pow]
          ring
  have hsCm : s ≤ Cm * N := hmassn s hcsN (hmi.trans (add_le_add le_rfl herr))
  have hsH : s ≤ 2 * maxRadius x n + 1 := by
    have h1 : (R : ℝ) ≤ (2 * maxRadius x n + 1) ^ d :=
      (Nat.cast_le.mpr (Finset.card_le_card
        (CERW.Support.Occupation.departureRange_subset_ballFinset x n))).trans
        (LatticeProb.card_ballFinset_le d hHnn)
    rw [← hsd] at h1
    exact le_of_pow_le_pow_left₀ (by omega) (by linarith only [hHnn]) h1
  have hnN : (n : ℝ) = N ^ (d + 1) := (rpow_frac_pow hnpos.le d).symm
  exact hfin N s R (maxLocalTime x n : ℝ) (maxRadius x n) n hN0 hnN hsd.symm (Nat.cast_nonneg _)
    (by linarith only [hd6, hdR]) hcsN hsCm hMs hHle hnMR hsH

/-- A measure bound for a set covered by three sets of small measure and a null set. -/
private lemma measure_le_of_subset_union_three {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A₁ A₂ A₃ N B : Set Ω} {a₁ a₂ a₃ c : ENNReal}
    (hsub : B ⊆ A₁ ∪ A₂ ∪ A₃ ∪ N) (h₁ : μ A₁ ≤ a₁) (h₂ : μ A₂ ≤ a₂) (h₃ : μ A₃ ≤ a₃)
    (hN : μ N = 0) (hc : a₁ + a₂ + a₃ ≤ c) : μ B ≤ c := by
  refine (measure_mono hsub).trans ((measure_union_le _ N).trans ?_)
  rw [hN, add_zero]
  refine (measure_union_le _ A₃).trans ((add_le_add (measure_union_le A₁ A₂) h₃).trans ?_)
  exact (add_le_add (add_le_add h₁ h₂) le_rfl).trans hc

/-- `prop:coarse`, for any kernel `b` with the kernel facts. -/
theorem coarse_bounds_of_kernelFacts {d : ℕ} (hd : 2 ≤ d) {b : Site d → ℝ} {h : ℝ → ℝ}
    (hK : KernelFacts d b h) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) → ∀ p : ℝ, 0 < p → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
        μ {ω | ¬ (c * N ^ d ≤ ((CERW.departureRange (X · ω) n).card : ℝ) ∧
                  ((CERW.departureRange (X · ω) n).card : ℝ) ≤ C * N ^ d ∧
                  c * N ≤ (CERW.maxLocalTime (X · ω) n : ℝ) ∧
                  (CERW.maxLocalTime (X · ω) n : ℝ) ≤ C * N ∧
                  c * N ≤ CERW.maxRadius (X · ω) n ∧ CERW.maxRadius (X · ω) n ≤ C * N)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cd, hCd, hloc⟩ := local_time_potential_of_kernelFacts.{u} hd hK
  obtain ⟨r₀, hr₀, hrad⟩ := radial_test_of_kernelFacts.{u} hd hK
  intro ε hε hεd p hp
  obtain ⟨Cl, hCl, hloc'⟩ := hloc ε hε hεd p hp
  obtain ⟨Cr, hCr, hrad'⟩ := hrad ε hε hεd p hp
  obtain ⟨Cv, hCv, hvec⟩ := exists_compensated_bound.{u} hd1 hε.le hεd hp
  have hK0 : 0 < max Cd Cl := lt_max_of_lt_left hCd
  obtain ⟨c, C₀, hc, hC₀, n₀, hn₀, hdet⟩ := coarse_deterministic.{u} hd hε hεd hK0 hCr hCv.le
    (bd := ⌈Real.sqrt d / 2⌉₊ + 6) (r₀ := r₀) (by omega)
  have hn₀p : 0 ≤ (n₀ : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨c, max C₀ (Cl + Cr + Cv + (n₀ : ℝ) ^ p), hc, lt_max_of_lt_left hC₀, ?_⟩
  intro Ω _ μ _ X hX n hn
  dsimp only
  by_cases hn₀le : n₀ ≤ n
  · have hnull : μ {ω | ¬ (X 0 ω = 0 ∧ ∀ j : ℕ, X (j + 1) ω - X j ω ∈ unitSteps d)} = 0 := by
      refine ae_iff.mp ?_
      filter_upwards [ae_iff.mpr hX.start,
        ae_all_iff.mpr (fun j => ae_sub_mem_unitSteps hd1 hε.le hεd hX j)] with ω h0 h1
      exact ⟨h0, h1⟩
    have hL1 := one_le_log_add_two hn
    have hCdK : Cd ≤ max Cd Cl := le_max_left _ _
    have hClK : Cl ≤ max Cd Cl := le_max_right _ _
    refine measure_le_of_subset_union_three (fun ω hω => ?_) (hloc' μ X hX n hn) (hrad' μ X hX n hn)
      (hvec hX n (by omega)) hnull ?_
    · by_contra hcon
      rw [Set.mem_union, Set.mem_union, Set.mem_union, not_or, not_or, not_or] at hcon
      obtain ⟨⟨⟨hA, hB⟩, hV⟩, hZ⟩ := hcon
      simp only [Set.mem_setOf_eq, not_not] at hA hB hZ
      simp only [Set.mem_setOf_eq, not_exists, not_and, not_lt] at hV
      obtain ⟨hM, hint, happ⟩ := hA
      have hlam := lam_le_sq hL1 d
      have hlam0 : 0 ≤ (if d = 2 then Real.log ((n : ℝ) + 2) ^ 2 else Real.log ((n : ℝ) + 2)) := by
        split_ifs
        · exact sq_nonneg _
        · linarith
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hdet X ω n hn₀le hZ.1 hZ.2
        (hM.trans (add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCdK hε.le)
            (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (mul_le_mul hClK hlam hlam0 hK0.le)))
        (fun s t hst htn => (hint s t hst htn).trans (add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCdK hε.le)
            (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (mul_le_mul hClK hlam hlam0 hK0.le)))
        (fun y hy => (happ y hy).trans
          ((mul_le_mul_of_nonneg_left (error_scale_le hL1 (Nat.cast_nonneg _) d) hCl.le).trans
            (mul_le_mul_of_nonneg_right hClK
              (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) (by linarith)))))
        hB hV
      have hNd : 0 ≤ ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ d :=
        pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) d
      have hN1 : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hCC : C₀ ≤ max C₀ (Cl + Cr + Cv + (n₀ : ℝ) ^ p) := le_max_left _ _
      exact hω ⟨h1, h2.trans (mul_le_mul_of_nonneg_right hCC hNd), h3,
        h4.trans (mul_le_mul_of_nonneg_right hCC hN1), h5,
        h6.trans (mul_le_mul_of_nonneg_right hCC hN1)⟩
    · have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      rw [← ENNReal.ofReal_add (mul_nonneg hCl.le hnp) (mul_nonneg hCr.le hnp),
        ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hCl.le hnp) (mul_nonneg hCr.le hnp))
          (mul_nonneg hCv.le hnp)]
      refine ENNReal.ofReal_le_ofReal (?_ : _ ≤ _)
      rw [← add_mul, ← add_mul]
      exact mul_le_mul_of_nonneg_right
        ((by linarith : Cl + Cr + Cv ≤ Cl + Cr + Cv + (n₀ : ℝ) ^ p).trans (le_max_right _ _)) hnp
  · exact (prob_le_one).trans (ENNReal.one_le_ofReal.mpr
      (one_le_mul_rpow_neg hp (by omega) (not_le.mp hn₀le).le
        ((by linarith : (n₀ : ℝ) ^ p ≤ Cl + Cr + Cv + (n₀ : ℝ) ^ p).trans (le_max_right _ _))))

end CERW.Support.Coarse
