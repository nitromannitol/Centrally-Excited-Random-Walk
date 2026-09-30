import CERW.Support.Coarse.Vector
import CERW.Support.Crossing.Kinematics
import CERW.Generic.Young.Absorb

/-!
# Crossings through a small set

`eq:crossing-before-young` and `eq:crossing`, as a deterministic implication. Take an interval
`[s, t)` whose sites satisfy `v · X_j > b > 0` and `|X_j| < r`, with `|v| = 1` and `b/r ≥ κ`, and
suppose `v · (X_t - X_s) ≥ h`. Each first departure in the interval has projected inward mean
`ε v · u_{X_j} > εκ`. So `v · (Z_t - Z_s) ≥ h + εκk`, where `k` is the number of first departures.
If `|Z_t - Z_s| ≤ C_v √((t - s) L)` (`eq:vector`) and `M_{s,t} ≤ C_I ε k^{1/d} + C_I λ`
(`eq:interval`), then `t - s ≤ m M_{s,t}` gives `(h + εκk)² ≤ C m L (ε k^{1/d} + λ)`. Young's
inequality absorbs the `k` term: `h² ≤ C_κ (m^γ L^γ + m λ L)` with `γ = 2d/(2d - 1)`.
-/

namespace CERW.Support.Coarse

open LatticeProb Finset CERW CERW.Support.Crossing

variable {d : ℕ}

/-- The compensated position gains, between `s` and `t`, the plain displacement plus `ε` times the
inward directions of the first departures in `[s, t)`. -/
private lemma compensated_sub_eq {Ω : Type*} (ε : ℝ) (X : ℕ → Ω → Site d) (ω : Ω)
    {s t : ℕ} (hst : s ≤ t) :
    compensated ε X t ω - compensated ε X s ω =
      (toSpace (X t ω) - toSpace (X s ω)) +
        ε • ∑ j ∈ Ico s t,
          (if X j ω ≠ 0 ∧ X j ω ∉ (range j).image (fun i => X i ω)
            then unitDir (toSpace (X j ω)) else 0) := by
  have hsum := Finset.sum_range_add_sum_Ico
    (fun j => (if X j ω ≠ 0 ∧ X j ω ∉ (range j).image (fun i => X i ω)
      then unitDir (toSpace (X j ω)) else 0)) hst
  unfold compensated
  rw [← hsum]
  rw [smul_add, sub_add_eq_sub_sub]
  abel

/-- The embedded origin is zero. -/
private lemma toSpace_zero' : toSpace (0 : Site d) = 0 := by
  ext i
  simp [toSpace]

/-- The embedded compensated increment projects to the plain projected increment plus `ε` times
the projected inward directions of the first departures. -/
private lemma inner_compensated_sub {Ω : Type*} (ε : ℝ) (X : ℕ → Ω → Site d) (ω : Ω)
    {s t : ℕ} (hst : s ≤ t) (v : EuclideanSpace ℝ (Fin d)) :
    inner ℝ v (compensated ε X t ω - compensated ε X s ω) =
      inner ℝ v (toSpace (X t ω) - toSpace (X s ω)) +
        ε * ∑ j ∈ Ico s t,
          inner ℝ v (if X j ω ≠ 0 ∧ X j ω ∉ (range j).image (fun i => X i ω)
            then unitDir (toSpace (X j ω)) else 0) := by
  rw [compensated_sub_eq ε X ω hst, inner_add_right, inner_smul_right, inner_sum]

/-- Every first departure in a crossing interval contributes more than `κ` to the projected
displacement. -/
private lemma sum_inner_unitDir_ge {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω)
    (v : EuclideanSpace ℝ (Fin d)) {κ b r : ℝ} (hb : 0 < b) (hκb : κ ≤ b / r) {s t : ℕ}
    (hsite : ∀ j ∈ Ico s t, b < inner ℝ v (toSpace (X j ω)) ∧ euclidNorm (X j ω) < r) :
    κ * (freshCount (fun j => X j ω) s t : ℝ) ≤
      ∑ j ∈ Ico s t,
        inner ℝ v (if X j ω ≠ 0 ∧ X j ω ∉ (range j).image (fun i => X i ω)
          then unitDir (toSpace (X j ω)) else 0) := by
  have hterm : ∀ j ∈ Ico s t,
      κ * (if X j ω ∉ (range j).image (fun i => X i ω) then (1 : ℝ) else 0) ≤
        inner ℝ v (if X j ω ≠ 0 ∧ X j ω ∉ (range j).image (fun i => X i ω)
          then unitDir (toSpace (X j ω)) else 0) := by
    intro j hj
    have hxj : X j ω ≠ 0 := by
      intro hx
      have hb' := (hsite j hj).1
      rw [hx, toSpace_zero'] at hb'
      simp only [inner_zero_right] at hb'
      linarith
    by_cases hfresh : X j ω ∉ (range j).image (fun i => X i ω)
    · rw [if_pos (show X j ω ≠ 0 ∧ X j ω ∉ (range j).image (fun i => X i ω)
          from ⟨hxj, hfresh⟩), if_pos hfresh]
      have hlt : b / r < inner ℝ v (unitDir (toSpace (X j ω))) :=
        div_lt_inner_unitDir hb (hsite j hj).1 (by simpa only [norm_toSpace] using (hsite j hj).2)
      simp only [mul_one]
      linarith
    · have hcond : ¬(X j ω ≠ 0 ∧ X j ω ∉ (range j).image (fun i => X i ω)) :=
        fun h => hfresh h.2
      rw [if_neg hcond, if_neg hfresh]
      simp
  calc κ * (freshCount (fun j => X j ω) s t : ℝ)
      = κ * (∑ j ∈ Ico s t,
          if X j ω ∉ (range j).image (fun i => X i ω) then (1 : ℝ) else 0) := by
        congr 1
        rw [freshCount, Finset.sum_boole]
        rfl
    _ = ∑ j ∈ Ico s t,
          κ * (if X j ω ∉ (range j).image (fun i => X i ω) then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum hterm

/-- `eq:crossing`: a crossing of `[s, t)` through sites with `v · x > b`, `|x| < r`, `b/r ≥ κ`, with
projected gain `h`, satisfies `h² ≤ C ((mL)^γ + mLλ)` whenever `eq:vector` and `eq:interval` hold on
the interval. Here `m` is the number of distinct sites and `γ = 2d/(2d - 1)`. -/
theorem exists_crossing_bound (hd : 1 ≤ d) {κ ε Cv CI : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (hCv : 0 ≤ Cv) (hCI : 0 ≤ CI) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (s t : ℕ)
      (v : EuclideanSpace ℝ (Fin d)) (b r h L lam : ℝ),
      s < t → ‖v‖ = 1 → 0 < b → κ ≤ b / r → 0 ≤ h → 0 ≤ L → 0 ≤ lam →
      (∀ j ∈ Ico s t, b < inner ℝ v (toSpace (X j ω)) ∧ euclidNorm (X j ω) < r) →
      h ≤ inner ℝ v (toSpace (X t ω) - toSpace (X s ω)) →
      ‖compensated ε X t ω - compensated ε X s ω‖ ≤ Cv * Real.sqrt (((t : ℝ) - s) * L) →
      (intervalMax (fun j => X j ω) s t : ℝ) ≤
        CI * ε * (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) + CI * lam →
      h ^ 2 ≤ C * ((((Ico s t).image fun j => X j ω).card * L) ^ ((2 * d : ℝ) / (2 * d - 1)) +
        ((Ico s t).image fun j => X j ω).card * L * lam) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := CERW.Generic.Young.sq_le_of_crossing hd
    (A := ε * κ) (B := Cv ^ 2 * CI * ε) (by positivity) (by positivity)
  refine ⟨C₀ * (1 + Cv ^ 2 * CI), by positivity, ?_⟩
  intro Ω X ω s t v b r h L lam hst hv hb hκb hh hL hlam hsite hgain hZ hM
  set m : ℕ := ((Ico s t).image fun j => X j ω).card with hm
  set k : ℕ := freshCount (fun j => X j ω) s t with hk
  have hstle : s ≤ t := le_of_lt hst
  have hstep1 : h + (ε * κ) * (k : ℝ) ≤
      inner ℝ v (compensated ε X t ω - compensated ε X s ω) := by
    rw [inner_compensated_sub ε X ω hstle v]
    have hsum := sum_inner_unitDir_ge X ω v (κ := κ) hb hκb hsite
    have hmul : (ε * κ) * (k : ℝ) ≤
        ε * ∑ j ∈ Ico s t,
          inner ℝ v (if X j ω ≠ 0 ∧ X j ω ∉ (range j).image (fun i => X i ω)
            then unitDir (toSpace (X j ω)) else 0) := by
      rw [← hk] at hsum
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum hε.le
    linarith [hgain]
  have hnorm : inner ℝ v (compensated ε X t ω - compensated ε X s ω) ≤
      ‖compensated ε X t ω - compensated ε X s ω‖ := by
    have h := real_inner_le_norm v (compensated ε X t ω - compensated ε X s ω)
    rwa [hv, one_mul] at h
  have hkey : h + (ε * κ) * (k : ℝ) ≤ Cv * Real.sqrt (((t : ℝ) - s) * L) :=
    hstep1.trans (hnorm.trans hZ)
  have hnonneg : 0 ≤ h + (ε * κ) * (k : ℝ) :=
    add_nonneg hh (mul_nonneg (mul_nonneg hε.le hκ.le) (Nat.cast_nonneg k))
  have hsq : (h + (ε * κ) * (k : ℝ)) ^ 2 ≤
      (Cv * Real.sqrt (((t : ℝ) - s) * L)) ^ 2 :=
    pow_le_pow_left₀ hnonneg hkey 2
  have ht_sub_s : 0 ≤ ((t : ℝ) - s) := by
    have : (s : ℝ) ≤ t := by exact_mod_cast hstle
    linarith
  have hprod : 0 ≤ ((t : ℝ) - s) * L := mul_nonneg ht_sub_s hL
  have hsqrt_sq : (Cv * Real.sqrt (((t : ℝ) - s) * L)) ^ 2 =
      Cv ^ 2 * (((t : ℝ) - s) * L) := by
    rw [mul_pow, Real.sq_sqrt hprod]
  have hcard : ((t : ℝ) - s) ≤ (m : ℝ) * (intervalMax (fun j => X j ω) s t : ℝ) := by
    have h := sub_le_card_mul_intervalMax (fun j => X j ω) s t
    have hcast : ((t - s : ℕ) : ℝ) ≤
        (((Ico s t).image fun j => X j ω).card : ℝ) *
          (intervalMax (fun j => X j ω) s t : ℝ) := by exact_mod_cast h
    rwa [Nat.cast_sub hstle, ← hm] at hcast
  have hdur : ((t : ℝ) - s) ≤
      (m : ℝ) * (CI * ε * (k : ℝ) ^ ((1 : ℝ) / d) + CI * lam) := by
    have h2 : (intervalMax (fun j => X j ω) s t : ℝ) ≤
        CI * ε * (k : ℝ) ^ ((1 : ℝ) / d) + CI * lam := hM
    exact hcard.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg m))
  have hcross : (h + (ε * κ) * (k : ℝ)) ^ 2 ≤
      (m : ℝ) * L * ((Cv ^ 2 * CI * ε) * (k : ℝ) ^ ((1 : ℝ) / d) + Cv ^ 2 * CI * lam) := by
    refine hsq.trans ?_
    rw [hsqrt_sq]
    calc Cv ^ 2 * (((t : ℝ) - s) * L)
        ≤ Cv ^ 2 * (((m : ℝ) *
            (CI * ε * (k : ℝ) ^ ((1 : ℝ) / d) + CI * lam)) * L) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdur hL) (sq_nonneg Cv)
      _ = (m : ℝ) * L *
            ((Cv ^ 2 * CI * ε) * (k : ℝ) ^ ((1 : ℝ) / d) + Cv ^ 2 * CI * lam) := by ring
  have hΛ : 0 ≤ Cv ^ 2 * CI * lam := by positivity
  have hyoung := hC₀ h (k : ℝ) (m : ℝ) L (Cv ^ 2 * CI * lam)
    hh (Nat.cast_nonneg k) (Nat.cast_nonneg m) hL hΛ hcross
  refine le_trans hyoung ?_
  have hM1 : 0 ≤ ((m : ℝ) * L) ^ ((2 * d : ℝ) / (2 * d - 1)) :=
    Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg m) hL) _
  have hM2 : 0 ≤ (m : ℝ) * L * lam := mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hL) hlam
  have hCv2 : 0 ≤ Cv ^ 2 := by simpa only [sq] using mul_nonneg hCv hCv
  have hCvCI : 0 ≤ Cv ^ 2 * CI := mul_nonneg hCv2 hCI
  have hprod1 : 0 ≤ (Cv ^ 2 * CI) * ((m : ℝ) * L * lam) := mul_nonneg hCvCI hM2
  have hprod2 : 0 ≤ (Cv ^ 2 * CI) * ((m : ℝ) * L) ^ ((2 * d : ℝ) / (2 * d - 1)) :=
    mul_nonneg hCvCI hM1
  have hbracket : (m : ℝ) * L * (Cv ^ 2 * CI * lam) ≤
      (Cv ^ 2 * CI) * ((m : ℝ) * L * lam) := le_of_eq (by ring)
  have hgoal : ((m : ℝ) * L) ^ ((2 * d : ℝ) / (2 * d - 1)) +
        (m : ℝ) * L * (Cv ^ 2 * CI * lam) ≤
      (1 + Cv ^ 2 * CI) * (((m : ℝ) * L) ^ ((2 * d : ℝ) / (2 * d - 1)) +
        (m : ℝ) * L * lam) := by
    nlinarith [hM1, hM2, hCvCI, hprod1, hprod2, hbracket]
  calc C₀ * (((m : ℝ) * L) ^ ((2 * d : ℝ) / (2 * d - 1)) +
          (m : ℝ) * L * (Cv ^ 2 * CI * lam))
      ≤ C₀ * ((1 + Cv ^ 2 * CI) * (((m : ℝ) * L) ^ ((2 * d : ℝ) / (2 * d - 1)) +
          (m : ℝ) * L * lam)) := mul_le_mul_of_nonneg_left hgoal hC₀pos.le
    _ = (C₀ * (1 + Cv ^ 2 * CI)) * (((m : ℝ) * L) ^ ((2 * d : ℝ) / (2 * d - 1)) +
          (m : ℝ) * L * lam) := by ring

end CERW.Support.Coarse
