module

public import CERW.LimitShapes.Exit.LocalTime
public import CERW.LimitShapes.Exit.Bracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Finite stopping and occupation estimates

These deterministic facts support the stopping argument of Proposition `prop:coarse`.
-/

namespace CERW.LimitShapes.Exit

open CERW LatticeProb

/-- One departure increases any given local time by at most one. -/
theorem localTime_succ_le {d : ℕ} (X : ℕ → Site d) (n : ℕ) (y : Site d) :
    localTime X (n + 1) y ≤ localTime X n y + 1 := by
  classical
  simp only [localTime, Finset.range_add_one, Finset.filter_insert]
  split_ifs
  · exact Finset.card_insert_le _ _
  · omega

/-- A first bad time exists before the horizon if occupation forces a stop;
the bootstrap estimate excludes the martingale alternative at that time. -/
theorem finite_bootstrap_stop {d : ℕ} (X : ℕ → Site d) (N : ℕ)
    (inside : ℕ → Prop) (P : Site d → Prop) (M : ℕ → Site d → ℝ)
    (R L B : ℝ) (hL : 0 ≤ L) (hN : B < (N : ℝ))
    (hlocal : ∀ n, n ≤ N → (∀ j, j < n → inside j) →
      (∀ y, P y → |M n y| < R) → ∀ y, (localTime X n y : ℝ) ≤ L)
    (hcount : ∀ n, n ≤ N → (∀ j, j < n → inside j) →
      (∀ y, (localTime X n y : ℝ) ≤ L + 1) → (n : ℝ) ≤ B)
    (hsmall : ∀ n, n ≤ N → (∀ j, j < n → inside j) →
      (∀ y, (localTime X n y : ℝ) ≤ L + 1) → ∀ y, P y → |M n y| < R) :
    ∃ τ, τ ≤ N ∧ ¬inside τ ∧ (∀ j, j < τ → inside j) ∧
      (∀ y, (localTime X τ y : ℝ) ≤ L + 1) := by
  classical
  let bad := fun n => ¬inside n ∨ ∃ y, P y ∧ R ≤ |M n y|
  have hex : ∃ n, n ≤ N ∧ bad n := by
    by_contra hn
    have hgood : ∀ n, n ≤ N → inside n ∧ ∀ y, P y → |M n y| < R := by
      intro n hnN
      have hb : ¬bad n := fun hb => hn ⟨n, hnN, hb⟩
      exact ⟨by by_contra hi; exact hb (Or.inl hi),
        fun y hy => lt_of_not_ge (fun hm => hb (Or.inr ⟨y, hy, hm⟩))⟩
    have hi : ∀ j, j < N → inside j := fun j hj => (hgood j (by omega)).1
    have hl := hlocal N le_rfl hi (hgood N le_rfl).2
    have hc := hcount N le_rfl hi (fun y => (hl y).trans (by linarith))
    linarith
  let τ := Nat.find hex
  have ht : τ ≤ N ∧ bad τ := Nat.find_spec hex
  have hbefore : ∀ j, j < τ → inside j ∧ ∀ y, P y → |M j y| < R := by
    intro j hj
    have hb : ¬bad j := by
      intro hb
      exact Nat.find_min hex hj ⟨by omega, hb⟩
    exact ⟨by by_contra hi; exact hb (Or.inl hi),
      fun y hy => lt_of_not_ge (fun hm => hb (Or.inr ⟨y, hy, hm⟩))⟩
  have hi : ∀ j, j < τ → inside j := fun j hj => (hbefore j hj).1
  have hl : ∀ y, (localTime X τ y : ℝ) ≤ L + 1 := by
    cases he : τ with
    | zero => simpa [localTime] using (show (0 : ℝ) ≤ L + 1 by linarith)
    | succ k =>
      have hk : k < τ := by omega
      have hkl := hlocal k (by omega) (fun j hj => hi j (by omega)) (hbefore k hk).2
      intro y
      have hs : (localTime X (k + 1) y : ℝ) ≤ (localTime X k y : ℝ) + 1 := by
        exact_mod_cast localTime_succ_le X k y
      exact hs.trans (by linarith [hkl y])
  refine ⟨τ, ht.1, ?_, hi, hl⟩
  rcases ht.2 with he | ⟨y, hy, hm⟩
  · exact he
  · exact False.elim ((not_lt_of_ge hm) (hsmall τ ht.1 hi hl y hy))

/-- Counting departures in a norm ball bounds the elapsed time by its volume times
the uniform local-time bound. -/
theorem time_le_of_localTime_bound {d : ℕ} (hd : 1 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (X : ℕ → Site d) (n : ℕ) {R K : ℝ} (hR : 1 ≤ R) (hK : 0 ≤ K)
    (hi : ∀ j, j < n → Ψ (toSpace (X j)) < R)
    (hl : ∀ y, (localTime X n y : ℝ) ≤ K * R) :
    (n : ℝ) ≤ K * (2 / normMin Ψ + 1) ^ d * R ^ (d + 1) := by
  classical
  obtain ⟨hm, hc⟩ := Generic.Norm.normMin_pos_mul_le hΨ hd
  have hr : 0 ≤ R / normMin Ψ := div_nonneg (by linarith) hm.le
  have hs : departureRange X n ⊆ ballFinset d (R / normMin Ψ) := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    apply mem_ballFinset_iff.mpr
    apply (le_div_iff₀ hm).mpr
    have hcj := hc (toSpace (X j))
    rw [norm_toSpace] at hcj
    linarith [hi j (Finset.mem_range.mp hj)]
  have hcard : ((departureRange X n).card : ℝ) ≤
      (2 / normMin Ψ + 1) ^ d * R ^ d := by
    calc
      _ ≤ ((ballFinset d (R / normMin Ψ)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hs
      _ ≤ (2 * (R / normMin Ψ) + 1) ^ d := card_ballFinset_le d hr
      _ ≤ ((2 / normMin Ψ + 1) * R) ^ d := by
        apply pow_le_pow_left₀ (by positivity)
        have : 2 * (R / normMin Ψ) = (2 / normMin Ψ) * R := by ring
        rw [this]
        nlinarith
      _ = _ := mul_pow _ _ _
  calc
    (n : ℝ) = ∑ y ∈ departureRange X n, (localTime X n y : ℝ) := by
      exact_mod_cast (Support.Occupation.sum_localTime_eq X n).symm
    _ ≤ ∑ _y ∈ departureRange X n, K * R := Finset.sum_le_sum (fun y _ => hl y)
    _ = ((departureRange X n).card : ℝ) * (K * R) := by simp
    _ ≤ ((2 / normMin Ψ + 1) ^ d * R ^ d) * (K * R) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hK (by linarith))
    _ = _ := by rw [pow_succ]; ring

/-- The Freedman expression has order `sqrt R * log R` when its bracket has
order `R * log R`. -/
theorem freedman_le_sqrt_mul_log {A E R V : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hR : 1 ≤ R) (hlog : 0 ≤ Real.log R) (hV : V ≤ E * R * Real.log R) :
    A * (Real.sqrt (V * Real.log R) + Real.log R) ≤
      (A * (Real.sqrt E + 1)) * Real.sqrt R * Real.log R := by
  have hs : 1 ≤ Real.sqrt R := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hR
  have hid : Real.sqrt (E * R * Real.log R * Real.log R) =
      Real.sqrt E * Real.sqrt R * Real.log R := by
    rw [show E * R * Real.log R * Real.log R = (E * R) * (Real.log R) ^ 2 by ring,
      Real.sqrt_mul (mul_nonneg hE (by linarith)), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hlog, Real.sqrt_mul hE]
  have hv := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hV hlog)
  rw [hid] at hv
  have hh : Real.log R ≤ Real.sqrt R * Real.log R := by nlinarith
  calc
    _ ≤ A * (Real.sqrt E * Real.sqrt R * Real.log R + Real.log R) := by gcongr
    _ ≤ A * (Real.sqrt E * Real.sqrt R * Real.log R +
        Real.sqrt R * Real.log R) := by gcongr
    _ = _ := by ring

/-- At a sufficiently large scale the bracket estimate has a single logarithmic
factor, uniformly in dimension two and higher. -/
theorem kernel_bracket_le_radius_log {d : ℕ} (Cb : ℝ)
    (hb : ∀ ε : ℝ, 0 ≤ ε →
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
      ∀ (X : ℕ → Site d) (n : ℕ) (y : Site d) (R L : ℝ), 1 ≤ R → 0 ≤ L →
        (∀ z ∈ departureRange X n, euclidNorm (z - y) ≤ R) →
        (∀ z ∈ departureRange X n, (localTime X n z : ℝ) ≤ L) →
        dynkinBracket (driftStepProb d ε ξ) (fun z => latticeKernel d (z - y))
          (fun z => latticeKernel d (z - y)) X n ≤
            Cb * L * (if d = 2 then Real.log (R + 2) else 1))
    (hCb : 0 ≤ Cb) {ε : ℝ} (hε : 0 ≤ ε)
    (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    (X : ℕ → Site d) (n : ℕ) (y : Site d) {b K R : ℝ}
    (hb1 : 1 ≤ b) (hK : 0 ≤ K) (hR : 2 ≤ R) (hbR : b + 2 ≤ R)
    (heR : Real.exp 1 ≤ R)
    (hdist : ∀ z ∈ departureRange X n, euclidNorm (z - y) ≤ b * R)
    (hl : ∀ z, (localTime X n z : ℝ) ≤ K * R) :
    dynkinBracket (driftStepProb d ε ξ) (fun z => latticeKernel d (z - y))
      (fun z => latticeKernel d (z - y)) X n ≤
        (2 * Cb * K) * R * Real.log R := by
  have hR0 : 0 < R := by linarith
  have hlog : 1 ≤ Real.log R := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) heR
  have hscale : 1 ≤ b * R := by nlinarith
  have hfactor : (if d = 2 then Real.log (b * R + 2) else 1) ≤
      2 * Real.log R := by
    split_ifs
    · have harg : b * R + 2 ≤ R ^ 2 := by nlinarith
      have hh := Real.log_le_log (by nlinarith : 0 < b * R + 2) harg
      simpa only [Real.log_pow, Nat.cast_ofNat] using hh
    · linarith
  have hh := hb ε hε ξ hξ X n y (b * R) (K * R) hscale
    (mul_nonneg hK hR0.le) hdist (fun z _ => hl z)
  calc
    _ ≤ Cb * (K * R) * (if d = 2 then Real.log (b * R + 2) else 1) := hh
    _ ≤ Cb * (K * R) * (2 * Real.log R) := by gcongr
    _ = _ := by ring

/-- For a fixed positive constant the bootstrap martingale bound is strictly below
the stopping threshold at sufficiently large radii. -/
theorem eventually_sqrt_mul_log_lt (D : ℝ) (hD : 0 < D) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → D * Real.sqrt R * Real.log R < R := by
  have he := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).bound
    (show 0 < 1 / (D + 1) by positivity)
  obtain ⟨r, hr⟩ := Filter.eventually_atTop.mp he
  refine ⟨max r 1, fun R hR => ?_⟩
  have hR1 : 1 ≤ R := (le_max_right r 1).trans hR
  have hR0 : 0 < R := by linarith
  have hb := hr R ((le_max_left r 1).trans hR)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, ← Real.sqrt_eq_rpow,
    abs_of_nonneg (Real.log_nonneg hR1), abs_of_nonneg (Real.sqrt_nonneg R)] at hb
  have hmul := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg R)
  have hsq := Real.sq_sqrt hR0.le
  have hs := Real.sqrt_pos.mpr hR0
  have hdiv : D * (1 / (D + 1)) < 1 := by
    rw [mul_one_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  calc
    _ ≤ D * (1 / (D + 1)) * R := by nlinarith
    _ < R := by nlinarith

end CERW.LimitShapes.Exit
