import CERW.Support.Coarse.OuterRadius
import CERW.Support.Crossing.OuterContradiction

/-!
# The outer fluctuation bound

`eq:outer-contradiction`, deterministically. Let `W = N Q^{1/d}` and `h = K₁ W L`.
Suppose the tail end `F(b + K₀ W L) ≤ C_t N^{2-d} L` holds with `K₀ ≤ K₁`, and
`c₁ N ≤ b ≤ c₂ N`. If the path reached radius `r = b + 3h` by time `n`, then at the
first time `τ` it does so, with `v = X_τ/|X_τ|` and `β = b + 2h`, the last entrance
into `{v · x > β}` starts a crossing interval. It has gain at least `h - 1` and radii
below `r`. Its distinct sites number at most `C₁ N L` by the tail end. The crossing
bound then contradicts `eq:outer-contradiction`. Hence `H_n ≤ b + 3 K₁ W L`.
-/

namespace CERW.Support.Coarse

open LatticeProb Finset CERW CERW.Support.Crossing CERW.Support.Occupation
open Filter Topology

variable {d : ℕ}

/-- The embedding of lattice sites is additive: `toSpace (x - y) = toSpace x - toSpace y`. -/
private lemma toSpace_sub_eq (x y : Site d) : toSpace (x - y) = toSpace x - toSpace y := by
  ext i
  simp [toSpace, Pi.sub_apply, Int.cast_sub]

/-- The origin of the lattice embeds as the origin of Euclidean space. -/
private lemma toSpace_zero_eq : toSpace (0 : Site d) = 0 := by
  ext i
  simp [toSpace]

/-- The direction of a nonzero vector has norm one. -/
private lemma norm_unitDir_eq_one {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    ‖unitDir x‖ = 1 := by
  rw [unitDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- The inner product of the direction of `x` with `x` is the norm of `x`. -/
private lemma inner_unitDir_self_eq (x : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (unitDir x) x = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [unitDir, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    field_simp

/-- If the path exceeds radius `r > b + 1` by time `n`, then at the first time `t` it reaches
radius `r` there is a crossing interval `[s, t)` in the direction `v = X_t / |X_t|`: all sites of
the interval have `v · x > b` and `|x| < r`, and the projected gain over it is at least
`r - (b + 1)`. -/
private lemma exists_crossing_interval {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ)
    (h0 : X 0 ω = 0) (hstep : ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d) {b r : ℝ}
    (hb : 0 ≤ b) (hbr : b + 1 < r) (hH : r < maxRadius (fun j => X j ω) n) :
    ∃ s t : ℕ, s < t ∧ t ≤ n ∧ ∃ v : EuclideanSpace ℝ (Fin d), ‖v‖ = 1 ∧
      (∀ j ∈ Ico s t, b < inner ℝ v (toSpace (X j ω)) ∧ euclidNorm (X j ω) < r) ∧
      r - (b + 1) ≤ inner ℝ v (toSpace (X t ω) - toSpace (X s ω)) := by
  classical
  have hzero : euclidNorm (X 0 ω) = 0 := by
    rw [← norm_toSpace, h0, toSpace_zero_eq, norm_zero]
  have hexn : ∃ j ∈ Finset.range (n + 1), r < euclidNorm (X j ω) :=
    (Finset.lt_sup'_iff _).mp hH
  have hex : ∃ j, r ≤ euclidNorm (X j ω) := by
    obtain ⟨j, -, hj⟩ := hexn
    exact ⟨j, hj.le⟩
  obtain ⟨τ, hτspec, hτmin⟩ :
      ∃ τ, r ≤ euclidNorm (X τ ω) ∧ ∀ j < τ, euclidNorm (X j ω) < r := by
    exact ⟨Nat.find hex, Nat.find_spec hex, fun j hj => not_le.mp (Nat.find_min hex hj)⟩
  have hτn : τ ≤ n := by
    obtain ⟨j, hj, hjr⟩ := hexn
    by_contra hlt
    rw [not_le] at hlt
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact absurd hjr (not_lt.mpr (hτmin j (lt_of_le_of_lt hjn hlt)).le)
  have hτpos : 0 < τ := by
    rcases Nat.eq_zero_or_pos τ with hτ | hτ
    · rw [hτ, hzero] at hτspec
      linarith
    · exact hτ
  have hxτ : toSpace (X τ ω) ≠ 0 := by
    intro hx
    rw [← norm_toSpace, hx, norm_zero] at hτspec
    linarith
  set v : EuclideanSpace ℝ (Fin d) := unitDir (toSpace (X τ ω)) with hvdef
  have hv : ‖v‖ = 1 := norm_unitDir_eq_one hxτ
  have hfτ : inner ℝ v (toSpace (X τ ω)) = euclidNorm (X τ ω) := by
    rw [hvdef, inner_unitDir_self_eq, norm_toSpace]
  obtain ⟨s, hs0, hsτ, hfs, hfin⟩ := exists_last_entrance
    (f := fun j => inner ℝ v (toSpace (X j ω))) (b := b) (τ := τ)
    (by rw [h0, toSpace_zero_eq, inner_zero_right]; exact hb)
    (fun j => by
      have hsub : inner ℝ v (toSpace (X (j + 1) ω)) - inner ℝ v (toSpace (X j ω)) ≤ 1 := by
        rw [← inner_sub_right, ← toSpace_sub_eq]
        exact inner_toSpace_le_one hv (hstep j)
      linarith)
    hτpos
  have hslt : s < τ := by
    refine lt_of_le_of_ne hsτ ?_
    rintro rfl
    rw [hfτ] at hfs
    linarith
  refine ⟨s, τ, hslt, hτn, v, hv, ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_Ico] at hj
    exact ⟨hfin j hj.1 hj.2, hτmin j hj.2⟩
  · rw [inner_sub_right, hfτ]
    linarith

/-- The projection on a unit vector is at most the Euclidean norm of a site. -/
private lemma inner_toSpace_le_euclidNorm {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    (x : Site d) : inner ℝ v (toSpace x) ≤ euclidNorm x := by
  have h := real_inner_le_norm v (toSpace x)
  rwa [hv, one_mul, norm_toSpace] at h

/-- The exponent `γ = 2d/(2d - 1)` of the crossing bound is positive once `d ≥ 1`. -/
private lemma gamma_pos (hd : 1 ≤ d) : 0 < (2 * d : ℝ) / (2 * d - 1) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_pos (by linarith) (by linarith)

/-- The scale `N = n^{1/(d+1)}`. -/
private noncomputable abbrev outerN (d : ℕ) (n : ℕ) : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))

/-- The logarithm `L = log (n + 2)`. -/
private noncomputable abbrev outerL (n : ℕ) : ℝ := Real.log (n + 2)

/-- The rate `Q` of `eq:rates`. -/
private noncomputable abbrev outerQ (d : ℕ) (n : ℕ) : ℝ :=
  if d = 2 then (outerL n / outerN d n) ^ ((1 : ℝ) / 2)
  else (outerL n / outerN d n) ^ ((d : ℝ) / (2 * d - 1))

/-- The outer excess `Q^{1/d}`. -/
private noncomputable abbrev outerRate (d : ℕ) (n : ℕ) : ℝ := (outerQ d n) ^ ((1 : ℝ) / d)

/-- The outer height `W L = N Q^{1/d} L`. -/
private noncomputable abbrev outerWL (d : ℕ) (n : ℕ) : ℝ :=
  outerN d n * outerRate d n * outerL n

/-- The scale `N` tends to infinity. -/
private lemma tendsto_outerN_atTop (d : ℕ) : Tendsto (outerN d) atTop atTop := by
  have hpos : (0 : ℝ) < (1 : ℝ) / ((d : ℝ) + 1) := by positivity
  have h := (tendsto_rpow_atTop hpos).comp tendsto_natCast_atTop_atTop
  refine Tendsto.congr' ?_ h
  filter_upwards with n
  rfl

/-- The outer excess times the log tends to zero: `Q^{1/d} L → 0`. -/
private lemma tendsto_outerRate_mul_L_zero (hd : 2 ≤ d) :
    Tendsto (fun n : ℕ => outerRate d n * outerL n) atTop (𝓝 0) := by
  simpa only [outerRate, outerQ, outerL, outerN] using
    CERW.Support.Main.tendsto_rate_rpow_mul_log_zero (d := d) hd

/-- The outer height equals its `d = 2` closed form. -/
private lemma outerWL_eq_height_two (n : ℕ) :
    outerWL 2 n =
      (n : ℝ) ^ ((1 : ℝ) / 3) *
        ((Real.log ((n : ℝ) + 2) / (n : ℝ) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 2)) ^
          ((1 : ℝ) / 2) *
        Real.log ((n : ℝ) + 2) := by
  dsimp only [outerWL, outerN, outerL, outerQ, outerRate]
  norm_num

/-- The outer height equals its `d ≥ 3` closed form. -/
private lemma outerWL_eq_height_three {d : ℕ} (h2 : ¬ d = 2) (n : ℕ) :
    outerWL d n =
      (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1)) *
        ((Real.log ((n : ℝ) + 2) / (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1))) ^
          ((d : ℝ) / (2 * (d : ℝ) - 1))) ^ ((1 : ℝ) / (d : ℝ)) *
        Real.log ((n : ℝ) + 2) := by
  dsimp only [outerWL, outerN, outerL, outerQ, outerRate]
  rw [if_neg h2]

/-- The outer height `W L = N Q^{1/d} L` tends to infinity. -/
private lemma tendsto_outerWL_atTop (hd : 2 ≤ d) : Tendsto (outerWL d) atTop atTop := by
  by_cases h2 : d = 2
  · subst d
    refine Tendsto.congr' ?_ tendsto_height_two
    filter_upwards with n
    exact (outerWL_eq_height_two n).symm
  · have hd3 : 3 ≤ d := by omega
    refine Tendsto.congr' ?_ (tendsto_height_three d hd3)
    filter_upwards with n
    exact (outerWL_eq_height_three h2 n).symm

/-- For positive `A, c` the outer height is eventually at least `√d/2 + 1` and stays below the
scale `c N`: `3 A W L + √d/2 ≤ c N` for all large `n`. -/
private lemma eventually_outer_bounds (hd : 2 ≤ d) {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt d / 2 + 1 ≤ A * outerWL d n ∧
      3 * A * outerWL d n + Real.sqrt d / 2 ≤ c * outerN d n := by
  have hH : Tendsto (fun n : ℕ => A * outerWL d n) atTop atTop :=
    (tendsto_outerWL_atTop hd).const_mul_atTop hA
  have h1 : ∀ᶠ n : ℕ in atTop, Real.sqrt d / 2 + 1 ≤ A * outerWL d n :=
    hH.eventually_ge_atTop _
  have hr : ∀ᶠ n : ℕ in atTop, outerRate d n * outerL n < c / (6 * A) :=
    (tendsto_outerRate_mul_L_zero hd).eventually_lt_const (by positivity)
  have hNbig : ∀ᶠ n : ℕ in atTop, Real.sqrt d / c ≤ outerN d n :=
    (tendsto_outerN_atTop d).eventually_ge_atTop _
  filter_upwards [h1, hr, hNbig] with n h1n hrn hNn
  refine ⟨h1n, ?_⟩
  have hNnonneg : 0 ≤ outerN d n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hrate : outerRate d n * outerL n ≤ c / (6 * A) := le_of_lt hrn
  have hstep1 : 3 * A * outerWL d n ≤ c / 2 * outerN d n := by
    have hWL : outerWL d n = outerN d n * (outerRate d n * outerL n) := by
      dsimp only [outerWL]; ring
    rw [hWL]
    have hcoef : 0 ≤ 3 * A := by positivity
    have hinner : outerN d n * (outerRate d n * outerL n) ≤ outerN d n * (c / (6 * A)) :=
      mul_le_mul_of_nonneg_left hrate hNnonneg
    have hmul : 3 * A * (outerN d n * (outerRate d n * outerL n)) ≤
        3 * A * (outerN d n * (c / (6 * A))) :=
      mul_le_mul_of_nonneg_left hinner hcoef
    have heq : 3 * A * (outerN d n * (c / (6 * A))) = c / 2 * outerN d n := by
      field_simp
      ring
    rwa [heq] at hmul
  have hsecond : Real.sqrt d / 2 ≤ c / 2 * outerN d n := by
    have hc2 : 0 ≤ c / 2 := by positivity
    have h := mul_le_mul_of_nonneg_left hNn hc2
    have heq : c / 2 * (Real.sqrt d / c) = Real.sqrt d / 2 := by field_simp
    rwa [heq] at h
  linarith [hstep1, hsecond]

/-- `eq:outer-contradiction`: under `eq:vector`, `eq:interval`, the inradius scale
`c₁ N ≤ b ≤ c₂ N` and the tail end, `H_n ≤ b + 3 K₁ W L` for all large `n`. -/
theorem exists_maxRadius_le_outer (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {Cv CI Ct K₀ K₁ c₁ c₂ : ℝ}
    (hCv : 0 ≤ Cv) (hCI : 0 ≤ CI) (hCt : 0 ≤ Ct) (hK₀ : 0 ≤ K₀) (hK : K₀ ≤ K₁) (hK₁ : 0 < K₁)
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ ≤ c₂) :
    ∃ n₀ : ℕ, ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ) (b : ℝ), n₀ ≤ n →
      let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
      let L : ℝ := Real.log (n + 2)
      let Q : ℝ := if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
      let W : ℝ := N * Q ^ ((1 : ℝ) / d)
      let lam : ℝ := if d = 2 then L ^ 2 else L
      X 0 ω = 0 → (∀ j, X (j + 1) ω - X j ω ∈ unitSteps d) →
      (∀ s t : ℕ, s < t → t ≤ n →
        ‖Support.Coarse.compensated ε X t ω - Support.Coarse.compensated ε X s ω‖ ≤
          Cv * Real.sqrt (((t : ℝ) - s) * L)) →
      (∀ s t : ℕ, s < t → t ≤ n →
        (intervalMax (fun j => X j ω) s t : ℝ) ≤
          CI * ε * (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) + CI * lam) →
      c₁ * N ≤ b → b ≤ c₂ * N →
      tail d (cellSet (fun j => X j ω) n) (b + K₀ * W * L) ≤ Ct * N ^ (2 - (d : ℝ)) * L →
        maxRadius (fun j => X j ω) n ≤ b + 3 * K₁ * W * L := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_crossing_bound (d := d) hd1 (κ := 1 / 2)
    (by norm_num) hε hCv hCI
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁₂
  set C₁ : ℝ := d * unitBallVolume d * (2 * c₂ + 1) ^ ((d : ℝ) - 1) * Ct + 1 with hC₁def
  have hC₁pos : 0 < C₁ := by
    rw [hC₁def]
    have hvol : 0 < (d : ℝ) * unitBallVolume d :=
      mul_pos (by exact_mod_cast (by omega : 0 < d)) (unitBallVolume_pos d)
    have hbase : 0 ≤ (2 * c₂ + 1) ^ ((d : ℝ) - 1) :=
      Real.rpow_nonneg (by linarith only [hc₂]) _
    have hprod : 0 ≤ d * unitBallVolume d * (2 * c₂ + 1) ^ ((d : ℝ) - 1) * Ct :=
      mul_nonneg (mul_nonneg hvol.le hbase) hCt
    linarith only [hprod]
  obtain ⟨n_a, hn_a⟩ := Filter.eventually_atTop.1
    (CERW.Support.Crossing.eventually_outer_lt (d := d) hd hK₁ hC₀pos hC₁pos)
  obtain ⟨n_b, hn_b⟩ := Filter.eventually_atTop.1
    (eventually_outer_bounds (d := d) hd hK₁ hc₂)
  refine ⟨max (max n_a n_b) 1, ?_⟩
  intro Ω X ω n b hn N L Q W lam h0 hstep hvec hint hb1 hb2 htail
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN : N = outerN d n := rfl
  have hLdef : L = outerL n := rfl
  have hL : 0 ≤ L := by
    rw [hLdef, outerL]
    exact Real.log_nonneg (by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith)
  have hNpos : 0 < N := by
    rw [hN, outerN]
    exact Real.rpow_pos_of_pos hnpos _
  have hlamdef : lam = (if d = 2 then L ^ 2 else L) := rfl
  have hWL : outerWL d n = W * L := rfl
  have hb_ge : Real.sqrt d / 2 + 1 ≤ K₁ * W * L := by
    have h := (hn_b n (le_trans (le_max_right n_a n_b)
      (le_trans (le_max_left (max n_a n_b) 1) hn))).1
    rw [hWL] at h
    simpa only [mul_assoc] using h
  have hb_le : 3 * K₁ * W * L + Real.sqrt d / 2 ≤ c₂ * N := by
    have h := (hn_b n (le_trans (le_max_right n_a n_b)
      (le_trans (le_max_left (max n_a n_b) 1) hn))).2
    rw [hWL, ← hN] at h
    simpa only [mul_assoc] using h
  have hcontr_a : C₀ * ((C₁ * N * L) ^ ((2 * d : ℝ) / (2 * d - 1)) *
      L ^ ((2 * d : ℝ) / (2 * d - 1)) + C₁ * N * L * lam * L) <
      (K₁ * W * L - 1) ^ 2 :=
    hn_a n (le_trans (le_max_left n_a n_b) (le_trans (le_max_left (max n_a n_b) 1) hn))
  clear_value N L Q W lam
  have hb_pos : 0 < b := by
    have hc₁N : 0 < c₁ * N := mul_pos hc₁ hNpos
    linarith [hb1, hc₁N]
  have hb_nonneg : 0 ≤ b := hb_pos.le
  have hsqrtpos : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
  have hsqrt_nonneg : 0 ≤ Real.sqrt d := hsqrtpos.le
  have hKWpos : 0 < K₁ * W * L := by linarith only [hb_ge, hsqrt_nonneg]
  have hKWnonneg : 0 ≤ K₁ * W * L := hKWpos.le
  have hWLpos : 0 < W * L := by
    have hprod : 0 < K₁ * (W * L) := by
      have h := hKWpos
      rwa [mul_assoc] at h
    exact pos_of_mul_pos_right hprod hK₁.le
  have hWLnonneg : 0 ≤ W * L := hWLpos.le
  have hlam : 0 ≤ lam := by
    rw [hlamdef]
    by_cases h2 : d = 2
    · rw [if_pos h2]; positivity
    · rw [if_neg h2]; exact hL
  by_contra hcon
  rw [not_le] at hcon
  have hβ : 0 ≤ b + 2 * K₁ * W * L := by linarith only [hb_nonneg, hKWnonneg]
  have hβsucc : b + 2 * K₁ * W * L + 1 < b + 3 * K₁ * W * L := by
    linarith only [hb_ge, hsqrtpos]
  obtain ⟨s', t, hst, htn, v, hv, hsite, hgain⟩ := exists_crossing_interval X ω n h0 hstep
    (b := b + 2 * K₁ * W * L) (r := b + 3 * K₁ * W * L) hβ hβsucc hcon
  have hβpos : 0 < b + 2 * K₁ * W * L := by linarith only [hb_nonneg, hKWpos]
  have hrpos : 0 < b + 3 * K₁ * W * L := by linarith only [hb_nonneg, hKWpos]
  have hκ : (1 / 2 : ℝ) ≤ (b + 2 * K₁ * W * L) / (b + 3 * K₁ * W * L) := by
    rw [le_div_iff₀ hrpos]
    linarith only [hb_nonneg, hKWnonneg]
  have hgain' : K₁ * W * L - 1 ≤ inner ℝ v (toSpace (X t ω) - toSpace (X s' ω)) :=
    by linarith only [hgain]
  set m : ℕ := ((Ico s' t).image fun j => X j ω).card with hm
  have hcross := hC₀ X ω s' t v (b + 2 * K₁ * W * L) (b + 3 * K₁ * W * L)
      (K₁ * W * L - 1) L lam hst hv hβpos hκ (by linarith only [hb_ge, hsqrt_nonneg]) hL hlam
      hsite hgain' (hvec s' t hst htn) (hint s' t hst htn)
  rw [← hm] at hcross
  clear hC₀ hvec hint h0 hstep hgain hgain' hβ hβsucc hcon hβpos hrpos hκ hN hLdef hlamdef hWL
  have hDmeas : MeasurableSet (cellSet (fun j => X j ω) n) := measurableSet_cellSet _ n
  have hDbdd : Bornology.IsBounded (cellSet (fun j => X j ω) n) :=
    (Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin d)))
      (r := maxRadius (fun j => X j ω) n + Real.sqrt d)).subset
      (cellSet_subset_ball hd1 (fun j => X j ω) n)
  have hβK : b + K₀ * W * L ≤ (b + 2 * K₁ * W * L) - Real.sqrt d / 2 := by
    have hK0WL : K₀ * (W * L) ≤ K₁ * (W * L) := mul_le_mul_of_nonneg_right hK hWLnonneg
    have h1 : K₀ * W * L ≤ K₁ * W * L := by
      simpa only [mul_assoc] using hK0WL
    linarith only [h1, hb_ge, hsqrt_nonneg]
  have hβKpos : 0 < (b + 2 * K₁ * W * L) - Real.sqrt d / 2 := by
    have h : Real.sqrt d / 2 < b + 2 * K₁ * W * L :=
      by linarith only [hb_ge, hb_nonneg, hsqrt_nonneg]
    linarith only [h]
  have hbKpos : 0 < b + K₀ * W * L := by
    have hK0 : 0 ≤ K₀ * (W * L) := mul_nonneg hK₀ hWLnonneg
    have hK0' : 0 ≤ K₀ * W * L := by
      simpa only [mul_assoc] using hK0
    linarith only [hb_pos, hK0']
  have htail_mono : tail d (cellSet (fun j => X j ω) n)
        ((b + 2 * K₁ * W * L) - Real.sqrt d / 2) ≤
      tail d (cellSet (fun j => X j ω) n) (b + K₀ * W * L) :=
    CERW.Support.Geometry.tail_antitoneOn hDmeas hDbdd
      (Set.mem_Ioi.mpr hbKpos) (Set.mem_Ioi.mpr hβKpos) hβK
  have htail' : tail d (cellSet (fun j => X j ω) n)
        ((b + 2 * K₁ * W * L) - Real.sqrt d / 2) ≤ Ct * N ^ (2 - (d : ℝ)) * L :=
    htail_mono.trans htail
  have hS : ((Ico s' t).image fun j => X j ω) ⊆ departureRange (fun j => X j ω) n := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr
      ⟨j, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp hj).2 htn), rfl⟩
  have hρ : Real.sqrt d / 2 < b + 2 * K₁ * W * L := by
    linarith only [hb_ge, hb_nonneg, hsqrt_nonneg]
  have hρR : b + 2 * K₁ * W * L ≤ b + 3 * K₁ * W * L := by
    linarith only [hKWnonneg]
  have hSR : ∀ x ∈ ((Ico s' t).image fun j => X j ω),
      b + 2 * K₁ * W * L < euclidNorm x ∧ euclidNorm x < b + 3 * K₁ * W * L := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨lt_of_lt_of_le (hsite j hj).1 (inner_toSpace_le_euclidNorm hv _), (hsite j hj).2⟩
  have hcard := card_le_tail hd1 (fun j => X j ω) n hS hρ hρR hSR
  rw [← hm] at hcard
  clear hDmeas hDbdd htail_mono hS hρ hρR hSR hβK hβKpos hbKpos v hv hsite hst htn hm
  have hpow : (b + 3 * K₁ * W * L + Real.sqrt d / 2) ^ ((d : ℝ) - 1) ≤
      (2 * c₂ + 1) ^ ((d : ℝ) - 1) * N ^ ((d : ℝ) - 1) := by
    have hbase_nonneg : 0 ≤ b + 3 * K₁ * W * L + Real.sqrt d / 2 := by
      linarith only [hb_nonneg, hKWnonneg, hsqrt_nonneg]
    have hrN : b + 3 * K₁ * W * L + Real.sqrt d / 2 ≤ (2 * c₂ + 1) * N := by
      have h2 : b + 3 * K₁ * W * L + Real.sqrt d / 2 ≤ 2 * (c₂ * N) := by
        linarith only [hb2, hb_le]
      have h3 : 2 * (c₂ * N) ≤ (2 * c₂ + 1) * N := by
        have hdiff : (2 * c₂ + 1) * N - 2 * (c₂ * N) = N := by ring
        linarith only [hNpos, hdiff]
      exact h2.trans h3
    have hdexp : 0 ≤ (d : ℝ) - 1 := by
      have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
      linarith only [hdR]
    have h := Real.rpow_le_rpow hbase_nonneg hrN hdexp
    have hpos1 : 0 ≤ 2 * c₂ + 1 := by linarith only [hc₂]
    have hmul : ((2 * c₂ + 1) * N) ^ ((d : ℝ) - 1) =
        (2 * c₂ + 1) ^ ((d : ℝ) - 1) * N ^ ((d : ℝ) - 1) :=
      Real.mul_rpow hpos1 hNpos.le
    rw [hmul] at h
    exact h
  have hNN : N ^ ((d : ℝ) - 1) * N ^ (2 - (d : ℝ)) = N := by
    rw [← Real.rpow_add hNpos, show (d : ℝ) - 1 + (2 - (d : ℝ)) = 1 by ring, Real.rpow_one]
  have hm_bound : (m : ℝ) ≤ C₁ * N * L := by
    have hAω : 0 ≤ d * unitBallVolume d :=
      mul_nonneg (Nat.cast_nonneg d) (unitBallVolume_pos d).le
    have hP2nonneg : 0 ≤ (2 * c₂ + 1) ^ ((d : ℝ) - 1) * N ^ ((d : ℝ) - 1) :=
      mul_nonneg (Real.rpow_nonneg (by linarith only [hc₂]) _) (Real.rpow_nonneg hNpos.le _)
    have hT1nonneg : 0 ≤ tail d (cellSet (fun j => X j ω) n)
        ((b + 2 * K₁ * W * L) - Real.sqrt d / 2) :=
      CERW.Support.Geometry.tail_nonneg _ _
    calc (m : ℝ)
        ≤ d * unitBallVolume d * (b + 3 * K₁ * W * L + Real.sqrt d / 2) ^ ((d : ℝ) - 1) *
            tail d (cellSet (fun j => X j ω) n)
              ((b + 2 * K₁ * W * L) - Real.sqrt d / 2) := hcard
      _ ≤ d * unitBallVolume d * ((2 * c₂ + 1) ^ ((d : ℝ) - 1) * N ^ ((d : ℝ) - 1)) *
            (Ct * N ^ (2 - (d : ℝ)) * L) := by
          have hP := mul_le_mul hpow htail' hT1nonneg hP2nonneg
          calc d * unitBallVolume d * (b + 3 * K₁ * W * L + Real.sqrt d / 2) ^ ((d : ℝ) - 1) *
                tail d (cellSet (fun j => X j ω) n) ((b + 2 * K₁ * W * L) - Real.sqrt d / 2)
              = (d * unitBallVolume d) *
                  ((b + 3 * K₁ * W * L + Real.sqrt d / 2) ^ ((d : ℝ) - 1) *
                    tail d (cellSet (fun j => X j ω) n)
                      ((b + 2 * K₁ * W * L) - Real.sqrt d / 2)) := by ring
            _ ≤ (d * unitBallVolume d) *
                  (((2 * c₂ + 1) ^ ((d : ℝ) - 1) * N ^ ((d : ℝ) - 1)) *
                    (Ct * N ^ (2 - (d : ℝ)) * L)) := mul_le_mul_of_nonneg_left hP hAω
            _ = d * unitBallVolume d * ((2 * c₂ + 1) ^ ((d : ℝ) - 1) * N ^ ((d : ℝ) - 1)) *
                  (Ct * N ^ (2 - (d : ℝ)) * L) := by ring
      _ = d * unitBallVolume d * (2 * c₂ + 1) ^ ((d : ℝ) - 1) * Ct *
            (N ^ ((d : ℝ) - 1) * N ^ (2 - (d : ℝ))) * L := by ring
      _ = d * unitBallVolume d * (2 * c₂ + 1) ^ ((d : ℝ) - 1) * Ct * N * L := by rw [hNN]
      _ ≤ C₁ * N * L := by
          have hcoef : d * unitBallVolume d * (2 * c₂ + 1) ^ ((d : ℝ) - 1) * Ct ≤ C₁ := by
            rw [hC₁def]; linarith
          have hNL : 0 ≤ N * L := mul_nonneg hNpos.le hL
          calc d * unitBallVolume d * (2 * c₂ + 1) ^ ((d : ℝ) - 1) * Ct * N * L
              = (d * unitBallVolume d * (2 * c₂ + 1) ^ ((d : ℝ) - 1) * Ct) * (N * L) := by
                ring
            _ ≤ C₁ * (N * L) := mul_le_mul_of_nonneg_right hcoef hNL
            _ = C₁ * N * L := by ring
  have hγpos : 0 < (2 * d : ℝ) / (2 * d - 1) := gamma_pos hd1
  have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hterm1 : ((m : ℝ) * L) ^ ((2 * d : ℝ) / (2 * d - 1)) ≤
      (C₁ * N * L) ^ ((2 * d : ℝ) / (2 * d - 1)) * L ^ ((2 * d : ℝ) / (2 * d - 1)) := by
    have hbase : 0 ≤ (m : ℝ) * L := mul_nonneg hm_nonneg hL
    have hmL : (m : ℝ) * L ≤ (C₁ * N * L) * L :=
      mul_le_mul_of_nonneg_right hm_bound hL
    have h := Real.rpow_le_rpow hbase hmL hγpos.le
    rwa [Real.mul_rpow (mul_nonneg (mul_nonneg hC₁pos.le hNpos.le) hL) hL] at h
  have hterm2 : (m : ℝ) * L * lam ≤ C₁ * N * L * lam * L := by
    have hmL : (m : ℝ) * L ≤ (C₁ * N * L) * L :=
      mul_le_mul_of_nonneg_right hm_bound hL
    calc (m : ℝ) * L * lam ≤ ((C₁ * N * L) * L) * lam :=
          mul_le_mul_of_nonneg_right hmL hlam
      _ = C₁ * N * L * lam * L := by ring
  have hcomb : C₀ * (((m : ℝ) * L) ^ ((2 * d : ℝ) / (2 * d - 1)) + (m : ℝ) * L * lam) ≤
      C₀ * ((C₁ * N * L) ^ ((2 * d : ℝ) / (2 * d - 1)) *
        L ^ ((2 * d : ℝ) / (2 * d - 1)) + C₁ * N * L * lam * L) :=
    mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) hC₀pos.le
  have hle : (K₁ * W * L - 1) ^ 2 ≤ C₀ * ((C₁ * N * L) ^ ((2 * d : ℝ) / (2 * d - 1)) *
      L ^ ((2 * d : ℝ) / (2 * d - 1)) + C₁ * N * L * lam * L) := le_trans hcross hcomb
  linarith only [hle, hcontr_a]

end CERW.Support.Coarse
