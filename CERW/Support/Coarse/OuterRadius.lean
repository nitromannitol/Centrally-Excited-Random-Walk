import CERW.Support.Coarse.Crossing
import CERW.Support.Coarse.CardTail
import CERW.Support.Crossing.LastEntrance
import CERW.Support.Crossing.Contradiction
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Coarse.CrossingArith
import CERW.Support.Occupation.SiteArith

/-!
# The outer radius is of order the mass scale

`eq:coarse-entrance`, `eq:coarse-cellcount`, `eq:coarse-contradiction` and `eq:HvsR`,
deterministically. Suppose `H_n > (B₀ + 1) s` with `s = R_n^{1/d}`. At the first time `τ` the path
reaches radius `(B₀ + 1) s`, put `v = X_τ/|X_τ|` and `b = (B₀ - 1) s`. The last entrance `s'` into
`{v · x > b}` before `τ` starts an interval of departures with projection greater than `b` and
radius less than `(B₀ + 1) s`. Along it the net projected gain is at least `s`. By the coarse tail,
the interval visits at most `C s L` distinct sites. The crossing bound then forces
`s² ≤ C (s^γ L^{2γ} + s L⁴)`, which fails for `s ≥ cN` and large `n`.
-/

namespace CERW.Support.Coarse

open LatticeProb Finset CERW CERW.Support.Crossing CERW.Support.Occupation

variable {d : ℕ}

/-- `eq:coarse-cellcount`: a crossing interval `[s, t)`, with `t ≤ n`, whose sites satisfy
`v · x > (B₀ - 1) σ` and `|x| < (B₀ + 1) σ`, visits at most `C σ L` distinct sites when the
coarse tail `F((B₀ - 2) σ) ≤ C_t σ^{2-d} L` holds and `σ ≥ max 1 √d`. -/
private lemma card_crossing_le (hd : 1 ≤ d) {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω)
    (n s t : ℕ) (v : EuclideanSpace ℝ (Fin d)) {B₀ Ct σ L : ℝ} (hB₀ : 3 ≤ B₀) (hσ : 1 ≤ σ)
    (hσd : Real.sqrt d ≤ σ) (htn : t ≤ n) (hv : ‖v‖ = 1)
    (hsite : ∀ j ∈ Ico s t, (B₀ - 1) * σ < inner ℝ v (toSpace (X j ω)) ∧
      euclidNorm (X j ω) < (B₀ + 1) * σ)
    (htail : tail d (cellSet (fun j => X j ω) n) ((B₀ - 2) * σ) ≤
      Ct * σ ^ (2 - (d : ℝ)) * L) :
    (((Ico s t).image fun j => X j ω).card : ℝ) ≤
      d * unitBallVolume d * (B₀ + 2) ^ ((d : ℝ) - 1) * Ct * σ * L := by
  have hσpos : 0 < σ := lt_of_lt_of_le one_pos hσ
  have hsqrt : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hS : ((Ico s t).image fun j => X j ω) ⊆ departureRange (fun j => X j ω) n := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr
      ⟨j, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp hj).2 htn), rfl⟩
  have hρ : Real.sqrt d / 2 < (B₀ - 1) * σ := by nlinarith
  have hρR : (B₀ - 1) * σ ≤ (B₀ + 1) * σ := by nlinarith
  have hSR : ∀ x ∈ ((Ico s t).image fun j => X j ω),
      (B₀ - 1) * σ < euclidNorm x ∧ euclidNorm x < (B₀ + 1) * σ := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨lt_of_lt_of_le (hsite j hj).1 (inner_toSpace_le_euclidNorm hv _), (hsite j hj).2⟩
  have hcard := card_le_tail hd (fun j => X j ω) n hS hρ hρR hSR
  have hD : MeasurableSet (cellSet (fun j => X j ω) n) := measurableSet_cellSet _ n
  have hDb : Bornology.IsBounded (cellSet (fun j => X j ω) n) :=
    (Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin d)))
      (r := maxRadius (fun j => X j ω) n + Real.sqrt d)).subset (cellSet_subset_ball hd _ n)
  have hmono : tail d (cellSet (fun j => X j ω) n) ((B₀ - 1) * σ - Real.sqrt d / 2) ≤
      tail d (cellSet (fun j => X j ω) n) ((B₀ - 2) * σ) := by
    refine CERW.Support.Geometry.tail_antitoneOn hD hDb ?_ ?_ ?_
    · exact Set.mem_Ioi.mpr (by nlinarith)
    · exact Set.mem_Ioi.mpr (by nlinarith)
    · nlinarith
  have hbase : (B₀ + 1) * σ + Real.sqrt d / 2 ≤ (B₀ + 2) * σ := by nlinarith
  have hexp : 0 ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hpow : ((B₀ + 1) * σ + Real.sqrt d / 2) ^ ((d : ℝ) - 1) ≤
      (B₀ + 2) ^ ((d : ℝ) - 1) * σ ^ ((d : ℝ) - 1) := by
    rw [← Real.mul_rpow (by linarith) hσpos.le]
    exact Real.rpow_le_rpow (by positivity) hbase hexp
  have hA : 0 ≤ (d : ℝ) * unitBallVolume d :=
    mul_nonneg (Nat.cast_nonneg d) (unitBallVolume_pos d).le
  have hT : 0 ≤ tail d (cellSet (fun j => X j ω) n) ((B₀ - 1) * σ - Real.sqrt d / 2) :=
    CERW.Support.Geometry.tail_nonneg _ _
  have hσσ : σ ^ ((d : ℝ) - 1) * σ ^ (2 - (d : ℝ)) = σ := by
    rw [← Real.rpow_add hσpos, show (d : ℝ) - 1 + (2 - d) = 1 by ring, Real.rpow_one]
  calc (((Ico s t).image fun j => X j ω).card : ℝ)
      ≤ d * unitBallVolume d * ((B₀ + 1) * σ + Real.sqrt d / 2) ^ ((d : ℝ) - 1) *
          tail d (cellSet (fun j => X j ω) n) ((B₀ - 1) * σ - Real.sqrt d / 2) := hcard
    _ ≤ d * unitBallVolume d * ((B₀ + 2) ^ ((d : ℝ) - 1) * σ ^ ((d : ℝ) - 1)) *
          (Ct * σ ^ (2 - (d : ℝ)) * L) := by
        gcongr
        exact hmono.trans htail
    _ = d * unitBallVolume d * (B₀ + 2) ^ ((d : ℝ) - 1) * Ct *
          (σ ^ ((d : ℝ) - 1) * σ ^ (2 - (d : ℝ))) * L := by ring
    _ = d * unitBallVolume d * (B₀ + 2) ^ ((d : ℝ) - 1) * Ct * σ * L := by rw [hσσ]

/-- The scale `c n^{1/(d+1)}` eventually exceeds any given bound. -/
private lemma exists_le_mul_rpow {c : ℝ} (hc : 0 < c) (K : ℝ) :
    ∃ n₂ : ℕ, ∀ n : ℕ, n₂ ≤ n → K ≤ c * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1)) := by
  have hpos : 0 < (1 : ℝ) / ((d : ℝ) + 1) := by positivity
  have ht : Filter.Tendsto (fun n : ℕ => c * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1)))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc
      ((tendsto_rpow_atTop hpos).comp tendsto_natCast_atTop_atTop)
  exact Filter.eventually_atTop.1 (ht.eventually_ge_atTop K)

/-- The exponent `γ = 2d/(2d - 1)` of the crossing bound is less than `2` once `d ≥ 2`. -/
private lemma gamma_lt_two (hd : 2 ≤ d) : (2 * d : ℝ) / (2 * d - 1) < 2 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- `eq:coarse-contradiction`, the algebra: from `m ≤ C₁ σ L` the crossing right-hand side is at
most `C (σ^γ L^{2γ} + σ L⁴)`. -/
private lemma crossing_terms_le {γ C₀ C₁ σ L m : ℝ} (hγ : 0 < γ) (hC₀ : 0 < C₀) (hC₁ : 0 ≤ C₁)
    (hσ : 0 < σ) (hL : 0 ≤ L) (hm0 : 0 ≤ m) (hm : m ≤ C₁ * σ * L) :
    C₀ * ((m * L) ^ γ + m * L * L ^ 2) ≤
      C₀ * (C₁ ^ γ + C₁ + 1) * (σ ^ γ * L ^ (2 * γ) + σ * L ^ (4 : ℝ)) := by
  have hmL : m * L ≤ C₁ * σ * L ^ 2 := by
    calc m * L ≤ C₁ * σ * L * L := mul_le_mul_of_nonneg_right hm hL
      _ = C₁ * σ * L ^ 2 := by ring
  have hL2 : (L ^ 2) ^ γ = L ^ (2 * γ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
    norm_num
  have hL4 : L ^ (4 : ℝ) = L ^ 4 := by norm_num
  have h1 : (m * L) ^ γ ≤ C₁ ^ γ * (σ ^ γ * L ^ (2 * γ)) := by
    calc (m * L) ^ γ ≤ (C₁ * σ * L ^ 2) ^ γ :=
          Real.rpow_le_rpow (mul_nonneg hm0 hL) hmL hγ.le
      _ = C₁ ^ γ * (σ ^ γ * L ^ (2 * γ)) := by
          rw [Real.mul_rpow (mul_nonneg hC₁ hσ.le) (by positivity),
            Real.mul_rpow hC₁ hσ.le, hL2, mul_assoc]
  have h2 : m * L * L ^ 2 ≤ C₁ * (σ * L ^ (4 : ℝ)) := by
    rw [hL4]
    calc m * L * L ^ 2 ≤ C₁ * σ * L ^ 2 * L ^ 2 :=
          mul_le_mul_of_nonneg_right hmL (by positivity)
      _ = C₁ * (σ * L ^ 4) := by ring
  have ha : 0 ≤ σ ^ γ * L ^ (2 * γ) :=
    mul_nonneg (Real.rpow_nonneg hσ.le _) (Real.rpow_nonneg hL _)
  have hb : 0 ≤ σ * L ^ (4 : ℝ) := mul_nonneg hσ.le (Real.rpow_nonneg hL _)
  have hCγ : 0 ≤ C₁ ^ γ := Real.rpow_nonneg hC₁ _
  have hsum : C₁ ^ γ * (σ ^ γ * L ^ (2 * γ)) + C₁ * (σ * L ^ (4 : ℝ)) ≤
      (C₁ ^ γ + C₁ + 1) * (σ ^ γ * L ^ (2 * γ) + σ * L ^ (4 : ℝ)) := by
    nlinarith [mul_nonneg hCγ hb, mul_nonneg hC₁ ha]
  calc C₀ * ((m * L) ^ γ + m * L * L ^ 2)
      ≤ C₀ * (C₁ ^ γ * (σ ^ γ * L ^ (2 * γ)) + C₁ * (σ * L ^ (4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC₀.le
    _ ≤ C₀ * ((C₁ ^ γ + C₁ + 1) * (σ ^ γ * L ^ (2 * γ) + σ * L ^ (4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum hC₀.le
    _ = C₀ * (C₁ ^ γ + C₁ + 1) * (σ ^ γ * L ^ (2 * γ) + σ * L ^ (4 : ℝ)) := by ring

/-- The numeric contradiction at the heart of `exists_maxRadius_le`: a cardinality bound
`m ≤ C₁ σ L`, a crossing lower bound `σ² ≤ C₀ ((mL)^γ + mL L²)`, and the
large-`n` bound `C₀ (C₁^γ + C₁ + 1) (σ^γ L^{2γ} + σ L⁴) < σ²` cannot all hold. -/
private lemma crossing_contradiction {γ C₀ C₁ σ L m : ℝ} (hγ : 0 < γ) (hC₀ : 0 < C₀)
    (hC₁ : 0 ≤ C₁) (hσ : 0 < σ) (hL : 0 ≤ L) (hm0 : 0 ≤ m) (hcard : m ≤ C₁ * σ * L)
    (hcross : σ ^ 2 ≤ C₀ * ((m * L) ^ γ + m * L * L ^ 2))
    (hlt : C₀ * (C₁ ^ γ + C₁ + 1) * (σ ^ γ * L ^ (2 * γ) + σ * L ^ (4 : ℝ)) < σ ^ 2) :
    False := by
  have hterms := crossing_terms_le hγ hC₀ hC₁ hσ hL hm0 hcard
  linarith

/-- `eq:HvsR`: on a path from the origin with unit steps, if `eq:vector` and `eq:interval` hold on
`[0, n]`, `s = R_n^{1/d} ≥ cN`, and the coarse tail `F((B₀ - 2) s) ≤ C_t s^{2-d} L` holds, then
`H_n ≤ (B₀ + 1) s` for all large `n`. -/
theorem exists_maxRadius_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {Cv CI Ct B₀ c : ℝ}
    (hCv : 0 ≤ Cv) (hCI : 0 ≤ CI) (hCt : 0 ≤ Ct) (hB₀ : 3 ≤ B₀) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ), n₀ ≤ n → X 0 ω = 0 →
      (∀ j, X (j + 1) ω - X j ω ∈ unitSteps d) →
      (∀ s t : ℕ, s < t → t ≤ n →
        ‖Support.Coarse.compensated ε X t ω - Support.Coarse.compensated ε X s ω‖ ≤
          Cv * Real.sqrt (((t : ℝ) - s) * Real.log (n + 2))) →
      (∀ s t : ℕ, s < t → t ≤ n →
        (intervalMax (fun j => X j ω) s t : ℝ) ≤
          CI * ε * (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) +
            CI * Real.log (n + 2) ^ 2) →
      c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ≤
        ((departureRange (fun j => X j ω) n).card : ℝ) ^ ((1 : ℝ) / d) →
      tail d (cellSet (fun j => X j ω) n)
          ((B₀ - 2) * ((departureRange (fun j => X j ω) n).card : ℝ) ^ ((1 : ℝ) / d)) ≤
        Ct * (((departureRange (fun j => X j ω) n).card : ℝ) ^ ((1 : ℝ) / d)) ^ (2 - (d : ℝ)) *
          Real.log (n + 2) →
      maxRadius (fun j => X j ω) n ≤
        (B₀ + 1) * ((departureRange (fun j => X j ω) n).card : ℝ) ^ ((1 : ℝ) / d) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_crossing_bound (d := d) hd1 (κ := 1 / 2) (by norm_num)
    hε hCv hCI
  set γ : ℝ := (2 * d : ℝ) / (2 * d - 1) with hγdef
  set C₁ : ℝ := d * unitBallVolume d * (B₀ + 2) ^ ((d : ℝ) - 1) * Ct with hC₁def
  have hC₁ : 0 ≤ C₁ := by
    have hB₂ : 0 ≤ (B₀ + 2) ^ ((d : ℝ) - 1) := Real.rpow_nonneg (by linarith) _
    have hω : 0 ≤ (d : ℝ) * unitBallVolume d :=
      mul_nonneg (Nat.cast_nonneg d) (unitBallVolume_pos d).le
    exact mul_nonneg (mul_nonneg hω hB₂) hCt
  have hCγ : 0 ≤ C₁ ^ γ := Real.rpow_nonneg hC₁ _
  have hCf : 0 < C₀ * (C₁ ^ γ + C₁ + 1) := mul_pos hC₀pos (by linarith)
  obtain ⟨n₁, hn₁⟩ := CERW.Support.Crossing.eventually_lt_sq (d := d) (gamma_lt_two hd) hCf hc
  obtain ⟨n₂, hn₂⟩ := exists_le_mul_rpow (d := d) hc ((d : ℝ) + 1)
  refine ⟨max n₁ n₂, ?_⟩
  intro Ω X ω n hn h0 hstep hvec hint hscale htail
  by_contra hcon
  rw [not_le] at hcon
  set σ : ℝ := ((departureRange (fun j => X j ω) n).card : ℝ) ^ ((1 : ℝ) / d) with hσdef
  set L : ℝ := Real.log (n + 2) with hLdef
  have hL : 0 ≤ L := Real.log_nonneg (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hσge : (d : ℝ) + 1 ≤ σ := (hn₂ n (le_trans (le_max_right _ _) hn)).trans hscale
  have hσ1 : 1 ≤ σ := by linarith
  have hσpos : 0 < σ := by linarith
  have hσd : Real.sqrt d ≤ σ := by
    refine le_trans ?_ hσge
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  have hb : 0 ≤ (B₀ - 1) * σ := by nlinarith
  obtain ⟨s', t, hst, htn, v, hv, hsite, hgain⟩ := exists_crossing_interval X ω n h0 hstep
    (b := (B₀ - 1) * σ) (r := (B₀ + 1) * σ) hb (by nlinarith) hcon
  have hbpos : 0 < (B₀ - 1) * σ := by nlinarith
  have hrpos : 0 < (B₀ + 1) * σ := by nlinarith
  have hκ : (1 / 2 : ℝ) ≤ (B₀ - 1) * σ / ((B₀ + 1) * σ) := by
    rw [le_div_iff₀ hrpos]
    nlinarith only [hB₀, hσpos.le]
  have hcross := hC₀ X ω s' t v ((B₀ - 1) * σ) ((B₀ + 1) * σ) σ L (L ^ 2) hst hv hbpos hκ
    hσpos.le hL (sq_nonneg L) hsite (by nlinarith only [hgain, hσ1]) (hvec s' t hst htn)
    (hint s' t hst htn)
  have hcard := card_crossing_le hd1 X ω n s' t v hB₀ hσ1 hσd htn hv hsite htail
  have hlt := hn₁ n (le_trans (le_max_left _ _) hn) σ hscale
  exact crossing_contradiction (gamma_pos hd1) hC₀pos hC₁ hσpos hL (Nat.cast_nonneg _)
    hcard hcross hlt

end CERW.Support.Coarse
