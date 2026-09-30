import CERW.Support.Coarse.TailEnd
import CERW.Support.Coarse.OuterBound
import CERW.Support.Contact.EnvelopeShell
import CERW.Support.Geometry.TailBounds

/-!
# The outer bound from the envelope

Deterministically, for all large `n`. Suppose `c₁ N ≤ b ≤ c₂ N`, `M_n ≤ C₁ N`,
`m = |D_n \ B(0, b)| ≤ C₂ N^d Q` and `ℓ_n ≤ C₂ (b - |·|)_+ + C₂ W`, with `W = N Q^{1/d}`.
Suppose also the vector, interval and radial clauses of the event.
1. `tail_le` gives `F(b) ≤ m / (d ω_d b^{d-1}) ≤ C N Q`.
2. `shellMax_le_of_envelope` gives `M_sh(r) ≤ C₂ W` for `r ≥ b + 3` (`eq:shellW`).
3. `exists_tailend` gives `F(b + K₀ W L) ≤ C_t N^{2-d} L`.
4. `exists_maxRadius_le_outer`, with `K₁ = K₀ + 1`, gives `H_n ≤ b + 3 K₁ W L`.
-/

namespace CERW.Support.Coarse

open MeasureTheory LatticeProb CERW

variable {d : ℕ}

/-- If a bounded measurable set `D` has excess volume `|D \ B(0, b)| ≤ C₂ N^d Q` beyond the
inradius `b ≥ c₁ N`, then its weighted exterior volume at `b` satisfies
`F(b) ≤ C₂ N Q / (d ω_d c₁^{d-1})`. -/
private lemma tail_le_of_excess (hd : 1 ≤ d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDb : Bornology.IsBounded D) {C₂ c₁ b N Q : ℝ}
    (hC₂ : 0 ≤ C₂)
    (hc₁ : 0 < c₁) (hN : 0 < N) (hb : c₁ * N ≤ b) (hQ : 0 ≤ Q)
    (hvol : (volume (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal
      ≤ C₂ * N ^ d * Q) :
    tail d D b ≤ C₂ / (d * unitBallVolume d * c₁ ^ ((d : ℝ) - 1)) * N * Q := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) * unitBallVolume d :=
    mul_pos (by exact_mod_cast (by omega : 0 < d)) (unitBallVolume_pos d)
  have hbpos : 0 < b := lt_of_lt_of_le (mul_pos hc₁ hN) hb
  have hcNpos : 0 < c₁ * N := mul_pos hc₁ hN
  have hD' : MeasurableSet (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) :=
    hD.diff Metric.isOpen_ball.measurableSet
  have hDb' : Bornology.IsBounded (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) :=
    hDb.subset Set.sdiff_subset
  have hset : D ∩ {v : EuclideanSpace ℝ (Fin d) | b < ‖v‖} =
      (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) ∩
        {v : EuclideanSpace ℝ (Fin d) | b < ‖v‖} := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_sdiff, Metric.mem_ball,
      dist_eq_norm, sub_zero]
    constructor
    · rintro ⟨hvD, hlt⟩
      exact ⟨⟨hvD, not_lt_of_gt hlt⟩, hlt⟩
    · rintro ⟨⟨hvD, _⟩, hlt⟩
      exact ⟨hvD, hlt⟩
  have htail_eq : tail d D b =
      tail d (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) b := by
    rw [tail, tail, hset]
  rw [htail_eq]
  have hle := CERW.Support.Geometry.tail_le hd hD' hDb' (s := b) hbpos
  have hden1pos : 0 < d * unitBallVolume d * b ^ ((d : ℝ) - 1) :=
    mul_pos hdpos (Real.rpow_pos_of_pos hbpos _)
  have hden2pos : 0 < d * unitBallVolume d * (c₁ * N) ^ ((d : ℝ) - 1) :=
    mul_pos hdpos (Real.rpow_pos_of_pos hcNpos _)
  have hmono : (volume (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal /
        (d * unitBallVolume d * b ^ ((d : ℝ) - 1))
      ≤ (C₂ * N ^ d * Q) / (d * unitBallVolume d * b ^ ((d : ℝ) - 1)) :=
    div_le_div_of_nonneg_right hvol hden1pos.le
  have hdenle : d * unitBallVolume d * (c₁ * N) ^ ((d : ℝ) - 1) ≤
      d * unitBallVolume d * b ^ ((d : ℝ) - 1) := by
    have hbase : (c₁ * N) ^ ((d : ℝ) - 1) ≤ b ^ ((d : ℝ) - 1) :=
      Real.rpow_le_rpow hcNpos.le hb (by linarith)
    exact mul_le_mul_of_nonneg_left hbase hdpos.le
  have hdiv : (C₂ * N ^ d * Q) / (d * unitBallVolume d * b ^ ((d : ℝ) - 1))
      ≤ (C₂ * N ^ d * Q) / (d * unitBallVolume d * (c₁ * N) ^ ((d : ℝ) - 1)) :=
    div_le_div_of_nonneg_left (by positivity) hden2pos hdenle
  have hNpow : N ^ d = N * N ^ ((d : ℝ) - 1) := by
    rw [← Real.rpow_natCast N d]
    conv_lhs => rw [show (d : ℝ) = 1 + ((d : ℝ) - 1) by ring]
    rw [Real.rpow_add hN, Real.rpow_one]
  have hcNpow : (c₁ * N) ^ ((d : ℝ) - 1) = c₁ ^ ((d : ℝ) - 1) * N ^ ((d : ℝ) - 1) :=
    Real.mul_rpow hc₁.le hN.le
  have heq : (C₂ * N ^ d * Q) / (d * unitBallVolume d * (c₁ * N) ^ ((d : ℝ) - 1))
      = C₂ / (d * unitBallVolume d * c₁ ^ ((d : ℝ) - 1)) * N * Q := by
    rw [hNpow, hcNpow]
    field_simp
  calc tail d (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) b
      ≤ (volume (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal /
          (d * unitBallVolume d * b ^ ((d : ℝ) - 1)) := hle
    _ ≤ (C₂ * N ^ d * Q) / (d * unitBallVolume d * b ^ ((d : ℝ) - 1)) := hmono
    _ ≤ (C₂ * N ^ d * Q) / (d * unitBallVolume d * (c₁ * N) ^ ((d : ℝ) - 1)) := hdiv
    _ = C₂ / (d * unitBallVolume d * c₁ ^ ((d : ℝ) - 1)) * N * Q := heq

/-- The outer bound: on the vector, interval and radial clauses, an inradius `b ≍ N` with excess
volume at most `C₂ N^d Q` and envelope `ℓ_n ≤ C₂ (b - |·|)_+ + C₂ W` give
`H_n ≤ b + C W L` for all large `n`. -/
theorem exists_outer_of_envelope (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {C₁ C₂ c₁ c₂ : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 ≤ C₂) (hc₁ : 0 < c₁) (hc₁₂ : c₁ ≤ c₂) {bd r₀ : ℕ} (hbd : 1 ≤ bd) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ) (b : ℝ),
      n₀ ≤ n →
      let Y : ℕ → Site d := fun j => X j ω
      let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
      let L : ℝ := Real.log (n + 2)
      let Q : ℝ := if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
      let W : ℝ := N * Q ^ ((1 : ℝ) / d)
      let lam : ℝ := if d = 2 then L ^ 2 else L
      let F : ℝ → ℝ := tail d (cellSet Y n)
      X 0 ω = 0 → (∀ j, X (j + 1) ω - X j ω ∈ unitSteps d) →
      (∀ s t : ℕ, s < t → t ≤ n →
        ‖compensated ε X t ω - compensated ε X s ω‖ ≤ C₁ * Real.sqrt (((t : ℝ) - s) * L)) →
      (∀ s t : ℕ, s < t → t ≤ n →
        (intervalMax Y s t : ℝ) ≤ C₁ * ε * (freshCount Y s t : ℝ) ^ ((1 : ℝ) / d) + C₁ * lam) →
      (∀ r : ℕ, r₀ ≤ r → r ≤ n →
        F ((r : ℝ) + bd) ≤ C₁ * shellMax Y n r * (F ((r : ℝ) - bd) - F ((r : ℝ) + bd)) +
          C₁ * (Real.sqrt ((maxLocalTime Y n : ℝ) * (r : ℝ) ^ (1 - (d : ℝ)) * F ((r : ℝ) - bd)
            * L) + (r : ℝ) ^ (1 - (d : ℝ)) * L)) →
      (maxLocalTime Y n : ℝ) ≤ C₁ * N →
      c₁ * N ≤ b → b ≤ c₂ * N →
      (volume (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal
        ≤ C₂ * N ^ d * Q →
      (∀ y : Site d, (localTime Y n y : ℝ) ≤ C₂ * max (b - euclidNorm y) 0 + C₂ * W) →
        maxRadius Y n ≤ b + C * W * L := by
  have hd1 : 1 ≤ d := by omega
  set Cbound : ℝ := C₂ / (d * unitBallVolume d * c₁ ^ ((d : ℝ) - 1)) with hCbound
  set Ctail : ℝ := max C₁ Cbound with hCtail
  have hCtail_ge : C₁ ≤ Ctail := by rw [hCtail]; exact le_max_left _ _
  have hCbound_le : Cbound ≤ Ctail := by rw [hCtail]; exact le_max_right _ _
  have hCtail_pos : 0 < Ctail := lt_of_lt_of_le hC₁ hCtail_ge
  have hCsh_pos : 0 < C₂ + 1 := by linarith
  have hbdR : (1 : ℝ) ≤ (bd : ℝ) := by exact_mod_cast hbd
  obtain ⟨K₀, Ct, hK₀, hCt, hn_tail⟩ :=
    exists_tailend (d := d) hd (Crad := C₁) (C₁ := Ctail) (Csh := C₂ + 1)
      (c₁ := c₁) (c₂ := c₂) (bd := (bd : ℝ)) (r₀ := (r₀ : ℝ))
      hC₁ hCtail_pos hCsh_pos hc₁ hbdR
  obtain ⟨n_tail, hn_tail⟩ := hn_tail
  obtain ⟨n_outer, hn_outer⟩ :=
    exists_maxRadius_le_outer (d := d) hd (ε := ε) hε
      (Cv := C₁) (CI := C₁) (Ct := Ct) (K₀ := K₀) (K₁ := K₀ + 1)
      (c₁ := c₁) (c₂ := c₂)
      hC₁.le hC₁.le hCt.le hK₀.le (by linarith) (by linarith) hc₁ hc₁₂
  refine ⟨3 * (K₀ + 1), by positivity, max (max n_tail n_outer) 1, ?_⟩
  intro Ω X ω n b hn Y N L Q W lam F h0 hstep hvec hint hrad hmaxL hcN hbc hvol henv
  have hn1 : 1 ≤ n := le_trans (le_max_right _ 1) hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnt : n_tail ≤ n :=
    le_trans (le_trans (le_max_left n_tail n_outer) (le_max_left _ 1)) hn
  have hno : n_outer ≤ n :=
    le_trans (le_trans (le_max_right n_tail n_outer) (le_max_left _ 1)) hn
  have hNpos : 0 < N := by
    change 0 < (n : ℝ) ^ ((1 : ℝ) / (d + 1))
    exact Real.rpow_pos_of_pos (by linarith) _
  have hLpos : 0 < L := by
    change 0 < Real.log (n + 2)
    exact Real.log_pos (by linarith)
  have hQnonneg : 0 ≤ Q := by
    change 0 ≤ (if d = 2 then (L / N) ^ ((1 : ℝ) / 2)
      else (L / N) ^ ((d : ℝ) / (2 * d - 1)))
    have hLN : 0 ≤ L / N := div_nonneg hLpos.le hNpos.le
    by_cases h2 : d = 2
    · rw [if_pos h2]; exact Real.rpow_nonneg hLN _
    · rw [if_neg h2]; exact Real.rpow_nonneg hLN _
  have hWnonneg : 0 ≤ W := by
    change 0 ≤ N * Q ^ ((1 : ℝ) / d)
    exact mul_nonneg hNpos.le (Real.rpow_nonneg hQnonneg _)
  have hDmeas : MeasurableSet (cellSet Y n) :=
    CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDbdd : Bornology.IsBounded (cellSet Y n) :=
    (Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin d)))
      (r := maxRadius Y n + Real.sqrt d)).subset
      (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n)
  have hFb : F b ≤ Ctail * N * Q := by
    have h1 : F b ≤ Cbound * N * Q := by
      change tail d (cellSet Y n) b ≤ Cbound * N * Q
      rw [hCbound]
      exact tail_le_of_excess hd1 hDmeas hDbdd hC₂ hc₁ hNpos hcN hQnonneg hvol
    have h2 : Cbound * N ≤ Ctail * N := mul_le_mul_of_nonneg_right hCbound_le hNpos.le
    calc F b ≤ Cbound * N * Q := h1
      _ ≤ Ctail * N * Q := mul_le_mul_of_nonneg_right h2 hQnonneg
  have hshell : ∀ r : ℕ, b + 3 ≤ r → (shellMax Y n r : ℝ) ≤ (C₂ + 1) * W := by
    intro r hr
    have h1 : (shellMax Y n r : ℝ) ≤ C₂ * W :=
      CERW.Support.Contact.shellMax_le_of_envelope Y n r (c₀ := C₂) (b := b) (A := C₂ * W)
        (by positivity) henv hr
    calc (shellMax Y n r : ℝ) ≤ C₂ * W := h1
      _ ≤ (C₂ + 1) * W := by nlinarith [hWnonneg]
  have hmaxL' : (maxLocalTime Y n : ℝ) ≤ Ctail * N := by
    calc (maxLocalTime Y n : ℝ) ≤ C₁ * N := hmaxL
      _ ≤ Ctail * N := mul_le_mul_of_nonneg_right hCtail_ge hNpos.le
  have htail_result : F (b + K₀ * W * L) ≤ Ct * N ^ (2 - (d : ℝ)) * L :=
    hn_tail Y n b hnt hcN hbc hmaxL' hFb hshell
      (fun r hr0 hrn => hrad r (by exact_mod_cast hr0) hrn)
  have hres := hn_outer X ω n b hno h0 hstep hvec hint hcN hbc htail_result
  exact hres

end CERW.Support.Coarse
