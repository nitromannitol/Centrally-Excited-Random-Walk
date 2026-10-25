module

public import CERW.Support.Outer.Radius.PlanarScales

@[expose] public section

/-!
# Planar Probes

Planar probes improve the bound on the potential near the outer radius. The local-time error and cap
estimate give the second exterior bound.
The section label `sec:outer-planar`
refers to the earlier source `paper/limit-shapes.tex`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

section

open Filter LatticeProb

/-- The probe of Step 2 of `sec:outer-planar`: at `y_t = (b + w + 4t) u` with `w ≤ t ≤ r/4`, the
site of
the cell of `y_t` is unvisited, so the pointwise bound there and the cell modulus give
`U_E(y_t) ≥ -(K₂ + C ε) P`. -/
lemma pl_probe {ε : ℝ} (hε : 0 < ε) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (Y : ℕ → Site 2) (n : ℕ) (b R w r P K2 : ℝ),
      innerRadius Y n = b → maxRadius Y n = R → w = R - b + 2 * Real.sqrt ((2 : ℕ) : ℝ) →
      0 < b → b ≤ 5 * r / 4 → 1 ≤ w → w ≤ r / 4 → 4 ≤ r → r ≤ n / 8 → 16 ≤ (n : ℝ) →
      Real.log (3 * r + 2) ≤ P →
      (∀ x : Site 2, b ≤ euclidNorm x → euclidNorm x ≤ 3 * n →
        |(localTime Y n x : ℝ) - potential 2 ε (cellSet Y n) (toSpace x)| ≤ K2 * P) →
      ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t → t ≤ r / 4 →
        -((K2 + Cc * ε) * P) ≤
          potential 2 ε (cellSet Y n \ Metric.ball 0 b) ((b + w + 4 * t) • u) := by
  obtain ⟨Cc, hCc, hcell⟩ :=
    CERW.Support.Geometry.exists_potential_cell_modulus (d := 2) le_rfl
  refine ⟨Cc, hCc, ?_⟩
  intro Y n b R w r P K2 hb hR hw hb0 hb2 hw1 hw2 hr4 hrn hn16 hlog3 hpt u hu t hwt htr
  have hs2 : 1 ≤ Real.sqrt ((2 : ℕ) : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have hs2' : Real.sqrt ((2 : ℕ) : ℝ) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hDm := CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDball := CERW.Support.Occupation.cellSet_subset_ball (d := 2) (by norm_num) Y n
  rw [hR] at hDball
  have hy : ‖(b + w + 4 * t) • u‖ = b + w + 4 * t := by
    rw [norm_smul, hu, mul_one, Real.norm_of_nonneg (by linarith)]
  have hyz := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell
    (mem_cell_cellCenter ((b + w + 4 * t) • u))
  generalize (b + w + 4 * t) • u = y at hy hyz ⊢
  generalize cellCenter y = z at hyz
  generalize Real.sqrt ((2 : ℕ) : ℝ) = s at hs2 hs2' hw hDball hcell hyz
  have hz1 := norm_le_norm_add_norm_sub' y (toSpace z)
  have hz2 := norm_le_norm_add_norm_sub' (toSpace z) y
  rw [norm_sub_rev] at hz2
  rw [norm_toSpace] at hz1 hz2
  have hz3 : ‖y‖ ≤ euclidNorm z + s / 2 := hz1.trans (add_le_add le_rfl hyz)
  have hz4 : euclidNorm z ≤ ‖y‖ + s / 2 := hz2.trans (add_le_add le_rfl hyz)
  have hℓ : localTime Y n z = 0 := by
    by_contra h
    have hz := mem_departureRange_iff.mpr (Nat.pos_of_ne_zero h)
    have := mem_ballFinset_iff.mp
      (CERW.Support.Occupation.departureRange_subset_ballFinset Y n hz)
    rw [hR] at this
    linarith
  have hzb : b ≤ ‖toSpace z‖ := by
    rw [norm_toSpace]
    linarith
  have hpz := hpt z (by linarith) (by linarith)
  rw [hℓ, Nat.cast_zero, zero_sub, abs_neg, pl_split (ε := ε) Y n hb hb0 hzb] at hpz
  have hc := hcell ε hε.le (3 * r) (by linarith) (cellSet Y n) hDm
    (hDball.trans (Metric.ball_subset_ball (by linarith))) y (toSpace z) (by linarith)
    (by linarith)
  rw [pl_split (ε := ε) Y n hb hb0 (y := y) (by linarith),
    pl_split (ε := ε) Y n hb hb0 hzb] at hc
  have hlogP : Cc * ε * Real.log (3 * r + 2) ≤ Cc * ε * P :=
    mul_le_mul_of_nonneg_left hlog3 (by positivity)
  have h1 := (abs_le.mp hc).1
  have h2 := (abs_le.mp hpz).1
  have e : (K2 + Cc * ε) * P = K2 * P + Cc * ε * P := by ring
  rw [e]
  linarith

/-- Step 2 of `sec:outer-planar`: from the pointwise bound, the probes give the cap volume bound
`|E ∩ B((b + w)u, t)| ≤ λ t` with `λ = K √(r lg)`, and Lemma `lem:near-far` bounds `U_E^+` in the
annulus by `C ((r lg)^{1/4} √w + √(r lg))`. -/
lemma pl_second (hnear : near_far) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / ((2 : ℕ) : ℝ)) {K2 Cm' : ℝ} (hK2 : 0 ≤ K2) (hCm0 : 0 ≤ Cm') :
    ∃ K : ℝ, 0 < K ∧ ∀ (Y : ℕ → Site 2) (n : ℕ) (b R w r lg : ℝ),
      innerRadius Y n = b → maxRadius Y n = R → w = R - b + 2 * Real.sqrt ((2 : ℕ) : ℝ) →
      0 < b → 3 * r / 4 ≤ b → b ≤ 5 * r / 4 → 1 ≤ w → w ≤ r / 4 → 4 ≤ r → r ≤ n / 8 →
      16 ≤ (n : ℝ) → 0 ≤ lg → 1 ≤ Real.sqrt (r * lg) →
      Real.log (3 * r + 2) ≤ Real.sqrt (r * lg) →
      (volume (cellSet Y n \ Metric.ball 0 b)).toReal ≤ Cm' * r * Real.sqrt (r * lg) →
      (∀ x : Site 2, b ≤ euclidNorm x → euclidNorm x ≤ 3 * n →
        |(localTime Y n x : ℝ) - potential 2 ε (cellSet Y n) (toSpace x)| ≤
          K2 * Real.sqrt (r * lg)) →
      ∀ y : EuclideanSpace ℝ (Fin 2), b ≤ ‖y‖ → ‖y‖ ≤ R + 2 * Real.sqrt ((2 : ℕ) : ℝ) →
        positivePotential 2 ε (cellSet Y n \ Metric.ball 0 b) y ≤
          K * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg)) := by
  obtain ⟨Cc, hCc, hprobe⟩ := pl_probe hε
  obtain ⟨Cnf, hCnf, hnf⟩ := hnear (d := 2) le_rfl ε hε hεd
  have hω := unitBallVolume_pos 2
  obtain ⟨K3, hK3⟩ : ∃ K3 : ℝ, K3 = K2 + Cc * ε := ⟨_, rfl⟩
  obtain ⟨K4, hK4⟩ : ∃ K4 : ℝ, K4 = 2 * ε * Cm' / unitBallVolume 2 := ⟨_, rfl⟩
  have hK30 : 0 ≤ K3 := by rw [hK3]; positivity
  have hK40 : 0 ≤ K4 := by rw [hK4]; positivity
  obtain ⟨K5, hK5⟩ : ∃ K5 : ℝ,
      K5 = unitBallVolume 2 / (2 * ε) * 5 ^ 2 * (K3 + K4) + 4 * Cm' + 1 := ⟨_, rfl⟩
  have hK5b : 0 ≤ unitBallVolume 2 / (2 * ε) * 5 ^ 2 * (K3 + K4) := by positivity
  have hK51 : 1 ≤ K5 := by linarith
  refine ⟨Cnf * K5, by positivity, ?_⟩
  intro Y n b R w r lg hb hR hw hb0 hb1 hb2 hw1 hw2 hr4 hrn hn16 hlg0 hP1 hlog3 hvolE hpt
    y hy1 hy2
  have hq4 : Real.sqrt (Real.sqrt (r * lg)) = (r * lg) ^ ((1 : ℝ) / 4) :=
    pl_sqrt_sqrt (by positivity)
  generalize Real.sqrt (r * lg) = P at hP1 hlog3 hvolE hpt hq4 ⊢
  have hP0 : 0 ≤ P := by linarith
  set E := cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) b with hE_def
  have hDb : Bornology.IsBounded (cellSet Y n) := Metric.isBounded_ball.subset
    (CERW.Support.Occupation.cellSet_subset_ball (by norm_num) Y n)
  have hEm : MeasurableSet E :=
    (CERW.Support.Occupation.measurableSet_cellSet Y n).diff measurableSet_ball
  have hEb : Bornology.IsBounded E := hDb.subset Set.sdiff_subset
  have hEsub : E ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w} := by
    have := sdiff_subset_annulus (d := 2) (by norm_num) Y n
    rw [hb, hR, ← hw] at this
    exact this
  have hEfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
  have hint : ∀ z, ∫ v in E, ‖v - z‖ ^ (2 - ((2 : ℕ) : ℝ)) = (volume E).toReal := by
    intro z
    have e : (2 : ℝ) - ((2 : ℕ) : ℝ) = 0 := by norm_num
    simp only [e, Real.rpow_zero, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  have hcap : ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t →
      volume (E ∩ Metric.ball ((b + w) • u) t) ≤ ENNReal.ofReal (K5 * P * t ^ (2 - 1)) := by
    intro u hu t hwt
    have ht0 : 0 < t := by linarith
    have ht1 : t ^ (2 - 1) = t := by norm_num
    rw [ENNReal.le_ofReal_iff_toReal_le ((hEb.subset Set.inter_subset_left).measure_lt_top.ne)
      (by positivity)]
    rcases le_or_gt t (r / 4) with htr | htr
    · have hlo := hprobe Y n b R w r P K2 hb hR hw hb0 hb2 hw1 hw2 hr4 hrn hn16 hlog3 hpt u hu t
        hwt htr
      rw [← hK3] at hlo
      have hy : ‖(b + w + 4 * t) • u‖ = b + w + 4 * t := by
        rw [norm_smul, hu, mul_one, Real.norm_of_nonneg (by linarith)]
      have hhi : positivePotential 2 ε E ((b + w + 4 * t) • u) ≤ K4 * P := by
        refine (positivePotential_le_of_outside le_rfl hε.le hEm hEb hb0 hEsub
          (by rw [hy]; linarith)).trans ?_
        rw [hint]
        calc ε / (unitBallVolume 2 * b) * (volume E).toReal
            ≤ ε / (unitBallVolume 2 * b) * (Cm' * r * P) := by gcongr
          _ ≤ K4 * P := by
            rw [hK4, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            have e : 2 * ε * Cm' / unitBallVolume 2 * P * (unitBallVolume 2 * b) =
                ε * Cm' * P * (2 * b) := by
              field_simp
            rw [e]
            calc ε * (Cm' * r * P) = ε * Cm' * P * r := by ring
              _ ≤ ε * Cm' * P * (2 * b) := by gcongr; linarith
      have h := cap_mass_of_probe le_rfl hε hEm hEb hEsub hb0 ht0 (by linarith) hu hlo hhi
      refine h.trans ?_
      rw [ht1]
      calc unitBallVolume 2 / (2 * ε) * 5 ^ 2 * (K3 * P + K4 * P) * t
          = (unitBallVolume 2 / (2 * ε) * 5 ^ 2 * (K3 + K4)) * P * t := by ring
        _ ≤ K5 * P * t := by gcongr; linarith
    · rw [ht1]
      calc (volume (E ∩ Metric.ball ((b + w) • u) t)).toReal ≤ (volume E).toReal :=
            ENNReal.toReal_mono hEfin (measure_mono Set.inter_subset_left)
        _ ≤ Cm' * r * P := hvolE
        _ ≤ Cm' * (4 * t) * P := by gcongr; linarith
        _ = (4 * Cm') * P * t := by ring
        _ ≤ K5 * P * t := by gcongr; linarith
  have hmass : ∀ z, ∫ v in E, ‖v - z‖ ^ (2 - ((2 : ℕ) : ℝ)) ≤ K5 * P * b := by
    intro z
    rw [hint]
    calc (volume E).toReal ≤ Cm' * r * P := hvolE
      _ ≤ Cm' * (2 * b) * P := by gcongr; linarith
      _ = (2 * Cm') * P * b := by ring
      _ ≤ K5 * P * b := by gcongr; linarith
  have hlam : 1 ≤ K5 * P := by
    calc (1 : ℝ) ≤ P := hP1
      _ = 1 * P := (one_mul P).symm
      _ ≤ K5 * P := mul_le_mul_of_nonneg_right hK51 hP0
  have hyw : ‖y‖ ≤ b + w := by
    rw [hw]
    convert hy2 using 1
    ring
  refine (hnf w b (K5 * P) hw1 (by linarith) hlam E hEm hEsub hcap hmass y hy1 hyw).trans ?_
  rw [← hq4]
  calc Cnf * (K5 * P * w ^ (2 - 1)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) + Cnf * (K5 * P)
      ≤ Cnf * (K5 * (Real.sqrt P * Real.sqrt w)) + Cnf * (K5 * P) := by
        gcongr
        exact pl_rpow_half_le hK51 hP0
    _ = Cnf * K5 * (Real.sqrt P * Real.sqrt w + P) := by ring

end

end CERW.Support.Outer.Radius
