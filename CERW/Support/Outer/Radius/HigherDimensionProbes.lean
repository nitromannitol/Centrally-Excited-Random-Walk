import CERW.Support.Outer.Radius.HigherDimensionScales

/-!
# Higher Dimension Probes

Exterior probes bound the potential and cap mass in higher dimensions. Their bounds give the
geometric estimate needed to control the outer width.
The section label `sec:outer-high`
refers to the earlier source `paper/limit-shapes.tex`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- Step 1 of `sec:outer-high`: at a probe point `y` beyond the outer radius, whose cell is
unvisited,
the potential of `E = D_n ∖ B(0,b)` is at most `C_p Θ` in absolute value. -/
lemma hx_probe_potential (hd : 2 ≤ d) {ε C₁ Cenv Ccm γ Θ : ℝ} (hε : 0 ≤ ε)
    (hCenv : 0 ≤ Cenv) (hCcm : 0 ≤ Ccm) (hγ : 0 ≤ γ)
    (hcm : ∀ ε : ℝ, 0 ≤ ε → ∀ R : ℝ, 1 ≤ R →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → D ⊆ Metric.ball 0 R →
      ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R → ‖y - z‖ ≤ Real.sqrt d →
        |potential d ε D y - potential d ε D z| ≤ Ccm * ε * Real.log (R + 2))
    {Y : ℕ → Site d} {n : ℕ} {b : ℝ} (hb : 0 < b) (hdn : (d : ℝ) ≤ n)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ cellSet Y n)
    (hL1 : 1 ≤ Real.log ((n : ℝ) + 2)) (hLΘ : Real.log ((n : ℝ) + 2) ≤ 2 * Θ)
    (hpoint : ∀ x : Site d, euclidNorm x ≤ 3 * n →
      |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
        C₁ * (Real.sqrt (braSum Y n x * Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2)))
    (hbra : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ 2 * n →
      braSum Y n (cellCenter y) ≤ Cenv * (Real.log ((n : ℝ) + 2) +
        positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y))
    {y : EuclideanSpace ℝ (Fin d)} (hyR : maxRadius Y n + Real.sqrt d / 2 < ‖y‖)
    (hyb : b ≤ ‖y‖) (hyn : ‖y‖ ≤ n)
    (hUp : positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y ≤ γ * Θ) :
    |potential d ε (cellSet Y n \ Metric.ball 0 b) y| ≤
      (max C₁ 0 * (Real.sqrt (2 * Cenv * (2 + γ)) + 2) +
        2 * (Ccm * ε) * (1 + Real.log (1 + Real.sqrt d))) * Θ := by
  have hd1 : 1 ≤ d := by omega
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hs0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hsd : Real.sqrt d ≤ d := by
    rw [Real.sqrt_le_left (by linarith), sq]
    calc (d : ℝ) = d * 1 := (mul_one _).symm
      _ ≤ d * d := mul_le_mul_of_nonneg_left hd' (by linarith)
  have hDm : MeasurableSet (cellSet Y n) := CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDsub : cellSet Y n ⊆ Metric.ball 0 ((n : ℝ) + Real.sqrt d) :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n).trans
      (Metric.ball_subset_ball (by linarith))
  have hDb : Bornology.IsBounded (cellSet Y n) := Metric.isBounded_ball.subset hDsub
  have hyz : ‖y - toSpace (cellCenter y)‖ ≤ Real.sqrt d / 2 :=
    CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter y)
  have hz1 : ‖y‖ ≤ ‖toSpace (cellCenter y)‖ + ‖y - toSpace (cellCenter y)‖ :=
    norm_le_norm_add_norm_sub' y (toSpace (cellCenter y))
  have hz2 : ‖toSpace (cellCenter y)‖ ≤ ‖y‖ + ‖y - toSpace (cellCenter y)‖ :=
    norm_le_norm_add_norm_sub y (toSpace (cellCenter y))
  rw [norm_toSpace] at hz1 hz2
  have hz0 : localTime Y n (cellCenter y) = 0 := by
    by_contra hne
    have hmem : cellCenter y ∈ departureRange Y n :=
      mem_departureRange_iff.mpr (Nat.pos_of_ne_zero hne)
    obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp hmem
    have hle := euclidNorm_le_maxRadius Y (Nat.le_of_lt (Finset.mem_range.mp hj))
    rw [hjz] at hle
    linarith
  have hpt := hpoint (cellCenter y) (by linarith)
  rw [hz0, Nat.cast_zero] at hpt
  have hW := hbra y hyb (by linarith)
  have hmod := hcm ε hε ((n : ℝ) + Real.sqrt d) (by linarith) (cellSet Y n) hDm hDsub y
    (toSpace (cellCenter y)) (by linarith) (by linarith)
  have hsplit := potential_split hd ε hDm hDb hb hball y
  rw [max_eq_right (by linarith), mul_zero, zero_add] at hsplit
  rw [hsplit] at hmod
  have hκ : 0 ≤ 1 + Real.log (1 + Real.sqrt d) := by
    have : 0 ≤ Real.log (1 + Real.sqrt d) := Real.log_nonneg (by linarith)
    linarith
  exact hx_probe_arith hCenv hγ (mul_nonneg hCcm hε) hκ (by linarith) hLΘ hpt hW hUp hmod
    (hx_log_shift d n hL1)

/-- Step 2 of `sec:outer-high`: the probe bounds give the cap bound `|E ∩ B((b+w)u,t)| ≤ K₃ Θ
t^{d-1}`
for every unit vector `u` and every `t ≥ w`; for `t > r/4` it follows from the mass bound. -/
lemma hx_cap (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) {b w r Θ lg Cp Cm' K₃ : ℝ}
    (hsub : E ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w}) (hw1 : 1 ≤ w) (hr : 0 < r) (hbr : r / 2 ≤ b)
    (hlg : 0 ≤ lg) (hlgΘ : lg ≤ Θ) (hCm' : 0 ≤ Cm')
    (hmass : (volume E).toReal ≤ Cm' * r ^ (d - 1) * lg)
    (hK₃s : unitBallVolume d / (2 * ε) * 5 ^ d * (Cp + 2 * ε / unitBallVolume d) ≤ K₃)
    (hK₃m : Cm' * 4 ^ (d - 1) ≤ K₃)
    (hprobe : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t → t ≤ r / 4 →
      -(Cp * Θ) ≤ potential d ε E ((b + w + 4 * t) • u) ∧
      positivePotential d ε E ((b + w + 4 * t) • u) ≤ 2 * ε / unitBallVolume d * Θ) :
    ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t →
      volume (E ∩ Metric.ball ((b + w) • u) t) ≤ ENNReal.ofReal (K₃ * Θ * t ^ (d - 1)) := by
  intro u hu t ht
  have hΘ : 0 ≤ Θ := hlg.trans hlgΘ
  have ht0 : 0 < t := by linarith
  have htd : 0 ≤ t ^ (d - 1) := pow_nonneg ht0.le _
  have hK₃ : 0 ≤ K₃ := (mul_nonneg hCm' (pow_nonneg (by norm_num) _)).trans hK₃m
  have hfin : volume (E ∩ Metric.ball ((b + w) • u) t) ≠ ⊤ :=
    ((hEb.subset Set.inter_subset_left).measure_lt_top).ne
  rw [ENNReal.le_ofReal_iff_toReal_le hfin (mul_nonneg (mul_nonneg hK₃ hΘ) htd)]
  rcases le_or_gt t (r / 4) with htr | htr
  · obtain ⟨hlo, hhi⟩ := hprobe u hu t ht htr
    have h := cap_mass_of_probe hd hε hE hEb hsub (by linarith) ht0 (by linarith) hu hlo hhi
    calc (volume (E ∩ Metric.ball ((b + w) • u) t)).toReal
        ≤ unitBallVolume d / (2 * ε) * 5 ^ d * (Cp * Θ + 2 * ε / unitBallVolume d * Θ) *
            t ^ (d - 1) := h
      _ = unitBallVolume d / (2 * ε) * 5 ^ d * (Cp + 2 * ε / unitBallVolume d) *
            (Θ * t ^ (d - 1)) := by ring
      _ ≤ K₃ * (Θ * t ^ (d - 1)) := mul_le_mul_of_nonneg_right hK₃s (mul_nonneg hΘ htd)
      _ = K₃ * Θ * t ^ (d - 1) := by ring
  · have hEfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
    have hmono : (volume (E ∩ Metric.ball ((b + w) • u) t)).toReal ≤ (volume E).toReal :=
      ENNReal.toReal_mono hEfin (measure_mono Set.inter_subset_left)
    have hr0 : 0 ≤ r := hr.le
    have hr4 : r ^ (d - 1) ≤ 4 ^ (d - 1) * t ^ (d - 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hr0 (by linarith) _
    calc (volume (E ∩ Metric.ball ((b + w) • u) t)).toReal ≤ Cm' * r ^ (d - 1) * lg :=
          hmono.trans hmass
      _ ≤ Cm' * (4 ^ (d - 1) * t ^ (d - 1)) * Θ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hr4 hCm') hlgΘ hlg
            (mul_nonneg hCm' (mul_nonneg (pow_nonneg (by norm_num) _) htd))
      _ = Cm' * 4 ^ (d - 1) * (Θ * t ^ (d - 1)) := by ring
      _ ≤ K₃ * (Θ * t ^ (d - 1)) := mul_le_mul_of_nonneg_right hK₃m (mul_nonneg hΘ htd)
      _ = K₃ * Θ * t ^ (d - 1) := by ring

/-- Step 3 of `sec:outer-high`: the envelope bound and the bound on `U_E^+` in the annulus bound the
largest local time beyond the inner radius by `C_env (2 + C_nf K₃) ((Θ w^{d-1})^{1/d} + Θ)`. -/
lemma hx_outer_bound (hd : 1 ≤ d) {ε : ℝ} {Y : ℕ → Site d} {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin d))} {b w Θ K₃ Cenv Cnf : ℝ}
    (hRbw : maxRadius Y n ≤ b + w) (hRn : maxRadius Y n ≤ n)
    (hL : Real.log ((n : ℝ) + 2) ≤ 2 * Θ) (hΘ : 0 ≤ Θ) (hw : 0 ≤ w) (hK₃ : 1 ≤ K₃)
    (hCenv : 0 ≤ Cenv) (hCnf : 0 ≤ Cnf)
    (henv : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ 2 * n →
      (localTime Y n (cellCenter y) : ℝ) ≤ Cenv * (Real.log ((n : ℝ) + 2) +
        positivePotential d ε E y))
    (hnf : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ b + w →
      positivePotential d ε E y ≤
        Cnf * (K₃ * Θ * w ^ (d - 1)) ^ ((1 : ℝ) / d) + Cnf * (K₃ * Θ)) :
    (outerMax Y n b : ℝ) ≤ Cenv * (2 + Cnf * K₃) * ((Θ * w ^ (d - 1)) ^ ((1 : ℝ) / d) + Θ) := by
  have hΘw : 0 ≤ Θ * w ^ (d - 1) := mul_nonneg hΘ (pow_nonneg hw _)
  set X : ℝ := (Θ * w ^ (d - 1)) ^ ((1 : ℝ) / d) with hX_def
  have hX : 0 ≤ X := Real.rpow_nonneg hΘw _
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hK₃X : (K₃ * Θ * w ^ (d - 1)) ^ ((1 : ℝ) / d) ≤ K₃ * X := by
    rw [mul_assoc, Real.mul_rpow (by linarith) hΘw]
    apply mul_le_mul_of_nonneg_right _ hX
    calc K₃ ^ ((1 : ℝ) / d) ≤ K₃ ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hK₃
          rw [div_le_one hdpos]
          exact_mod_cast hd
      _ = K₃ := Real.rpow_one K₃
  have hRHS : 0 ≤ Cenv * (2 + Cnf * K₃) * (X + Θ) :=
    mul_nonneg (mul_nonneg hCenv (add_nonneg (by norm_num) (mul_nonneg hCnf (by linarith))))
      (by linarith)
  unfold outerMax
  rcases Finset.eq_empty_or_nonempty
      ((departureRange Y n).filter (fun z => b ≤ euclidNorm z)) with hs | hs
  · rw [hs, Finset.sup_empty, Nat.bot_eq_zero, Nat.cast_zero]
    exact hRHS
  · obtain ⟨z, hz, hsup⟩ := Finset.exists_mem_eq_sup _ hs (localTime Y n)
    rw [hsup]
    obtain ⟨hzA, hzb⟩ := Finset.mem_filter.mp hz
    have hzR : euclidNorm z ≤ maxRadius Y n := by
      obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp hzA
      rw [← hjz]
      exact euclidNorm_le_maxRadius Y (Nat.le_of_lt (Finset.mem_range.mp hj))
    have hnz : ‖toSpace z‖ = euclidNorm z := norm_toSpace z
    have hcc : cellCenter (toSpace z) = z :=
      (eq_cellCenter_of_mem_cell (toSpace_mem_cell z)).symm
    have h1 := henv (toSpace z) (by rw [hnz]; exact hzb) (by rw [hnz]; linarith)
    have h2 := hnf (toSpace z) (by rw [hnz]; exact hzb) (by rw [hnz]; linarith)
    rw [hcc] at h1
    have h4 := mul_le_mul_of_nonneg_left hK₃X hCnf
    have h3 : Real.log ((n : ℝ) + 2) + positivePotential d ε E (toSpace z) ≤
        (2 + Cnf * K₃) * (X + Θ) := by
      linarith
    calc (localTime Y n z : ℝ)
        ≤ Cenv * (Real.log ((n : ℝ) + 2) + positivePotential d ε E (toSpace z)) := h1
      _ ≤ Cenv * ((2 + Cnf * K₃) * (X + Θ)) := mul_le_mul_of_nonneg_left h3 hCenv
      _ = Cenv * (2 + Cnf * K₃) * (X + Θ) := by ring

end CERW.Support.Outer.Radius
