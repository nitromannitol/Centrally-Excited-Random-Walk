module

public import CERW.Support.Outer.Radius.HigherDimensionProbes

@[expose] public section

/-!
# Higher Dimension Exterior
The exterior envelope and cap estimates bound the local times beyond the inner radius.
This gives the exterior bound of `sec:outer-high` in the earlier source `paper/limit-shapes.tex`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- Steps 1 to 4 of `sec:outer-high` for a fixed path at a fixed large time `n`: the curvature size
`Θ = log n + r⁻¹ sup_y ∫_E |v-y|^{2-d}` satisfies `log n ≤ Θ ≤ K_θ (w²/r + log n)` and bounds the
largest local time beyond the inner radius. -/
lemma hx_path (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) {C₁ Cm' Cenv Cnf Ccm Kθ K₃ : ℝ}
    (hCm' : 0 < Cm') (hCenv : 0 < Cenv) (hCnf : 0 < Cnf) (hCcm : 0 ≤ Ccm)
    (hK₃s : unitBallVolume d / (2 * ε) * 5 ^ d *
      ((max C₁ 0 * (Real.sqrt (2 * Cenv * (2 + 2 * ε / unitBallVolume d)) + 2) +
        2 * (Ccm * ε) * (1 + Real.log (1 + Real.sqrt d))) + 2 * ε / unitBallVolume d) ≤ K₃)
    (hK₃m : Cm' * 4 ^ (d - 1) ≤ K₃) (hK₃2 : 2 ≤ K₃)
    (hKθ : ∀ Θ lg r w : ℝ, 0 < lg → lg ≤ Θ → 0 < r →
      Θ ≤ lg + (((d : ℝ) - 2) * unitBallVolume d / 2 * w ^ 2 + ((d : ℝ) - 1) *
        ((K₃ * 3 ^ (d - 1) * Θ) ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
          (Cm' * r ^ (d - 1) * lg) ^ ((1 : ℝ) / ((d : ℝ) - 1)))) / r →
      Θ ≤ Kθ * (w ^ 2 / r + lg))
    (hnf : ∀ w b lam : ℝ, 1 ≤ w → w ≤ b → 1 ≤ lam →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D →
        D ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w} →
        (∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t →
          volume (D ∩ Metric.ball ((b + w) • u) t) ≤ ENNReal.ofReal (lam * t ^ (d - 1))) →
        (∀ y : EuclideanSpace ℝ (Fin d), ∫ v in D, ‖v - y‖ ^ (2 - (d : ℝ)) ≤ lam * b) →
        ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ b + w →
          positivePotential d ε D y ≤ Cnf * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) + Cnf * lam)
    (hcm : ∀ ε : ℝ, 0 ≤ ε → ∀ R : ℝ, 1 ≤ R →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → D ⊆ Metric.ball 0 R →
      ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R → ‖y - z‖ ≤ Real.sqrt d →
        |potential d ε D y - potential d ε D z| ≤ Ccm * ε * Real.log (R + 2))
    {Y : ℕ → Site d} {n : ℕ} (hj : ∀ j, euclidNorm (Y j) ≤ j)
    (hpoint : ∀ x : Site d, euclidNorm x ≤ 3 * n →
      |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
        C₁ * (Real.sqrt (braSum Y n x * Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2)))
    (henv : ∀ y : EuclideanSpace ℝ (Fin d), innerRadius Y n ≤ ‖y‖ → ‖y‖ ≤ 2 * n →
      braSum Y n (cellCenter y) ≤ Cenv * (Real.log ((n : ℝ) + 2) +
        positivePotential d ε (cellSet Y n \ Metric.ball 0 (innerRadius Y n)) y) ∧
      (localTime Y n (cellCenter y) : ℝ) ≤ Cenv * (Real.log ((n : ℝ) + 2) +
        positivePotential d ε (cellSet Y n \ Metric.ball 0 (innerRadius Y n)) y))
    (hr : 0 < radius d ε n) (hbr1 : radius d ε n / 2 ≤ innerRadius Y n)
    (hbr2 : innerRadius Y n ≤ 2 * radius d ε n) (h4r : 4 * radius d ε n ≤ n)
    (hdn : (d : ℝ) ≤ n) (hlg1 : 1 ≤ Real.log n)
    (hLlg : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n)
    (hmass : (volume (cellSet Y n \ Metric.ball 0 (innerRadius Y n))).toReal ≤
      Cm' * radius d ε n ^ (d - 1) * Real.log n)
    (hw : maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d ≤ radius d ε n / 8) :
    ∃ Θ : ℝ, Real.log n ≤ Θ ∧
      Θ ≤ Kθ * ((maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) ^ 2 / radius d ε n +
        Real.log n) ∧
      (outerMax Y n (innerRadius Y n) : ℝ) ≤ Cenv * (2 + Cnf * K₃) *
        ((Θ * (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) ^ (d - 1)) ^ ((1 : ℝ) / d) +
          Θ) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hs1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd1)
  have hRn : maxRadius Y n ≤ n := Finset.sup'_le _ _ fun j hj' =>
    (hj j).trans (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj'))
  have hbR : innerRadius Y n ≤ maxRadius Y n + Real.sqrt d / 2 := innerRadius_le hd1 Y n
  have hball := ball_innerRadius_subset hd1 Y n
  have hsub := sdiff_subset_annulus hd1 Y n
  set b := innerRadius Y n with hb_def
  set R := maxRadius Y n with hR_def
  set r := radius d ε n with hr_def
  set lg := Real.log n with hlg_def
  set L := Real.log ((n : ℝ) + 2) with hL_def
  set w := R - b + 2 * Real.sqrt d with hw_def
  set E := cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b with hE_def
  have hb0 : 0 < b := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hwb : w ≤ b := by linarith
  have hEm : MeasurableSet E :=
    (CERW.Support.Occupation.measurableSet_cellSet Y n).diff Metric.isOpen_ball.measurableSet
  have hEb : Bornology.IsBounded E :=
    (Metric.isBounded_ball.subset (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n)).subset
      Set.sdiff_subset
  have hn0 : (0 : ℝ) < n := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hL1 : 1 ≤ L := hlg1.trans (Real.log_le_log hn0 (by linarith))
  -- the curvature size `Θ`
  set I : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ∫ v in E, ‖v - y‖ ^ (2 - (d : ℝ))
    with hI_def
  have hbdd : BddAbove (Set.range I) := integral_rpow_bddAbove hd hEm hEb
  have hI0 : ∀ y, 0 ≤ I y := fun y =>
    setIntegral_nonneg hEm fun v _ => Real.rpow_nonneg (norm_nonneg _) _
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = sSup (Set.range I) := ⟨_, rfl⟩
  have hIS : ∀ y, I y ≤ S := fun y => hS ▸ le_csSup hbdd (Set.mem_range_self y)
  have hS0 : 0 ≤ S := (hI0 0).trans (hIS 0)
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : ℝ, Θ = lg + S / r := ⟨_, rfl⟩
  have hlgΘ : lg ≤ Θ := by
    rw [hΘ]
    linarith [div_nonneg hS0 hr.le]
  have hΘ0 : 0 ≤ Θ := by linarith
  have hIΘ : ∀ y, I y ≤ r * Θ := by
    intro y
    have e : r * Θ = r * lg + S := by
      rw [hΘ, mul_add, mul_div_cancel₀ S hr.ne']
    have : 0 ≤ r * lg := mul_nonneg hr.le (by linarith)
    linarith [hIS y]
  have hLΘ : L ≤ 2 * Θ := by linarith
  -- Steps 1 and 2: the probes and the cap bound
  have hprobe : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t → t ≤ r / 4 →
      -((max C₁ 0 * (Real.sqrt (2 * Cenv * (2 + 2 * ε / unitBallVolume d)) + 2) +
        2 * (Ccm * ε) * (1 + Real.log (1 + Real.sqrt d))) * Θ) ≤
        potential d ε E ((b + w + 4 * t) • u) ∧
      positivePotential d ε E ((b + w + 4 * t) • u) ≤ 2 * ε / unitBallVolume d * Θ := by
    intro u hu t ht htr
    have hnorm : ‖(b + w + 4 * t) • u‖ = b + w + 4 * t := by
      rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hUp : positivePotential d ε E ((b + w + 4 * t) • u) ≤ 2 * ε / unitBallVolume d * Θ :=
      (positivePotential_le_of_outside hd2 hε.le hEm hEb hb0 hsub
        (by rw [hnorm]; linarith)).trans
        (hx_outside_arith hε.le hω hb0 hΘ0 (hIΘ _) (by linarith))
    refine ⟨?_, hUp⟩
    have h := hx_probe_potential hd2 hε.le hCenv.le hCcm (by positivity) hcm hb0 hdn hball hL1
      hLΘ hpoint (fun y hy1 hy2 => (henv y hy1 hy2).1) (y := (b + w + 4 * t) • u)
      (by rw [hnorm]; linarith) (by rw [hnorm]; linarith) (by rw [hnorm]; linarith) hUp
    exact neg_le_of_abs_le h
  have hcap := hx_cap hd2 hε hEm hEb hsub hw1 hr hbr1 (by linarith) hlgΘ hCm'.le hmass hK₃s
    hK₃m hprobe
  -- Step 3: `lem:near-far` and the envelope
  have hlam1 : 1 ≤ K₃ * Θ := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hintb : ∀ y, I y ≤ K₃ * Θ * b := by
    intro y
    have h2 : 2 * (Θ * b) ≤ K₃ * (Θ * b) := mul_le_mul_of_nonneg_right hK₃2 (mul_nonneg hΘ0 hb0.le)
    have h3 : r * Θ ≤ 2 * b * Θ := mul_le_mul_of_nonneg_right (by linarith) hΘ0
    calc I y ≤ r * Θ := hIΘ y
      _ ≤ K₃ * Θ * b := by linarith
  have hU := hnf w b (K₃ * Θ) hw1 hwb hlam1 E hEm hsub hcap hintb
  have hmain := hx_outer_bound hd1 (by linarith) hRn hLΘ hΘ0 (by linarith) (by linarith)
    hCenv.le hCnf.le (fun y hy1 hy2 => (henv y hy1 hy2).2) hU
  -- Step 4: the bound on `Θ`
  have hloc : ∀ (y : EuclideanSpace ℝ (Fin d)) (t : ℝ), w ≤ t →
      (volume (E ∩ Metric.ball y t)).toReal ≤ K₃ * Θ * 3 ^ (d - 1) * t ^ (d - 1) :=
    fun y t ht => local_mass_of_cap hd1 hsub (by linarith) hcap y ht (by linarith)
  have hm : 0 < Cm' * r ^ (d - 1) * lg := mul_pos (mul_pos hCm' (pow_pos hr _)) (by linarith)
  have hlam : 0 < K₃ * Θ * 3 ^ (d - 1) := mul_pos (by linarith) (pow_pos (by norm_num) _)
  have hSle : S ≤ ((d : ℝ) - 2) * unitBallVolume d / 2 * w ^ 2 + ((d : ℝ) - 1) *
      ((K₃ * 3 ^ (d - 1) * Θ) ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
        (Cm' * r ^ (d - 1) * lg) ^ ((1 : ℝ) / ((d : ℝ) - 1))) := by
    rw [hS]
    refine csSup_le (Set.range_nonempty _) (Set.forall_mem_range.2 fun y => ?_)
    have h := integral_rpow_le_of_local_mass hd hEm hEb (by linarith) hlam hm hloc hmass y
    rw [show K₃ * Θ * 3 ^ (d - 1) = K₃ * 3 ^ (d - 1) * Θ by ring] at h
    calc I y ≤ _ := h
      _ = _ := by ring
  refine ⟨Θ, hlgΘ, hKθ Θ lg r w (by linarith) hlgΘ hr ?_, hmain⟩
  calc Θ = lg + S / r := hΘ
    _ ≤ _ := by gcongr

/-- Steps 1 to 4 of `sec:outer-high`: with `w = R_out - b + 2√d` at most `r/8`, there is a
curvature size `Θ ≥ log n` with `Θ ≤ C (w²/r + log n)` such that the largest local time outside
the inner ball is at most `C ((Θ w^{d-1})^{1/d} + Θ)`. -/
theorem high_exterior (hd : 3 ≤ d) (hN : NewtonConv d) (hnear : near_far) {ε : ℝ}
    (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) (C₀ C₁ Cin Cm : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      LocalPathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n → MassOK d ε Cm Y n →
      maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d ≤ radius d ε n / 8 →
      ∃ Θ : ℝ, Real.log n ≤ Θ ∧
        Θ ≤ K * ((maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) ^ 2 / radius d ε n +
          Real.log n) ∧
        (outerMax Y n (innerRadius Y n) : ℝ) ≤ K * ((Θ * (maxRadius Y n - innerRadius Y n +
          2 * Real.sqrt d) ^ (d - 1)) ^ ((1 : ℝ) / d) + Θ) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨Cenv, hCenv, nenv, henv⟩ := envelope_high hd hN hε C₁
  obtain ⟨Cnf, hCnf, hnf⟩ := hnear hd2 ε hε hεd
  obtain ⟨Ccm, hCcm, hcm⟩ := CERW.Support.Geometry.exists_potential_cell_modulus hd2
  set Cm' : ℝ := max Cm 1 with hCm'_def
  have hCm' : 0 < Cm' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set Cp : ℝ := max C₁ 0 * (Real.sqrt (2 * Cenv * (2 + 2 * ε / unitBallVolume d)) + 2) +
    2 * (Ccm * ε) * (1 + Real.log (1 + Real.sqrt d)) with hCp_def
  have hCp : 0 ≤ Cp := by
    have h1 : 0 ≤ max C₁ 0 := le_max_right _ _
    have h2 : 0 ≤ Real.log (1 + Real.sqrt d) :=
      Real.log_nonneg (by linarith [Real.sqrt_nonneg (d : ℝ)])
    rw [hCp_def]
    positivity
  set Ks : ℝ := unitBallVolume d / (2 * ε) * 5 ^ d * (Cp + 2 * ε / unitBallVolume d)
    with hKs_def
  have hKs : 0 ≤ Ks := by
    rw [hKs_def]
    positivity
  have hCm4 : 0 ≤ Cm' * 4 ^ (d - 1) := by positivity
  set K₃ : ℝ := Ks + Cm' * 4 ^ (d - 1) + 2 with hK₃_def
  have hK₃s : Ks ≤ K₃ := by linarith
  have hK₃m : Cm' * 4 ^ (d - 1) ≤ K₃ := by linarith
  have hK₃2 : 2 ≤ K₃ := by linarith
  obtain ⟨Kθ, hKθpos, hKθ⟩ := hx_theta_arith hd (a := K₃ * 3 ^ (d - 1)) (c := Cm')
    (c₁ := ((d : ℝ) - 2) * unitBallVolume d / 2) (mul_pos (by linarith) (pow_pos (by norm_num) _))
    hCm'
    (div_nonneg (mul_nonneg (by linarith) hω.le) (by norm_num))
  obtain ⟨n₁, hn₁⟩ := hx_scales hd1 hε (2 * max Cin 0)
  have hKb : 0 ≤ Cenv * (2 + Cnf * K₃) := by positivity
  refine ⟨Kθ + Cenv * (2 + Cnf * K₃), by linarith, max n₁ (max nenv d), ?_⟩
  intro Y n hn hP hI hM hw
  have hn₁' : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnenv : nenv ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hdn : d ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨hr, hKr, h4r⟩ := hn₁ n hn₁'
  obtain ⟨hlg1, hLlg⟩ := hx_log_facts (n := n) (by omega)
  have hlg0 : 0 ≤ Real.log n := by linarith
  have hj := CERW.Support.Occupation.euclidNorm_le_of_steps Y hP.start hP.step
  have hq : qrate d ε n = Real.log n / radius d ε n := by
    rw [qrate, if_neg (by omega)]
  have hrq : radius d ε n * qrate d ε n = Real.log n := by
    rw [hq]
    field_simp
  have hin : |innerRadius Y n - radius d ε n| ≤ max Cin 0 * Real.log n := by
    have h := hI.1
    rw [mul_assoc, hrq] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlg0)
  obtain ⟨hin1, hin2⟩ := abs_le.mp hin
  have hmass : (volume (cellSet Y n \ Metric.ball 0 (innerRadius Y n))).toReal ≤
      Cm' * radius d ε n ^ (d - 1) * Real.log n := by
    have h : (volume (cellSet Y n \ Metric.ball 0 (innerRadius Y n))).toReal ≤
        Cm * radius d ε n ^ d * qrate d ε n := hM
    have hpow : radius d ε n ^ d = radius d ε n ^ (d - 1) * radius d ε n := by
      rw [← pow_succ]
      congr 1
      omega
    have e : Cm * radius d ε n ^ d * qrate d ε n = Cm * (radius d ε n ^ (d - 1) * Real.log n) := by
      rw [hpow, hq]
      field_simp
    have hnn : 0 ≤ radius d ε n ^ (d - 1) * Real.log n := mul_nonneg (pow_nonneg hr.le _) hlg0
    calc _ ≤ Cm * radius d ε n ^ d * qrate d ε n := h
      _ = Cm * (radius d ε n ^ (d - 1) * Real.log n) := e
      _ ≤ Cm' * (radius d ε n ^ (d - 1) * Real.log n) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
      _ = Cm' * radius d ε n ^ (d - 1) * Real.log n := by ring
  have henv' := henv Y n hnenv hj hP.point (innerRadius Y n) (innerRadius_nonneg Y n)
    (ball_innerRadius_subset hd1 Y n)
  obtain ⟨Θ, h1, h2, h3⟩ := hx_path hd hε hCm' hCenv hCnf hCcm hK₃s hK₃m hK₃2 hKθ
    hnf hcm hj hP.point henv' hr (by linarith) (by linarith) h4r
    (by exact_mod_cast hdn) hlg1 hLlg hmass hw
  have hwr : 0 ≤ (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) ^ 2 / radius d ε n +
      Real.log n := add_nonneg (div_nonneg (sq_nonneg _) hr.le) hlg0
  have hX : 0 ≤ (Θ * (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) ^ (d - 1)) ^
      ((1 : ℝ) / d) + Θ := by
    have hw0 : 0 ≤ maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d := by
      have := innerRadius_le hd1 Y n
      have : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
      linarith
    have hΘ0 : 0 ≤ Θ := hlg0.trans h1
    exact add_nonneg (Real.rpow_nonneg (mul_nonneg hΘ0 (pow_nonneg hw0 _)) _) hΘ0
  refine ⟨Θ, h1, ?_, ?_⟩
  · exact h2.trans (mul_le_mul_of_nonneg_right (by linarith) hwr)
  · exact h3.trans (mul_le_mul_of_nonneg_right (by linarith) hX)

end CERW.Support.Outer.Radius
