import CERW.Support.Outer.Radius.PathBounds

/-!
# Inner Geometry

The inner ball lies in the cell set, and its complement is contained in an annulus. The inner-radius
estimates bound the volume of that complement and split its potential.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- The ball of radius `R_in(n)` lies in `D_n`. -/
theorem ball_innerRadius_subset (hd : 1 ≤ d) (Y : ℕ → Site d) (n : ℕ) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (innerRadius Y n) ⊆ cellSet Y n :=
  (CERW.Support.Contact.exists_contact_cell hd Y n).1

/-- The inner radius is nonnegative. -/
theorem innerRadius_nonneg (Y : ℕ → Site d) (n : ℕ) : 0 ≤ innerRadius Y n :=
  Real.sInf_nonneg (by rintro _ ⟨y, _, rfl⟩; exact norm_nonneg y)

/-- The outer radius is nonnegative. -/
lemma gd_maxRadius_nonneg (Y : ℕ → Site d) (n : ℕ) : 0 ≤ maxRadius Y n :=
  (LatticeProb.euclidNorm_nonneg (Y 0)).trans (euclidNorm_le_maxRadius Y (Nat.zero_le n))

/-- The inner radius is at most `R_out(n) + √d/2`. -/
theorem innerRadius_le (hd : 1 ≤ d) (Y : ℕ → Site d) (n : ℕ) :
    innerRadius Y n ≤ maxRadius Y n + Real.sqrt d / 2 := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hR := gd_maxRadius_nonneg Y n
  have hsq : 0 ≤ Real.sqrt d / 2 := by positivity
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨v, hv⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin d))
    (show 0 ≤ maxRadius Y n + Real.sqrt d / 2 + η / 2 by linarith)
  have hvD : v ∉ cellSet Y n := fun hvD => by
    have := CERW.Support.Occupation.norm_le_of_mem_cellSet Y n hvD
    linarith
  calc innerRadius Y n ≤ ‖v‖ := csInf_le ⟨0, by rintro _ ⟨y, _, rfl⟩; exact norm_nonneg y⟩
        ⟨v, hvD, rfl⟩
    _ ≤ maxRadius Y n + Real.sqrt d / 2 + η := by linarith

/-- `E = D_n ∖ B(0,b)` lies in the annulus `{b ≤ |v| ≤ b + w}` with `w = R_out - b + 2√d`. -/
theorem sdiff_subset_annulus (hd : 1 ≤ d) (Y : ℕ → Site d) (n : ℕ) :
    cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (innerRadius Y n) ⊆
      {v | innerRadius Y n ≤ ‖v‖ ∧
        ‖v‖ ≤ innerRadius Y n + (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d)} := by
  rintro v ⟨hvD, hvb⟩
  have hsq : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · rwa [Metric.mem_ball, dist_zero_right, not_lt] at hvb
  · have := CERW.Support.Occupation.cellSet_subset_ball hd Y n hvD
    rw [mem_ball_zero_iff] at this
    linarith

/-- The Euclidean norm is a norm in the sense of `CERW.IsNorm`. -/
lemma gd_isNorm : CERW.IsNorm (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) :=
  ⟨norm_add_le, fun t x => by simp only [norm_smul, Real.norm_eq_abs],
    fun x hx => norm_eq_zero.mp hx⟩

/-- `lem:layer` for the Euclidean norm: a set in an annulus of width `a` has potential at most
`2dεa` in absolute value. -/
theorem annulus_potential_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (ha : 0 < a)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hsub : D ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + a}) (y : EuclideanSpace ℝ (Fin d)) :
    |potential d ε D y| ≤ 2 * d * ε * a := by
  have hsub' : D ⊆ {v | max b 0 ≤ ‖v‖ ∧ ‖v‖ ≤ max b 0 + a} := by
    intro v hv
    obtain ⟨h1, h2⟩ := hsub hv
    have h3 := norm_nonneg v
    refine ⟨max_le h1 h3, ?_⟩
    rcases le_total b 0 with hb | hb
    · rw [max_eq_right hb]
      linarith
    · rw [max_eq_left hb]
      exact h2
  have h := CERW.Support.Norm.layer_potential hd gd_isNorm hε (le_max_right b 0) ha hD hsub' y
  rwa [CERW.Support.Inner.normPotential_norm_eq (by omega)] at h

/-- Splitting the potential over a measurable subset of finite volume. -/
lemma gd_potential_sdiff_eq (hd : 1 ≤ d) {ε : ℝ}
    {A D : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (hAD : A ⊆ D) (y : EuclideanSpace ℝ (Fin d)) :
    potential d ε D y = potential d ε A y + potential d ε (D \ A) y := by
  have hF : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) D :=
    CERW.Support.Geometry.integrableOn_potentialIntegrand hd hD hDfin y
  have hFA : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) A := hF.mono_set hAD
  have hFE : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) (D \ A) := hF.mono_set Set.sdiff_subset
  have hunion : A ∪ (D \ A) = D := Set.union_sdiff_cancel hAD
  have hsplit : ∫ v in D, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d =
      (∫ v in A, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) +
      (∫ v in D \ A, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) := by
    conv_lhs => rw [← hunion]
    exact setIntegral_union Set.disjoint_sdiff_right (hD.diff hA) hFA hFE
  unfold potential
  rw [hsplit]
  ring

/-- `eq:ballpotential-euclid` and the decomposition `U_{D_n} = U_{B(0,b)} + U_E`. -/
theorem potential_split (hd : 2 ≤ d) (ε : ℝ) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDb : Bornology.IsBounded D) {b : ℝ} (hb : 0 < b)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ D) (y : EuclideanSpace ℝ (Fin d)) :
    potential d ε D y =
      2 * d * ε * max (b - ‖y‖) 0 + potential d ε (D \ Metric.ball 0 b) y := by
  rw [gd_potential_sdiff_eq (by omega) measurableSet_ball hD hDb.measure_lt_top.ne hball y,
    CERW.Support.Geometry.potential_ball hd ε hb y]

/-- Rescaling by `r`: `|D ∖ B(0,r)| ≤ r^d |r⁻¹ D ∆ B(0,1)|`. -/
lemma gd_volume_sdiff_ball_le {r : ℝ} (hr : 0 < r)
    (D : Set (EuclideanSpace ℝ (Fin d))) :
    volume (D \ Metric.ball 0 r) ≤ ENNReal.ofReal (r ^ d) *
      volume ((r⁻¹ • D) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  have hpre : D \ Metric.ball 0 r =
      (fun x : EuclideanSpace ℝ (Fin d) => r⁻¹ • x) ⁻¹'
        ((r⁻¹ • D) \ Metric.ball 0 1) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_preimage, Set.smul_mem_smul_set_iff₀ (inv_ne_zero hr.ne'),
      mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr,
      inv_mul_lt_iff₀ hr, mul_one]
  rw [hpre, Measure.addHaar_preimage_smul volume (inv_ne_zero hr.ne'),
    finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_pos (pow_pos hr d)]
  exact mul_le_mul_right (measure_mono fun x hx => Or.inl hx) _

/-- The shell `B(0,r) ∖ B(0,b)` has volume at most `ω_d d r^d t` when `1 - b/r ≤ t`. -/
lemma gd_volume_shell_le (hd : 1 ≤ d) {r b : ℝ} (hr : 0 < r) (hb : 0 ≤ b) {t : ℝ}
    (ht : 1 - b / r ≤ t) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r \ Metric.ball 0 b) ≤
      ENNReal.ofReal (unitBallVolume d * d * r ^ d * t) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  rcases le_or_gt r b with hrb | hbr
  · rw [Set.sdiff_eq_empty.mpr (Metric.ball_subset_ball hrb), measure_empty]
    exact zero_le
  have hω := unitBallVolume_pos d
  have hrd : 0 < r ^ d := pow_pos hr d
  have hbd : 0 ≤ b ^ d := pow_nonneg hb d
  have hV : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) =
      ENNReal.ofReal (unitBallVolume d) :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  rw [measure_sdiff (Metric.ball_subset_ball hbr.le) measurableSet_ball.nullMeasurableSet
      measure_ball_lt_top.ne, Measure.addHaar_ball _ _ hr.le, Measure.addHaar_ball _ _ hb,
    finrank_euclideanSpace_fin, hV, ← ENNReal.ofReal_mul hrd.le, ← ENNReal.ofReal_mul hbd,
    ← ENNReal.ofReal_sub _ (mul_nonneg hbd hω.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hbern : 1 + (d : ℝ) * (b / r - 1) ≤ (1 + (b / r - 1)) ^ d :=
    one_add_mul_le_pow (by have : 0 ≤ b / r := div_nonneg hb hr.le; linarith) d
  rw [show 1 + (b / r - 1) = b / r by ring] at hbern
  have hbpow : b ^ d = r ^ d * (b / r) ^ d := by rw [div_pow]; field_simp
  have hkey : r ^ d - b ^ d ≤ (d : ℝ) * r ^ d * t := by
    rw [hbpow]
    calc r ^ d - r ^ d * (b / r) ^ d ≤ r ^ d - r ^ d * (1 + d * (b / r - 1)) := by
          have := mul_le_mul_of_nonneg_left hbern hrd.le
          linarith
      _ = r ^ d * ((d : ℝ) * (1 - b / r)) := by ring
      _ ≤ r ^ d * ((d : ℝ) * t) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg d)) hrd.le
      _ = (d : ℝ) * r ^ d * t := by ring
  calc r ^ d * unitBallVolume d - b ^ d * unitBallVolume d
      = (r ^ d - b ^ d) * unitBallVolume d := by ring
    _ ≤ ((d : ℝ) * r ^ d * t) * unitBallVolume d := mul_le_mul_of_nonneg_right hkey hω.le
    _ = unitBallVolume d * d * r ^ d * t := by ring

/-- `eq:mass`: the volume outside the inner ball, from the volume clause and the inner radius
clause of Proposition `prop:inner`. -/
theorem mass_of_inner (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {Cin : ℝ} (hCin : 0 ≤ Cin)
    (Y : ℕ → Site d) {n : ℕ} (hn : 1 ≤ n) (h : InnerOK d ε Cin Y n) :
    MassOK d ε (Cin * (1 + d * unitBallVolume d)) Y n := by
  obtain ⟨hin, hvol, -⟩ := h
  have hω := unitBallVolume_pos d
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hr : 0 < radius d ε n := by
    unfold radius
    refine Real.rpow_pos_of_pos ?_ _
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hb0 := innerRadius_nonneg Y n
  set r := radius d ε n with hrdef
  set q := qrate d ε n with hqdef
  set b := innerRadius Y n with hbdef
  have hrd : 0 < r ^ d := pow_pos hr d
  have hq : 0 ≤ q := by
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    rw [hqdef]
    unfold qrate
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact div_nonneg hlog hr.le
  have ht : 0 ≤ Cin * q := mul_nonneg hCin hq
  have hbr : 1 - b / r ≤ Cin * q := by
    rw [show 1 - b / r = (r - b) / r by field_simp, div_le_iff₀ hr]
    have h1 : r - b ≤ |b - r| := by rw [abs_sub_comm]; exact le_abs_self _
    have h2 : Cin * q * r = Cin * r * q := by ring
    linarith
  have hsub : cellSet Y n \ Metric.ball 0 b ⊆
      (cellSet Y n \ Metric.ball 0 r) ∪ (Metric.ball 0 r \ Metric.ball 0 b) := by
    rintro v ⟨hvD, hvb⟩
    by_cases hvr : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r
    · exact Or.inr ⟨hvr, hvb⟩
    · exact Or.inl ⟨hvD, hvr⟩
  have h1 : volume (cellSet Y n \ Metric.ball 0 r) ≤ ENNReal.ofReal (r ^ d * (Cin * q)) := by
    rw [ENNReal.ofReal_mul hrd.le]
    exact (gd_volume_sdiff_ball_le hr _).trans (mul_le_mul_right hvol _)
  have h2 := gd_volume_shell_le (d := d) (by omega) hr hb0 hbr
  have h3 : volume (cellSet Y n \ Metric.ball 0 b) ≤
      ENNReal.ofReal (r ^ d * (Cin * q) + unitBallVolume d * d * r ^ d * (Cin * q)) := by
    rw [ENNReal.ofReal_add (mul_nonneg hrd.le ht)
      (mul_nonneg (mul_nonneg (mul_nonneg hω.le hdpos.le) hrd.le) ht)]
    exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add h1 h2))
  have h4 := ENNReal.toReal_le_of_le_ofReal
    (add_nonneg (mul_nonneg hrd.le ht)
      (mul_nonneg (mul_nonneg (mul_nonneg hω.le hdpos.le) hrd.le) ht)) h3
  unfold MassOK
  calc (volume (cellSet Y n \ Metric.ball 0 b)).toReal
      ≤ r ^ d * (Cin * q) + unitBallVolume d * d * r ^ d * (Cin * q) := h4
    _ = Cin * (1 + d * unitBallVolume d) * r ^ d * q := by ring
/-! ### Newton's theorem for the radial convolution -/

end CERW.Support.Outer.Radius
