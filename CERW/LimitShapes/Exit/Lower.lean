module

public import CERW.LimitShapes.Exit.LowerAux
public import CERW.LimitShapes.Exit.LowerScales

@[expose] public section

/-!
# The deterministic lower exit-time bound

The approximation and crossing estimates in Proposition `prop:coarse` force a macroscopic
inner ball. The excess and layer bounds give the occupation density needed to integrate over
that ball.
-/

namespace CERW.LimitShapes.Exit

open CERW LatticeProb MeasureTheory Filter
open CERW.Support.Occupation

/-- The lower exit-time bound from the potential approximation and crossing estimates
of Proposition `prop:coarse`. -/
theorem exists_exit_lower_of_approximation {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε) (Cerr Ccross : ℝ) (hCerr : 0 < Cerr) (hCcross : 0 < Ccross) :
    ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ (X : ℕ → Site d) (n : ℕ), X 0 = 0 →
        (∀ j, X (j + 1) - X j ∈ CERW.unitSteps d) →
        (∀ j : ℕ, j < n → Ψ (CERW.toSpace (X j)) < R) →
        R ≤ Ψ (CERW.toSpace (X n)) →
        (∀ y : EuclideanSpace ℝ (Fin d),
          ‖y‖ ≤ (1 / CERW.normMin Ψ + Real.sqrt d) * R →
          |CERW.cellLocalTime X n y -
            CERW.normPotential d ε Ψ (CERW.cellSet X n) y| ≤
              Cerr * Real.sqrt R * Real.log R) →
        (∀ a : ℝ, 0 ≤ a → CERW.maxRadius X n ≤ a / CERW.normMin Ψ +
          Ccross * (1 + (CERW.LimitShapes.exteriorLocalTime Ψ X n a : ℝ)) * Real.log R) →
        c * R ^ (d + 1) ≤ (n : ℝ) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨hm, hmin⟩ := Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hΛ : 0 < normMax Ψ := hm.trans_le
    (Support.Norm.ContactAssembly.normMin_le_normMax hd1 hΨ)
  have hV : 0 < normBallVolume Ψ :=
    Support.Norm.ContactAssembly.normBallVolume_pos' hd1 hΨ
  obtain ⟨Cg, hCg, hgeom⟩ := Support.Norm.inner_geometry hd hΨ hε
    Support.Norm.norm_ball_potential Support.Norm.layer_potential
    Support.Norm.norm_potential_geometry
  let T : ℝ := 1 / normMin Ψ + Real.sqrt d
  let A : ℝ := unitBallVolume d / (2 * ε) * ((1 + normMax Ψ / normMin Ψ) * T) ^ d
  let k : ℝ := normMin Ψ / (2 * normMax Ψ)
  let η : ℝ := min (1 / (2 * normMax Ψ * Ccross)) ((d : ℝ) * ε * k / 2)
  have hT : 0 < T := by dsimp [T]; positivity
  have hω := unitBallVolume_pos d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hη₁ : η ≤ 1 / (2 * normMax Ψ * Ccross) := min_le_left _ _
  have hη₂ : η ≤ (d : ℝ) * ε * k / 2 := min_le_right _ _
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.mp
    (eventually_lower_error_small d hA hCerr.le hCg.le hη)
  let c : ℝ := ((d : ℝ) * ε * k / 2) * normBallVolume Ψ * (k / 2) ^ d
  refine ⟨c, by dsimp [c]; positivity, max r₀ (max 4 (Real.exp 1)), ?_, ?_⟩
  · exact (by norm_num : (2 : ℝ) ≤ 4).trans
      ((le_max_left 4 _).trans (le_max_right r₀ _))
  intro R hR X n hX0 hstep hi hex ha hcross
  have hR4 : 4 ≤ R := (le_max_left 4 _).trans ((le_max_right r₀ _).trans hR)
  have hRpos : 0 < R := by linarith
  have hlog : 1 ≤ Real.log R := by
    have he : Real.exp 1 ≤ R := (le_max_right 4 _).trans ((le_max_right r₀ _).trans hR)
    simpa only [Real.log_exp] using Real.log_le_log (by positivity) he
  have hn : 1 ≤ n := by
    by_contra hh
    have hn0 : n = 0 := by omega
    have hz : Ψ (toSpace (X n)) = 0 := by
      rw [hn0, hX0]
      rw [toSpace_zero]
      exact (Generic.Norm.map_zero_nonneg_neg hΨ).1
    linarith
  let S : ℝ := T * R
  let δ : ℝ := Cerr * Real.sqrt R * Real.log R
  let b : ℝ := normInnerRadius Ψ X n
  let I : ℝ := ∫ v in cellSet X n \ {v | Ψ v < b}, (Ψ v - b)
  let B : ℝ := δ + Cg * (A * R ^ d * δ) ^ ((1 : ℝ) / (d + 1))
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmargin : maxRadius X n + Real.sqrt d < S :=
    first_exit_radius_lt hd hΨ hR4 X n hX0 hstep hi
  have hDS : cellSet X n ⊆ Metric.ball 0 S := by
    intro v hv
    exact mem_ball_zero_iff.mpr
      ((mem_ball_zero_iff.mp (cellSet_subset_ball hd1 X n hv)).trans hmargin)
  have hcontact : ∀ y : EuclideanSpace ℝ (Fin d), Ψ y = b →
      y ∈ closure (cellSet X n)ᶜ → normPotential d ε Ψ (cellSet X n) y ≤ δ := by
    intro y hy hcl
    have hs := Support.Norm.ContactShared.contact_setup hd hΨ X n hn hX0 hy hcl
    exact contact_potential_le_of_approximation hd hΨ hε X n hDS ha hcl
      (hs.2.2.2.1.trans_lt hmargin)
  obtain ⟨hb, _, hI, hIle, _, _, hprof⟩ := hgeom X n hX0 hn hDS
    (fun y hy => ha y (mem_ball_zero_iff.mp hy).le) hcontact
  change 0 < b at hb
  change 0 ≤ I at hI
  have hIbound : I ≤ A * R ^ d * δ := by
    calc
      I ≤ unitBallVolume d / (2 * ε) *
          ((1 + normMax Ψ / normMin Ψ) * S) ^ d * δ := hIle
      _ = A * R ^ d * δ := by
        dsimp only [A, S]
        rw [show (1 + normMax Ψ / normMin Ψ) * (T * R) =
          ((1 + normMax Ψ / normMin Ψ) * T) * R by ring, mul_pow]
        ring
  have hprofile : ∀ y : EuclideanSpace ℝ (Fin d),
      |cellLocalTime X n y - 2 * d * ε * max (b - Ψ y) 0| ≤ B := by
    intro y
    have hp : I ^ ((1 : ℝ) / (d + 1)) ≤
        (A * R ^ d * δ) ^ ((1 : ℝ) / (d + 1)) :=
      Real.rpow_le_rpow hI hIbound (by positivity)
    exact (hprof y).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hp hCg.le))
  have hsmall : (1 + B) * Real.log R ≤ η * R :=
    hr₀ R ((le_max_left r₀ _).trans hR)
  have hBsmall : B ≤ (d : ℝ) * ε * k / 2 * R := by
    have hh : B ≤ (1 + B) * Real.log R := by nlinarith
    exact hh.trans (hsmall.trans (mul_le_mul_of_nonneg_right hη₂ hRpos.le))
  have hext : (exteriorLocalTime Ψ X n b : ℝ) ≤ B :=
    Support.Norm.CoarseVolume.localTime_filter_le_of_profile X n hprofile hB
  have hc : maxRadius X n ≤ b / normMin Ψ + Ccross * (η * R) := by
    calc
      maxRadius X n ≤ b / normMin Ψ +
          Ccross * (1 + (exteriorLocalTime Ψ X n b : ℝ)) * Real.log R := hcross b hb.le
      _ ≤ b / normMin Ψ + Ccross * ((1 + B) * Real.log R) := by
        apply add_le_add le_rfl
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (add_le_add le_rfl hext) (by linarith))
          hCcross.le
      _ ≤ b / normMin Ψ + Ccross * (η * R) := by gcongr
  have hx : R ≤ normMax Ψ * maxRadius X n :=
    hex.trans ((Generic.Norm.le_normMax_mul hΨ (toSpace (X n))).trans
      (mul_le_mul_of_nonneg_left (by
        rw [norm_toSpace]; exact euclidNorm_le_maxRadius X le_rfl) hΛ.le))
  have hηcross : Ccross * η ≤ 1 / (2 * normMax Ψ) := by
    have hh := mul_le_mul_of_nonneg_left hη₁ hCcross.le
    have he : Ccross * (1 / (2 * normMax Ψ * Ccross)) =
        1 / (2 * normMax Ψ) := by field_simp
    rwa [he] at hh
  have hbR : k * R ≤ b := by
    have hc' : maxRadius X n ≤ b / normMin Ψ + R / (2 * normMax Ψ) := by
      apply hc.trans
      apply add_le_add le_rfl
      calc
        Ccross * (η * R) = (Ccross * η) * R := by ring
        _ ≤ (1 / (2 * normMax Ψ)) * R :=
          mul_le_mul_of_nonneg_right hηcross hRpos.le
        _ = R / (2 * normMax Ψ) := by ring
    have hh := mul_le_mul_of_nonneg_left hc' hΛ.le
    have he : normMax Ψ * (R / (2 * normMax Ψ)) = R / 2 := by field_simp
    rw [mul_add, he] at hh
    have hbhalf : R / 2 ≤ normMax Ψ * (b / normMin Ψ) := by
      linarith only [hx, hh]
    have hmb : normMin Ψ * (R / 2) ≤ normMax Ψ * b := by
      calc
        _ ≤ normMin Ψ * (normMax Ψ * (b / normMin Ψ)) :=
          mul_le_mul_of_nonneg_left hbhalf hm.le
        _ = normMax Ψ * b := by field_simp
    dsimp only [k]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * normMax Ψ)).mpr
    nlinarith only [hmb]
  have hr : 0 < k * R / 2 := by positivity
  have hsub : {y : EuclideanSpace ℝ (Fin d) | Ψ y < k * R / 2} ⊆ cellSet X n := by
    apply Set.Subset.trans _ (Support.Norm.CoarseVolume.sublevel_subset_cellSet hΨ X n)
    intro y hy
    change Ψ y < b
    dsimp only [Set.mem_setOf_eq] at hy
    linarith
  have hl : ∀ y, Ψ y < k * R / 2 →
      ((d : ℝ) * ε * k / 2) * R ≤ cellLocalTime X n y := by
    intro y hy
    have hh := (abs_le.mp (hprofile y)).1
    have hmy : k * R / 2 ≤ b - Ψ y := by linarith only [hbR, hy]
    have hm : k * R / 2 ≤ max (b - Ψ y) 0 := hmy.trans (le_max_left _ _)
    have hp := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * (d : ℝ) * ε by positivity)
    linarith only [hh, hp, hBsmall]
  have ht := time_lower_of_cellLocalTime hΨ X n hr (by positivity) hsub hl
  calc
    c * R ^ (d + 1) = ((d : ℝ) * ε * k / 2 * R) * normBallVolume Ψ *
        (k * R / 2) ^ d := by
      dsimp only [c]
      rw [pow_succ, show k * R / 2 = k / 2 * R by ring, mul_pow]
      ring
    _ ≤ n := ht

end CERW.LimitShapes.Exit
