import CERW.LimitShapes.LogLower.Arithmetic

/-!
# Trial and quadratic tails for the logarithmic lower bounds

The trial and shell estimates of Proposition 9.4 (`prop:log-lower`) are combined with
Azuma for the stopped quadratic martingale. All geometric and elliptic trial inputs are
reused from the existing lower-bound proof.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open LatticeProb (Site euclidNorm ballFinset)

namespace CERW.LimitShapes.LogLower

open CERW.Support.Statements CERW CERW.Support.Law
open private radius stepBound_mem exists_card_shell exists_quadraticMart_le
  exists_radius_ge nat_eq_radius trial_length_le_count count_ge_length
  mem_departureRange_of_lt_innerRadius trial_tail from CERW.Support.Lower.LogLower

variable {d : ℕ}

/-- The tail bounds of `prop:log-lower` (i): for large `n` and `h₀ ≤ h ≤ r_n/8`, the probability
of `{R_in ≥ r_n - h, R_out ≤ r_n + h}` is at most `exp(-c r_n^{d-1} e^{-C h})`, and the probability
of `{R_out ≤ r_n + h}` is at most that plus `exp(-c r_n^{d-3} h²)`. -/
theorem radii_tail_bounds (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) :
    ∃ c C h₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < h₀ ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X →
        ∀ n : ℕ, n₀ ≤ n → ∀ h : ℝ, h₀ ≤ h → h ≤ radius d ε n / 8 →
          μ {ω | radius d ε n - h ≤ innerRadius (X · ω) n ∧
              maxRadius (X · ω) n ≤ radius d ε n + h} ≤
            ENNReal.ofReal (Real.exp (-(c * radius d ε n ^ (d - 1) * Real.exp (-(C * h))))) ∧
          μ {ω | maxRadius (X · ω) n ≤ radius d ε n + h} ≤
            ENNReal.ofReal (Real.exp (-(c * radius d ε n ^ (d - 1) * Real.exp (-(C * h)))) +
              Real.exp (-(c * radius d ε n ^ ((d : ℝ) - 3) * h ^ 2))) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
  obtain ⟨hp₀, hp₀1⟩ := stepBound_mem hd1 hε hεd
  obtain ⟨cS, hS, hcS, hhS, hshell⟩ := exists_card_shell hd1
  obtain ⟨c₁, c₂, hD, hc₁, hc₂, hhD, hdet⟩ := exists_quadraticMart_le hd hε
  set s : ℝ := Real.sqrt d with hsdef
  set p₀ : ℝ := 1 / (2 * (d : ℝ)) - ε / 2 with hp₀def
  set C : ℝ := (4 * s + 1) * (-Real.log p₀) with hCdef
  have hC : 0 < C := by
    have : Real.log p₀ < 0 := Real.log_neg hp₀ (by linarith)
    exact mul_pos (by positivity) (by linarith)
  set c₃ : ℝ := cS / (2 * (4 * s + 1)) with hc₃def
  set c₄ : ℝ := c₁ / (2 * (4 * s + 1)) with hc₄def
  set cA : ℝ := c₂ ^ 2 / (169 * ε * unitBallVolume d) with hcAdef
  have hc₃ : 0 < c₃ := by positivity
  have hc₄ : 0 < c₄ := by positivity
  have hcA : 0 < cA := by positivity
  set c : ℝ := min c₃ (min c₄ cA) with hcdef
  have hcpos : 0 < c := lt_min hc₃ (lt_min hc₄ hcA)
  have hc₃c : c ≤ c₃ := min_le_left _ _
  have hc₄c : c ≤ c₄ := (min_le_right _ _).trans (min_le_left _ _)
  have hcAc : c ≤ cA := (min_le_right _ _).trans (min_le_right _ _)
  set h₀ : ℝ := max (max hS hD) 1 with hh₀def
  set κ' : ℝ := 2 * d * ε * unitBallVolume d / (d + 1) with hκ'def
  have hκ' : 0 < κ' := by positivity
  set r₁ : ℝ := max 1 (max (1 / c₃) (max (1 / c₄) ((4 * s + 1) / (8 * κ')))) with hr₁def
  obtain ⟨n₀, hn₀⟩ := exists_radius_ge hd1 hε r₁
  refine ⟨c, C, h₀, hcpos, hC, lt_of_lt_of_le one_pos (le_max_right _ _), n₀, ?_⟩
  intro Ω _ μ _ X hX n hn h hhh hhr
  set r : ℝ := radius d ε n with hrdef
  have hrr : r₁ ≤ r := hn₀ n hn
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hrr
  have hrA : 1 / c₃ ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans hrr)
  have hrB : 1 / c₄ ≤ r :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans ((le_max_right _ _).trans hrr)
  have hrC : (4 * s + 1) / (8 * κ') ≤ r :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hrr))
  have hh1 : 1 ≤ h := (le_max_right _ _).trans hhh
  have hhS' : hS ≤ h := ((le_max_left _ _).trans (le_max_left _ _)).trans hhh
  have hhD' : hD ≤ h := ((le_max_right _ _).trans (le_max_left _ _)).trans hhh
  have hh8 : 8 * h ≤ r := by linarith
  have hhpos : 0 < h := by linarith
  have hn_eq : (n : ℝ) = 2 * d * ε * unitBallVolume d * r ^ (d + 1) / (d + 1) :=
    nat_eq_radius hd1 hε n
  have hTn : ⌈4 * h * s⌉₊ ≤ n := by
    refine trial_length_le_count hh1 hh8 (count_ge_length hd hκ' hr1 hrC ?_)
    rw [hn_eq, hκ'def]
    ring
  have hY1 : r ≤ r ^ (d - 1) := le_self_pow₀ hr1 (by omega)
  have hY0 : 0 ≤ r ^ (d - 1) := pow_nonneg (by linarith) _
  have hE0 : 0 ≤ Real.exp (-(C * h)) := (Real.exp_pos _).le
  have hc₃Y : 1 ≤ c₃ * r ^ (d - 1) := by
    have h1 : 1 ≤ r * c₃ := by
      have := hrA
      rwa [div_le_iff₀ hc₃] at this
    calc 1 ≤ r * c₃ := h1
      _ = c₃ * r := mul_comm _ _
      _ ≤ c₃ * r ^ (d - 1) := mul_le_mul_of_nonneg_left hY1 hc₃.le
  have hc₄Y : 1 ≤ c₄ * r ^ (d - 1) := by
    have h1 : 1 ≤ r * c₄ := by
      have := hrB
      rwa [div_le_iff₀ hc₄] at this
    calc 1 ≤ r * c₄ := h1
      _ = c₄ * r := mul_comm _ _
      _ ≤ c₄ * r ^ (d - 1) := mul_le_mul_of_nonneg_left hY1 hc₄.le
  have hb1 : μ {ω | r - h ≤ innerRadius (X · ω) n ∧ maxRadius (X · ω) n ≤ r + h} ≤
      ENNReal.ofReal (Real.exp (-(c * r ^ (d - 1) * Real.exp (-(C * h))))) := by
    set S : Finset (Site d) :=
      (ballFinset d (r - h - 1)).filter fun x => r - 2 * h < euclidNorm x with hSdef
    have hsub : {ω | r - h ≤ innerRadius (X · ω) n ∧ maxRadius (X · ω) n ≤ r + h} ⊆
        {ω | maxRadius (fun j => X j ω) n ≤ r + h ∧
          S.card ≤ (departureRange (fun j => X j ω) n ∩ S).card} := by
      rintro ω ⟨hin, hmax⟩
      refine ⟨hmax, ?_⟩
      have hSA : S ⊆ departureRange (fun j => X j ω) n := by
        intro y hy
        have hy' := Finset.mem_filter.mp hy
        have h1 : euclidNorm y ≤ r - h - 1 := LatticeProb.mem_ballFinset_iff.mp hy'.1
        exact mem_departureRange_of_lt_innerRadius hin (by linarith)
      rw [Finset.inter_eq_right.mpr hSA]
    have hk : cS * r ^ (d - 1) * h ≤ (S.card : ℝ) := hshell r h hhS' hh8
    exact (measure_mono hsub).trans ((trial_tail hd1 hε hεd hX S
      (fun x hx => (Finset.mem_filter.mp hx).2) hh1 hcS hY0 hk hc₃Y hTn).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₃c hY0) hE0)))))
  have hb2 : μ {ω | maxRadius (X · ω) n ≤ r + h} ≤
      ENNReal.ofReal (Real.exp (-(c * r ^ (d - 1) * Real.exp (-(C * h)))) +
        Real.exp (-(c * r ^ ((d : ℝ) - 3) * h ^ 2))) := by
    set Λ : Finset (Site d) :=
      (ballFinset d (r + h)).filter fun y => r - 2 * h < euclidNorm y with hΛdef
    set k₁ : ℕ := ⌈c₁ * r ^ (d - 1) * h⌉₊ with hk₁def
    have hsub : {ω | maxRadius (X · ω) n ≤ r + h} ⊆
        {ω | maxRadius (fun j => X j ω) n ≤ r + h ∧
          k₁ ≤ (departureRange (fun j => X j ω) n ∩ Λ).card} ∪
        {ω | (∀ j ≤ n, euclidNorm (X j ω) ≤ r + h) ∧
          quadraticMart ε (fun j => X j ω) n ≤ -(c₂ * r ^ d * h)} := by
      intro ω hω
      by_cases hk : k₁ ≤ (departureRange (fun j => X j ω) n ∩ Λ).card
      · exact Or.inl ⟨hω, hk⟩
      · right
        refine ⟨fun j hj => (euclidNorm_le_maxRadius _ hj).trans hω, ?_⟩
        have hm : (((departureRange (fun j => X j ω) n ∩ Λ).card : ℕ) : ℝ) <
            c₁ * r ^ (d - 1) * h := Nat.lt_ceil.mp (not_le.mp hk)
        exact hdet (fun j => X j ω) n r h hr1 hhD' hh8 hn_eq hω hm
    have hEa : μ {ω | maxRadius (fun j => X j ω) n ≤ r + h ∧
          k₁ ≤ (departureRange (fun j => X j ω) n ∩ Λ).card} ≤
        ENNReal.ofReal (Real.exp (-(c * r ^ (d - 1) * Real.exp (-(C * h))))) :=
      (trial_tail hd1 hε hεd hX Λ (fun x hx => (Finset.mem_filter.mp hx).2) hh1 hc₁ hY0
        (Nat.le_ceil _) hc₄Y hTn).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₄c hY0) hE0))))
    have hr3 : 0 ≤ r ^ ((d : ℝ) - 3) := Real.rpow_nonneg (by linarith) _
    have hEb : μ {ω | (∀ j ≤ n, euclidNorm (X j ω) ≤ r + h) ∧
          quadraticMart ε (fun j => X j ω) n ≤ -(c₂ * r ^ d * h)} ≤
        ENNReal.ofReal (Real.exp (-(c * r ^ ((d : ℝ) - 3) * h ^ 2))) :=
      (outer_quadratic_tail hd hε hεd hX hc₂ hr1 hhpos hh8 hn_eq).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcAc hr3)
            (sq_nonneg h)))))
    calc μ {ω | maxRadius (X · ω) n ≤ r + h}
        ≤ μ ({ω | maxRadius (fun j => X j ω) n ≤ r + h ∧
          k₁ ≤ (departureRange (fun j => X j ω) n ∩ Λ).card} ∪
          {ω | (∀ j ≤ n, euclidNorm (X j ω) ≤ r + h) ∧
            quadraticMart ε (fun j => X j ω) n ≤ -(c₂ * r ^ d * h)}) := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-(c * r ^ (d - 1) * Real.exp (-(C * h))))) +
          ENNReal.ofReal (Real.exp (-(c * r ^ ((d : ℝ) - 3) * h ^ 2))) := add_le_add hEa hEb
      _ = ENNReal.ofReal (Real.exp (-(c * r ^ (d - 1) * Real.exp (-(C * h)))) +
          Real.exp (-(c * r ^ ((d : ℝ) - 3) * h ^ 2))) :=
          (ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le).symm
  exact ⟨hb1, hb2⟩


end CERW.LimitShapes.LogLower
