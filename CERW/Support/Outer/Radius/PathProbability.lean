import CERW.Support.Outer.Radius.RampProbability

/-!
# Path Probability

The fluctuation event supplies the deterministic path facts with uniform constants. The radius
formula and logarithmic estimates prepare the final large-time bounds.
The retained labels `eq:vector`
refer to the earlier source `paper/limit-shapes.tex`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- The compensated position of the fluctuation event is `compPath` of the path. -/
lemma pf_compensated_eq {Ω : Type*} (ε : ℝ) (X : ℕ → Ω → Site d) (ω : Ω) (t : ℕ) :
    CERW.Support.Coarse.compensated ε X t ω = compPath d ε (fun j => X j ω) t := by
  unfold CERW.Support.Coarse.compensated compPath
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h0 : X j ω = 0
  · simp [h0, departureRange, CERW.Support.Occupation.toSpace_zero]
  · simp [h0, departureRange]

/-- The good event of the fluctuation theorem's proof gives the path facts. -/
lemma pf_of_fluctEvent {ε C₀ C₁ : ℝ} (hC₁ : 0 ≤ C₁) {b : Site d → ℝ} {bd r₀ : ℕ}
    {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) {n : ℕ}
    (h : CERW.Support.Main.fluctEvent d ε b C₀ C₁ bd r₀ X ω n) :
    PathFacts d ε C₀ (2 * C₁) (fun j => X j ω) n := by
  dsimp only [CERW.Support.Main.fluctEvent] at h
  obtain ⟨⟨h0, hs⟩, -, hM, hH, -, hglob, hpt, hlm, -, hvec, -⟩ := h
  have hL := mono_log_nonneg n
  refine ⟨h0, hs, hM, hH, fun y hy => ?_, fun x hx => ?_, fun s t hst htn => ?_⟩
  · refine (hglob y hy).trans (mul_le_mul_of_nonneg_right (by linarith) ?_)
    split_ifs
    · exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) hL
    · exact add_nonneg (Real.sqrt_nonneg _) hL
  · have h1 := hpt x hx
    have h2 := hlm x hx
    have hW : braSum (fun j => X j ω) n x = ∑ j ∈ Finset.range n,
        (1 + euclidNorm (X j ω - x)) ^ (2 - 2 * (d : ℝ)) := rfl
    rw [← hW] at h2
    have h3 : |(localTime (fun j => X j ω) n x : ℝ) -
        potential d ε (cellSet (fun j => X j ω) n) (toSpace x)| ≤
        |(localTime (fun j => X j ω) n x : ℝ) -
          potential d ε (cellSet (fun j => X j ω) n) (toSpace x) +
            CERW.Support.Law.dynkin ε (fun z => b (z - x)) X n ω| +
          |CERW.Support.Law.dynkin ε (fun z => b (z - x)) X n ω| := by
      have := abs_sub (a := (localTime (fun j => X j ω) n x : ℝ) -
          potential d ε (cellSet (fun j => X j ω) n) (toSpace x) +
            CERW.Support.Law.dynkin ε (fun z => b (z - x)) X n ω)
        (b := CERW.Support.Law.dynkin ε (fun z => b (z - x)) X n ω)
      simpa using this
    have h4 : 0 ≤ Real.sqrt (braSum (fun j => X j ω) n x * Real.log ((n : ℝ) + 2)) :=
      Real.sqrt_nonneg _
    calc _ ≤ C₁ * Real.log ((n : ℝ) + 2) +
          C₁ * (Real.sqrt (braSum (fun j => X j ω) n x * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2)) := h3.trans (add_le_add h1 h2)
      _ ≤ 2 * C₁ * (Real.sqrt (braSum (fun j => X j ω) n x * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2)) := by nlinarith [mul_nonneg hC₁ h4, mul_nonneg hC₁ hL]
  · rw [← pf_compensated_eq, ← pf_compensated_eq]
    refine (hvec s t hst htn).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))

/-- The events of `prop:coarse`, `lem:local`, `eq:pointwise`, `eq:localmart` and `eq:vector`. -/
theorem exists_pathFacts_prob (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) {p : ℝ}
    (hp : 0 < p) :
    ∃ C₀ C₁ C : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ PathFacts d ε C₀ C₁ (fun j => X j ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨b, h, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts hd
  obtain ⟨r₀, hr₀⟩ := CERW.Support.Main.exists_event_prob.{u} hd hK
  obtain ⟨C₀, C₁, hC₀, hC₁, hprob⟩ := hr₀ ε hε hεd p hp
  refine ⟨C₀, 2 * C₁, C₁, hC₀, by positivity, hC₁, ?_⟩
  intro Ω _ μ _ X hX n hn
  refine le_trans (measure_mono ?_) (hprob μ X hX n hn)
  intro ω hω hE
  exact hω (pf_of_fluctEvent hC₁.le X ω hE)
/-! ### The deterministic cores -/

/-- The radius is `a n^{1/(d+1)}` with `a > 0`. -/
lemma tk_radius_eq (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, radius d ε n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
  have hω := unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : 0 < ((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d) := by positivity
  refine ⟨(((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1)),
    Real.rpow_pos_of_pos hc _, fun n => ?_⟩
  unfold radius
  rw [show ((d : ℝ) + 1) * n / (2 * d * ε * unitBallVolume d) =
    (((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d)) * n by ring]
  exact Real.mul_rpow hc.le (Nat.cast_nonneg n)

/-- Every power of `log n` is eventually at most any positive power of the radius. -/
lemma tk_log_pow_le (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {A : ℝ} (hA : 0 ≤ A) (K : ℝ)
    {s : ℝ} (hs : 0 < s) : ∀ᶠ n : ℕ in atTop, K * Real.log n ^ A ≤ radius d ε n ^ s := by
  obtain ⟨a, ha, hr⟩ := tk_radius_eq hd hε
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : 0 < ((1 : ℝ) / (d + 1)) * s := by positivity
  have hlim := CERW.Support.Main.tendsto_log_rpow_div_rpow A hc
  have hpos : 0 < a ^ s / (|K| + 1) := by positivity
  filter_upwards [hlim.eventually (gt_mem_nhds hpos), eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnc : 0 < (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * s) := Real.rpow_pos_of_pos hn0 _
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hlogle : Real.log n ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log hn0 (by linarith)
  have h1 : Real.log n ^ A ≤ Real.log ((n : ℝ) + 2) ^ A :=
    Real.rpow_le_rpow hlog0 hlogle hA
  have h2 : Real.log ((n : ℝ) + 2) ^ A <
      a ^ s / (|K| + 1) * (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * s) := by
    rwa [div_lt_iff₀ hnc] at hn
  rw [hr n, Real.mul_rpow ha.le (Real.rpow_nonneg hn0.le _), ← Real.rpow_mul hn0.le]
  have hK : K * Real.log n ^ A ≤ (|K| + 1) * Real.log n ^ A :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (Real.rpow_nonneg hlog0 _)
  calc K * Real.log n ^ A ≤ (|K| + 1) * Real.log n ^ A := hK
    _ ≤ (|K| + 1) * Real.log ((n : ℝ) + 2) ^ A :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (|K| + 1) * (a ^ s / (|K| + 1) * (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * s)) :=
        mul_le_mul_of_nonneg_left h2.le (by positivity)
    _ = a ^ s * (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * s) := by field_simp

end CERW.Support.Outer.Radius
