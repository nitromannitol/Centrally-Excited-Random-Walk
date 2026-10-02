import CERW.Generic.Martingale.LilAssembly.PaddedConstruction

/-!
# The structural fields of the padded data

The padded process of a martingale with a sure bound on its increments, with the gate of
`padGate`, is a square-integrable martingale for the joined filtration, started at zero, with
bound `padB` and nondecreasing predictable bracket `padVar`, which is, almost surely, the
predictable bracket of the padded process and tends to infinity.
-/

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.LilLower
open CERW.Generic.Martingale.CLT (pathBracket)

variable {Ω : Type*} {Ξ : Type*} {m0 : MeasurableSpace Ω} {mΞ : MeasurableSpace Ξ}

/-- The clipped conditional variance at time `j` is measurable at time `j`. -/
private lemma stronglyMeasurable_clipVar (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (S : ℕ → Ω → ℝ) (j : ℕ) : StronglyMeasurable[ℱ j] (clipVar μ ℱ S j) :=
  (stronglyMeasurable_condExp.measurable.max measurable_const).stronglyMeasurable

/-- The pathwise bracket at time `i + 1` is measurable at time `i`. -/
private lemma stronglyMeasurable_pathBracket_succ (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (S : ℕ → Ω → ℝ) (i : ℕ) : StronglyMeasurable[ℱ i] (pathBracket μ ℱ S (i + 1)) := by
  refine Finset.stronglyMeasurable_fun_sum (Finset.range (i + 1)) fun j hj => ?_
  exact (stronglyMeasurable_clipVar μ ℱ S j).mono
    (ℱ.mono (Nat.le_of_lt_succ (Finset.mem_range.1 hj)))

/-- The ratio that controls the gate is measurable at time `i`. -/
theorem stronglyMeasurable_gateRatio (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ)
    (hB : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1))) (i : ℕ) :
    StronglyMeasurable[ℱ i] (gateRatio μ ℱ S B i) := by
  have hP : Measurable[ℱ i] (pathBracket μ ℱ S (i + 1)) :=
    (stronglyMeasurable_pathBracket_succ μ ℱ S i).measurable
  have hBi : Measurable[ℱ i] (B (i + 1)) := (hB i).measurable
  refine Measurable.stronglyMeasurable ?_
  unfold gateRatio
  refine Measurable.div (hBi.mul ?_) ?_
  · exact (Real.measurable_log.comp (Real.measurable_log.comp
      (hP.max measurable_const))).sqrt
  · exact hP.sqrt

/-- The gate at time `j` is measurable at time `j`. -/
theorem stronglyMeasurable_padGate (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ)
    (hB : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1))) (εg : ℝ) (N j : ℕ) :
    StronglyMeasurable[ℱ j] (padGate μ ℱ S B εg N j) := by
  exact stronglyMeasurable_levelGate (stronglyMeasurable_gateRatio μ ℱ S B hB) εg N j

/-- The gate takes only the values `0` and `1`. -/
theorem padGate_eq_zero_or_one (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ)
    (εg : ℝ) (N j : ℕ) (ω : Ω) :
    padGate μ ℱ S B εg N j ω = 0 ∨ padGate μ ℱ S B εg N j ω = 1 := by
  exact levelGate_eq_zero_or_one _ _ _ _ _

/-- The padded process is a martingale for the joined filtration. -/
theorem padData_mart
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (ℱ : Filtration ℕ m0) {𝒦 : ℕ → MeasurableSpace Ξ} {ε : ℕ → Ξ → ℝ}
    (hε : SignSequence ν 𝒦 ε) {S B : ℕ → Ω → ℝ} (hS : SureData μ ℱ S B) (εg : ℝ)
    (N : ℕ) :
    Martingale (padProc μ ℱ S B εg N ε) (liftFiltration ℱ 𝒦 hε.mono hε.le) (μ.prod ν) := by
  exact martingale_padded μ ν ℱ hε hS.mart hS.memLp
    (stronglyMeasurable_padGate μ ℱ S B hS.bPred εg N) (padGate_eq_zero_or_one μ ℱ S B εg N)

/-- The padded process is square integrable. -/
theorem padData_memLp
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (ℱ : Filtration ℕ m0) {𝒦 : ℕ → MeasurableSpace Ξ} {ε : ℕ → Ξ → ℝ}
    (hε : SignSequence ν 𝒦 ε) {S B : ℕ → Ω → ℝ} (hS : SureData μ ℱ S B) (εg : ℝ)
    (N : ℕ) :
    ∀ n, MemLp ((padProc μ ℱ S B εg N ε) n) 2 (μ.prod ν) := by
  intro n
  exact memLp_padded μ ν hε hS.memLp (padGate_eq_zero_or_one μ ℱ S B εg N)
    (fun j => ((stronglyMeasurable_padGate μ ℱ S B hS.bPred εg N j).mono (ℱ.le j)).measurable) n

/-- The padded process starts at zero. -/
theorem padData_zero (μ : Measure Ω) (ℱ : Filtration ℕ m0) (ε : ℕ → Ξ → ℝ)
    {S B : ℕ → Ω → ℝ} (hS : SureData μ ℱ S B) (εg : ℝ) (N : ℕ) :
    ∀ z : Ω × Ξ, (padProc μ ℱ S B εg N ε) 0 z = 0 := by
  intro z
  exact hS.zero z.1

/-- The bound at time `n + 1` is measurable at time `n`. -/
theorem padData_bPred
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (ℱ : Filtration ℕ m0) {𝒦 : ℕ → MeasurableSpace Ξ} {ε : ℕ → Ξ → ℝ}
    (hε : SignSequence ν 𝒦 ε) {S B : ℕ → Ω → ℝ} (hS : SureData μ ℱ S B) (εg : ℝ)
    (N : ℕ) :
    ∀ n, StronglyMeasurable[liftFiltration ℱ 𝒦 hε.mono hε.le n]
      (padB (Ξ := Ξ) μ ℱ S B εg N (n + 1)) := by
  intro n
  have hG : Measurable[ℱ n] (padGate μ ℱ S B εg N n) :=
    (stronglyMeasurable_padGate μ ℱ S B hS.bPred εg N n).measurable
  have hB : Measurable[ℱ n] (B (n + 1)) := (hS.bPred n).measurable
  exact stronglyMeasurable_comp_fst_joinSigma (𝒦 n)
    ((hG.mul (hB.max measurable_const)).add (measurable_const.sub hG)).stronglyMeasurable

/-- The increments of the padded process are surely bounded by `padB`. -/
theorem padData_bInc
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (ℱ : Filtration ℕ m0) {𝒦 : ℕ → MeasurableSpace Ξ} {ε : ℕ → Ξ → ℝ}
    (hε : SignSequence ν 𝒦 ε) {S B : ℕ → Ω → ℝ} (hS : SureData μ ℱ S B) (εg : ℝ)
    (N : ℕ) :
    ∀ (n : ℕ) (z : Ω × Ξ),
      |(padProc μ ℱ S B εg N ε) (n + 1) z - (padProc μ ℱ S B εg N ε) n z| ≤
        padB (Ξ := Ξ) μ ℱ S B εg N (n + 1) z := by
  intro n z
  have hsign : |ε (n + 1) z.2| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 (hε.sq_eq_one _ _).le
  have hbound := hS.bInc n z.1
  show |padded S (padGate μ ℱ S B εg N) ε n z +
      padGate μ ℱ S B εg N n z.1 * (S (n + 1) z.1 - S n z.1) +
      (1 - padGate μ ℱ S B εg N n z.1) * ε (n + 1) z.2 - padded S (padGate μ ℱ S B εg N) ε n z| ≤
    padGate μ ℱ S B εg N n z.1 * max (B (n + 1) z.1) 0 + (1 - padGate μ ℱ S B εg N n z.1)
  rcases padGate_eq_zero_or_one μ ℱ S B εg N n z.1 with h | h <;> rw [h]
  · have h2 : padded S (padGate μ ℱ S B εg N) ε n z + 0 * (S (n + 1) z.1 - S n z.1) +
        (1 - 0) * ε (n + 1) z.2 - padded S (padGate μ ℱ S B εg N) ε n z = ε (n + 1) z.2 := by
      ring
    rw [h2]
    linarith
  · have h2 : padded S (padGate μ ℱ S B εg N) ε n z + 1 * (S (n + 1) z.1 - S n z.1) +
        (1 - 1) * ε (n + 1) z.2 - padded S (padGate μ ℱ S B εg N) ε n z =
        S (n + 1) z.1 - S n z.1 := by
      ring
    rw [h2]
    linarith

/-- The bracket at time `n + 1` is measurable at time `n`. -/
theorem padData_vPred
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (ℱ : Filtration ℕ m0) {𝒦 : ℕ → MeasurableSpace Ξ} {ε : ℕ → Ξ → ℝ}
    (hε : SignSequence ν 𝒦 ε) {S B : ℕ → Ω → ℝ} (hS : SureData μ ℱ S B) (εg : ℝ)
    (N : ℕ) :
    ∀ n, StronglyMeasurable[liftFiltration ℱ 𝒦 hε.mono hε.le n]
      (padVar (Ξ := Ξ) μ ℱ S B εg N (n + 1)) := by
  intro n
  exact stronglyMeasurable_comp_fst_joinSigma (𝒦 n)
    (stronglyMeasurable_paddedBracket_succ (stronglyMeasurable_clipVar μ ℱ S)
      (stronglyMeasurable_padGate μ ℱ S B hS.bPred εg N) n)

/-- The bracket starts at zero. -/
theorem padData_vZero (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ) (εg : ℝ)
    (N : ℕ) :
    ∀ z : Ω × Ξ, padVar (Ξ := Ξ) μ ℱ S B εg N 0 z = 0 := by
  intro z
  simp [padBracket, paddedBracket]

/-- The bracket is nondecreasing at every point. -/
theorem padData_vMono (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ) (εg : ℝ)
    (N : ℕ) :
    ∀ (n : ℕ) (z : Ω × Ξ),
      padVar (Ξ := Ξ) μ ℱ S B εg N n z ≤ padVar (Ξ := Ξ) μ ℱ S B εg N (n + 1) z := by
  intro n z
  exact paddedBracket_mono (fun _ => le_max_right _ _)
    (fun j => padGate_eq_zero_or_one μ ℱ S B εg N j z.1) n

/-- The bracket is the predictable bracket of the padded process, almost surely. -/
theorem padData_vBracket
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (ℱ : Filtration ℕ m0) {𝒦 : ℕ → MeasurableSpace Ξ} {ε : ℕ → Ξ → ℝ}
    (hε : SignSequence ν 𝒦 ε) {S B : ℕ → Ω → ℝ} (hS : SureData μ ℱ S B) (εg : ℝ)
    (N : ℕ) :
    ∀ᵐ z ∂(μ.prod ν), ∀ n,
      padVar (Ξ := Ξ) μ ℱ S B εg N n z =
        CERW.predBracket (μ.prod ν) (liftFiltration ℱ 𝒦 hε.mono hε.le)
          (padProc μ ℱ S B εg N ε) (padProc μ ℱ S B εg N ε) n z := by
  have hnn : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ (μ[fun ω => (S (j + 1) ω - S j ω) ^ 2 | ℱ j]) ω :=
    ae_all_iff.2 fun j => condExp_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
  have hall : ∀ᵐ z ∂(μ.prod ν), ∀ n, CERW.predBracket (μ.prod ν)
      (liftFiltration ℱ 𝒦 hε.mono hε.le) (padProc μ ℱ S B εg N ε) (padProc μ ℱ S B εg N ε) n z =
      paddedBracket (fun j ω => (μ[fun ω => (S (j + 1) ω - S j ω) ^ 2 | ℱ j]) ω)
        (padGate μ ℱ S B εg N) n z.1 :=
    ae_all_iff.2 fun n => predBracket_padded_ae_eq μ ν ℱ hε hS.memLp
      (stronglyMeasurable_padGate μ ℱ S B hS.bPred εg N) (padGate_eq_zero_or_one μ ℱ S B εg N) n
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hnn, hall] with z hz1 hz2 n
  rw [hz2 n]
  show paddedBracket (clipVar μ ℱ S) (padGate μ ℱ S B εg N) n z.1 = _
  unfold paddedBracket
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [clipVar, max_eq_left (hz1 j)]

/-- The bracket tends to infinity, almost surely. -/
theorem padData_vInf
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (ℱ : Filtration ℕ m0) {S B : ℕ → Ω → ℝ} (hS : SureData μ ℱ S B) (εg : ℝ) (N : ℕ) :
    ∀ᵐ z ∂(μ.prod ν), Tendsto (fun n => padVar (Ξ := Ξ) μ ℱ S B εg N n z) atTop atTop := by
  have hpath : ∀ᵐ ω ∂μ, ∀ k, pathBracket μ ℱ S k ω = CERW.predBracket μ ℱ S S k ω :=
    ae_all_iff.2 fun k => CERW.Generic.Martingale.CLT.pathBracket_ae_eq_predBracket μ ℱ S k
  have hP : ∀ᵐ ω ∂μ, Tendsto (fun n => ∑ j ∈ Finset.range n, clipVar μ ℱ S j ω) atTop atTop := by
    filter_upwards [hpath, hS.vInf] with ω h1 h2
    exact h2.congr fun n => (h1 n).symm
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hP] with z hz
  exact tendsto_paddedBracket_atTop (fun _ => le_max_right _ _)
    (fun j => padGate_eq_zero_or_one μ ℱ S B εg N j z.1)
    (fun j => levelGate_antitone _ _ _ _ _) hz

end CERW.Generic.Martingale.LilAssembly
