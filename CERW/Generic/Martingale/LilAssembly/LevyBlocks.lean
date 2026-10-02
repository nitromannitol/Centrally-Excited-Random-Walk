import CERW.Generic.Martingale.LilLower.StoppedLevy
import CERW.Generic.Martingale.LilAssembly.CondExpGe

/-!
# Lévy's Borel–Cantelli lemma along the blocks

If, from some block on, every event `F` before block `k` on which the start time `N` has passed
is followed by the block event `k + 1` with probability at least `q_k μ F`, with `q_k ≤ 1` and
`∑ q_k = ∞`, and the passage times eventually pass `N`, then the block events occur infinitely
often almost surely.
-/

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology

/-- One block of Lévy's argument: on a set `G` of the sub-σ-algebra `m` the conditional probability
of `E` is at least `q`, if `E` has conditional probability at least `q` inside `G` on average. -/
theorem levy_blocks_step {Ω : Type*} {m m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hm : m ≤ m0) {G E : Set Ω} (hG : MeasurableSet[m] G)
    (hE : MeasurableSet E) {q : ℝ} (hq1 : q ≤ 1)
    (h : ∀ F, MeasurableSet[m] F → F ⊆ G → q * (μ F).toReal ≤ (μ (F ∩ E)).toReal) :
    ∀ᵐ ω ∂μ, ω ∈ G → q ≤ (μ[E.indicator (1 : Ω → ℝ) | m]) ω := by
  have hG0 : MeasurableSet G := hm _ hG
  have hA : MeasurableSet (E ∪ Gᶜ) := hE.union hG0.compl
  have hcond : ∀ F : Set Ω, MeasurableSet[m] F →
      q * (μ F).toReal ≤ (μ (F ∩ (E ∪ Gᶜ))).toReal := by
    intro F hF
    have hF0 : MeasurableSet F := hm _ hF
    have h1 := h (F ∩ G) (hF.inter hG) Set.inter_subset_right
    have h2 : μ.real (F ∩ G) + μ.real (F \ G) = μ.real F :=
      measureReal_inter_add_sdiff (μ := μ) (s := F) hG0
    have h3 : μ.real (F ∩ G ∩ E ∪ F \ G) ≤ μ.real (F ∩ (E ∪ Gᶜ)) := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      rintro ω (⟨⟨hF1, hG1⟩, hE1⟩ | ⟨hF1, hG1⟩)
      · exact ⟨hF1, Or.inl hE1⟩
      · exact ⟨hF1, Or.inr hG1⟩
    have h4 : μ.real (F ∩ G ∩ E ∪ F \ G) = μ.real (F ∩ G ∩ E) + μ.real (F \ G) := by
      refine measureReal_union ?_ (hF0.diff hG0)
      exact Set.disjoint_left.2 fun ω hω hω' => hω'.2 hω.1.2
    have h5 : q * μ.real (F \ G) ≤ μ.real (F \ G) :=
      mul_le_of_le_one_left measureReal_nonneg hq1
    have h8 : q * μ.real F = q * μ.real (F ∩ G) + q * μ.real (F \ G) := by
      rw [← h2, mul_add]
    show q * μ.real F ≤ μ.real (F ∩ (E ∪ Gᶜ))
    rw [h8]
    have h10 : q * μ.real (F ∩ G) ≤ μ.real (F ∩ G ∩ E) := h1
    linarith
  have h1 := condExp_ge_of_sets μ hm (E ∪ Gᶜ) q hA hcond
  have hint : ∀ S : Set Ω, MeasurableSet S → Integrable (S.indicator (1 : Ω → ℝ)) μ :=
    fun S hS => (integrable_const (1 : ℝ)).indicator hS
  have h2 := condExp_indicator (m := m) (hint (E ∪ Gᶜ) hA) hG
  have h3 := condExp_indicator (m := m) (hint E hE) hG
  have heq : G.indicator ((E ∪ Gᶜ).indicator (1 : Ω → ℝ)) = G.indicator (E.indicator 1) := by
    ext ω
    by_cases hω : ω ∈ G
    · by_cases hωE : ω ∈ E <;> simp [hω, hωE]
    · simp [hω]
  filter_upwards [h1, h2, h3] with ω h1 h2 h3 hωG
  calc q ≤ (μ[(E ∪ Gᶜ).indicator (1 : Ω → ℝ) | m]) ω := h1
    _ = G.indicator (μ[(E ∪ Gᶜ).indicator (1 : Ω → ℝ) | m]) ω :=
        (Set.indicator_of_mem hωG _).symm
    _ = (μ[G.indicator ((E ∪ Gᶜ).indicator (1 : Ω → ℝ)) | m]) ω := h2.symm
    _ = (μ[G.indicator (E.indicator (1 : Ω → ℝ)) | m]) ω := by rw [heq]
    _ = G.indicator (μ[E.indicator (1 : Ω → ℝ) | m]) ω := h3
    _ = (μ[E.indicator (1 : Ω → ℝ) | m]) ω := Set.indicator_of_mem hωG _

/-- Partial sums of a sequence that dominates `q` from `M` on and is nonnegative diverge. -/
theorem levy_blocks_tendsto {q c : ℕ → ℝ}
    (hdiv : Tendsto (fun n => ∑ k ∈ Finset.range n, q k) atTop atTop) (M : ℕ)
    (hc0 : ∀ k, 0 ≤ c k) (hcq : ∀ k, M ≤ k → q k ≤ c k) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, c k) atTop atTop := by
  refine (tendsto_add_atTop_iff_nat M).1 ?_
  have h1 : Tendsto (fun n => ∑ k ∈ Finset.range (M + n), q k) atTop atTop :=
    hdiv.comp (tendsto_atTop_mono (fun n => Nat.le_add_left n M) tendsto_id)
  have h2 : Tendsto (fun n => ∑ k ∈ Finset.range n, q (M + k)) atTop atTop := by
    have h3 := tendsto_atTop_add_const_right atTop (-(∑ k ∈ Finset.range M, q k)) h1
    refine h3.congr fun n => ?_
    rw [Finset.sum_range_add]
    ring
  refine tendsto_atTop_mono (fun n => ?_) h2
  rw [add_comm n M, Finset.sum_range_add]
  have h4 : 0 ≤ ∑ k ∈ Finset.range M, c k := Finset.sum_nonneg fun k _ => hc0 k
  have h5 : ∑ k ∈ Finset.range n, q (M + k) ≤ ∑ k ∈ Finset.range n, c (M + k) :=
    Finset.sum_le_sum fun k _ => hcq _ (by omega)
  linarith

/-- Lévy's Borel–Cantelli lemma along the blocks, from a lower bound on events before each block. -/
theorem levy_blocks {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (τ : ℕ → Ω → WithTop ℕ) (hτ : ∀ k, IsStoppingTime ℱ (τ k))
    (hmono : ∀ k ω, τ k ω ≤ τ (k + 1) ω) {E : ℕ → Set Ω}
    (hE : ∀ k, MeasurableSet[(hτ k).measurableSpace] (E k)) {q : ℕ → ℝ}
    (hq1 : ∀ k, q k ≤ 1)
    (hdiv : Tendsto (fun n => ∑ k ∈ Finset.range n, q k) atTop atTop) (N k₀ : ℕ)
    (hN : ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, (N : WithTop ℕ) ≤ τ k ω)
    (hbound : ∀ k, k₀ ≤ k → ∀ F, MeasurableSet[(hτ k).measurableSpace] F →
      F ⊆ {ω | (N : WithTop ℕ) ≤ τ k ω} → q k * (μ F).toReal ≤ (μ (F ∩ E (k + 1))).toReal) :
    ∀ᵐ ω ∂μ, ω ∈ limsup E atTop := by
  have hstep : ∀ k, ∀ᵐ ω ∂μ, k₀ ≤ k → (N : WithTop ℕ) ≤ τ k ω →
      q k ≤ (μ[(E (k + 1)).indicator (1 : Ω → ℝ) | (hτ k).measurableSpace]) ω := by
    intro k
    by_cases hk : k₀ ≤ k
    · have hG : MeasurableSet[(hτ k).measurableSpace] {ω | (N : WithTop ℕ) ≤ τ k ω} :=
        (hτ k).measurableSet_ge' N
      have hE0 : MeasurableSet (E (k + 1)) := (hτ (k + 1)).measurableSpace_le _ (hE (k + 1))
      filter_upwards [levy_blocks_step μ (hτ k).measurableSpace_le hG hE0 (hq1 k)
        (hbound k hk)] with ω hω _ hωG using hω hωG
    · exact Filter.Eventually.of_forall fun ω hk' => absurd hk' hk
  have hnn : ∀ k, ∀ᵐ ω ∂μ,
      0 ≤ (μ[(E (k + 1)).indicator (1 : Ω → ℝ) | (hτ k).measurableSpace]) ω := by
    intro k
    have hE0 : MeasurableSet (E (k + 1)) := (hτ (k + 1)).measurableSpace_le _ (hE (k + 1))
    refine condExp_nonneg (Filter.Eventually.of_forall fun ω => ?_)
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hE' : ∀ k, MeasurableSet[(hτ k).measurableSpace] (E k) := hE
  filter_upwards [LilLower.ae_mem_limsup_iff_stopped (μ := μ) ℱ τ hτ hmono hE',
    ae_all_iff.2 hstep, ae_all_iff.2 hnn, hN] with ω h1 h2 h3 h4
  refine h1.2 ?_
  obtain ⟨K, hK⟩ := eventually_atTop.1 h4
  exact levy_blocks_tendsto hdiv (max k₀ K) h3 fun k hk =>
    h2 k (le_trans (le_max_left _ _) hk) (hK k (le_trans (le_max_right _ _) hk))

end CERW.Generic.Martingale.LilAssembly
