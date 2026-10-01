import CERW.Support.Statements
import CERW.Support.LocalTime
import CERW.Support.LocalTime.LatticeKernelFacts
import CERW.Support.Law.Dynkin
import CERW.Support.Drift.Dynkin
import CERW.Generic.Martingale.Clamp
import CERW.Support.Geometry.BallCompare
import CERW.Support.Geometry.Bound
import CERW.Support.Geometry.Newton
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Main.ScaleLimits
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Lower bounds on the local times near the origin

`thm:sharp` (iii) (Theorem 1.3 (iii)): for `d ≥ 2`, `0 < ε < 1/d` and large `n`, with probability
at least `1 - n^{-c}` some site `|x| ≤ r_n^{1/2}` has
`|ℓ_n(x) - 2dε (r_n - |x|)| ≥ c √r_n log n` if `d = 2` and `≥ c √(r_n log n)` if `d ≥ 3`.

Step 1 applies Lemma 9.1 (ii) (`exp_deviation`) to the martingales `S^i = -M^{f_i} / σ_n`, where
`M^f` is the Dynkin martingale `CERW.Support.Law.dynkin`, a martingale for the path filtration
(`martingale_dynkin`), and `f_i` is a translate `g_{y_i}` of the lattice kernel (`d ≥ 3`) or the
difference `g_{y_i + k e} - g_{y_i}` (`d = 2`). Lemma 9.3 (`separated_brackets`) controls their
brackets, written with `dynkinBracket`, outside an event of probability `O(n^{-10})`; the
predictable bracket of two Dynkin martingales is `dynkinBracket` almost surely
(`ae_predBracket_dynkin`), and the martingales are clamped to have surely bounded increments.
Step 2 passes from the martingales to the local times by the pointwise decomposition
`ℓ_n(y) = U_{D_n}(y) - M^y_n + O(log n)` (`eq:pointwise`) and the bound
`|U_{D_n}(y) - 2dε (r_n - |y|)| ≤ C r_n q_n` for `|y| ≤ r_n / 2` (`eq:bulk-potential-only`),
which follows from the fluctuation bounds (`fluctuation_rates`); for `d = 2` it uses the difference
of the decomposition at the two sites `y_i` and `y_i + k e`. The hypothesis `bulk_profile`
(Proposition 9.2) is not needed.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Lower

open CERW.Support.Statements

section Helpers

open LatticeProb CERW CERW.Support.Law CERW.Support.LocalTime CERW.Support.Occupation

variable {d : ℕ}

/-- The scale `r_n = ((d+1) n / (2 d ε ω_d))^{1/(d+1)}`. -/
private noncomputable def scaleR (d : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  (((d : ℝ) + 1) * n / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))

/-- The normalizer `σ = √(R log R)` (`d = 2`) or `√R` (`d ≥ 3`). -/
private noncomputable def sigmaOf (d : ℕ) (R : ℝ) : ℝ :=
  if d = 2 then Real.sqrt (R * Real.log R) else Real.sqrt R

/-- The deviation level `β = (4 √C)⁻¹ (log R)^{1/2}`, so that `C β² = (log R)/16`. -/
private noncomputable def betaOf (C R : ℝ) : ℝ :=
  1 / (4 * Real.sqrt C) * Real.sqrt (Real.log R)

/-- The spacing `k = ⌊R^{1/8}⌋` (and the number `m` of martingales). -/
private noncomputable def kOf (R : ℝ) : ℕ := ⌊R ^ ((1 : ℝ) / 8)⌋₊

/-- The spacing `⌈R^{1/4}⌉` of the sites `y_i`. -/
private noncomputable def sepStep (R : ℝ) : ℕ := ⌈R ^ ((1 : ℝ) / 4)⌉₊

/-- The test function `f_i` of Step 1: the difference `g_{y_i + k e} - g_{y_i}` of translates of the
kernel `g` when `d = 2`, and `g_{y_i}` when `d ≥ 3`, with `y_i = i ⌈R^{1/4}⌉ e` and
`k = ⌊R^{1/8}⌋`. -/
private noncomputable def sepF (d : ℕ) (g : Site d → ℝ) (e : Site d) (R : ℝ) (i : ℕ)
    (z : Site d) : ℝ :=
  if d = 2 then
    g (z - (((i * sepStep R : ℕ) : ℤ) • e + ((kOf R : ℕ) : ℤ) • e)) -
      g (z - ((i * sepStep R : ℕ) : ℤ) • e)
  else g (z - ((i * sepStep R : ℕ) : ℤ) • e)

/-- The mean-spread identity for a pair of weighted families: for weights `p` of total mass one and
any constants `c, c'`,
`Σ p (a - m_a)(b - m_b) = Σ p (a - c)(b - c') - (m_a - c)(m_b - c')`. -/
private theorem predBracketDynkin_sum_mul_sub_mean {ι : Type*} (s : Finset ι) (p a b : ι → ℝ)
    (hp : ∑ i ∈ s, p i = 1) (c c' : ℝ) :
    ∑ i ∈ s, p i * ((a i - ∑ j ∈ s, p j * a j) * (b i - ∑ j ∈ s, p j * b j)) =
      ∑ i ∈ s, p i * ((a i - c) * (b i - c')) -
        (∑ j ∈ s, p j * a j - c) * (∑ j ∈ s, p j * b j - c') := by
  set m := ∑ j ∈ s, p j * a j with hm
  set m' := ∑ j ∈ s, p j * b j with hm'
  have hterm : ∀ i ∈ s, p i * ((a i - m) * (b i - m')) =
      p i * ((a i - c) * (b i - c')) - (m' - c') * (p i * a i) - (m - c) * (p i * b i) +
        ((m - c) * (m' - c') + (m - c) * c' + (m' - c') * c) * p i := by
    intro i _
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hp, ← hm,
    ← hm']
  ring

/-- Almost surely, the conditional expectation of the product of the increments of the Dynkin
martingales of `f` and `g` at time `t` is the path functional `Σ_e p_t(e) Δ_e f Δ_e g` minus the
product of the conditional means. -/
private theorem predBracketDynkin_condExp_mul {Ω : Type*} [MeasurableSpace Ω] {ε : ℝ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hd : 1 ≤ d) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1 / (d : ℝ)) (hX : IsCERW μ ε X) (f g : Site d → ℝ) (t : ℕ) :
    μ[fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) *
        (dynkin ε g X (t + 1) ω - dynkin ε g X t ω) | pathFiltration hX.measurable t]
      =ᵐ[μ] fun ω =>
        ∑ e ∈ unitSteps d, stepProb d ε (fun j => X j ω) t e *
          ((f (X t ω + e) - f (X t ω)) * (g (X t ω + e) - g (X t ω))) -
        (nextMean ε f (fun j => X j ω) t - f (X t ω)) *
          (nextMean ε g (fun j => X j ω) t - g (X t ω)) := by
  set h : ((i : Finset.Iic t) → Site d) → Site d → ℝ :=
    fun p z => (f z - nextMean ε f (extendPath p) t) * (g z - nextMean ε g (extendPath p) t)
    with hh
  have hprod : (fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) *
        (dynkin ε g X (t + 1) ω - dynkin ε g X t ω)) =
      fun ω => h (pastPath X t ω) (X (t + 1) ω) := by
    funext ω
    rw [dynkin_succ_sub, dynkin_succ_sub, nextMean_pastPath, nextMean_pastPath, hh]
  have hint := integrable_path_next hd hε0 hε1 hX t h
  rw [hprod]
  filter_upwards [condExp_path_next hd hε0 hε1 hX t h hint] with ω hω
  rw [hω]
  simp only [hh, ← nextMean_pastPath]
  have hcov := predBracketDynkin_sum_mul_sub_mean (unitSteps d)
    (fun e => stepProb d ε (fun j => X j ω) t e) (fun e => f (X t ω + e)) (fun e => g (X t ω + e))
    (sum_stepProb hd ε _ t) (f (X t ω)) (g (X t ω))
  simp only [nextMean] at hcov ⊢
  rw [hcov]

/-- Almost surely, the predictable bracket of two Dynkin martingales is the path functional
`dynkinBracket`. -/
private theorem ae_predBracket_dynkin {Ω : Type*} [MeasurableSpace Ω] {ε : ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hd : 1 ≤ d) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1 / (d : ℝ)) (hX : IsCERW μ ε X) (f g : Site d → ℝ) (n : ℕ) :
    ∀ᵐ ω ∂μ, predBracket μ (pathFiltration hX.measurable) (dynkin ε f X) (dynkin ε g X) n ω =
      dynkinBracket (stepProb d ε) f g (fun j => X j ω) n := by
  have hall := ae_all_iff.mpr fun t : ℕ => predBracketDynkin_condExp_mul hd hε0 hε1 hX f g t
  filter_upwards [hall] with ω hω
  rw [predBracket, Finset.sum_apply, dynkinBracket]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hω t, CERW.Support.Drift.stepMean_stepProb hd, CERW.Support.Drift.stepMean_stepProb hd]

/-- The bracket of two functions of a path depends on the path only up to time `n`. -/
private lemma maxDynkin_dynkinBracket_congr (ε : ℝ) (f g : Site d → ℝ) {x y : ℕ → Site d}
    {n : ℕ} (h : ∀ j ≤ n, x j = y j) :
    dynkinBracket (stepProb d ε) f g x n = dynkinBracket (stepProb d ε) f g y n := by
  unfold dynkinBracket stepMean
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := (Finset.mem_range.mp hj).le
  have hh : ∀ i ≤ j, x i = y i := fun i hi => h i (hi.trans hjn)
  simp only [stepProb_congr hh, h j hjn]

/-- A predicate on paths that depends only on the path up to time `n` defines a measurable event
for the walk. -/
private lemma maxDynkin_measurableSet {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → Site d}
    (hX : ∀ n, Measurable (X n)) (n : ℕ) (P : (ℕ → Site d) → Prop)
    (hP : ∀ x y : ℕ → Site d, (∀ j ≤ n, x j = y j) → (P x ↔ P y)) :
    MeasurableSet {ω | P (fun j => X j ω)} := by
  have h : {ω | P (fun j => X j ω)} = pastPath X n ⁻¹' {p | P (extendPath p)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact hP _ _ fun j hj => (extendPath_pastPath X hj ω).symm
  rw [h]
  exact measurable_pastPath hX n (MeasurableSet.of_discrete)

/-- Rescaling two processes by `c` rescales their predictable bracket by `c ^ 2`, almost
surely. -/
private lemma maxDynkin_predBracket_smul {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (Y Z : ℕ → Ω → ℝ) (c : ℝ) (n : ℕ) :
    predBracket μ ℱ (c • Y) (c • Z) n =ᵐ[μ] fun ω => c ^ 2 * predBracket μ ℱ Y Z n ω := by
  have h : ∀ t, μ[fun ω => ((c • Y) (t + 1) ω - (c • Y) t ω) *
        ((c • Z) (t + 1) ω - (c • Z) t ω) | ℱ t] =ᵐ[μ]
      fun ω => c ^ 2 * μ[fun ω => (Y (t + 1) ω - Y t ω) * (Z (t + 1) ω - Z t ω) | ℱ t] ω := by
    intro t
    have hfun : (fun ω => ((c • Y) (t + 1) ω - (c • Y) t ω) *
        ((c • Z) (t + 1) ω - (c • Z) t ω)) =
        (c ^ 2) • (fun ω => (Y (t + 1) ω - Y t ω) * (Z (t + 1) ω - Z t ω)) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun]
    exact condExp_smul (c ^ 2) _ _
  filter_upwards [ae_all_iff.mpr h] with ω hω
  simp only [predBracket, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => hω t

/-- Processes that agree almost surely at all times have almost surely equal predictable
brackets. -/
private lemma maxDynkin_predBracket_congr {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) {S S' T T' : ℕ → Ω → ℝ} (hS : ∀ᵐ ω ∂μ, ∀ t, S' t ω = S t ω)
    (hT : ∀ᵐ ω ∂μ, ∀ t, T' t ω = T t ω) (n : ℕ) :
    predBracket μ ℱ S' T' n =ᵐ[μ] predBracket μ ℱ S T n := by
  have h : ∀ t, μ[fun ω => (S' (t + 1) ω - S' t ω) * (T' (t + 1) ω - T' t ω) | ℱ t] =ᵐ[μ]
      μ[fun ω => (S (t + 1) ω - S t ω) * (T (t + 1) ω - T t ω) | ℱ t] := fun t =>
    condExp_congr_ae (by
      filter_upwards [hS, hT] with ω h1 h2
      simp only [h1, h2])
  filter_upwards [ae_all_iff.mpr h] with ω hω
  simp only [predBracket, Finset.sum_apply]
  exact Finset.sum_congr rfl fun t _ => hω t

/-- Lemma 9.1 (ii) for the normalized Dynkin martingales `-M^{f_i}/σ`: if the brackets are
controlled outside an event of probability at most `α`, then with probability at least
`1 - C (m⁻¹ e^{Cβ²} + β²δ + β³b + e^{Cβ²} √α)` some `-M^{f_i}_n/σ` is at least `c β`. -/
private theorem exists_max_dynkin_large (hexp : exp_deviation.{u}) (hd : 1 ≤ d) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1 / (d : ℝ)) {c₀ C₀ : ℝ} (hc₀ : 0 < c₀) (hcC : c₀ ≤ C₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d), IsCERW μ ε X →
      ∀ (m n : ℕ), 0 < m → 0 < n → ∀ (f : Fin m → Site d → ℝ) (σ B δ α β : ℝ),
      0 < σ → 0 < B → 0 ≤ δ → 0 ≤ α → α ≤ 1 →
      (∀ i x e, e ∈ unitSteps d → |f i (x + e) - f i x| ≤ B) →
      μ {ω | ¬ ∀ i j : Fin m,
          (i = j → c₀ ≤ dynkinBracket (stepProb d ε) (f i) (f j) (fun t => X t ω) n / σ ^ 2 ∧
            dynkinBracket (stepProb d ε) (f i) (f j) (fun t => X t ω) n / σ ^ 2 ≤ C₀) ∧
          (i ≠ j → |dynkinBracket (stepProb d ε) (f i) (f j) (fun t => X t ω) n / σ ^ 2| ≤ δ)}
        ≤ ENNReal.ofReal α →
      C ≤ β → β * (2 * B / σ) ≤ c → β ^ 2 * δ + β ^ 3 * (2 * B / σ) ≤ 1 →
      (μ {ω | ∀ i : Fin m, -dynkin ε (f i) X n ω / σ < c * β}).toReal ≤
        C * ((m : ℝ)⁻¹ * Real.exp (C * β ^ 2) + β ^ 2 * δ + β ^ 3 * (2 * B / σ) +
          Real.exp (C * β ^ 2) * Real.sqrt α) := by
  obtain ⟨c, C, hc, hC, H⟩ := hexp c₀ C₀ hc₀ hcC
  refine ⟨c, C, hc, hC, ?_⟩
  intro Ω _ μ _ X hX m n hm hn f σ B δ α β hσ hB hδ hα hα1 hfB hμE hCβ hβb hδβ
  have hb0 : 0 < 2 * B / σ := div_pos (by linarith) hσ
  have hS0m : ∀ i, Martingale ((-σ⁻¹) • dynkin ε (f i) X) (pathFiltration hX.measurable) μ :=
    fun i => (martingale_dynkin hd hε0 hε1 hX (f i)).smul _
  have hS0inc : ∀ i t, ∀ᵐ ω ∂μ,
      |((-σ⁻¹) • dynkin ε (f i) X) (t + 1) ω - ((-σ⁻¹) • dynkin ε (f i) X) t ω| ≤
        2 * B / σ := by
    intro i t
    filter_upwards [ae_abs_dynkin_succ_sub_le hd hε0 hε1 hX (f i)] with ω hω
    have h1 := hω t B fun e he => hfB i (X t ω) e he
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr hσ), ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right h1 hσ.le
  have hex : ∀ i, ∃ M' : ℕ → Ω → ℝ, Martingale M' (pathFiltration hX.measurable) μ ∧
      (∀ t ω, |M' (t + 1) ω - M' t ω| ≤ 2 * B / σ) ∧
      (∀ ω, M' 0 ω = ((-σ⁻¹) • dynkin ε (f i) X) 0 ω) ∧
      ∀ᵐ ω ∂μ, ∀ t, M' t ω = ((-σ⁻¹) • dynkin ε (f i) X) t ω :=
    fun i => CERW.Generic.Martingale.exists_martingale_clamp (hS0m i) hb0.le (hS0inc i)
  choose S hSm hSinc hS0 hSae using hex
  have hbr : ∀ i j, ∀ᵐ ω ∂μ, predBracket μ (pathFiltration hX.measurable) (S i) (S j) n ω =
      dynkinBracket (stepProb d ε) (f i) (f j) (fun t => X t ω) n / σ ^ 2 := by
    intro i j
    filter_upwards [maxDynkin_predBracket_congr μ (pathFiltration hX.measurable)
      (hSae i) (hSae j) n,
      maxDynkin_predBracket_smul μ (pathFiltration hX.measurable) (dynkin ε (f i) X)
        (dynkin ε (f j) X) (-σ⁻¹) n,
      ae_predBracket_dynkin hd hε0 hε1 hX (f i) (f j) n] with ω h1 h2 h3
    rw [h1, h2, h3]
    field_simp
  set E : Set Ω := {ω | ∀ i j : Fin m,
      (i = j → c₀ ≤ dynkinBracket (stepProb d ε) (f i) (f j) (fun t => X t ω) n / σ ^ 2 ∧
        dynkinBracket (stepProb d ε) (f i) (f j) (fun t => X t ω) n / σ ^ 2 ≤ C₀) ∧
      (i ≠ j → |dynkinBracket (stepProb d ε) (f i) (f j) (fun t => X t ω) n / σ ^ 2| ≤ δ)}
    with hE
  have hEmeas : MeasurableSet E := by
    refine maxDynkin_measurableSet hX.measurable n (fun x => ∀ i j : Fin m,
      (i = j → c₀ ≤ dynkinBracket (stepProb d ε) (f i) (f j) x n / σ ^ 2 ∧
        dynkinBracket (stepProb d ε) (f i) (f j) x n / σ ^ 2 ≤ C₀) ∧
      (i ≠ j → |dynkinBracket (stepProb d ε) (f i) (f j) x n / σ ^ 2| ≤ δ)) ?_
    intro x y hxy
    simp only [maxDynkin_dynkinBracket_congr ε _ _ hxy]
  have hEc : μ Eᶜ ≤ ENNReal.ofReal α := hμE
  have hE1 : 1 - α ≤ (μ E).toReal := by
    have h1 : μ Eᶜ = 1 - μ E := prob_compl_eq_one_sub hEmeas
    have h2 : (μ Eᶜ).toReal ≤ α := ENNReal.toReal_le_of_le_ofReal hα hEc
    rw [h1, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one] at h2
    linarith
  have hdiag : ∀ i, ∀ᵐ ω ∂μ, ω ∈ E →
      c₀ ≤ predBracket μ (pathFiltration hX.measurable) (S i) (S i) n ω ∧
        predBracket μ (pathFiltration hX.measurable) (S i) (S i) n ω ≤ C₀ := by
    intro i
    filter_upwards [hbr i i] with ω h1 hω
    rw [h1]
    exact (hω i i).1 rfl
  have hoff : ∀ i j, i ≠ j → ∀ᵐ ω ∂μ, ω ∈ E →
      |predBracket μ (pathFiltration hX.measurable) (S i) (S j) n ω| ≤ δ := by
    intro i j hij
    filter_upwards [hbr i j] with ω h1 hω
    rw [h1]
    exact (hω i j).2 hij
  have hmain := H μ (pathFiltration hX.measurable) m n hm hn (2 * B / σ) δ α hb0 hδ hα hα1 S hSm
    (fun i ω => by rw [hS0 i ω]; simp) (fun i t _ ω => hSinc i t ω) E hEmeas hE1 hdiag β hCβ hβb
  have hfinal := hmain.2 hoff hδβ
  have hset : {ω | ∀ i : Fin m, -dynkin ε (f i) X n ω / σ < c * β} =ᵐ[μ]
      {ω | ∀ i : Fin m, S i n ω < c * β} := by
    filter_upwards [ae_all_iff.mpr (fun i => hSae i)] with ω hω
    refine propext (forall_congr' fun i => ?_)
    rw [hω i n]
    simp only [Pi.smul_apply, smul_eq_mul]
    have h : -σ⁻¹ * dynkin ε (f i) X n ω = -dynkin ε (f i) X n ω / σ := by ring
    rw [h]
  rw [measure_congr hset]
  exact hfinal

/-- The scale `r n = (κ n)^{1/(d+1)}` tends to infinity. -/
private theorem scaleBasic_tendsto_scale {κ : ℝ} (hκ : 0 < κ) (r : ℕ → ℝ)
    (hr : ∀ n : ℕ, r n = (κ * n) ^ ((1 : ℝ) / (d + 1))) : Tendsto r atTop atTop := by
  have hp : (0 : ℝ) < 1 / ((d : ℝ) + 1) := by positivity
  have h1 : Tendsto (fun n : ℕ => κ * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hκ
  exact Tendsto.congr (fun n => (hr n).symm) ((tendsto_rpow_atTop hp).comp h1)

/-- For large `n` the scale `r n = (κ n)^{1/(d+1)}` is at most `n`. -/
private theorem scaleBasic_scale_le (hd : 1 ≤ d) {κ : ℝ} (hκ : 0 < κ) (r : ℕ → ℝ)
    (hr : ∀ n : ℕ, r n = (κ * n) ^ ((1 : ℝ) / (d + 1))) : ∀ᶠ n : ℕ in atTop, r n ≤ n := by
  filter_upwards [eventually_ge_atTop (⌈κ⌉₊ + 1)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hκn : κ ≤ n := (Nat.le_ceil κ).trans (by exact_mod_cast (by omega : ⌈κ⌉₊ ≤ n))
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hpow : κ * n ≤ (n : ℝ) ^ (d + 1) := by
    calc κ * n ≤ n * n := mul_le_mul_of_nonneg_right hκn hn0
      _ = (n : ℝ) ^ 2 := (sq (n : ℝ)).symm
      _ ≤ (n : ℝ) ^ (d + 1) := pow_le_pow_right₀ hn1 (by omega)
  rw [hr n]
  calc (κ * n) ^ ((1 : ℝ) / (d + 1)) ≤ ((n : ℝ) ^ (d + 1)) ^ ((1 : ℝ) / (d + 1)) :=
        Real.rpow_le_rpow (by positivity) hpow (by positivity)
    _ = n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
      have : ((d + 1 : ℕ) : ℝ) * (1 / ((d : ℝ) + 1)) = 1 := by
        push_cast
        field_simp
      rw [this, Real.rpow_one]

/-- For large `n`, `Cs n^{-10} ≤ 1`. -/
private theorem scaleBasic_const_rpow_le {Cs : ℝ} :
    ∀ᶠ n : ℕ in atTop, Cs * (n : ℝ) ^ (-(10 : ℝ)) ≤ 1 := by
  filter_upwards [eventually_ge_atTop (⌈Cs⌉₊ + 1)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hCs : Cs ≤ n := (Nat.le_ceil Cs).trans (by exact_mod_cast (by omega : ⌈Cs⌉₊ ≤ n))
  have hn0 : (0 : ℝ) < n := by linarith
  have h10 : (n : ℝ) ≤ (n : ℝ) ^ 10 := by
    calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n : ℝ) ^ 10 := pow_le_pow_right₀ hn1 (by norm_num)
  have : (n : ℝ) ^ (-(10 : ℝ)) = ((n : ℝ) ^ 10)⁻¹ := by
    rw [Real.rpow_neg hn0.le]
    norm_cast
  rw [this, ← div_eq_mul_inv, div_le_one (by positivity)]
  exact hCs.trans h10

/-- `√R ≤ σ` once `R ≥ 3`. -/
private theorem scaleBasic_sqrt_le_sigma (d : ℕ) {R : ℝ} (hR : 3 ≤ R) :
    Real.sqrt R ≤ sigmaOf d R := by
  unfold sigmaOf
  split_ifs
  · apply Real.sqrt_le_sqrt
    have h1 : 1 ≤ Real.log R := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    nlinarith
  · exact le_rfl

/-- The normalizer `σ` is positive for large `R`. -/
private theorem scaleBasic_sigma_pos (d : ℕ) : ∀ᶠ R : ℝ in atTop, 0 < sigmaOf d R := by
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with R hR
  exact lt_of_lt_of_le (Real.sqrt_pos.2 (by linarith)) (scaleBasic_sqrt_le_sigma d hR)

/-- For large `R`, the spacing `k = ⌊R^{1/8}⌋` is at least `1` and `k⁻¹ ≤ 2 R^{-1/8}`. -/
private theorem scaleBasic_kOf : ∀ᶠ R : ℝ in atTop,
    1 ≤ kOf R ∧ ((kOf R : ℕ) : ℝ)⁻¹ ≤ 2 * R ^ (-(1 : ℝ) / 8) := by
  filter_upwards [eventually_ge_atTop (256 : ℝ)] with R hR
  have hR0 : 0 < R := by linarith
  have ht : (2 : ℝ) ≤ R ^ ((1 : ℝ) / 8) := by
    have h8 : (2 : ℝ) = ((256 : ℝ)) ^ ((1 : ℝ) / 8) := by
      rw [show (256 : ℝ) = 2 ^ (8 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h8]
    exact Real.rpow_le_rpow (by norm_num) hR (by norm_num)
  have hk1 : 1 ≤ kOf R := by
    unfold kOf
    exact Nat.le_floor (by norm_num; linarith)
  refine ⟨hk1, ?_⟩
  have hlt : R ^ ((1 : ℝ) / 8) < (kOf R : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk : (1 : ℝ) ≤ (kOf R : ℝ) := by exact_mod_cast hk1
  have hneg : R ^ (-(1 : ℝ) / 8) = (R ^ ((1 : ℝ) / 8))⁻¹ := by
    rw [neg_div, Real.rpow_neg hR0.le]
  rw [hneg]
  have hhalf : R ^ ((1 : ℝ) / 8) / 2 ≤ (kOf R : ℝ) := by linarith
  calc ((kOf R : ℕ) : ℝ)⁻¹ ≤ (R ^ ((1 : ℝ) / 8) / 2)⁻¹ := inv_anti₀ (by linarith) hhalf
    _ = 2 * (R ^ ((1 : ℝ) / 8))⁻¹ := by field_simp

/-- For large `R`, `i ⌈R^{1/4}⌉ + k ≤ √R` for all `i ≤ k = ⌊R^{1/8}⌋`. -/
private theorem scaleBasic_sep : ∀ᶠ R : ℝ in atTop, ∀ i : ℕ, i ≤ kOf R →
    ((i * sepStep R : ℕ) : ℝ) + (kOf R : ℝ) ≤ Real.sqrt R := by
  filter_upwards [eventually_ge_atTop (256 : ℝ)] with R hR i hi
  have hR0 : 0 < R := by linarith
  set t : ℝ := R ^ ((1 : ℝ) / 8) with ht_def
  have ht : (2 : ℝ) ≤ t := by
    have h8 : (2 : ℝ) = ((256 : ℝ)) ^ ((1 : ℝ) / 8) := by
      rw [show (256 : ℝ) = 2 ^ (8 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [ht_def, h8]
    exact Real.rpow_le_rpow (by norm_num) hR (by norm_num)
  have ht0 : 0 ≤ t := by linarith
  have h4 : R ^ ((1 : ℝ) / 4) = t ^ 2 := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
    norm_num
  have hsq : Real.sqrt R = t ^ 4 := by
    rw [Real.sqrt_eq_rpow, ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
    norm_num
  have hk : (kOf R : ℝ) ≤ t := Nat.floor_le (by positivity)
  have hS : (sepStep R : ℝ) ≤ t ^ 2 + 1 := by
    have : (sepStep R : ℝ) < R ^ ((1 : ℝ) / 4) + 1 := Nat.ceil_lt_add_one (by positivity)
    rw [h4] at this
    exact this.le
  have hi' : (i : ℝ) ≤ kOf R := by exact_mod_cast hi
  have hS0 : (0 : ℝ) ≤ sepStep R := Nat.cast_nonneg _
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ kOf R := Nat.cast_nonneg _
  push_cast
  rw [hsq]
  have h1 : (i : ℝ) * sepStep R ≤ t * (t ^ 2 + 1) :=
    mul_le_mul (hi'.trans hk) hS hS0 ht0
  have h2 : t ^ 3 + 2 * t ≤ t ^ 4 := by
    have : t ^ 3 - t ^ 2 - 2 ≥ 0 := by nlinarith [sq_nonneg (t - 2), mul_nonneg ht0 ht0]
    nlinarith [mul_nonneg ht0 this]
  nlinarith

/-- For large `R`, `C ≤ β = (4 √C)⁻¹ √(log R)`. -/
private theorem scaleBasic_le_beta {C : ℝ} (hC : 0 < C) :
    ∀ᶠ R : ℝ in atTop, C ≤ betaOf C R := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (16 * C ^ 3)] with R hR
  have hs : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
  have h1 : 4 * Real.sqrt C * C ≤ Real.sqrt (Real.log R) := by
    apply Real.le_sqrt_of_sq_le
    have : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC.le
    calc (4 * Real.sqrt C * C) ^ 2 = 16 * (Real.sqrt C) ^ 2 * C ^ 2 := by ring
      _ = 16 * C ^ 3 := by rw [this]; ring
      _ ≤ Real.log R := hR
  unfold betaOf
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith

/-- Powers of `log R` are eventually dominated by any positive power of `R`. -/
private theorem scaleBasic_log_rpow_div_le (a : ℝ) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, Real.log R ^ a / R ^ c ≤ ε :=
  ((isLittleO_log_rpow_rpow_atTop a hc).tendsto_div_nhds_zero).eventually (Iic_mem_nhds hε)

/-- For large `R`, `β · (2 B / σ) ≤ c`. -/
private theorem scaleBasic_beta_mul (d : ℕ) {C B c : ℝ} (hC : 0 < C) (hB : 0 < B) (hc : 0 < c) :
    ∀ᶠ R : ℝ in atTop, betaOf C R * (2 * B / sigmaOf d R) ≤ c := by
  have hc₀ : 0 < 1 / (4 * Real.sqrt C) := by
    have : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
    positivity
  set c₀ : ℝ := 1 / (4 * Real.sqrt C) with hc₀_def
  have hK : 0 < c₀ * (2 * B) := by positivity
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    scaleBasic_log_rpow_div_le (1 / 2) (c := 1 / 2) (ε := c / (c₀ * (2 * B)))
      (by norm_num) (div_pos hc hK)] with R hR hlog
  have hR0 : 0 < R := by linarith
  have hσ := scaleBasic_sqrt_le_sigma d hR
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hβ : betaOf C R = c₀ * Real.sqrt (Real.log R) := rfl
  calc betaOf C R * (2 * B / sigmaOf d R)
      ≤ c₀ * Real.sqrt (Real.log R) * (2 * B / Real.sqrt R) := by
        rw [hβ]
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (by positivity) hsR hσ) (by positivity)
    _ = (c₀ * (2 * B)) * (Real.log R ^ ((1 : ℝ) / 2) / R ^ ((1 : ℝ) / 2)) := by
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        ring
    _ ≤ (c₀ * (2 * B)) * (c / (c₀ * (2 * B))) := mul_le_mul_of_nonneg_left hlog hK.le
    _ = c := by field_simp

/-- For large `R`, `β² (Cs R^{-1/4}) + β³ (2 B / σ) ≤ 1`. -/
private theorem scaleBasic_beta_sum (d : ℕ) {C B Cs : ℝ} (hC : 0 < C) (hB : 0 < B)
    (hCs : 0 < Cs) : ∀ᶠ R : ℝ in atTop,
    betaOf C R ^ 2 * (Cs * R ^ (-(1 : ℝ) / 4)) + betaOf C R ^ 3 * (2 * B / sigmaOf d R) ≤ 1 := by
  have hc₀ : 0 < 1 / (4 * Real.sqrt C) := by
    have : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
    positivity
  set c₀ : ℝ := 1 / (4 * Real.sqrt C) with hc₀_def
  have hK1 : 0 < c₀ ^ 2 * Cs := by positivity
  have hK2 : 0 < c₀ ^ 3 * (2 * B) := by positivity
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    scaleBasic_log_rpow_div_le 1 (c := 1 / 4) (ε := 1 / (2 * (c₀ ^ 2 * Cs)))
      (by norm_num) (by positivity),
    scaleBasic_log_rpow_div_le (3 / 2) (c := 1 / 2) (ε := 1 / (2 * (c₀ ^ 3 * (2 * B))))
      (by norm_num) (by positivity)] with R hR hlog1 hlog2
  have hR0 : 0 < R := by linarith
  have hL : 0 < Real.log R := Real.log_pos (by linarith)
  have hσ := scaleBasic_sqrt_le_sigma d hR
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hβ : betaOf C R = c₀ * Real.sqrt (Real.log R) := rfl
  have hsL : Real.sqrt (Real.log R) ^ 2 = Real.log R := Real.sq_sqrt hL.le
  have hneg : R ^ (-(1 : ℝ) / 4) = (R ^ ((1 : ℝ) / 4))⁻¹ := by
    rw [neg_div, Real.rpow_neg hR0.le]
  have h1 : betaOf C R ^ 2 * (Cs * R ^ (-(1 : ℝ) / 4)) =
      (c₀ ^ 2 * Cs) * (Real.log R ^ (1 : ℝ) / R ^ ((1 : ℝ) / 4)) := by
    rw [hβ, hneg, Real.rpow_one, mul_pow, hsL]
    field_simp
  have hpow3 : Real.sqrt (Real.log R) ^ 3 = Real.log R ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  have h2 : betaOf C R ^ 3 * (2 * B / sigmaOf d R) ≤
      (c₀ ^ 3 * (2 * B)) * (Real.log R ^ ((3 : ℝ) / 2) / R ^ ((1 : ℝ) / 2)) := by
    calc betaOf C R ^ 3 * (2 * B / sigmaOf d R)
        ≤ betaOf C R ^ 3 * (2 * B / Real.sqrt R) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left (by positivity) hsR hσ) (by rw [hβ]; positivity)
      _ = (c₀ ^ 3 * (2 * B)) * (Real.log R ^ ((3 : ℝ) / 2) / R ^ ((1 : ℝ) / 2)) := by
          rw [hβ, mul_pow, hpow3, Real.sqrt_eq_rpow]
          ring
  have h3 : (c₀ ^ 2 * Cs) * (Real.log R ^ (1 : ℝ) / R ^ ((1 : ℝ) / 4)) ≤ 1 / 2 := by
    calc (c₀ ^ 2 * Cs) * (Real.log R ^ (1 : ℝ) / R ^ ((1 : ℝ) / 4))
        ≤ (c₀ ^ 2 * Cs) * (1 / (2 * (c₀ ^ 2 * Cs))) := mul_le_mul_of_nonneg_left hlog1 hK1.le
      _ = 1 / 2 := by field_simp
  have h4 : (c₀ ^ 3 * (2 * B)) * (Real.log R ^ ((3 : ℝ) / 2) / R ^ ((1 : ℝ) / 2)) ≤ 1 / 2 := by
    calc (c₀ ^ 3 * (2 * B)) * (Real.log R ^ ((3 : ℝ) / 2) / R ^ ((1 : ℝ) / 2))
        ≤ (c₀ ^ 3 * (2 * B)) * (1 / (2 * (c₀ ^ 3 * (2 * B)))) :=
          mul_le_mul_of_nonneg_left hlog2 hK2.le
      _ = 1 / 2 := by field_simp
  rw [h1]
  linarith

/-- The elementary scale inequalities for large `n`, with `r n = (κ n)^{1/(d+1)}`. -/
private theorem scale_basic (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) (r : ℕ → ℝ)
    (hr : ∀ n : ℕ, r n = (κ * n) ^ ((1 : ℝ) / (d + 1))) {Cs CE cE B : ℝ} (hCs : 0 < Cs)
    (hCE : 0 < CE) (hcE : 0 < cE) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 4 ≤ r n ∧ r n ≤ n ∧ 0 < sigmaOf d (r n) ∧ 1 ≤ kOf (r n) ∧
      ((kOf (r n) : ℕ) : ℝ)⁻¹ ≤ 2 * r n ^ (-(1 : ℝ) / 8) ∧
      (∀ i : ℕ, i ≤ kOf (r n) →
        ((i * sepStep (r n) : ℕ) : ℝ) + (kOf (r n) : ℝ) ≤ Real.sqrt (r n)) ∧
      CE ≤ betaOf CE (r n) ∧
      betaOf CE (r n) * (2 * B / sigmaOf d (r n)) ≤ cE ∧
      betaOf CE (r n) ^ 2 * (Cs * r n ^ (-(1 : ℝ) / 4)) +
        betaOf CE (r n) ^ 3 * (2 * B / sigmaOf d (r n)) ≤ 1 ∧
      Cs * (n : ℝ) ^ (-(10 : ℝ)) ≤ 1 := by
  have htend : Tendsto r atTop atTop := scaleBasic_tendsto_scale hκ r hr
  filter_upwards [eventually_ge_atTop 2, htend.eventually (eventually_ge_atTop (4 : ℝ)),
    scaleBasic_scale_le (by omega) hκ r hr, htend.eventually (scaleBasic_sigma_pos d),
    htend.eventually scaleBasic_kOf, htend.eventually scaleBasic_sep,
    htend.eventually (scaleBasic_le_beta hCE), htend.eventually (scaleBasic_beta_mul d hCE hB hcE),
    htend.eventually (scaleBasic_beta_sum d hCE hB hCs),
    scaleBasic_const_rpow_le (Cs := Cs)] with n h2 h4 hle hσ hk hsep hβ hβmul hβsum hCsn
  exact ⟨h2, h4, hle, hσ, hk.1, hk.2, hsep, hβ, hβmul, hβsum, hCsn⟩

/-- `C β² = (log R)/16` for the deviation level `β`. -/
private theorem scaleFinal_mul_beta_sq {C : ℝ} (hC : 0 < C) {R : ℝ} (hR : 1 ≤ R) :
    C * betaOf C R ^ 2 = Real.log R / 16 := by
  have hL : 0 ≤ Real.log R := Real.log_nonneg hR
  unfold betaOf
  rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hC.le, Real.sq_sqrt hL]
  field_simp
  ring

/-- `exp (C β²) = R^{1/16}` for the deviation level `β`. -/
private theorem scaleFinal_exp_beta {C : ℝ} (hC : 0 < C) {R : ℝ} (hR : 1 ≤ R) :
    Real.exp (C * betaOf C R ^ 2) = R ^ ((1 : ℝ) / 16) := by
  rw [scaleFinal_mul_beta_sq hC hR, Real.rpow_def_of_pos (by linarith)]
  congr 1
  ring

/-- `1 ≤ log R` once `R ≥ 3`. -/
private theorem scaleFinal_one_le_log {R : ℝ} (hR : 3 ≤ R) : 1 ≤ Real.log R := by
  have h := Real.exp_one_lt_d9
  have : Real.exp 1 < R := by linarith
  exact ((Real.lt_log_iff_exp_lt (by linarith)).2 this).le

/-- The inverse of the spacing `k = ⌊R^{1/8}⌋` is at most `2 R^{-1/8}`. -/
private theorem scaleFinal_inv_kOf_le {R : ℝ} (hR : 1 ≤ R) :
    ((kOf R : ℕ) : ℝ)⁻¹ ≤ 2 * R ^ (-(1 : ℝ) / 8) := by
  have hx : 1 ≤ R ^ ((1 : ℝ) / 8) := Real.one_le_rpow hR (by norm_num)
  have hk1 : 1 ≤ kOf R := Nat.le_floor (by simpa using hx)
  have hlt : R ^ ((1 : ℝ) / 8) < (kOf R : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk : (1 : ℝ) ≤ kOf R := by exact_mod_cast hk1
  have hneg : R ^ (-(1 : ℝ) / 8) = (R ^ ((1 : ℝ) / 8))⁻¹ := by
    rw [← Real.rpow_neg (by linarith)]
    ring_nf
  rw [hneg]
  have hxpos : 0 < R ^ ((1 : ℝ) / 8) := by linarith
  have hk0 : (0 : ℝ) < kOf R := by linarith
  have h2 : (kOf R : ℝ)⁻¹ * R ^ ((1 : ℝ) / 8) ≤ 2 := by
    rw [inv_mul_le_iff₀ hk0]
    linarith
  calc ((kOf R : ℕ) : ℝ)⁻¹ = ((kOf R : ℝ)⁻¹ * R ^ ((1 : ℝ) / 8)) * (R ^ ((1 : ℝ) / 8))⁻¹ := by
        field_simp
    _ ≤ 2 * (R ^ ((1 : ℝ) / 8))⁻¹ := by gcongr

/-- `√R ≤ σ` once `R ≥ 3`. -/
private theorem scaleFinal_sqrt_le_sigma (d : ℕ) {R : ℝ} (hR : 3 ≤ R) :
    Real.sqrt R ≤ sigmaOf d R := by
  unfold sigmaOf
  split_ifs
  · apply Real.sqrt_le_sqrt
    have := scaleFinal_one_le_log hR
    nlinarith
  · exact le_rfl

/-- `log R ≤ 16 R^{1/16}`. -/
private theorem scaleFinal_log_le {R : ℝ} (hR : 0 ≤ R) :
    Real.log R ≤ 16 * R ^ ((1 : ℝ) / 16) := by
  have := Real.log_le_rpow_div hR (ε := 1 / 16) (by norm_num)
  linarith [this, show R ^ ((1 : ℝ) / 16) / (1 / 16) = 16 * R ^ ((1 : ℝ) / 16) by ring]

/-- If `κ N = R^{d+1}` with `R` large, then `R ≤ N`, `log N ≤ (d+2) log R` and
`log (N+2) ≤ (d+3) log R`. -/
private theorem scaleFinal_scale_bounds (hd : 1 ≤ d) {κ : ℝ} (hκ : 0 < κ) {R N : ℝ}
    (hR : 3 ≤ R) (hRκ : κ ≤ R) (hRκ' : κ⁻¹ ≤ R) (hN : κ * N = R ^ (d + 1)) :
    R ≤ N ∧ Real.log N ≤ ((d : ℝ) + 2) * Real.log R ∧
      Real.log (N + 2) ≤ ((d : ℝ) + 3) * Real.log R := by
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hpow : 0 < R ^ (d + 1) := pow_pos hR0 _
  have hN0 : 0 < N := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos hκ.le (not_lt.mp h)
    linarith
  have hRd : R ≤ R ^ d := by
    calc R = R ^ 1 := (pow_one R).symm
      _ ≤ R ^ d := pow_le_pow_right₀ hR1 hd
  have hRN : R ≤ N := by
    have h1 : κ * R ≤ κ * N := by
      rw [hN, pow_succ]
      calc κ * R ≤ R * R := by gcongr
        _ ≤ R ^ d * R := by gcongr
    exact le_of_mul_le_mul_left h1 hκ
  have hN1 : N ≤ R ^ (d + 2) := by
    have h1 : 1 ≤ R * κ := by
      calc (1 : ℝ) = κ⁻¹ * κ := by field_simp
        _ ≤ R * κ := by gcongr
    calc N = 1 * N := (one_mul N).symm
      _ ≤ (R * κ) * N := by gcongr
      _ = R * R ^ (d + 1) := by rw [← hN]; ring
      _ = R ^ (d + 2) := by ring
  have hN2 : N + 2 ≤ R ^ (d + 3) := by
    have h3 : (2 : ℝ) ≤ R := by linarith
    have hN2' : (2 : ℝ) ≤ N := by linarith
    calc N + 2 ≤ 2 * N := by linarith
      _ ≤ 2 * R ^ (d + 2) := by gcongr
      _ ≤ R * R ^ (d + 2) := by gcongr
      _ = R ^ (d + 3) := by ring
  refine ⟨hRN, ?_, ?_⟩
  · calc Real.log N ≤ Real.log (R ^ (d + 2)) := Real.log_le_log hN0 hN1
      _ = ((d : ℝ) + 2) * Real.log R := by rw [Real.log_pow]; push_cast; ring
  · calc Real.log (N + 2) ≤ Real.log (R ^ (d + 3)) := Real.log_le_log (by linarith) hN2
      _ = ((d : ℝ) + 3) * Real.log R := by rw [Real.log_pow]; push_cast; ring

/-- `√(N^{-10}) = N^{-5}`. -/
private theorem scaleFinal_sqrt_rpow_neg_ten {N : ℝ} (hN : 0 < N) :
    Real.sqrt (N ^ (-(10 : ℝ))) = N ^ (-(5 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN.le]
  norm_num

/-- `N^{-c} = κ^{c} R^{-1/32}` for `c = 1/(32 (d+1))`, `κ N = R^{d+1}`. -/
private theorem scaleFinal_rpow_scale {κ : ℝ} (hκ : 0 < κ) {R N : ℝ} (hR : 0 < R)
    (hN : κ * N = R ^ (d + 1)) :
    N ^ (-(1 / (32 * ((d : ℝ) + 1)))) = κ ^ (1 / (32 * ((d : ℝ) + 1))) * R ^ (-(1 / 32 : ℝ)) := by
  have hNeq : N = R ^ (d + 1) / κ := by
    field_simp
    linarith
  have hd1 : ((d : ℝ) + 1) ≠ 0 := by positivity
  rw [hNeq, Real.div_rpow (by positivity) hκ.le, ← Real.rpow_natCast, ← Real.rpow_mul hR.le,
    Real.rpow_neg hκ.le, div_inv_eq_mul, mul_comm]
  congr 2
  push_cast
  field_simp

/-- The spacing term: `C k⁻¹ R^{1/16} ≤ 2 C R^{-1/16}`. -/
private theorem scaleFinal_term_spacing {C : ℝ} (hC : 0 ≤ C) {R : ℝ} (hR : 1 ≤ R) :
    C * (((kOf R : ℕ) : ℝ)⁻¹ * R ^ ((1 : ℝ) / 16)) ≤ 2 * C * R ^ (-(1 : ℝ) / 16) := by
  have h1 : R ^ (-(1 : ℝ) / 8) * R ^ ((1 : ℝ) / 16) = R ^ (-(1 : ℝ) / 16) := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  calc C * (((kOf R : ℕ) : ℝ)⁻¹ * R ^ ((1 : ℝ) / 16))
      ≤ C * ((2 * R ^ (-(1 : ℝ) / 8)) * R ^ ((1 : ℝ) / 16)) := by
        gcongr
        exact scaleFinal_inv_kOf_le hR
    _ = 2 * C * R ^ (-(1 : ℝ) / 16) := by rw [← h1]; ring

/-- The bracket term `C β² (Cs R^{-1/4}) ≤ Cs R^{-1/16}`. -/
private theorem scaleFinal_term_bracket {C Cs : ℝ} (hC : 0 < C) (hCs : 0 ≤ Cs) {R : ℝ}
    (hR : 3 ≤ R) :
    C * (betaOf C R ^ 2 * (Cs * R ^ (-(1 : ℝ) / 4))) ≤ Cs * R ^ (-(1 : ℝ) / 16) := by
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hp : Real.log R / 16 ≤ R ^ ((1 : ℝ) / 16) := by linarith [scaleFinal_log_le hR0.le]
  have h2 : R ^ ((1 : ℝ) / 16) * R ^ (-(1 : ℝ) / 4) ≤ R ^ (-(1 : ℝ) / 16) := by
    rw [← Real.rpow_add hR0]
    exact Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  calc C * (betaOf C R ^ 2 * (Cs * R ^ (-(1 : ℝ) / 4)))
      = (C * betaOf C R ^ 2) * (Cs * R ^ (-(1 : ℝ) / 4)) := by ring
    _ = Real.log R / 16 * (Cs * R ^ (-(1 : ℝ) / 4)) := by rw [scaleFinal_mul_beta_sq hC hR1]
    _ ≤ R ^ ((1 : ℝ) / 16) * (Cs * R ^ (-(1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
    _ = Cs * (R ^ ((1 : ℝ) / 16) * R ^ (-(1 : ℝ) / 4)) := by ring
    _ ≤ Cs * R ^ (-(1 : ℝ) / 16) := mul_le_mul_of_nonneg_left h2 hCs

/-- The term `C β³ (2B/σ) ≤ (8 B/√C) R^{-1/16}`. -/
private theorem scaleFinal_term_cube (d : ℕ) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) {R : ℝ}
    (hR : 3 ≤ R) :
    C * (betaOf C R ^ 3 * (2 * B / sigmaOf d R)) ≤
      (8 * B / Real.sqrt C) * R ^ (-(1 : ℝ) / 16) := by
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hsq0 : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hsC : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
  have hL1 : 1 ≤ Real.log R := scaleFinal_one_le_log hR
  have hp : Real.log R / 16 ≤ R ^ ((1 : ℝ) / 16) := by linarith [scaleFinal_log_le hR0.le]
  have h3 : R ^ ((1 : ℝ) / 16) * R ^ ((1 : ℝ) / 16) * R ^ (-(1 : ℝ) / 2) ≤
      R ^ (-(1 : ℝ) / 16) := by
    rw [← Real.rpow_add hR0, ← Real.rpow_add hR0]
    exact Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  have hsL : Real.sqrt (Real.log R) ≤ Real.log R := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  have hβle : betaOf C R ≤ (1 / (4 * Real.sqrt C)) * (16 * R ^ ((1 : ℝ) / 16)) := by
    calc betaOf C R = (1 / (4 * Real.sqrt C)) * Real.sqrt (Real.log R) := rfl
      _ ≤ (1 / (4 * Real.sqrt C)) * Real.log R := by gcongr
      _ ≤ (1 / (4 * Real.sqrt C)) * (16 * R ^ ((1 : ℝ) / 16)) := by
        gcongr
        exact scaleFinal_log_le hR0.le
  have hβ0 : 0 ≤ betaOf C R := mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hσq : 2 * B / sigmaOf d R ≤ 2 * B * R ^ (-(1 : ℝ) / 2) := by
    have : R ^ (-(1 : ℝ) / 2) = (Real.sqrt R)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hR0.le]
      ring_nf
    rw [this, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by positivity) hsq0 (scaleFinal_sqrt_le_sigma d hR)
  have hσ0 : 0 ≤ 2 * B / sigmaOf d R :=
    div_nonneg (by positivity) (le_trans hsq0.le (scaleFinal_sqrt_le_sigma d hR))
  have hprod : (Real.log R / 16) * betaOf C R * (2 * B / sigmaOf d R) ≤
      R ^ ((1 : ℝ) / 16) * ((1 / (4 * Real.sqrt C)) * (16 * R ^ ((1 : ℝ) / 16))) *
        (2 * B * R ^ (-(1 : ℝ) / 2)) :=
    mul_le_mul (mul_le_mul hp hβle hβ0 (by positivity)) hσq hσ0 (by positivity)
  calc C * (betaOf C R ^ 3 * (2 * B / sigmaOf d R))
      = ((C * betaOf C R ^ 2) * betaOf C R) * (2 * B / sigmaOf d R) := by ring
    _ = (Real.log R / 16) * betaOf C R * (2 * B / sigmaOf d R) := by
        rw [scaleFinal_mul_beta_sq hC hR1]
    _ ≤ R ^ ((1 : ℝ) / 16) * ((1 / (4 * Real.sqrt C)) * (16 * R ^ ((1 : ℝ) / 16))) *
        (2 * B * R ^ (-(1 : ℝ) / 2)) := hprod
    _ = (8 * B / Real.sqrt C) *
        (R ^ ((1 : ℝ) / 16) * R ^ ((1 : ℝ) / 16) * R ^ (-(1 : ℝ) / 2)) := by
        field_simp
        ring
    _ ≤ (8 * B / Real.sqrt C) * R ^ (-(1 : ℝ) / 16) := by gcongr

/-- The terms involving the time `N ≥ R`: `C R^{1/16} √(Cs N^{-10}) + (Cs + Cu) N^{-10} ≤
(C √Cs + Cs + Cu) R^{-1/16}`. -/
private theorem scaleFinal_term_time {C Cs Cu : ℝ} (hC : 0 ≤ C) (hCs : 0 < Cs) (hCu : 0 ≤ Cu)
    {R N : ℝ} (hR : 1 ≤ R) (hRN : R ≤ N) :
    C * (R ^ ((1 : ℝ) / 16) * Real.sqrt (Cs * N ^ (-(10 : ℝ)))) +
        Cs * N ^ (-(10 : ℝ)) + Cu * N ^ (-(10 : ℝ)) ≤
      (C * Real.sqrt Cs + Cs + Cu) * R ^ (-(1 : ℝ) / 16) := by
  have hR0 : 0 < R := by linarith
  have hN0 : 0 < N := by linarith
  have h4 : R ^ ((1 : ℝ) / 16) * R ^ (-(5 : ℝ)) ≤ R ^ (-(1 : ℝ) / 16) := by
    rw [← Real.rpow_add hR0]
    exact Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
  have h5 : R ^ (-(10 : ℝ)) ≤ R ^ (-(1 : ℝ) / 16) :=
    Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
  have hN5 : Real.sqrt (Cs * N ^ (-(10 : ℝ))) ≤ Real.sqrt Cs * R ^ (-(5 : ℝ)) := by
    rw [Real.sqrt_mul hCs.le, scaleFinal_sqrt_rpow_neg_ten hN0]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hR0 hRN (by norm_num))
      (Real.sqrt_nonneg _)
  have hN10 : N ^ (-(10 : ℝ)) ≤ R ^ (-(10 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hR0 hRN (by norm_num)
  have hT4 : C * (R ^ ((1 : ℝ) / 16) * Real.sqrt (Cs * N ^ (-(10 : ℝ)))) ≤
      C * Real.sqrt Cs * R ^ (-(1 : ℝ) / 16) := by
    calc C * (R ^ ((1 : ℝ) / 16) * Real.sqrt (Cs * N ^ (-(10 : ℝ))))
        ≤ C * (R ^ ((1 : ℝ) / 16) * (Real.sqrt Cs * R ^ (-(5 : ℝ)))) := by gcongr
      _ = C * Real.sqrt Cs * (R ^ ((1 : ℝ) / 16) * R ^ (-(5 : ℝ))) := by ring
      _ ≤ C * Real.sqrt Cs * R ^ (-(1 : ℝ) / 16) := by gcongr
  have hT5 : Cs * N ^ (-(10 : ℝ)) ≤ Cs * R ^ (-(1 : ℝ) / 16) :=
    mul_le_mul_of_nonneg_left (hN10.trans h5) hCs.le
  have hT6 : Cu * N ^ (-(10 : ℝ)) ≤ Cu * R ^ (-(1 : ℝ) / 16) :=
    mul_le_mul_of_nonneg_left (hN10.trans h5) hCu
  linarith

/-- Absorbing a constant: if `R^{-1/32} < δ / K` then `K R^{-1/16} ≤ δ R^{-1/32}`. -/
private theorem scaleFinal_absorb {K δ R : ℝ} (hK : 0 < K) (hR : 0 < R)
    (hw : R ^ (-(1 / 32 : ℝ)) < δ / K) :
    K * R ^ (-(1 : ℝ) / 16) ≤ δ * R ^ (-(1 / 32 : ℝ)) := by
  have hw0 : 0 < R ^ (-(1 / 32 : ℝ)) := Real.rpow_pos_of_pos hR _
  have h6 : R ^ (-(1 : ℝ) / 16) = R ^ (-(1 / 32 : ℝ)) * R ^ (-(1 / 32 : ℝ)) := by
    rw [← Real.rpow_add hR]
    norm_num
  have hKδ : K * (δ / K) = δ := by field_simp
  calc K * R ^ (-(1 : ℝ) / 16) = K * (R ^ (-(1 / 32 : ℝ)) * R ^ (-(1 / 32 : ℝ))) := by rw [h6]
    _ ≤ K * ((δ / K) * R ^ (-(1 / 32 : ℝ))) := by gcongr
    _ = δ * R ^ (-(1 / 32 : ℝ)) := by rw [← mul_assoc, hKδ]

/-- Part (a) of `scale_final` in terms of the scale `R` and the time `N` with `κ N = R^{d+1}`. -/
private theorem scaleFinal_a_real (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {Cs CE B Cu : ℝ}
    (hCs : 0 < Cs) (hCE : 0 < CE) (hB : 0 < B) (hCu : 0 ≤ Cu) :
    ∀ᶠ R : ℝ in atTop, ∀ N : ℝ, κ * N = R ^ (d + 1) →
      CE * (((kOf R : ℕ) : ℝ)⁻¹ * Real.exp (CE * betaOf CE R ^ 2) +
          betaOf CE R ^ 2 * (Cs * R ^ (-(1 : ℝ) / 4)) +
          betaOf CE R ^ 3 * (2 * B / sigmaOf d R) +
          Real.exp (CE * betaOf CE R ^ 2) * Real.sqrt (Cs * N ^ (-(10 : ℝ)))) +
        Cs * N ^ (-(10 : ℝ)) + Cu * N ^ (-(10 : ℝ)) ≤
        N ^ (-(1 / (32 * ((d : ℝ) + 1)))) := by
  have hKpos : 0 < 2 * CE + Cs + 8 * B / Real.sqrt CE + (CE * Real.sqrt Cs + Cs + Cu) := by
    positivity
  have hδ : 0 < κ ^ (1 / (32 * ((d : ℝ) + 1))) /
      (2 * CE + Cs + 8 * B / Real.sqrt CE + (CE * Real.sqrt Cs + Cs + Cu)) := by positivity
  filter_upwards [eventually_ge_atTop (max 3 (max κ κ⁻¹)),
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 32)).eventually (gt_mem_nhds hδ)]
    with R hR hw N hN
  have hR3 : 3 ≤ R := le_trans (le_max_left _ _) hR
  have hRκ : κ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hRκ' : κ⁻¹ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  obtain ⟨hRN, -, -⟩ := scaleFinal_scale_bounds (d := d) (by omega) hκ hR3 hRκ hRκ' hN
  have hfin := scaleFinal_absorb hKpos hR0 hw
  have hT1 := scaleFinal_term_spacing hCE.le hR1
  have hT2 := scaleFinal_term_bracket hCE hCs.le hR3
  have hT3 := scaleFinal_term_cube d hCE hB hR3
  have hT4 := scaleFinal_term_time hCE.le hCs hCu hR1 hRN
  rw [scaleFinal_exp_beta hCE hR1, scaleFinal_rpow_scale hκ hR0 hN]
  linarith

/-- For `d = 2`: `σ c_E β / 2 = (c_E / (8 √C)) √R (log R)`, where `σ = √(R log R)`. -/
private theorem scaleFinal_sigma_beta_two {d : ℕ} (h2 : d = 2) {C c R : ℝ} (hC : 0 < C)
    (hR : 0 ≤ R) :
    sigmaOf d R * (c * betaOf C R) / 2 =
      c / (8 * Real.sqrt C) * (Real.sqrt R * Real.sqrt (Real.log R) ^ 2) := by
  have hsC : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
  simp only [sigmaOf, if_pos h2, betaOf]
  rw [Real.sqrt_mul hR]
  field_simp
  ring

/-- For `d ≥ 3`: `σ c_E β / 2 = (c_E / (8 √C)) √R (log R)^{1/2}`, where `σ = √R`. -/
private theorem scaleFinal_sigma_beta_ne_two {d : ℕ} (h2 : d ≠ 2) {C c R : ℝ} (hC : 0 < C) :
    sigmaOf d R * (c * betaOf C R) / 2 =
      c / (8 * Real.sqrt C) * (Real.sqrt R * Real.sqrt (Real.log R)) := by
  have hsC : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
  simp only [sigmaOf, if_neg h2, betaOf]
  field_simp
  ring

/-- `√(R x) ≤ √R √L D` when `x ≤ D L` and `D ≥ 1`. -/
private theorem scaleFinal_sqrt_bound {R L D x : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hD : 1 ≤ D)
    (hx : x ≤ D * L) : Real.sqrt (R * x) ≤ Real.sqrt R * Real.sqrt L * D := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hDD : D ≤ D ^ 2 := by nlinarith
  calc R * x ≤ R * (D * L) := mul_le_mul_of_nonneg_left hx hR
    _ ≤ R * (D ^ 2 * L) := by gcongr
    _ = (Real.sqrt R * Real.sqrt L * D) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hR, Real.sq_sqrt hL]
      ring

/-- The algebraic core of part (b) for `d = 2`. -/
private theorem scaleFinal_b_two_alg {γ D Cpt Cu a ℓ x y w : ℝ} (hγ : 0 < γ) (hD : 1 ≤ D)
    (hCpt : 0 ≤ Cpt) (hCu : 0 ≤ Cu) (ha : 0 < a) (hℓ : 0 < ℓ) (hx : x ≤ D * ℓ ^ 2)
    (hy : y ≤ (D + 1) * ℓ ^ 2) (hw : w ≤ a * ℓ * D) (h1 : 4 * Cpt * (D + 1) / γ ≤ a)
    (h2 : 4 * Cu * D / γ ≤ ℓ) :
    γ / (4 * D) * (a * x) ≤ γ * (a * ℓ ^ 2) - (Cpt * y + Cu * w) := by
  have hD0 : 0 < D := by linarith
  have hm0 : 0 ≤ γ * (a * ℓ ^ 2) := by positivity
  have hA : γ / (4 * D) * (a * x) ≤ γ / 4 * (a * ℓ ^ 2) := by
    calc γ / (4 * D) * (a * x) ≤ γ / (4 * D) * (a * (D * ℓ ^ 2)) := by gcongr
      _ = γ / 4 * (a * ℓ ^ 2) := by field_simp
  have hCpt' : Cpt * (D + 1) ≤ γ / 4 * a := by
    rw [div_le_iff₀ hγ] at h1
    linarith
  have hB : Cpt * y ≤ γ / 4 * (a * ℓ ^ 2) := by
    calc Cpt * y ≤ Cpt * ((D + 1) * ℓ ^ 2) := by gcongr
      _ = (Cpt * (D + 1)) * ℓ ^ 2 := by ring
      _ ≤ (γ / 4 * a) * ℓ ^ 2 := by gcongr
      _ = γ / 4 * (a * ℓ ^ 2) := by ring
  have hCu' : Cu * D ≤ γ / 4 * ℓ := by
    rw [div_le_iff₀ hγ] at h2
    linarith
  have hC : Cu * w ≤ γ / 4 * (a * ℓ ^ 2) := by
    calc Cu * w ≤ Cu * (a * ℓ * D) := by gcongr
      _ = (Cu * D) * (a * ℓ) := by ring
      _ ≤ (γ / 4 * ℓ) * (a * ℓ) := by gcongr
      _ = γ / 4 * (a * ℓ ^ 2) := by ring
  linarith

/-- The algebraic core of part (b) for `d ≥ 3`. -/
private theorem scaleFinal_b_three_alg {γ D Cpt Cu a ℓ x y w : ℝ} (hγ : 0 < γ) (hD : 1 ≤ D)
    (hCpt : 0 ≤ Cpt) (hCu : 0 ≤ Cu) (ha : 0 < a) (hℓ : 0 < ℓ) (hx : x ≤ D * ℓ ^ 2)
    (hy : y ≤ (D + 1) * ℓ ^ 2) (hw : w ≤ a * ℓ * D) (hLa : ℓ ^ 2 ≤ 2 * a)
    (h3 : 8 * ((Cpt + Cu) * (D + 1)) ^ 2 / γ ^ 2 ≤ a) :
    γ / (4 * D) * w ≤ γ * (a * ℓ) - (Cpt * y + Cu * x) := by
  have hD0 : 0 < D := by linarith
  have hm1 : 0 ≤ γ * (a * ℓ) := by positivity
  have hA : γ / (4 * D) * w ≤ γ / 4 * (a * ℓ) := by
    calc γ / (4 * D) * w ≤ γ / (4 * D) * (a * ℓ * D) := by gcongr
      _ = γ / 4 * (a * ℓ) := by field_simp
  have hSℓ : (Cpt + Cu) * (D + 1) * ℓ ≤ γ / 2 * a := by
    have hγ2 : 0 < γ ^ 2 := by positivity
    rw [div_le_iff₀ hγ2] at h3
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    calc ((Cpt + Cu) * (D + 1) * ℓ) ^ 2 = ((Cpt + Cu) * (D + 1)) ^ 2 * ℓ ^ 2 := by
          rw [mul_pow]
      _ ≤ ((Cpt + Cu) * (D + 1)) ^ 2 * (2 * a) := by gcongr
      _ = (2 * ((Cpt + Cu) * (D + 1)) ^ 2) * a := by ring
      _ ≤ (γ ^ 2 * a / 4) * a := by
        apply mul_le_mul_of_nonneg_right _ ha.le
        linarith
      _ = (γ / 2 * a) ^ 2 := by ring
  have hxℓ : x ≤ (D + 1) * ℓ ^ 2 := hx.trans (by gcongr; linarith)
  have hCC : Cpt * y + Cu * x ≤ γ / 2 * (a * ℓ) := by
    calc Cpt * y + Cu * x ≤ Cpt * ((D + 1) * ℓ ^ 2) + Cu * ((D + 1) * ℓ ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hy hCpt) (mul_le_mul_of_nonneg_left hxℓ hCu)
      _ = ((Cpt + Cu) * (D + 1) * ℓ) * ℓ := by ring
      _ ≤ (γ / 2 * a) * ℓ := by gcongr
      _ = γ / 2 * (a * ℓ) := by ring
  linarith

/-- Part (b) of `scale_final` in terms of the scale `R` and the time `N` with `κ N = R^{d+1}`. -/
private theorem scaleFinal_b_real (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {CE cE Cpt Cu : ℝ}
    (hCE : 0 < CE) (hcE : 0 < cE) (hCpt : 0 ≤ Cpt) (hCu : 0 ≤ Cu) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ R : ℝ in atTop, ∀ N : ℝ, κ * N = R ^ (d + 1) →
      c * (if d = 2 then Real.sqrt R * Real.log N else Real.sqrt (R * Real.log N)) ≤
        sigmaOf d R * (cE * betaOf CE R) / 2 -
          (Cpt * Real.log (N + 2) +
            Cu * (if d = 2 then Real.sqrt (R * Real.log N) else Real.log N)) := by
  have hsCE : 0 < Real.sqrt CE := Real.sqrt_pos.2 hCE
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = cE / (8 * Real.sqrt CE) := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by rw [hγ]; positivity
  have hD1 : (1 : ℝ) ≤ (d : ℝ) + 2 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hD0 : (0 : ℝ) < (d : ℝ) + 2 := by linarith
  refine ⟨γ / (4 * ((d : ℝ) + 2)), by positivity, ?_⟩
  have hM1 : ∀ᶠ R : ℝ in atTop,
      max (4 * Cpt * (((d : ℝ) + 2) + 1) / γ)
        (8 * ((Cpt + Cu) * (((d : ℝ) + 2) + 1)) ^ 2 / γ ^ 2) ≤ Real.sqrt R :=
    Real.tendsto_sqrt_atTop.eventually_ge_atTop _
  have hM2 : ∀ᶠ R : ℝ in atTop, 4 * Cu * ((d : ℝ) + 2) / γ ≤ Real.sqrt (Real.log R) :=
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (max 3 (max κ κ⁻¹)), hM1, hM2] with R hR hM1 hM2 N hN
  have hR3 : 3 ≤ R := le_trans (le_max_left _ _) hR
  have hRκ : κ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hRκ' : κ⁻¹ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  have hR0 : 0 < R := by linarith
  obtain ⟨-, hx, hy⟩ := scaleFinal_scale_bounds (d := d) (by omega) hκ hR3 hRκ hRκ' hN
  have hL1 : 1 ≤ Real.log R := scaleFinal_one_le_log hR3
  have hL0 : 0 ≤ Real.log R := by linarith
  have ha0 : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hℓ0 : 0 < Real.sqrt (Real.log R) := Real.sqrt_pos.2 (by linarith)
  have hx' : Real.log N ≤ ((d : ℝ) + 2) * Real.sqrt (Real.log R) ^ 2 := by
    rw [Real.sq_sqrt hL0]
    exact hx
  have hy' : Real.log (N + 2) ≤ (((d : ℝ) + 2) + 1) * Real.sqrt (Real.log R) ^ 2 := by
    rw [Real.sq_sqrt hL0]
    calc Real.log (N + 2) ≤ ((d : ℝ) + 3) * Real.log R := hy
      _ = (((d : ℝ) + 2) + 1) * Real.log R := by ring
  have hw := scaleFinal_sqrt_bound hR0.le hL0 hD1 hx
  by_cases h2 : d = 2
  · simp only [if_pos h2]
    rw [scaleFinal_sigma_beta_two h2 hCE hR0.le, ← hγ]
    exact scaleFinal_b_two_alg hγ0 hD1 hCpt hCu ha0 hℓ0 hx' hy' hw
      (le_trans (le_max_left _ _) hM1) hM2
  · simp only [if_neg h2]
    rw [scaleFinal_sigma_beta_ne_two h2 hCE, ← hγ]
    have hLa : Real.sqrt (Real.log R) ^ 2 ≤ 2 * Real.sqrt R := by
      have := Real.log_le_rpow_div hR0.le (ε := 1 / 2) (by norm_num)
      rw [← Real.sqrt_eq_rpow] at this
      rw [Real.sq_sqrt hL0]
      linarith
    exact scaleFinal_b_three_alg hγ0 hD1 hCpt hCu ha0 hℓ0 hx' hy' hw hLa
      (le_trans (le_max_right _ _) hM1)
/-- The final scale inequalities for large `n`: the failure probability is at most `n^{-c}`, and
the deviation `σ c_E β / 2` exceeds the error terms by `c` times the scale of the bound. -/
private theorem scale_final (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) (r : ℕ → ℝ)
    (hr : ∀ n : ℕ, r n = (κ * n) ^ ((1 : ℝ) / (d + 1))) {Cs CE cE B Cpt Cu : ℝ} (hCs : 0 < Cs)
    (hCE : 0 < CE) (hcE : 0 < cE) (hB : 0 < B) (hCpt : 0 ≤ Cpt) (hCu : 0 ≤ Cu) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      CE * (((kOf (r n) : ℕ) : ℝ)⁻¹ * Real.exp (CE * betaOf CE (r n) ^ 2) +
          betaOf CE (r n) ^ 2 * (Cs * r n ^ (-(1 : ℝ) / 4)) +
          betaOf CE (r n) ^ 3 * (2 * B / sigmaOf d (r n)) +
          Real.exp (CE * betaOf CE (r n) ^ 2) * Real.sqrt (Cs * (n : ℝ) ^ (-(10 : ℝ)))) +
        Cs * (n : ℝ) ^ (-(10 : ℝ)) + Cu * (n : ℝ) ^ (-(10 : ℝ)) ≤ (n : ℝ) ^ (-c) ∧
      c * (if d = 2 then Real.sqrt (r n) * Real.log n else Real.sqrt (r n * Real.log n)) ≤
        sigmaOf d (r n) * (cE * betaOf CE (r n)) / 2 -
          (Cpt * Real.log ((n : ℝ) + 2) +
            Cu * (if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n)) := by
  have hrn : ∀ n : ℕ, κ * (n : ℝ) = r n ^ (d + 1) := fun n => by
    rw [hr n, Geometry.rpow_inv_succ_pow d (by positivity)]
  have hrt : Tendsto r atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => κ * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hκ
    have h2 := (tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / ((d : ℝ) + 1))).comp h1
    exact h2.congr (fun n => (hr n).symm)
  obtain ⟨c₂, hc₂, h₂⟩ := scaleFinal_b_real hd hκ hCE hcE hCpt hCu
  have h₁ := scaleFinal_a_real hd hκ hCs hCE hB hCu
  refine ⟨min (1 / (32 * ((d : ℝ) + 1))) c₂, lt_min (by positivity) hc₂, ?_⟩
  filter_upwards [eventually_ge_atTop 1, hrt.eventually h₁, hrt.eventually h₂] with n hn h1 h2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨(h1 n (hrn n)).trans ?_, ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg (min_le_left _ _))
  · have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hΛ : 0 ≤ (if d = 2 then Real.sqrt (r n) * Real.log n
        else Real.sqrt (r n * Real.log n)) := by
      split_ifs
      · exact mul_nonneg (Real.sqrt_nonneg _) hlog
      · exact Real.sqrt_nonneg _
    calc min (1 / (32 * ((d : ℝ) + 1))) c₂ * (if d = 2 then Real.sqrt (r n) * Real.log n
          else Real.sqrt (r n * Real.log n))
        ≤ c₂ * (if d = 2 then Real.sqrt (r n) * Real.log n
          else Real.sqrt (r n * Real.log n)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hΛ
      _ ≤ _ := h2 n (hrn n)

/-- At distance at least `ρ` from `v`, the potential's integrand is at most `ρ^{1-d}`. -/
private lemma bulkPotential_abs_potentialIntegrand_le_inv_pow (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 < ρ)
    {v z : EuclideanSpace ℝ (Fin d)} (hvz : ρ ≤ ‖v - z‖) :
    |inner ℝ (unitDir v) (v - z) / ‖v - z‖ ^ d| ≤ (ρ ^ (d - 1))⁻¹ := by
  refine (Geometry.abs_potentialIntegrand_le v z).trans ?_
  have hw : 0 < ‖v - z‖ := hρ.trans_le hvz
  have h : ‖v - z‖ ^ (1 - (d : ℝ)) = (‖v - z‖ ^ (d - 1))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hw.le]
    congr 1
    rw [Nat.cast_sub hd]
    push_cast
    ring
  rw [h]
  exact inv_anti₀ (pow_pos hρ _) (pow_le_pow_left₀ hρ.le hvz _)

/-- The potential of a bounded measurable set `D` differs from that of `B(0, r)` at a point `z`
at distance at least `ρ` from `D ∆ B(0, r)` by at most `(2ε / ω_d) ρ^{1-d} |D ∆ B(0, r)|`. -/
private theorem bulkPotential_abs_potential_sub_ball_le (hd : 2 ≤ d) {ε r ρ m : ℝ} (hε : 0 < ε)
    (hρ : 0 < ρ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) {z : EuclideanSpace ℝ (Fin d)}
    (hfar : ∀ v ∈ D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ρ ≤ ‖v - z‖)
    (hm : (volume (D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)).toReal ≤ m) :
    |potential d ε D z - potential d ε (Metric.ball 0 r) z| ≤
      2 * ε / unitBallVolume d * ((ρ ^ (d - 1))⁻¹ * m) := by
  have hω := unitBallVolume_pos d
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hM0 : 0 ≤ (ρ ^ (d - 1))⁻¹ := by positivity
  exact (Geometry.abs_potential_sub_ball_le_of_integrand_le hd hε.le hD hDb (z := z) (r := r)
    (M := (ρ ^ (d - 1))⁻¹)
    (fun v hv => bulkPotential_abs_potentialIntegrand_le_inv_pow (by omega) hρ
      (hfar v hv))).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm hM0) hc)

/-- Every point of `D_n ∆ B(0, r)` has norm at least `r - A` when `r - A ≤ R_in(n)` and
`A ≥ 0`. -/
private lemma bulkPotential_le_norm_of_mem_symmDiff {X : ℕ → Site d} {n : ℕ} {r A : ℝ}
    (hA : 0 ≤ A) (hin : r - A ≤ innerRadius X n) {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ cellSet X n ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) : r - A ≤ ‖v‖ := by
  rcases Set.mem_symmDiff.mp hv with ⟨_, hvB⟩ | ⟨_, hvD⟩
  · have h1 : r ≤ ‖v‖ := not_lt.mp (fun h => hvB (mem_ball_zero_iff.mpr h))
    linarith
  · have h2 : innerRadius X n ≤ ‖v‖ :=
      csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact norm_nonneg w⟩ ⟨v, hvD, rfl⟩
    linarith

/-- For `ρ > 0` and `t > 0`, `((t ρ)^{d-1})⁻¹ ρ^d = (t^{d-1})⁻¹ ρ` when `d ≥ 1`. -/
private lemma bulkPotential_inv_mul_pow_mul_pow (hd : 1 ≤ d) {t ρ : ℝ} (ht : 0 < t)
    (hρ : 0 < ρ) : ((t * ρ) ^ (d - 1))⁻¹ * ρ ^ d = (t ^ (d - 1))⁻¹ * ρ := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel, mul_pow, pow_succ ρ k]
  have : 0 < t ^ k := pow_pos ht k
  have : 0 < ρ ^ k := pow_pos hρ k
  field_simp

/-- `log n` is eventually at most `c (κ n)^{1/(d+1)}`, for every `c > 0`. -/
private lemma bulkPotential_eventually_log_le_mul (d : ℕ) {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log n ≤ c * (κ * n) ^ ((1 : ℝ) / (d + 1)) := by
  have hs : (0 : ℝ) < 1 / (d + 1) := by positivity
  have hO := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hs).def
    (c := c * κ ^ ((1 : ℝ) / (d + 1))) (by positivity)
  have h' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hO
  filter_upwards [h'] with n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn0 _)] at hn
  rw [Real.mul_rpow hκ.le hn0]
  calc Real.log n ≤ |Real.log n ^ (1 : ℝ)| := by rw [Real.rpow_one]; exact le_abs_self _
    _ ≤ c * κ ^ ((1 : ℝ) / (d + 1)) * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := hn
    _ = c * (κ ^ ((1 : ℝ) / (d + 1)) * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) := by ring

/-- The width of the inner-radius error is a quarter of `ρ` at most: if `ℓ ≤ c ρ` and
`ℓ ≤ c² ρ` with `c = 1 / (4 C₁)`, then `C₁ · (√(ρ ℓ) or ℓ) ≤ ρ / 4`. -/
private lemma bulkPotential_width_le (d : ℕ) {ρ ℓ C₁ : ℝ} (hC₁ : 0 < C₁) (hρ : 0 ≤ ρ)
    (h1 : ℓ ≤ 1 / (4 * C₁) * ρ) (h2 : ℓ ≤ (1 / (4 * C₁)) ^ 2 * ρ) :
    C₁ * (if d = 2 then Real.sqrt (ρ * ℓ) else ℓ) ≤ ρ / 4 := by
  have hc0 : 0 ≤ 1 / (4 * C₁) := by positivity
  have hcC : C₁ * (1 / (4 * C₁)) = 1 / 4 := by
    field_simp
  split_ifs
  · have hs : Real.sqrt (ρ * ℓ) ≤ 1 / (4 * C₁) * ρ := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      calc ρ * ℓ ≤ ρ * ((1 / (4 * C₁)) ^ 2 * ρ) := mul_le_mul_of_nonneg_left h2 hρ
        _ = (1 / (4 * C₁) * ρ) ^ 2 := by ring
    calc C₁ * Real.sqrt (ρ * ℓ) ≤ C₁ * (1 / (4 * C₁) * ρ) :=
          mul_le_mul_of_nonneg_left hs hC₁.le
      _ = ρ / 4 := by rw [← mul_assoc, hcC]; ring
  · calc C₁ * ℓ ≤ C₁ * (1 / (4 * C₁) * ρ) := mul_le_mul_of_nonneg_left h1 hC₁.le
      _ = ρ / 4 := by rw [← mul_assoc, hcC]; ring

/-- The volume scale `ρ q` for `q = √(ℓ / ρ)` (`d = 2`) or `ℓ / ρ` (`d ≥ 3`) is `√(ρ ℓ)` or `ℓ`. -/
private lemma bulkPotential_mul_q_eq (d : ℕ) {ρ ℓ : ℝ} (hρ : 0 < ρ) (hℓ : 0 ≤ ℓ) :
    ρ * (if d = 2 then Real.sqrt (ℓ / ρ) else ℓ / ρ) =
      if d = 2 then Real.sqrt (ρ * ℓ) else ℓ := by
  split_ifs
  · have hsρ : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
    rw [Real.sqrt_div hℓ, Real.sqrt_mul hρ.le]
    calc ρ * (Real.sqrt ℓ / Real.sqrt ρ)
        = (Real.sqrt ρ * Real.sqrt ρ) * (Real.sqrt ℓ / Real.sqrt ρ) := by
          rw [Real.mul_self_sqrt hρ.le]
      _ = Real.sqrt ρ * Real.sqrt ℓ := by field_simp
  · field_simp

/-- The deterministic core: if `|R_in(n) - r_n| ≤ C₁ r_n q_n` and `|r_n⁻¹ D_n ∆ B(0, 1)| ≤ C₁ q_n`,
then for all large `n` the potential of `D_n` is within `K r_n q_n` of `2 d ε (r_n - |y|)` at
every site with `|y| ≤ r_n / 2`. -/
private theorem bulkPotential_core (hd : 2 ≤ d) {ε κ C₁ : ℝ} (hε : 0 < ε) (hκ : 0 < κ)
    (hC₁ : 0 < C₁) (r : ℕ → ℝ) (hr : ∀ n : ℕ, r n = (κ * n) ^ ((1 : ℝ) / (d + 1))) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ Y : ℕ → Site d,
      |innerRadius Y n - r n| ≤
          C₁ * (if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n) →
      volume (((r n)⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
        ENNReal.ofReal (C₁ * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n) →
      ∀ y : Site d, euclidNorm y ≤ r n / 2 →
        |potential d ε (cellSet Y n) (toSpace y) - 2 * d * ε * (r n - euclidNorm y)| ≤
          K * if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n := by
  have hω := unitBallVolume_pos d
  have hd1 : 1 ≤ d := by omega
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * ε / unitBallVolume d := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ht0 : (0 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = 1 / (4 * C₁) := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁]; positivity
  obtain ⟨cs, hcs⟩ : ∃ cs : ℝ, cs = min c₁ (c₁ ^ 2) := ⟨_, rfl⟩
  have hcs0 : 0 < cs := by rw [hcs]; exact lt_min hc₁0 (by positivity)
  refine ⟨a * ((1 / 4 : ℝ) ^ (d - 1))⁻¹ * C₁ + 1, by positivity, ?_⟩
  filter_upwards [bulkPotential_eventually_log_le_mul d hκ hcs0, eventually_ge_atTop 2]
    with n hlog hn2
  intro Y hin hvolY y hy
  rw [← hr n] at hlog
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρpos : 0 < r n := by rw [hr n]; exact Real.rpow_pos_of_pos (mul_pos hκ hn0) _
  have hρ0 : 0 ≤ r n := hρpos.le
  have hℓ0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have h1c : Real.log n ≤ 1 / (4 * C₁) * r n := by
    rw [← hc₁]
    refine hlog.trans (mul_le_mul_of_nonneg_right ?_ hρ0)
    rw [hcs]
    exact min_le_left _ _
  have h2c : Real.log n ≤ (1 / (4 * C₁)) ^ 2 * r n := by
    rw [← hc₁]
    refine hlog.trans (mul_le_mul_of_nonneg_right ?_ hρ0)
    rw [hcs]
    exact min_le_right _ _
  have hwidth := bulkPotential_width_le d hC₁ hρ0 h1c h2c
  have hA0 : 0 ≤ C₁ * (if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n) :=
    mul_nonneg hC₁.le (by split_ifs <;> [exact Real.sqrt_nonneg _; exact hℓ0])
  have hinner : r n - C₁ * (if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n) ≤
      innerRadius Y n := by linarith [(abs_le.mp hin).1]
  have hDm : MeasurableSet (cellSet Y n) := Occupation.measurableSet_cellSet Y n
  have hDb : Bornology.IsBounded (cellSet Y n) :=
    Metric.isBounded_ball.subset (Occupation.cellSet_subset_ball hd1 Y n)
  have hq0 : 0 ≤ C₁ * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n :=
    mul_nonneg hC₁.le (by split_ifs <;> positivity)
  have hvol := Geometry.toReal_volume_symmDiff_le hρpos hq0 (cellSet Y n) hvolY
  have hz : ‖toSpace y‖ ≤ r n / 2 := by rw [norm_toSpace]; exact hy
  have hfar : ∀ v ∈ cellSet Y n ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r n),
      1 / 4 * r n ≤ ‖v - toSpace y‖ := by
    intro v hv
    have h1 := bulkPotential_le_norm_of_mem_symmDiff hA0 hinner hv
    have h2 : ‖v‖ - ‖toSpace y‖ ≤ ‖v - toSpace y‖ := norm_sub_norm_le v (toSpace y)
    linarith
  have hpot := bulkPotential_abs_potential_sub_ball_le hd hε (mul_pos ht0 hρpos) hDm hDb hfar hvol
  have hUB : potential d ε (Metric.ball 0 (r n)) (toSpace y) =
      2 * d * ε * (r n - euclidNorm y) := by
    rw [Geometry.potential_ball hd ε hρpos, norm_toSpace, max_eq_left (by linarith)]
  have hB0 : 0 ≤ if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n := by
    split_ifs <;> [exact Real.sqrt_nonneg _; exact hℓ0]
  rw [← hUB]
  have hcalc : a * (((1 / 4 * r n) ^ (d - 1))⁻¹ *
      (r n ^ d * (C₁ * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n))) =
      a * ((1 / 4 : ℝ) ^ (d - 1))⁻¹ * C₁ *
        (if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n) := by
    rw [← mul_assoc (((1 / 4 * r n) ^ (d - 1))⁻¹), bulkPotential_inv_mul_pow_mul_pow hd1 ht0 hρpos,
      ← bulkPotential_mul_q_eq d hρpos hℓ0]
    ring
  rw [← ha] at hpot
  calc _ ≤ a * (((1 / 4 * r n) ^ (d - 1))⁻¹ *
        (r n ^ d * (C₁ * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n))) :=
        hpot
    _ = a * ((1 / 4 : ℝ) ^ (d - 1))⁻¹ * C₁ *
        (if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n) := hcalc
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hB0

/-- `eq:bulk-potential-only`: with probability at least `1 - C n^{-10}`, the potential of `D_n`
differs from `2 d ε (r_n - |y|)` by at most `C r_n q_n` at every site with `|y| ≤ r_n / 2`, where
`r_n q_n` is `√(r_n log n)` if `d = 2` and `log n` if `d ≥ 3`. -/
private theorem bulk_potential_only (hfluct : fluctuation_rates.{u}) (hd : 2 ≤ d) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / (d : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₁ : ℕ, ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, n₁ ≤ n →
      μ {ω | ¬ ∀ y : Site d, euclidNorm y ≤ scaleR d ε n / 2 →
          |potential d ε (cellSet (fun j => X j ω) n) (toSpace y) -
              2 * d * ε * (scaleR d ε n - euclidNorm y)| ≤
            C * (if d = 2 then Real.sqrt (scaleR d ε n * Real.log n) else Real.log n)} ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (-(10 : ℝ))) := by
  obtain ⟨C₁, hC₁, hprob, -⟩ := hfluct hd ε hε0 hε1 10 (by norm_num)
  have hω0 := unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (d + 1) / (2 * d * ε * unitBallVolume d) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hrκ : ∀ n : ℕ, scaleR d ε n = (κ * n) ^ ((1 : ℝ) / (d + 1)) := fun n => by
    rw [scaleR, hκ, mul_div_right_comm]
  obtain ⟨K, hK, hev⟩ := bulkPotential_core hd hε0 hκ0 hC₁ (scaleR d ε) hrκ
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨max K C₁, lt_max_of_lt_left hK, max N 2, ?_⟩
  intro Ω _ μ _ X hX n hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  refine le_trans (measure_mono ?_)
    ((hprob μ X hX n hn2).trans (ENNReal.ofReal_le_ofReal ?_))
  · intro ω hω hg
    apply hω
    intro y hy
    obtain ⟨hA, hvol, -⟩ := hg
    have hA1 : |innerRadius (fun j => X j ω) n - scaleR d ε n| ≤
        C₁ * (if d = 2 then Real.sqrt (scaleR d ε n * Real.log n) else Real.log n) := by
      by_cases hd2 : d = 2
      · simp only [if_pos hd2] at hA ⊢
        exact hA.1
      · simp only [if_neg hd2] at hA ⊢
        exact hA.1
    have hB0 : 0 ≤ if d = 2 then Real.sqrt (scaleR d ε n * Real.log n) else Real.log n := by
      split_ifs <;> [exact Real.sqrt_nonneg _; exact Real.log_natCast_nonneg n]
    exact (hN n hnN (fun j => X j ω) hA1 hvol y hy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hB0)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- The Dynkin martingale of a difference is the difference of the Dynkin martingales. -/
private theorem dynkin_sub_fun (ε : ℝ) (a b : Site d → ℝ) {Ω : Type*} (X : ℕ → Ω → Site d)
    (t : ℕ) (ω : Ω) :
    dynkin ε (fun z => a z - b z) X t ω = dynkin ε a X t ω - dynkin ε b X t ω := by
  simp only [dynkin, nextMean, mul_sub, Finset.sum_sub_distrib]
  ring

/-- The norm of a multiple `N e` of a unit vector is `N`. -/
private theorem euclidNorm_natCast_smul_unit (i : Fin d) (N : ℕ) :
    euclidNorm (((N : ℕ) : ℤ) • LatticeProb.unit i) = (N : ℝ) := by
  have h : ∑ l : Fin d, ((((N : ℕ) : ℤ) • LatticeProb.unit i) l : ℝ) ^ 2 = (N : ℝ) ^ 2 := by
    rw [Finset.sum_eq_single i]
    · simp [LatticeProb.unit]
    · intro l _ hl
      simp [LatticeProb.unit, hl]
    · simp
  unfold euclidNorm
  rw [h, Real.sqrt_sq (Nat.cast_nonneg N)]

/-- The increments of `f_i` are bounded by twice the bound on the increments of the kernel. -/
private theorem abs_sepF_add_sub_le (g : Site d → ℝ) (e : Site d) (R : ℝ) (i : ℕ) {Cg : ℝ}
    (hg : ∀ u e', e' ∈ unitSteps d → |g (u + e') - g u| ≤ Cg) (x e' : Site d)
    (he : e' ∈ unitSteps d) : |sepF d g e R i (x + e') - sepF d g e R i x| ≤ 2 * Cg := by
  have hCg : 0 ≤ Cg := (abs_nonneg _).trans (hg 0 e' he)
  unfold sepF
  split_ifs with h2
  · have h1 := hg (x - (((i * sepStep R : ℕ) : ℤ) • e + ((kOf R : ℕ) : ℤ) • e)) e' he
    have h3 := hg (x - ((i * sepStep R : ℕ) : ℤ) • e) e' he
    rw [show x + e' - (((i * sepStep R : ℕ) : ℤ) • e + ((kOf R : ℕ) : ℤ) • e) =
        x - (((i * sepStep R : ℕ) : ℤ) • e + ((kOf R : ℕ) : ℤ) • e) + e' by abel,
      show x + e' - ((i * sepStep R : ℕ) : ℤ) • e = x - ((i * sepStep R : ℕ) : ℤ) • e + e' by
        abel]
    calc _ ≤ |g (x - (((i * sepStep R : ℕ) : ℤ) • e + ((kOf R : ℕ) : ℤ) • e) + e') -
            g (x - (((i * sepStep R : ℕ) : ℤ) • e + ((kOf R : ℕ) : ℤ) • e))| +
          |g (x - ((i * sepStep R : ℕ) : ℤ) • e + e') - g (x - ((i * sepStep R : ℕ) : ℤ) • e)| := by
          refine le_trans (le_of_eq ?_) (abs_sub _ _)
          ring_nf
      _ ≤ Cg + Cg := add_le_add h1 h3
      _ = 2 * Cg := by ring
  · have h3 := hg (x - ((i * sepStep R : ℕ) : ℤ) • e) e' he
    rw [show x + e' - ((i * sepStep R : ℕ) : ℤ) • e = x - ((i * sepStep R : ℕ) : ℤ) • e + e' by
      abel]
    linarith

/-- Linear arithmetic at one site: a large negative Dynkin martingale gives a large deviation of the
local time. -/
private theorem dev_lower_single {ℓ U M V T P Eu : ℝ} (h1 : |ℓ - U + M| ≤ P) (h2 : |U - V| ≤ Eu)
    (hM : T ≤ -M) : T - (P + Eu) ≤ |ℓ - V| := by
  have a1 := (abs_le.mp h1).1
  have a2 := (abs_le.mp h2).1
  have a3 := le_abs_self (ℓ - V)
  linarith

/-- Linear arithmetic at two sites: a large difference of the Dynkin martingales gives a large
deviation of the local time at one of the two sites. -/
private theorem dev_lower_pair {ℓ ℓ' U U' M M' V V' T P Eu : ℝ} (h1 : |ℓ - U + M| ≤ P)
    (h1' : |ℓ' - U' + M'| ≤ P) (h2 : |U - V| ≤ Eu) (h2' : |U' - V'| ≤ Eu)
    (hM : T ≤ -(M' - M)) : T / 2 - (P + Eu) ≤ max |ℓ - V| |ℓ' - V'| := by
  have a1 := abs_le.mp h1
  have a1' := abs_le.mp h1'
  have a2 := abs_le.mp h2
  have a2' := abs_le.mp h2'
  have b1 := le_abs_self (ℓ' - V')
  have b2 := neg_abs_le (ℓ - V)
  have c1 : |ℓ' - V'| ≤ max |ℓ - V| |ℓ' - V'| := le_max_right _ _
  have c2 : |ℓ - V| ≤ max |ℓ - V| |ℓ' - V'| := le_max_left _ _
  linarith [a1.1, a1.2, a1'.1, a1'.2, a2.1, a2.2, a2'.1, a2'.2]

/-- At a site `p` of norm at most `√R`, a large negative Dynkin martingale of `g(· - p)` produces a
site with a large deviation of the local time. -/
private theorem exists_site_single {ε R P Eu T : ℝ} {n : ℕ} {Ω : Type*} (X : ℕ → Ω → Site d)
    (ω : Ω)
    (hP : ∀ y : Site d, euclidNorm y ≤ Real.sqrt R →
      |(localTime (fun j => X j ω) n y : ℝ) -
          potential d ε (cellSet (fun j => X j ω) n) (toSpace y) +
          dynkin ε (fun z => latticeKernel d (z - y)) X n ω| ≤ P)
    (hU : ∀ y : Site d, euclidNorm y ≤ Real.sqrt R →
      |potential d ε (cellSet (fun j => X j ω) n) (toSpace y) -
          2 * d * ε * (R - euclidNorm y)| ≤ Eu)
    (p : Site d) (hp : euclidNorm p ≤ Real.sqrt R) (hT0 : 0 ≤ T)
    (hT : T ≤ -dynkin ε (fun z => latticeKernel d (z - p)) X n ω) :
    ∃ x : Site d, euclidNorm x ≤ Real.sqrt R ∧
      T / 2 - (P + Eu) ≤
        |(localTime (fun j => X j ω) n x : ℝ) - 2 * d * ε * (R - euclidNorm x)| := by
  refine ⟨p, hp, ?_⟩
  have := dev_lower_single (hP p hp) (hU p hp) hT
  linarith

/-- At two sites `p`, `q` of norm at most `√R`, a large negative Dynkin martingale of
`g(· - q) - g(· - p)` produces a site with a large deviation of the local time. -/
private theorem exists_site_pair {ε R P Eu T : ℝ} {n : ℕ} {Ω : Type*} (X : ℕ → Ω → Site d)
    (ω : Ω)
    (hP : ∀ y : Site d, euclidNorm y ≤ Real.sqrt R →
      |(localTime (fun j => X j ω) n y : ℝ) -
          potential d ε (cellSet (fun j => X j ω) n) (toSpace y) +
          dynkin ε (fun z => latticeKernel d (z - y)) X n ω| ≤ P)
    (hU : ∀ y : Site d, euclidNorm y ≤ Real.sqrt R →
      |potential d ε (cellSet (fun j => X j ω) n) (toSpace y) -
          2 * d * ε * (R - euclidNorm y)| ≤ Eu)
    (p q : Site d) (hp : euclidNorm p ≤ Real.sqrt R) (hq : euclidNorm q ≤ Real.sqrt R)
    (hT : T ≤ -dynkin ε (fun z => latticeKernel d (z - q) - latticeKernel d (z - p)) X n ω) :
    ∃ x : Site d, euclidNorm x ≤ Real.sqrt R ∧
      T / 2 - (P + Eu) ≤
        |(localTime (fun j => X j ω) n x : ℝ) - 2 * d * ε * (R - euclidNorm x)| := by
  rw [dynkin_sub_fun ε (fun z => latticeKernel d (z - q)) (fun z => latticeKernel d (z - p)) X n
    ω] at hT
  have := dev_lower_pair (hP p hp) (hP q hq) (hU p hp) (hU q hq) hT
  rcases max_choice
    |(localTime (fun j => X j ω) n p : ℝ) - 2 * d * ε * (R - euclidNorm p)|
    |(localTime (fun j => X j ω) n q : ℝ) - 2 * d * ε * (R - euclidNorm q)| with h | h
  · exact ⟨p, hp, by rw [h] at this; exact this⟩
  · exact ⟨q, hq, by rw [h] at this; exact this⟩

/-- The failure probability is at most the sum of the failure probabilities. -/
private theorem measure_union_four_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {S A B C D : Set Ω} (h : S ⊆ A ∪ B ∪ C ∪ D) : μ S ≤ μ A + μ B + μ C + μ D := by
  calc μ S ≤ μ (A ∪ B ∪ C ∪ D) := measure_mono h
    _ ≤ μ (A ∪ B ∪ C) + μ D := measure_union_le _ _
    _ ≤ μ (A ∪ B) + μ C + μ D := by gcongr; exact measure_union_le _ _
    _ ≤ μ A + μ B + μ C + μ D := by gcongr; exact measure_union_le _ _

/-- If `S` avoids no point outside `A ∪ B ∪ C ∪ D` with `D` null, then `μ S` is at most the sum
of the bounds for `A`, `B` and `C`. -/
private theorem measure_le_add_of_four {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {S A B C D : Set Ω} {a b c : ENNReal}
    (h : ∀ ω, ω ∉ A → ω ∉ B → ω ∉ C → ω ∉ D → ω ∉ S) (hA : μ A ≤ a) (hB : μ B ≤ b)
    (hC : μ C ≤ c) (hD : μ D = 0) : μ S ≤ a + b + c := by
  have hsub : S ⊆ A ∪ B ∪ C ∪ D := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    exact h ω hcon.1.1.1 hcon.1.1.2 hcon.1.2 hcon.2 hω
  calc μ S ≤ μ A + μ B + μ C + μ D := measure_union_four_le μ hsub
    _ ≤ a + b + c + 0 := by rw [hD]; gcongr
    _ = a + b + c := add_zero _

/-- **Theorem 1.3 (iii)** for fixed `d` and `ε`, in terms of the scale `r_n`. -/
private theorem sharp_bulk_core (hsep : separated_brackets.{u}) (hexp : exp_deviation.{u})
    (hfluct : fluctuation_rates.{u}) (hd : 2 ≤ d) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1 / (d : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
      μ {ω | ¬ ∃ x : Site d, euclidNorm x ≤ Real.sqrt (scaleR d ε n) ∧
          c * (if d = 2 then Real.sqrt (scaleR d ε n) * Real.log n
            else Real.sqrt (scaleR d ε n * Real.log n)) ≤
            |(localTime (fun j => X j ω) n x : ℝ) -
              2 * d * ε * (scaleR d ε n - euclidNorm x)|} ≤
        ENNReal.ofReal ((n : ℝ) ^ (-c)) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hε2 : ε ≤ 1 := by
    have h1 : ε * d < 1 := (lt_div_iff₀ hdpos).mp hε1
    have h2 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    nlinarith
  have hω := unitBallVolume_pos d
  set κ : ℝ := ((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d) with hκ
  have hκ0 : 0 < κ := by positivity
  have hr : ∀ n : ℕ, scaleR d ε n = (κ * n) ^ ((1 : ℝ) / (d + 1)) := by
    intro n
    unfold scaleR
    congr 1
    rw [hκ]
    ring
  obtain ⟨c₀, C₀, Cs, hc₀, hcC, hCs, n₀, hsepn⟩ := hsep hd ε hε0 hε1
  obtain ⟨cE, CE, hcE, hCE, hMax⟩ := exists_max_dynkin_large hexp hd1 hε0.le hε1 hc₀ hcC
  obtain ⟨h, hK⟩ := exists_kernelFacts_latticeKernel hd
  obtain ⟨Cg, hCg⟩ := hK.gradBound
  obtain ⟨Cpt, hCpt0, hPt⟩ := exists_abs_localTime_sub_potential_add_dynkin_le.{u} hd hK
  obtain ⟨Cu, hCu0, n₁, hpot⟩ := bulk_potential_only hfluct hd hε0 hε1
  have hgb : ∀ u e', e' ∈ unitSteps d →
      |latticeKernel d (u + e') - latticeKernel d u| ≤ max Cg 1 := by
    intro u e' he
    refine (hCg u e' he).trans ?_
    have h1 : (1 + euclidNorm u) ^ (1 - (d : ℝ)) ≤ 1 :=
      rpow_one_add_le_one (euclidNorm_nonneg _) (by
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
        linarith)
    have h0 : 0 ≤ (1 + euclidNorm u) ^ (1 - (d : ℝ)) :=
      Real.rpow_nonneg (by linarith [euclidNorm_nonneg u]) _
    have hm0 : 0 ≤ max Cg 1 := le_trans zero_le_one (le_max_right _ _)
    calc Cg * (1 + euclidNorm u) ^ (1 - (d : ℝ))
        ≤ max Cg 1 * (1 + euclidNorm u) ^ (1 - (d : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h0
      _ ≤ max Cg 1 * 1 := mul_le_mul_of_nonneg_left h1 hm0
      _ = max Cg 1 := mul_one _
  have hCg₁0 : 0 < max Cg 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hB0 : 0 < 2 * max Cg 1 := by positivity
  obtain ⟨c1, hc1, hfin⟩ := scale_final hd hκ0 (scaleR d ε) hr hCs hCE hcE hB0 hCpt0 hCu0.le
  have hbasic := scale_basic hd hκ0 (scaleR d ε) hr hCs hCE hcE hB0
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hbasic.and hfin)
  refine ⟨c1, hc1, max (max n₀ n₁) N, ?_⟩
  intro Ω _ μ _ X hX n hn
  have hn₀ : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₁ : n₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨⟨h2n, h4, hRn, hσ, hk1, hkinv, hsites, hCEβ, hβb, hβδ, hα1⟩, hP6, hP7⟩ := hN n hnN
  set R : ℝ := scaleR d ε n with hRdef
  set σ : ℝ := sigmaOf d R with hσdef
  set β : ℝ := betaOf CE R with hβdef
  set α : ℝ := Cs * (n : ℝ) ^ (-(10 : ℝ)) with hαdef
  set e₁ : Site d := LatticeProb.unit (⟨0, by omega⟩ : Fin d) with he₁
  have hβ0 : 0 ≤ β := by
    rw [hβdef]
    unfold betaOf
    positivity
  have hα0 : 0 ≤ α := by positivity
  have hsepE : μ {ω | ¬ ∀ i j : Fin (kOf R),
      (i = j → c₀ ≤ dynkinBracket (stepProb d ε) (sepF d (latticeKernel d) e₁ R (i.val + 1))
            (sepF d (latticeKernel d) e₁ R (j.val + 1)) (fun t => X t ω) n / σ ^ 2 ∧
          dynkinBracket (stepProb d ε) (sepF d (latticeKernel d) e₁ R (i.val + 1))
            (sepF d (latticeKernel d) e₁ R (j.val + 1)) (fun t => X t ω) n / σ ^ 2 ≤ C₀) ∧
      (i ≠ j → |dynkinBracket (stepProb d ε) (sepF d (latticeKernel d) e₁ R (i.val + 1))
            (sepF d (latticeKernel d) e₁ R (j.val + 1)) (fun t => X t ω) n / σ ^ 2| ≤
          Cs * R ^ (-(1 : ℝ) / 4))} ≤ ENNReal.ofReal α := by
    refine le_trans (measure_mono ?_) (hsepn μ X hX n hn₀)
    intro ω hω hev
    refine hω (fun i j => ?_)
    obtain ⟨h1, h2⟩ := hev (i.val + 1) (j.val + 1) (by omega) (Nat.succ_le_of_lt i.isLt)
      (by omega) (Nat.succ_le_of_lt j.isLt)
    refine ⟨fun hij => h1 (by rw [hij]), fun hij => h2 (fun h => hij (Fin.ext (by omega)))⟩
  have hmax := hMax μ X hX (kOf R) n (by omega) (by omega)
    (fun i => sepF d (latticeKernel d) e₁ R (i.val + 1)) σ (2 * max Cg 1)
    (Cs * R ^ (-(1 : ℝ) / 4)) α β hσ hB0 (by positivity) hα0 hα1
    (fun i x e he => abs_sepF_add_sub_le (latticeKernel d) e₁ R (i.val + 1) hgb x e he)
    hsepE hCEβ hβb hβδ
  have hFmax : μ {ω | ∀ i : Fin (kOf R),
      -dynkin ε (sepF d (latticeKernel d) e₁ R (i.val + 1)) X n ω / σ < cE * β} ≤
      ENNReal.ofReal (CE * (((kOf R : ℕ) : ℝ)⁻¹ * Real.exp (CE * β ^ 2) +
        β ^ 2 * (Cs * R ^ (-(1 : ℝ) / 4)) + β ^ 3 * (2 * (2 * max Cg 1) / σ) +
        Real.exp (CE * β ^ 2) * Real.sqrt α)) := by
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
      (le_trans ENNReal.toReal_nonneg hmax)]
    exact hmax
  have hPmax0 : 0 ≤ CE * (((kOf R : ℕ) : ℝ)⁻¹ * Real.exp (CE * β ^ 2) +
        β ^ 2 * (Cs * R ^ (-(1 : ℝ) / 4)) + β ^ 3 * (2 * (2 * max Cg 1) / σ) +
        Real.exp (CE * β ^ 2) * Real.sqrt α) := le_trans ENNReal.toReal_nonneg hmax
  have hpotE := hpot μ X hX n hn₁
  have hnull : μ {ω | ¬ (X 0 ω = 0 ∧ ∀ j, euclidNorm (X j ω) ≤ j)} = 0 := by
    have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
      rw [ae_iff]
      exact hX.start
    exact ae_iff.mp (h0.and (ae_euclidNorm_le hd1 hε0.le hε1 hX))
  have hRn1 : (1 : ℝ) ≤ R := by linarith
  have hsqrtR : Real.sqrt R ≤ R / 2 := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hsqrtn : Real.sqrt R ≤ 3 * n := by linarith
  have hsum := measure_le_add_of_four μ (S := {ω | ¬ ∃ x : Site d, euclidNorm x ≤ Real.sqrt R ∧
      c1 * (if d = 2 then Real.sqrt R * Real.log n else Real.sqrt (R * Real.log n)) ≤
        |(localTime (fun j => X j ω) n x : ℝ) - 2 * d * ε * (R - euclidNorm x)|}) ?_
    hsepE hpotE hFmax hnull
  · refine hsum.trans ?_
    rw [← ENNReal.ofReal_add hα0 (by positivity), ← ENNReal.ofReal_add (by positivity) hPmax0]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · intro ω hA hB hC hD hS
    simp only [Set.mem_setOf_eq, not_not] at hA hB hD
    simp only [Set.mem_setOf_eq, not_forall, not_lt] at hC
    obtain ⟨i, hi⟩ := hC
    have hP : ∀ y : Site d, euclidNorm y ≤ Real.sqrt R →
        |(localTime (fun j => X j ω) n y : ℝ) -
            potential d ε (cellSet (fun j => X j ω) n) (toSpace y) +
            dynkin ε (fun z => latticeKernel d (z - y)) X n ω| ≤ Cpt * Real.log (n + 2) :=
      fun y hy => hPt ε hε0.le hε2 X ω hD.1 hD.2 n (by omega) y (hy.trans hsqrtn)
    have hU : ∀ y : Site d, euclidNorm y ≤ Real.sqrt R →
        |potential d ε (cellSet (fun j => X j ω) n) (toSpace y) -
            2 * d * ε * (R - euclidNorm y)| ≤
          Cu * (if d = 2 then Real.sqrt (R * Real.log n) else Real.log n) :=
      fun y hy => hB y (hy.trans hsqrtR)
    have hT : σ * (cE * β) ≤ -dynkin ε (sepF d (latticeKernel d) e₁ R (i.val + 1)) X n ω := by
      have := (le_div_iff₀ hσ).mp hi
      linarith
    have hT0 : 0 ≤ σ * (cE * β) := mul_nonneg hσ.le (mul_nonneg hcE.le hβ0)
    have hnorm : ∀ N : ℕ, euclidNorm (((N : ℕ) : ℤ) • e₁) = N :=
      fun N => euclidNorm_natCast_smul_unit _ N
    have hjk : i.val + 1 ≤ kOf R := Nat.succ_le_of_lt i.isLt
    have hpn : euclidNorm ((((i.val + 1) * sepStep R : ℕ) : ℤ) • e₁) ≤ Real.sqrt R := by
      rw [hnorm]
      have h1 := hsites (i.val + 1) hjk
      have h2 : (0 : ℝ) ≤ (kOf R : ℝ) := Nat.cast_nonneg _
      linarith
    obtain ⟨x, hx, hxdev⟩ : ∃ x : Site d, euclidNorm x ≤ Real.sqrt R ∧
        σ * (cE * β) / 2 - (Cpt * Real.log ((n : ℝ) + 2) +
          Cu * (if d = 2 then Real.sqrt (R * Real.log n) else Real.log n)) ≤
        |(localTime (fun j => X j ω) n x : ℝ) - 2 * d * ε * (R - euclidNorm x)| := by
      by_cases hd2 : d = 2
      · have hqn : euclidNorm ((((i.val + 1) * sepStep R : ℕ) : ℤ) • e₁ +
            ((kOf R : ℕ) : ℤ) • e₁) ≤ Real.sqrt R := by
          rw [show (((i.val + 1) * sepStep R : ℕ) : ℤ) • e₁ + ((kOf R : ℕ) : ℤ) • e₁ =
              (((i.val + 1) * sepStep R + kOf R : ℕ) : ℤ) • e₁ by rw [Nat.cast_add, add_smul],
            hnorm]
          rw [Nat.cast_add]
          exact hsites (i.val + 1) hjk
        have hsf : sepF d (latticeKernel d) e₁ R (i.val + 1) = fun z =>
            latticeKernel d (z - ((((i.val + 1) * sepStep R : ℕ) : ℤ) • e₁ +
              ((kOf R : ℕ) : ℤ) • e₁)) -
              latticeKernel d (z - (((i.val + 1) * sepStep R : ℕ) : ℤ) • e₁) := by
          funext z
          simp only [sepF, if_pos hd2]
        rw [hsf] at hT
        exact exists_site_pair X ω hP hU _ _ hpn hqn hT
      · have hsf : sepF d (latticeKernel d) e₁ R (i.val + 1) = fun z =>
            latticeKernel d (z - (((i.val + 1) * sepStep R : ℕ) : ℤ) • e₁) := by
          funext z
          simp only [sepF, if_neg hd2]
        rw [hsf] at hT
        exact exists_site_single X ω hP hU _ hpn hT0 hT
    exact hS ⟨x, hx, le_trans hP7 hxdev⟩

/-- **Theorem 1.3 (iii)** (`thm:sharp`): with probability at least `1 - n^{-c}`, some site
`|x| ≤ r_n^{1/2}` has a deviation `|ℓ_n(x) - 2dε (r_n - |x|)|` of at least `c √r_n log n`
(`d = 2`) or `c √(r_n log n)` (`d ≥ 3`). It follows from Lemma 9.1 (ii) for the martingales
`-M^{f_i} / σ_n`, whose brackets Lemma 9.3 controls, and the pointwise decomposition of the local
times with `eq:bulk-potential-only`. -/
theorem sharp_bulk_of (hsep : separated_brackets.{u}) (hexp : exp_deviation.{u})
    (hfluct : fluctuation_rates.{u}) : sharp_bulk.{u} := by
  intro d hd ωd ε hε0 hε1 r
  exact sharp_bulk_core hsep hexp hfluct hd hε0 hε1

end Helpers

end CERW.Support.Lower
