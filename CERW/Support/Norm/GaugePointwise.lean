import CERW.Support.Norm.GaugeLocalTime
import CERW.Support.Norm.ContactPotential

/-!
# The fine pointwise local-time bound for the walk driven by a gauge

For a compact convex `K ⊆ ℝ^d`, `d ≥ 2`, with the origin in its interior, its Minkowski functional
`ψ = gauge K` (not necessarily even), a drift `ε > 0` with `ε max {ψ(e_i), ψ(-e_i)} < 1/d` and any
choice `ξ(x) ∈ ∂ψ(x)` of subgradients (`ξ 0 = 0`), the local time `ℓ_n(y)` of the walk
`IsDriftCERW μ ε ξ X` at every lattice site `|y| ≤ 3n` is within
`C (√(Σ_{j<n} (1 + |X_j - y|)^{2-2d} log (n + 2)) + log (n + 2))` of the potential `U_{D_n}(y)`
of the cell set, with probability at least `1 - C n^{-p}` and a constant `C` that does not depend on
`ξ`, the walk or `n`.

The proof has two parts.

* *The deterministic part.* The Dynkin decomposition of the local time at `y` for the lattice
  kernel `b`,
  `ℓ_n(y) = b(X_n - y) - b(-y) + ε Σ_{x ∈ A_n} ξ(x) · Db(x - y) - 𝓜^y_n`
  (`ContactDynkin.localTime_eq_driftDynkin`), the logarithmic growth of `b`, and the discretization
  of the potential by the source sum, `|ε Σ ξ(x) · Db(x - y) - U_{D_n}(y)| ≤ C ε log (R' + 2)`
  (`GaugeCellGradient.gauge_abs_source_sum_sub_normPotential_le`, which rests on the cell estimate
  for the gauge and the growth of its distributional Laplacian), give
  `|ℓ_n(y) - U_{D_n}(y) + 𝓜^y_n| ≤ C (1 + ε) log (n + 2)` for every path with `|X_j| ≤ j`.
* *The probabilistic part.* The local martingale bound `|𝓜^y_n| ≤ C (√(B_y L) + L)` for all
  `|y| ≤ 3n` simultaneously with probability `1 - C n^{-p}`, with the bracket
  `B_y = Σ_{j<n} (1 + |X_j - y|)^{2-2d}` (`ContactDynkin.exists_drift_local_mart`, Freedman's
  inequality at dyadic brackets and a union bound), a bound that does not involve the body.

Neither evenness nor a norm enters: the body is used through the discretization of the potential
and the coordinate bound `ε |ξ_i| ≤ 1/d` of the subgradients.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.GaugePointwise

open CERW CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel
  CERW.Support.Norm.GaugeCellGradient CERW.Support.Norm.GaugeLocalTime
  CERW.Support.Occupation

variable {d : ℕ}

/-! ### Arithmetic of the logarithms -/

/-- The logarithmic comparison constant `1 + log(4 + √d)/log 3` is nonnegative. -/
private lemma one_add_log_div_log_three_nonneg (d : ℕ) :
    0 ≤ 1 + Real.log (4 + Real.sqrt d) / Real.log 3 := by
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogd : 0 ≤ Real.log (4 + Real.sqrt d) :=
    Real.log_nonneg (by linarith [Real.sqrt_nonneg d] : (1 : ℝ) ≤ 4 + Real.sqrt d)
  have := div_nonneg hlogd (le_of_lt hlog3pos)
  linarith

/-- For `n ≥ 1`, the logarithm of `4n + √d + 2` is at most the logarithmic comparison
constant times `log(n + 2)`. -/
private lemma log_four_mul_add_sqrt_add_two_le (d n : ℕ) (hn : 1 ≤ n) :
    Real.log (4 * (n : ℝ) + Real.sqrt d + 2) ≤
      (1 + Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hsn : Real.sqrt d ≤ Real.sqrt d * n := by
    simpa using mul_le_mul_of_nonneg_left hn1 hs
  have hle1 : 4 * (n : ℝ) + Real.sqrt d + 2 ≤ (4 + Real.sqrt d) * ((n : ℝ) + 2) := by
    nlinarith [hs, hsn, hn1]
  have hpos1 : 0 < 4 * (n : ℝ) + Real.sqrt d + 2 := by linarith [hs, hn1]
  have hn2 : 0 < (n : ℝ) + 2 := by linarith [hn1]
  have h4 : 0 < 4 + Real.sqrt d := by linarith [hs]
  have hpos2 : 0 < (4 + Real.sqrt d) * ((n : ℝ) + 2) := mul_pos h4 hn2
  have hlog1 : Real.log (4 * (n : ℝ) + Real.sqrt d + 2) ≤
      Real.log ((4 + Real.sqrt d) * ((n : ℝ) + 2)) :=
    Real.log_le_log hpos1 hle1
  have hmul : Real.log ((4 + Real.sqrt d) * ((n : ℝ) + 2)) =
      Real.log (4 + Real.sqrt d) + Real.log ((n : ℝ) + 2) := by
    rw [Real.log_mul]
    · exact ne_of_gt h4
    · exact ne_of_gt hn2
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3 : Real.log 3 ≤ Real.log ((n : ℝ) + 2) := by
    apply Real.log_le_log (by norm_num)
    have h3n : 3 ≤ n + 2 := by omega
    exact_mod_cast h3n
  have hlogd : 0 ≤ Real.log (4 + Real.sqrt d) :=
    Real.log_nonneg (by linarith [hs] : (1 : ℝ) ≤ 4 + Real.sqrt d)
  have hratio : 1 ≤ Real.log ((n : ℝ) + 2) / Real.log 3 := by
    rw [le_div_iff₀ hlog3pos]
    linarith
  have hstep : Real.log (4 + Real.sqrt d) ≤
      (Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2) := by
    calc Real.log (4 + Real.sqrt d) = Real.log (4 + Real.sqrt d) * 1 := by ring
      _ ≤ Real.log (4 + Real.sqrt d) * (Real.log ((n : ℝ) + 2) / Real.log 3) :=
          mul_le_mul_of_nonneg_left hratio hlogd
      _ = (Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2) := by ring
  calc Real.log (4 * (n : ℝ) + Real.sqrt d + 2)
      ≤ Real.log ((4 + Real.sqrt d) * ((n : ℝ) + 2)) := hlog1
    _ = Real.log (4 + Real.sqrt d) + Real.log ((n : ℝ) + 2) := hmul
    _ ≤ Real.log ((n : ℝ) + 2) +
        (Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2) := by
        linarith [hstep]
    _ = (1 + Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2) := by ring

/-- Logarithmic growth of `b` transfers to a bound by `log (R' + 2)` at points of norm at most
`R'`, with a nonnegative constant. -/
private lemma abs_le_max_mul_log {b : Site d → ℝ} {Cb : ℝ}
    (hCb : ∀ x, |b x| ≤ Cb * Real.log (euclidNorm x + 2)) {z : Site d} {R' : ℝ}
    (hz : euclidNorm z ≤ R') :
    |b z| ≤ max Cb 0 * Real.log (R' + 2) := by
  have hlog0 : 0 ≤ Real.log (euclidNorm z + 2) :=
    Real.log_nonneg (by linarith [LatticeProb.euclidNorm_nonneg z])
  calc |b z| ≤ Cb * Real.log (euclidNorm z + 2) := hCb z
    _ ≤ max Cb 0 * Real.log (euclidNorm z + 2) :=
        mul_le_mul_of_nonneg_right (le_max_left Cb 0) hlog0
    _ ≤ max Cb 0 * Real.log (R' + 2) :=
        mul_le_mul_of_nonneg_left
          (Real.log_le_log (by linarith [LatticeProb.euclidNorm_nonneg z]) (by linarith))
          (le_max_right Cb 0)


/-- The two endpoint terms and the source-sum error combine into `(2 C_b + C_S)(1 + ε) L`. -/
private lemma abs_endpoint_add_source_le {a₁ a₂ s Cb CS ε L : ℝ} (hb₁ : |a₁| ≤ Cb * L)
    (hb₂ : |a₂| ≤ Cb * L) (hs : |s| ≤ CS * ε * L) (hCb : 0 ≤ Cb) (hCS : 0 ≤ CS) (hε : 0 ≤ ε)
    (hL : 0 ≤ L) : |a₁ - a₂ + s| ≤ (2 * Cb + CS) * (1 + ε) * L := by
  have h1 : 0 ≤ (2 * Cb * ε) * L := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCb) hε) hL
  have h2 : 0 ≤ CS * L := mul_nonneg hCS hL
  calc |a₁ - a₂ + s| ≤ |a₁ - a₂| + |s| := abs_add_le _ _
    _ ≤ (|a₁| + |a₂|) + |s| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ Cb * L + Cb * L + CS * ε * L := add_le_add (add_le_add hb₁ hb₂) hs
    _ ≤ (2 * Cb + CS) * (1 + ε) * L := by linarith

/-- The fine pointwise bound from the Dynkin decomposition and the local martingale bound: if
`|a + m| ≤ c₁ L` and `|m| ≤ c₂ (s + L)` then `|a| ≤ (c₁ + c₂)(s + L)`. -/
private lemma abs_le_add_of_abs_add_le {a m L s c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁)
    (hs : 0 ≤ s) (h1 : |a + m| ≤ c₁ * L) (h2 : |m| ≤ c₂ * (s + L)) :
    |a| ≤ (c₁ + c₂) * (s + L) := by
  have h3 : |a| ≤ |a + m| + |m| := by
    calc |a| = |(a + m) - m| := by ring_nf
      _ ≤ |a + m| + |m| := abs_sub _ _
  have h4 : c₁ * L ≤ c₁ * (s + L) := mul_le_mul_of_nonneg_left (by linarith) hc₁
  calc |a| ≤ c₁ * L + c₂ * (s + L) := h3.trans (add_le_add h1 h2)
    _ ≤ c₁ * (s + L) + c₂ * (s + L) := by linarith
    _ = (c₁ + c₂) * (s + L) := by ring

/-- Every departure site of a path with `|Y_j| ≤ j` is within `4n + √d` of a target `|y| ≤ 3n`. -/
private lemma departureRange_dist_le (Y : ℕ → Site d) (hpath : ∀ j, euclidNorm (Y j) ≤ j)
    (n : ℕ) (y : Site d) (hy : euclidNorm y ≤ 3 * n) :
    ∀ x ∈ departureRange Y n, euclidNorm (x - y) ≤ 4 * (n : ℝ) + Real.sqrt d := by
  intro x hx
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  rw [departureRange] at hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  have hjn : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
  have hxnorm : euclidNorm (Y j) ≤ (n : ℝ) := (hpath j).trans hjn
  calc euclidNorm (Y j - y)
      ≤ euclidNorm (Y j) + euclidNorm y := euclidNorm_sub_le _ _
    _ ≤ (n : ℝ) + 3 * (n : ℝ) := add_le_add hxnorm hy
    _ = 4 * (n : ℝ) := by ring
    _ ≤ 4 * (n : ℝ) + Real.sqrt d := by linarith

/-! ### The deterministic part -/

open CERW.Support.Law CERW.Support.LocalTime CERW.Support.Drift in
/-- **The pointwise decomposition of the local time at a gauge.** Let `K` be compact and convex
with the origin in its interior, `ψ = gauge K`, and `b` a lattice potential kernel. For `ε ≥ 0`,
every choice `ξ(x) ∈ ∂ψ(x)` of subgradients with `ξ 0 = 0` and every path from the origin with
`|X_j| ≤ j`,
`ℓ_n(y) - U_{D_n}(y) + 𝓜^y_n = O((1 + ε) log (n + 2))` for the lattice targets `|y| ≤ 3n`, with a
constant independent of `ε`, `ξ` and the path. -/
theorem gauge_abs_localTime_sub_normPotential_add_driftDynkin_le (hd : 2 ≤ d)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {b : Site d → ℝ} {h : ℝ → ℝ} (hKF : KernelFacts d b h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω), X 0 ω = 0 →
      (∀ j, euclidNorm (X j ω) ≤ j) → ∀ n : ℕ, 1 ≤ n → ∀ y : Site d,
      euclidNorm y ≤ 3 * n →
        |(localTime (fun j => X j ω) n y : ℝ) -
            normPotential d ε (gauge K) (cellSet (fun j => X j ω) n) (toSpace y) +
            driftDynkin ε ξ (fun z => b (z - y)) X n ω| ≤ C * (1 + ε) * Real.log (n + 2) := by
  obtain ⟨R, Ca, hR, hgradA⟩ := hKF.gradAsymp
  obtain ⟨Cg, hgrad⟩ := hKF.gradBound
  obtain ⟨Cb, hb⟩ := hKF.growth
  obtain ⟨C_S, hCS, hsource⟩ :=
    gauge_abs_source_sum_sub_normPotential_le hd hR hgradA hgrad hK hc h0
  set Cb' : ℝ := max Cb 0 with hCb'
  set K' : ℝ := 1 + Real.log (4 + Real.sqrt d) / Real.log 3 with hK'
  have hCb'0 : 0 ≤ Cb' := le_max_right Cb 0
  have hKnn : 0 ≤ K' := one_add_log_div_log_three_nonneg d
  refine ⟨(2 * Cb' + C_S) * K', mul_nonneg (by linarith) hKnn, ?_⟩
  intro ε hε ξ hξ hξ0 Ω X ω h0' hpath n hn y hy
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  set R' : ℝ := 4 * (n : ℝ) + Real.sqrt d with hR'
  set U : ℝ := normPotential d ε (gauge K) (cellSet (fun j => X j ω) n) (toSpace y) with hU
  rw [CERW.Support.Norm.ContactDynkin.localTime_eq_driftDynkin hKF.poisson ε ξ hξ0 X ω h0' n y]
  set S : ℝ := ∑ x ∈ departureRange (fun j => X j ω) n, inner ℝ (ξ x) (centralDiff b (x - y))
    with hS
  have hgoal_eq : (b (X n ω - y) - b (-y) + ε * S - driftDynkin ε ξ (fun z => b (z - y)) X n ω) -
        U + driftDynkin ε ξ (fun z => b (z - y)) X n ω =
      b (X n ω - y) - b (-y) + (ε * S - U) := by ring
  rw [hgoal_eq]
  have hR'1 : 1 ≤ R' := by
    rw [hR']
    linarith
  have hsub : euclidNorm (X n ω - y) ≤ R' := by
    calc euclidNorm (X n ω - y) ≤ euclidNorm (X n ω) + euclidNorm y := euclidNorm_sub_le _ _
      _ ≤ (n : ℝ) + 3 * (n : ℝ) := add_le_add (hpath n) hy
      _ = 4 * (n : ℝ) := by ring
      _ ≤ R' := by rw [hR']; linarith
  have hneg : euclidNorm (-y) ≤ R' := by
    rw [CERW.Generic.Lattice.euclidNorm_neg]
    rw [hR']
    linarith
  have hb1 := abs_le_max_mul_log hb hsub
  have hb2 := abs_le_max_mul_log hb hneg
  have hsrc := hsource ε hε ξ hξ hξ0 (fun j => X j ω) n y R' hR'1
    (departureRange_dist_le (fun j => X j ω) (fun j => hpath j) n y hy)
  have hlogR' : 0 ≤ Real.log (R' + 2) := Real.log_nonneg (by linarith)
  have hcomb : |b (X n ω - y) - b (-y) + (ε * S - U)| ≤
      (2 * Cb' + C_S) * (1 + ε) * Real.log (R' + 2) :=
    abs_endpoint_add_source_le hb1 hb2 hsrc hCb'0 hCS hε hlogR'
  have hlogK : Real.log (R' + 2) ≤ K' * Real.log ((n : ℝ) + 2) := by
    rw [hR', hK']
    exact log_four_mul_add_sqrt_add_two_le d n hn
  have hcoef : 0 ≤ (2 * Cb' + C_S) * (1 + ε) := by
    exact mul_nonneg (by linarith) (by linarith)
  calc |b (X n ω - y) - b (-y) + (ε * S - U)|
      ≤ (2 * Cb' + C_S) * (1 + ε) * Real.log (R' + 2) := hcomb
    _ ≤ (2 * Cb' + C_S) * (1 + ε) * (K' * Real.log ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hlogK hcoef
    _ = (2 * Cb' + C_S) * K' * (1 + ε) * Real.log ((n : ℝ) + 2) := by ring

/-! ### The probabilistic part: the fine pointwise bound -/

open CERW.Support.Law CERW.Support.LocalTime CERW.Support.Drift in
/-- **The fine pointwise local-time bound for the gauge of a convex body.** Let `K` be a compact
convex set with the origin in its interior and `ψ = gauge K`; let `d ≥ 2` and `ε > 0` with
`ε max {ψ(e_i), ψ(-e_i)} < 1/d`; let `p > 0`. There is a constant `C`, before every subgradient
selection `ξ(x) ∈ ∂ψ(x)` (`ξ 0 = 0`) and every walk `IsDriftCERW μ ε ξ X`, such that for all
`n ≥ 2` with probability at least `1 - C n^{-p}`, simultaneously for all lattice sites `|y| ≤ 3n`,
`|ℓ_n(y) - U_{D_n}(y)| ≤ C (√(Σ_{j<n} (1 + |X_j - y|)^{2-2d} log (n + 2)) + log (n + 2))`. -/
theorem gauge_pointwise_local_time (hd : 2 ≤ d) :
    ∀ {K : Set (EuclideanSpace ℝ (Fin d))}, IsCompact K → Convex ℝ K →
    (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K →
    ∀ ε : ℝ, 0 < ε →
    (∀ i : Fin d, ε * gauge K (CERW.coordVec i) < 1 / (d : ℝ) ∧
      ε * gauge K (-CERW.coordVec i) < 1 / (d : ℝ)) →
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient (gauge K) (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (∀ y : Site d, euclidNorm y ≤ 3 * n →
            |(CERW.localTime (fun j => X j ω) n y : ℝ) -
                CERW.normPotential d ε (gauge K) (CERW.cellSet (fun j => X j ω) n)
                  (CERW.toSpace y)| ≤
              C * (Real.sqrt ((∑ j ∈ Finset.range n,
                (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
                Real.log ((n : ℝ) + 2)))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  intro K hK hc h0 ε hε hell p hp
  have hd1 : 1 ≤ d := by omega
  obtain ⟨b, h, hKF⟩ := CERW.Support.LocalTime.exists_kernelFacts hd
  obtain ⟨Cg, hgrad⟩ := hKF.gradBound
  obtain ⟨C_pt, hCpt, hpt⟩ :=
    gauge_abs_localTime_sub_normPotential_add_driftDynkin_le hd hK hc h0 hKF
  obtain ⟨C_B, hCB, hMB⟩ :=
    CERW.Support.Norm.ContactDynkin.exists_drift_local_mart hd hε.le hgrad hp
  have hP : 0 ≤ C_pt * (1 + ε) := mul_nonneg hCpt (by linarith)
  have hC : 0 < C_pt * (1 + ε) + C_B := by linarith
  refine ⟨C_pt * (1 + ε) + C_B, hC, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn2
  have hξ' : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ) := drift_coord_bound_gauge hε.le hell hξ hξ0
  have hnull : μ {ω | ¬ (X 0 ω = 0 ∧ ∀ j : ℕ, euclidNorm (X j ω) ≤ j)} = 0 := by
    refine ae_iff.mp ?_
    have h0' : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
      rw [ae_iff]
      exact hX.start
    filter_upwards [h0', CERW.Support.Drift.ae_euclidNorm_le_drift hd1 hε.le hξ' hX] with ω a b
    exact ⟨a, b⟩
  refine CERW.Support.Law.measure_le_of_subset_union (fun ω hω => ?_) (hMB hξ' hX n hn2) hnull
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith [hP])
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨hA, hN⟩ := hcon
  simp only [Set.mem_setOf_eq, not_not] at hN
  apply hω
  intro y hy
  have hMBω : |driftDynkin ε ξ (fun z => b (z - y)) X n ω| ≤
      C_B * (Real.sqrt ((∑ j ∈ Finset.range n,
        (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log (n + 2)) +
          Real.log (n + 2)) := by
    by_contra hnot
    exact hA ⟨y, hy, not_le.mp hnot⟩
  exact abs_le_add_of_abs_add_le
    (mul_nonneg hCpt (by linarith)) (Real.sqrt_nonneg _)
    (hpt ε hε.le ξ hξ hξ0 X ω hN.1 hN.2 n (by omega) y hy) hMBω

/-! ### The distributional Laplacian is determined by the body -/

section Uniqueness

open scoped ContDiff CompactlySupported Pointwise Convolution

/-- A compactly supported continuous function is uniformly approximated, within `δ`, by a smooth
compactly supported function whose support lies in the unit neighbourhood of the support of `f`. -/
private lemma exists_smooth_approx (f : C_c(EuclideanSpace ℝ (Fin d), ℝ)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ tsupport (f : EuclideanSpace ℝ (Fin d) → ℝ) +
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ∧
      ∀ a, dist (g a) (f a) ≤ δ := by
  have hfc : Continuous (f : EuclideanSpace ℝ (Fin d) → ℝ) := f.continuous
  have hfs : HasCompactSupport (f : EuclideanSpace ℝ (Fin d) → ℝ) := f.hasCompactSupport
  have huc : UniformContinuous (f : EuclideanSpace ℝ (Fin d) → ℝ) :=
    hfs.uniformContinuous_of_continuous hfc
  obtain ⟨η, hη, hηδ⟩ := Metric.uniformContinuous_iff.mp huc δ hδ
  set ε : ℝ := min η 1 with hε
  have hε0 : 0 < ε := lt_min hη one_pos
  set φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
    ⟨ε / 2, ε, half_pos hε0, half_lt_self hε0⟩ with hφ
  refine ⟨((φ.normed (volume : Measure (EuclideanSpace ℝ (Fin d)))) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (EuclideanSpace ℝ (Fin d)))]
      (f : EuclideanSpace ℝ (Fin d) → ℝ)), ?_, ?_, ?_, ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hfc.locallyIntegrable
  · exact φ.hasCompactSupport_normed.convolution _ hfs
  · have hcompact : IsCompact (tsupport (f : EuclideanSpace ℝ (Fin d) → ℝ) +
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
      hfs.isCompact.add (isCompact_closedBall _ _)
    refine closure_minimal ?_ hcompact.isClosed
    refine (support_convolution_subset_swap _).trans ?_
    refine Set.add_subset_add subset_closure ?_
    rw [φ.support_normed_eq]
    exact (Metric.ball_subset_closedBall).trans
      (Metric.closedBall_subset_closedBall (min_le_right _ _))
  · intro a
    refine φ.dist_normed_convolution_le hfc.aestronglyMeasurable (fun x hx => ?_)
    have hx' : dist x a < η := lt_of_lt_of_le hx (min_le_left _ _)
    exact (hηδ hx').le

/-- Two locally finite measures with the same integrals against the smooth compactly supported
functions have the same integrals against the compactly supported continuous functions. -/
private lemma integral_eq_of_smooth {m₁ m₂ : Measure (EuclideanSpace ℝ (Fin d))}
    [IsLocallyFiniteMeasure m₁] [IsLocallyFiniteMeasure m₂]
    (h : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ v, φ v ∂m₁ = ∫ v, φ v ∂m₂) (f : C_c(EuclideanSpace ℝ (Fin d), ℝ)) :
    ∫ v, f v ∂m₁ = ∫ v, f v ∂m₂ := by
  have hfs : HasCompactSupport (f : EuclideanSpace ℝ (Fin d) → ℝ) := f.hasCompactSupport
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support hfs
  choose g hg using fun k : ℕ => exists_smooth_approx f (δ := 1 / ((k : ℝ) + 1)) (by positivity)
  set S : Set (EuclideanSpace ℝ (Fin d)) := tsupport (f : EuclideanSpace ℝ (Fin d) → ℝ) +
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 with hS
  have hSc : IsCompact S := hfs.isCompact.add (isCompact_closedBall _ _)
  have hgS : ∀ k a, a ∉ S → g k a = 0 := by
    intro k a ha
    by_contra hne
    exact ha ((hg k).2.2.1 (subset_closure (Function.mem_support.mpr hne)))
  have hlim : ∀ (m : Measure (EuclideanSpace ℝ (Fin d))) [IsLocallyFiniteMeasure m],
      Tendsto (fun k : ℕ => ∫ v, g k v ∂m) atTop (𝓝 (∫ v, f v ∂m)) := by
    intro m _
    refine tendsto_integral_of_dominated_convergence
      (fun a => S.indicator (fun _ => M + 1) a) (fun k => ?_) ?_ (fun k => ?_) ?_
    · exact ((hg k).1.continuous.aestronglyMeasurable)
    · exact (integrable_indicator_iff hSc.measurableSet).mpr
        (integrableOn_const hSc.measure_lt_top.ne)
    · refine Eventually.of_forall fun a => ?_
      by_cases ha : a ∈ S
      · rw [Set.indicator_of_mem ha]
        have h1 := (hg k).2.2.2 a
        have h2 : |f a| ≤ M := by
          have := hM a
          rwa [Real.norm_eq_abs] at this
        rw [Real.norm_eq_abs]
        have h3 : 1 / ((k : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith
        have h4 := abs_sub_abs_le_abs_sub (g k a) (f a)
        rw [Real.dist_eq] at h1
        linarith
      · rw [Set.indicator_of_notMem ha, hgS k a ha, norm_zero]
    · refine Eventually.of_forall fun a => ?_
      have hz : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      refine tendsto_iff_dist_tendsto_zero.mpr ?_
      exact squeeze_zero (fun k => dist_nonneg) (fun k => (hg k).2.2.2 a) hz
  exact tendsto_nhds_unique (hlim m₁)
    ((hlim m₂).congr fun k => (h (g k) (hg k).1 (hg k).2.1).symm)


/-- **Uniqueness of the distributional Laplacian.** A locally finite measure is determined by its
integrals against the smooth compactly supported functions: two locally finite measures that are
distributional Laplacians of the same function are equal. -/
theorem eq_of_isDistribLaplacian {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {m₁ m₂ : Measure (EuclideanSpace ℝ (Fin d))} [IsLocallyFiniteMeasure m₁]
    [IsLocallyFiniteMeasure m₂] (h₁ : CERW.IsDistribLaplacian Ψ m₁)
    (h₂ : CERW.IsDistribLaplacian Ψ m₂) : m₁ = m₂ := by
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => integral_eq_of_smooth
    (fun φ hφ hc => ?_) f
  rw [h₁ φ hφ hc, h₂ φ hφ hc]

/-- **The distributional Laplacian of the gauge is unique.** For a compact convex `K` with the
origin in its interior there is exactly one locally finite measure `m` with
`IsDistribLaplacian (gauge K) m`, so the measure of the cell estimate and of the growth bound is
determined by the body. -/
theorem gauge_laplacian_existsUnique {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    ∃! m : Measure (EuclideanSpace ℝ (Fin d)),
      IsLocallyFiniteMeasure m ∧ CERW.IsDistribLaplacian (gauge K) m := by
  obtain ⟨m, hm, hlap⟩ := CERW.Support.Norm.GaugeLaplacian.exists_isDistribLaplacian_gauge hK hc h0
  refine ⟨m, ⟨hm, hlap⟩, fun m' hm' => ?_⟩
  haveI := hm'.1
  haveI := hm
  exact eq_of_isDistribLaplacian hm'.2 hlap

end Uniqueness

/-! ### Consumption at bodies that are not symmetric -/

section Consumption

open CERW.Support.Norm.GaugePotential (cornerTriangle isCompact_cornerTriangle
  convex_cornerTriangle zero_mem_interior_cornerTriangle gauge_cornerTriangle_eq)

/-- **The fine pointwise bound at the non-even planar body `cutDisc`, `ε = 1/4`.** The gauge of
`cutDisc` is not a norm. A subgradient selection, an actual walk `IsDriftCERW μ (1/4) ξ X` and a
locally finite distributional Laplacian of the gauge that charges every ball about the origin exist,
and for this selection every walk of this law satisfies the fine pointwise bound, for every `p > 0`
and `n ≥ 2`, with probability at least `1 - C n^{-p}`. -/
theorem cutDisc_pointwise_local_time {p : ℝ} (hp : 0 < p) :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 →
        CERW.IsSubgradient (gauge cutDisc) (CERW.toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), CERW.IsDriftCERW μ (1 / 4 : ℝ) ξ X) ∧
      (∃ m : Measure (EuclideanSpace ℝ (Fin 2)), IsLocallyFiniteMeasure m ∧
        CERW.IsDistribLaplacian (gauge cutDisc) m ∧
        (∀ {ρ : ℝ}, 0 < ρ → 0 < m (Metric.ball 0 ρ)) ∧
        ∀ m' : Measure (EuclideanSpace ℝ (Fin 2)), IsLocallyFiniteMeasure m' →
          CERW.IsDistribLaplacian (gauge cutDisc) m' → m' = m) ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site 2), CERW.IsDriftCERW μ (1 / 4 : ℝ) ξ X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ (∀ y : Site 2, euclidNorm y ≤ 3 * n →
              |(CERW.localTime (fun j => X j ω) n y : ℝ) -
                  CERW.normPotential 2 (1 / 4 : ℝ) (gauge cutDisc)
                    (CERW.cellSet (fun j => X j ω) n) (CERW.toSpace y)| ≤
                C * (Real.sqrt ((∑ j ∈ Finset.range n,
                  (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * ((2 : ℕ) : ℝ))) *
                    Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2)))}
            ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hell : ∀ i : Fin 2,
      (1 / 4 : ℝ) * gauge cutDisc (CERW.coordVec i) < 1 / ((2 : ℕ) : ℝ) ∧
      (1 / 4 : ℝ) * gauge cutDisc (-CERW.coordVec i) < 1 / ((2 : ℕ) : ℝ) :=
    fun i => cutDisc_ellipticity i
  obtain ⟨ξ, hξ, hξ0, hwalk⟩ := exists_isDriftCERW_gauge (d := 2) (by norm_num)
    convex_cutDisc zero_mem_interior_cutDisc (by norm_num) hell
  obtain ⟨-, m, hm, hlap, hpos, -⟩ := cutDisc_laplacian_cell
  have huniq : ∀ m' : Measure (EuclideanSpace ℝ (Fin 2)), IsLocallyFiniteMeasure m' →
      CERW.IsDistribLaplacian (gauge cutDisc) m' → m' = m := fun m' hm' hlap' => by
    haveI := hm'
    haveI := hm
    exact eq_of_isDistribLaplacian hlap' hlap
  obtain ⟨C, hC, hbound⟩ := gauge_pointwise_local_time (d := 2) le_rfl
    isCompact_cutDisc convex_cutDisc zero_mem_interior_cutDisc
    (1 / 4 : ℝ) (by norm_num) hell p hp
  exact ⟨ξ, hξ, hξ0, hwalk, ⟨m, hm, hlap, hpos, huniq⟩, C, hC,
    fun μ _ X hX n hn => hbound ξ hξ hξ0 μ X hX n hn⟩

/-- **The fine pointwise bound at a body with corners, `ε = 1/4`.** The gauge of the triangle
`cornerTriangle` is not differentiable along the ray through the vertex `(-1,-1)` and is not even. A
subgradient selection, an actual walk `IsDriftCERW μ (1/4) ξ X` and a locally finite distributional
Laplacian of the gauge that charges every ball about the origin exist, and for this selection every
walk of this law satisfies the fine pointwise bound, for every `p > 0` and `n ≥ 2`, with probability
at least `1 - C n^{-p}`. -/
theorem cornerTriangle_pointwise_local_time {p : ℝ} (hp : 0 < p) :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 →
        CERW.IsSubgradient (gauge cornerTriangle) (CERW.toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), CERW.IsDriftCERW μ (1 / 4 : ℝ) ξ X) ∧
      (∃ m : Measure (EuclideanSpace ℝ (Fin 2)), IsLocallyFiniteMeasure m ∧
        CERW.IsDistribLaplacian (gauge cornerTriangle) m ∧
        (∀ {ρ : ℝ}, 0 < ρ → 0 < m (Metric.ball 0 ρ)) ∧
        ∀ m' : Measure (EuclideanSpace ℝ (Fin 2)), IsLocallyFiniteMeasure m' →
          CERW.IsDistribLaplacian (gauge cornerTriangle) m' → m' = m) ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site 2), CERW.IsDriftCERW μ (1 / 4 : ℝ) ξ X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ (∀ y : Site 2, euclidNorm y ≤ 3 * n →
              |(CERW.localTime (fun j => X j ω) n y : ℝ) -
                  CERW.normPotential 2 (1 / 4 : ℝ) (gauge cornerTriangle)
                    (CERW.cellSet (fun j => X j ω) n) (CERW.toSpace y)| ≤
                C * (Real.sqrt ((∑ j ∈ Finset.range n,
                  (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * ((2 : ℕ) : ℝ))) *
                    Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2)))}
            ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hell : ∀ i : Fin 2,
      (1 / 4 : ℝ) * gauge cornerTriangle (CERW.coordVec i) < 1 / ((2 : ℕ) : ℝ) ∧
      (1 / 4 : ℝ) * gauge cornerTriangle (-CERW.coordVec i) < 1 / ((2 : ℕ) : ℝ) :=
    by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, gauge_cornerTriangle_eq]
      norm_num [CERW.coordVec]
    · simp only [Fin.mk_one, gauge_cornerTriangle_eq]
      norm_num [CERW.coordVec]
  obtain ⟨ξ, hξ, hξ0, hwalk⟩ := exists_isDriftCERW_gauge (d := 2) (by norm_num)
    convex_cornerTriangle zero_mem_interior_cornerTriangle (by norm_num) hell
  obtain ⟨-, m, hm, hlap, hpos, -⟩ := cornerTriangle_laplacian_cell
  have huniq : ∀ m' : Measure (EuclideanSpace ℝ (Fin 2)), IsLocallyFiniteMeasure m' →
      CERW.IsDistribLaplacian (gauge cornerTriangle) m' → m' = m := fun m' hm' hlap' => by
    haveI := hm'
    haveI := hm
    exact eq_of_isDistribLaplacian hlap' hlap
  obtain ⟨C, hC, hbound⟩ := gauge_pointwise_local_time (d := 2) le_rfl
    isCompact_cornerTriangle convex_cornerTriangle zero_mem_interior_cornerTriangle
    (1 / 4 : ℝ) (by norm_num) hell p hp
  exact ⟨ξ, hξ, hξ0, hwalk, ⟨m, hm, hlap, hpos, huniq⟩, C, hC,
    fun μ _ X hX n hn => hbound ξ hξ hξ0 μ X hX n hn⟩

end Consumption

end CERW.Support.Norm.GaugePointwise
