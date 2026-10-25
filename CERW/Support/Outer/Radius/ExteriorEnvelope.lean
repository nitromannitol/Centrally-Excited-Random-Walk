module

public import CERW.Support.Outer.Radius.PotentialConvolution

@[expose] public section

/-!
# Exterior Envelope

The local-time bracket outside the inner ball is bounded by an exterior potential envelope. The
convolution estimate and discrete absorption close this bound.
The retained labels `eq:convolution-bound`, `eq:envelopehigh`, `eq:potential-convolution`
refer to the earlier source `paper/limit-shapes.tex`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- `eq:convolution-bound`, `eq:potential-convolution` and `eq:envelopehigh` (`d ≥ 3`): beyond the
inner ball the bracket `W_x` and the local time at the site `x` of a point `y` are bounded by
`log n` plus the positive potential of `E = D_n ∖ B(0,b)` at `y`. -/
theorem envelope_high (hd : 3 ≤ d) (hN : NewtonConv d) {ε : ℝ} (hε : 0 < ε) (c₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      (∀ j, euclidNorm (Y j) ≤ j) →
      (∀ x : Site d, euclidNorm x ≤ 3 * n →
        |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
          c₁ * (Real.sqrt (braSum Y n x * Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2))) →
      ∀ b : ℝ, 0 ≤ b → Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ cellSet Y n →
      ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ 2 * n →
        braSum Y n (cellCenter y) ≤ C * (Real.log ((n : ℝ) + 2) +
          positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y) ∧
        (localTime Y n (cellCenter y) : ℝ) ≤ C * (Real.log ((n : ℝ) + 2) +
          positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  set C₁ : ℝ := max c₁ 0 with hC₁def
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  obtain ⟨CM, hCM0, hCM⟩ := CERW.Support.Geometry.exists_potential_cell_modulus hd2
  set C₃ : ℝ := 2 * CM * ε with hC₃def
  have hC₃ : 0 ≤ C₃ := by positivity
  obtain ⟨c₀, α₁, hc₀, hα₁, hlat⟩ := ev_kernel_sum_le hd hC₁
  obtain ⟨β, hβ, hpot⟩ := ev_sum_cellWeight_mul_potential_le hd hN hε hC₃
  set m : ℝ := ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun ζ => ev_chi_nonneg _
  set K : ℝ := (2 * β + α₁ + 2 * m) / c₀ with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨1 + C₃ + C₁ * K + 2 * C₁ + K, by positivity, max 2 ⌈4 * Real.sqrt d⌉₊, ?_⟩
  intro Y n hn hYn hfine b hb hball y hby hyn
  have hn2 : 2 ≤ n := le_of_max_le_left hn
  have hn4 : 4 * Real.sqrt d ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hn)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hsd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hL1 : 1 ≤ L := CERW.Support.Law.one_le_log_add_two hn2
  have hmax : maxRadius Y n ≤ n := ev_maxRadius_le_nat Y n hYn
  have hDmeas : MeasurableSet (cellSet Y n) := CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDsub : cellSet Y n ⊆ Metric.ball 0 ((n : ℝ) + Real.sqrt d) :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n).trans
      (Metric.ball_subset_ball (by linarith))
  have hDbdd : Bornology.IsBounded (cellSet Y n) := Metric.isBounded_ball.subset hDsub
  have hEmeas : MeasurableSet (cellSet Y n \ Metric.ball 0 b) := hDmeas.diff measurableSet_ball
  have hEfin : volume (cellSet Y n \ Metric.ball 0 b) ≠ ⊤ :=
    (hDbdd.subset Set.sdiff_subset).measure_lt_top.ne
  have hfine₁ : ∀ x : Site d, euclidNorm x ≤ 3 * n →
      |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
        C₁ * (Real.sqrt (braSum Y n x * L) + L) := by
    intro x hx
    exact (hfine x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (add_nonneg (Real.sqrt_nonneg _) (by linarith)))
  have hmod : ∀ u v : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ 2 * ((n : ℝ) + Real.sqrt d) →
      ‖u - v‖ ≤ Real.sqrt d →
      |potential d ε (cellSet Y n) u - potential d ε (cellSet Y n) v| ≤ C₃ * L := by
    intro u v hu huv
    have h := hCM ε hε.le ((n : ℝ) + Real.sqrt d) (by linarith) (cellSet Y n) hDmeas hDsub
      u v hu huv
    have hsq : (n : ℝ) + Real.sqrt d + 2 ≤ ((n : ℝ) + 2) ^ 2 := by
      have e : ((n : ℝ) + 2) ^ 2 = (n : ℝ) * n + 3 * n + 2 + ((n : ℝ) + 2) := by ring
      have := mul_nonneg hn0 hn0
      linarith
    have hlog : Real.log ((n : ℝ) + Real.sqrt d + 2) ≤ 2 * L := by
      have h3 : Real.log (((n : ℝ) + 2) ^ 2) = 2 * L := by
        rw [Real.log_pow, hL]
        norm_num
      rw [← h3]
      exact Real.log_le_log (by linarith) hsq
    calc |potential d ε (cellSet Y n) u - potential d ε (cellSet Y n) v|
        ≤ CM * ε * Real.log ((n : ℝ) + Real.sqrt d + 2) := h
      _ ≤ CM * ε * (2 * L) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = C₃ * L := by rw [hC₃def]; ring
  have hzy : ‖toSpace (cellCenter y) - y‖ ≤ Real.sqrt d / 2 := by
    rw [norm_sub_rev]
    exact CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter y)
  set P : ℝ := positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y with hPdef
  have hP0 : 0 ≤ P := ev_positivePotential_nonneg hε.le _ _
  set W : ℝ := braSum Y n (cellCenter y) with hWdef
  have hb1 : c₀ * W ≤ 2 * ∑ x ∈ LatticeProb.ballFinset d (2 * n),
      ev_cellWeight d y x * potential d ε (cellSet Y n) (toSpace x) + α₁ * L :=
    hlat Y n (fun x => potential d ε (cellSet Y n) (toSpace x)) hYn hfine₁ y (cellCenter y) hzy
  have hb2 : ∑ x ∈ LatticeProb.ballFinset d (2 * n),
      ev_cellWeight d y x * potential d ε (cellSet Y n) (toSpace x) ≤ β * L + m * P :=
    hpot Y n hn2 hn4 hYn hmod b y hb hball hby hyn
  have hW0 : 0 ≤ W := by
    rw [hWdef]
    unfold braSum
    exact Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg (Y j - cellCenter y)]) _
  have hW : W ≤ K * (L + P) := by
    refine le_of_mul_le_mul_left ?_ hc₀
    have h1 : c₀ * W ≤ (2 * β + α₁) * L + 2 * m * P := by
      linarith
    have h2 : c₀ * (K * (L + P)) = (2 * β + α₁ + 2 * m) * (L + P) := by
      rw [hK]
      field_simp
    rw [h2]
    have h3 : 0 ≤ (2 * β + α₁) * P := mul_nonneg (by linarith) hP0
    have h4 : 0 ≤ 2 * m * L := mul_nonneg (by linarith) (by linarith)
    linarith
  have hLP : 0 ≤ L + P := by linarith
  have hKC : K ≤ 1 + C₃ + C₁ * K + 2 * C₁ + K := by
    have := mul_nonneg hC₁ hK0
    linarith
  refine ⟨hW.trans (mul_le_mul_of_nonneg_right hKC hLP), ?_⟩
  have hzn : euclidNorm (cellCenter y) ≤ 3 * n := by
    have h1 : ‖toSpace (cellCenter y)‖ - ‖y‖ ≤ ‖toSpace (cellCenter y) - y‖ :=
      norm_sub_norm_le _ _
    rw [norm_toSpace] at h1
    linarith
  have hℓ : (localTime Y n (cellCenter y) : ℝ) -
      potential d ε (cellSet Y n) (toSpace (cellCenter y)) ≤ C₁ * (Real.sqrt (W * L) + L) :=
    (abs_le.mp (hfine₁ (cellCenter y) hzn)).2
  have hUz : potential d ε (cellSet Y n) (toSpace (cellCenter y)) ≤
      potential d ε (cellSet Y n) y + C₃ * L := by
    have h := hmod y (toSpace (cellCenter y)) (by linarith)
      (by rw [norm_sub_rev]; linarith)
    have := (abs_le.mp h).1
    linarith
  have hUy : potential d ε (cellSet Y n) y ≤ P := by
    rw [ev_potential_split hd2 ε hDmeas hDbdd hb hball y,
      max_eq_right (by linarith : b - ‖y‖ ≤ 0), mul_zero, zero_add]
    exact ev_potential_le_positivePotential hd1 hε.le hEmeas hEfin y
  have hsqrt : Real.sqrt (W * L) ≤ W + L := by
    have h1 : W * L ≤ (W + L) ^ 2 := by
      have e : (W + L) ^ 2 = W * L + (W * W + W * L + L * L) := by ring
      have := mul_nonneg hW0 hW0
      have := mul_nonneg hW0 (by linarith : (0 : ℝ) ≤ L)
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ L) (by linarith : (0 : ℝ) ≤ L)
      linarith
    calc Real.sqrt (W * L) ≤ Real.sqrt ((W + L) ^ 2) := Real.sqrt_le_sqrt h1
      _ = W + L := Real.sqrt_sq (by linarith)
  have hC₁sq : C₁ * Real.sqrt (W * L) ≤ C₁ * (K * (L + P) + L) :=
    mul_le_mul_of_nonneg_left (hsqrt.trans (by linarith)) hC₁
  have e : (1 + C₃ + C₁ * K + 2 * C₁ + K) * (L + P) =
      (P + C₃ * L + C₁ * (K * (L + P) + L) + C₁ * L) +
        (L + C₃ * P + 2 * C₁ * P + K * (L + P)) := by ring
  have h5 : 0 ≤ C₃ * P := mul_nonneg hC₃ hP0
  have h6 : 0 ≤ 2 * C₁ * P := mul_nonneg (by linarith) hP0
  have h7 : 0 ≤ K * (L + P) := mul_nonneg hK0 hLP
  have h8 : (localTime Y n (cellCenter y) : ℝ) ≤
      P + C₃ * L + C₁ * (K * (L + P) + L) + C₁ * L := by
    have e2 : C₁ * (Real.sqrt (W * L) + L) = C₁ * Real.sqrt (W * L) + C₁ * L := by ring
    linarith
  linarith
/-! ### The geometry of a set in an annulus -/

end CERW.Support.Outer.Radius
