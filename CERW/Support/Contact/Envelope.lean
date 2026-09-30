import CERW.Support.Geometry.Newton
import CERW.Support.Geometry.Bound
import CERW.Support.Occupation.Cells
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellSetVolume

/-!
# The local-time envelope and the inner inclusion

With `D = D_n ⊇ B(0, b)` and `E = D \ B(0, b)` of volume `m`, `U_D = U_{B(0,b)} + U_E`. By
`eq:ballpotential`, `U_{B(0,b)}(y) = 2dε (b - |y|)_+`, and by `eq:packing`, `|U_E| ≤ C_d ε m^{1/d}`.
So `eq:pointwise` turns into the envelope `ℓ_n(y) ≤ 2dε (b - |y|)_+ + C_d ε m^{1/d} + |ρ| + |M|`.
Also, every lattice point in `B(0, b)` lies in `A_n`, which is the inner inclusion of `eq:sandwich`.
-/

namespace CERW.Support.Contact

open MeasureTheory LatticeProb CERW CERW.Support.Geometry CERW.Support.Occupation

variable {d : ℕ}

/-- The envelope: if `B(0, b) ⊆ D_n` with `b > 0` and `ℓ_n(y) = U_{D_n}(y) + ρ - M`, then
`ℓ_n(y) ≤ 2dε (b - |y|)_+ + 2dε ω_d^{-1/d} |D_n \ B(0, b)|^{1/d} + |ρ| + |M|`. -/
theorem localTime_le_envelope (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) (X : ℕ → Site d) (n : ℕ)
    {b : ℝ} (hb : 0 < b) (hball : Metric.ball 0 b ⊆ cellSet X n) (y : Site d) {ρ M : ℝ}
    (hpt : (localTime X n y : ℝ) = potential d ε (cellSet X n) (toSpace y) + ρ - M) :
    (localTime X n y : ℝ) ≤ 2 * d * ε * max (b - euclidNorm y) 0 +
      2 * d * ε * unitBallVolume d ^ (-(1 : ℝ) / d) *
        (volume (cellSet X n \ Metric.ball 0 b)).toReal ^ ((1 : ℝ) / d) + |ρ| + |M| := by
  have hd1 : 1 ≤ d := by omega
  have hDmeas : MeasurableSet (cellSet X n) := measurableSet_cellSet X n
  have hbmeas : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) :=
    measurableSet_ball
  have hDlt : volume (cellSet X n) < ⊤ :=
    lt_of_le_of_lt (measure_mono (cellSet_subset_ball hd1 X n)) measure_ball_lt_top
  have hDfin : volume (cellSet X n) ≠ ⊤ := hDlt.ne
  have hEmeas : MeasurableSet (cellSet X n \ Metric.ball 0 b) := hDmeas.diff hbmeas
  have hEfin : volume (cellSet X n \ Metric.ball 0 b) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.sdiff_subset) hDlt).ne
  let F : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun v => inner ℝ (unitDir v) (v - toSpace y) / ‖v - toSpace y‖ ^ d
  have hintD : IntegrableOn F (cellSet X n) volume :=
    integrableOn_potentialIntegrand hd1 hDmeas hDfin (toSpace y)
  have hintB : IntegrableOn F (Metric.ball 0 b) volume := hintD.mono_set hball
  have hintE : IntegrableOn F (cellSet X n \ Metric.ball 0 b) volume :=
    hintD.mono_set Set.sdiff_subset
  have hunion : Metric.ball 0 b ∪ (cellSet X n \ Metric.ball 0 b) = cellSet X n :=
    Set.union_sdiff_cancel hball
  have hsplit : ∫ v in cellSet X n, F v =
      (∫ v in Metric.ball 0 b, F v) + (∫ v in cellSet X n \ Metric.ball 0 b, F v) := by
    conv_lhs => rw [← hunion]
    exact setIntegral_union Set.disjoint_sdiff_right hEmeas hintB hintE
  have hpotD : potential d ε (cellSet X n) (toSpace y) =
      potential d ε (Metric.ball 0 b) (toSpace y) +
        potential d ε (cellSet X n \ Metric.ball 0 b) (toSpace y) := by
    change (2 * ε / unitBallVolume d) * (∫ v in cellSet X n, F v) =
      (2 * ε / unitBallVolume d) * (∫ v in Metric.ball 0 b, F v) +
        (2 * ε / unitBallVolume d) *
          (∫ v in cellSet X n \ Metric.ball 0 b, F v)
    rw [hsplit]
    ring
  have hpotB : potential d ε (Metric.ball 0 b) (toSpace y) =
      2 * d * ε * max (b - euclidNorm y) 0 := by
    rw [potential_ball hd ε hb (toSpace y), norm_toSpace]
  have hpotE : potential d ε (cellSet X n \ Metric.ball 0 b) (toSpace y) ≤
      2 * d * ε * unitBallVolume d ^ (-(1 : ℝ) / d) *
        (volume (cellSet X n \ Metric.ball 0 b)).toReal ^ ((1 : ℝ) / d) :=
    le_trans (le_abs_self _) (abs_potential_le hd1 hε hEmeas hEfin (toSpace y))
  rw [hpt, hpotD, hpotB]
  linarith [hpotE, le_abs_self ρ, neg_abs_le M]

/-- The inner inclusion: if `B(0, b) ⊆ D_n`, every site with `|x| < b` is a departure site. -/
theorem mem_departureRange_of_lt (X : ℕ → Site d) (n : ℕ) {b : ℝ}
    (hball : Metric.ball 0 b ⊆ cellSet X n) {x : Site d} (hx : euclidNorm x < b) :
    x ∈ departureRange X n := by
  have hmem : toSpace x ∈ Metric.ball 0 b := by
    rw [Metric.mem_ball, dist_zero_right, norm_toSpace]
    exact hx
  have hcenter : cellCenter (toSpace x) ∈ departureRange X n :=
    (mem_cellSet_iff X n (toSpace x)).mp (hball hmem)
  rwa [← eq_cellCenter_of_mem_cell (toSpace_mem_cell x)] at hcenter

end CERW.Support.Contact
