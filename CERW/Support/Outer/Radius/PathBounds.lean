import CERW.Support.Statements
import CERW.Support.Main.EventProb
import CERW.Support.Main.BorelCantelli
import CERW.Support.Main.LimitShape
import CERW.Support.Main.ScaleLimits
import CERW.Support.Drift.Bridge
import CERW.Support.Norm.BallLayer
import CERW.Support.Contact.ContactCell
import CERW.Support.Inner.InnerRadius
import CERW.Support.Contact.ContactLower
import CERW.Support.Contact.Kernel
import CERW.Support.Geometry.Assembly
import CERW.Support.LocalTime.KernelAsymptotics
import CERW.Support.LocalTime.LocalMart
import CERW.Support.Drift.Dynkin

/-!
# Path Bounds

The radius, bracket sum and path events collect the deterministic inputs to the outer-radius
argument. Their monotonicity allows a common choice of event constants.
The retained labels `eq:linear-mart`, `eq:newton-convolution`, `eq:radial-convolution`
refer to the earlier source `paper/limit-shapes.tex`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- The radius `r_n = ((d+1) n / (2 d ε ω_d))^{1/(d+1)}` of `eq:radius`. -/
noncomputable def radius (d : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  ((d + 1) * n / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))

/-- The rate `q_n` of `eq:qn`. -/
noncomputable def qrate (d : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  if d = 2 then Real.sqrt (Real.log n / radius d ε n) else Real.log n / radius d ε n

/-- The bracket sum `W_x = Σ_{j<n} (1 + |Y_j - x|)^{2-2d}` of the local martingale at `x`. -/
noncomputable def braSum (Y : ℕ → Site d) (n : ℕ) (x : Site d) : ℝ :=
  ∑ j ∈ Finset.range n, (1 + euclidNorm (Y j - x)) ^ (2 - 2 * (d : ℝ))

/-- The compensated position `Z_t = X_t + ε Σ_{j<t} I_j u_{X_j}` of a path. -/
noncomputable def compPath (d : ℕ) (ε : ℝ) (Y : ℕ → Site d) (t : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  toSpace (Y t) + ε • ∑ j ∈ Finset.range t,
    if Y j ∉ departureRange Y j then unitDir (toSpace (Y j)) else 0

/-- The linear martingale event of `eq:linear-mart` for the Euclidean walk, for every direction
`u_s` with `|s| ≤ n` and every level `k`. -/
def LinOK (d : ℕ) (ε C₁ : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  ∀ s : Site d, euclidNorm s ≤ n → ∀ k : ℕ, k ≤ n →
    |dynkinMart (driftStepProb d ε (fun z => unitDir (toSpace z)))
        (fun z => max (inner ℝ (unitDir (toSpace s)) (toSpace z) - k) 0) Y n|
      ≤ C₁ * (Real.sqrt (Real.log n *
            ∑ z ∈ (departureRange Y n).filter
              (fun z => (k : ℝ) - 1 < inner ℝ (unitDir (toSpace s)) (toSpace z)),
            (localTime Y n z : ℝ)) + Real.log n)

/-- The deterministic consequences of the good events of local-time and crossing good events
(`sec:local`, `sec:crossing`). -/
structure PathFacts (d : ℕ) (ε C₀ C₁ : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop where
  start : Y 0 = 0
  step : ∀ j, Y (j + 1) - Y j ∈ unitSteps d
  maxLoc : (maxLocalTime Y n : ℝ) ≤ C₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1))
  maxRad : maxRadius Y n ≤ C₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1))
  glob : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
    |cellLocalTime Y n y - potential d ε (cellSet Y n) y| ≤ C₁ *
      (if d = 2 then Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2) + Real.log ((n : ℝ) + 2)
        else Real.sqrt (maxLocalTime Y n * Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2))
  point : ∀ x : Site d, euclidNorm x ≤ 3 * n →
    |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
      C₁ * (Real.sqrt (braSum Y n x * Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2))
  vec : ∀ s t : ℕ, s < t → t ≤ n →
    ‖compPath d ε Y t - compPath d ε Y s‖ ≤ C₁ * Real.sqrt (((t : ℝ) - s) * Real.log ((n : ℝ) + 2))

/-- The local-time inputs to the outer-radius and profile estimates. The crossing estimate
is supplied separately, so these inputs do not include the vector martingale bound. -/
structure LocalPathFacts (d : ℕ) (ε C₀ C₁ : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop where
  start : Y 0 = 0
  step : ∀ j, Y (j + 1) - Y j ∈ unitSteps d
  maxLoc : (maxLocalTime Y n : ℝ) ≤ C₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1))
  maxRad : maxRadius Y n ≤ C₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1))
  glob : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
    |cellLocalTime Y n y - potential d ε (cellSet Y n) y| ≤ C₁ *
      (if d = 2 then Real.sqrt (maxLocalTime Y n) * Real.log ((n : ℝ) + 2) + Real.log ((n : ℝ) + 2)
        else Real.sqrt (maxLocalTime Y n * Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2))
  point : ∀ x : Site d, euclidNorm x ≤ 3 * n →
    |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
      C₁ * (Real.sqrt (braSum Y n x * Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2))

/-- Path bounds supply local-time bounds by forgetting the vector estimate. -/
instance {ε C₀ C₁ : ℝ} {Y : ℕ → Site d} {n : ℕ} :
    Coe (PathFacts d ε C₀ C₁ Y n) (LocalPathFacts d ε C₀ C₁ Y n) where
  coe h := ⟨h.start, h.step, h.maxLoc, h.maxRad, h.glob, h.point⟩

/-- The clauses of Proposition `prop:inner` for a path. -/
def InnerOK (d : ℕ) (ε C : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  |innerRadius Y n - radius d ε n| ≤ C * radius d ε n * qrate d ε n ∧
  volume (((radius d ε n)⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
      ≤ ENNReal.ofReal (C * qrate d ε n) ∧
  ∀ y : EuclideanSpace ℝ (Fin d),
    |cellLocalTime Y n y - 2 * d * ε * max (radius d ε n - ‖y‖) 0|
      ≤ C * radius d ε n * qrate d ε n ^ ((1 : ℝ) / d)

/-- The maximal local time over the visited sites of norm at least `b`. -/
noncomputable def outerMax (Y : ℕ → Site d) (n : ℕ) (b : ℝ) : ℕ :=
  ((departureRange Y n).filter (fun z => b ≤ euclidNorm z)).sup (localTime Y n)

-- Preserve rewriting and unfolding through the original private aliases.
attribute [reducible] radius qrate braSum outerMax

/-- The mass bound of `eq:mass` for the part of `D_n` outside the inner ball. -/
def MassOK (d : ℕ) (ε Cm : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  (volume (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (innerRadius Y n))).toReal
    ≤ Cm * radius d ε n ^ d * qrate d ε n

/-- The crossing bound `eq:euclid-crossing`. -/
def CrossOK (d : ℕ) (Ccr : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  ∀ b : ℝ, 0 ≤ b → maxRadius Y n ≤ b + Ccr * (1 + (outerMax Y n b : ℝ)) * Real.log n

/-! ### Monotonicity in the constants -/

/-- The logarithm `log (n + 2)` is nonnegative. -/
lemma mono_log_nonneg (n : ℕ) : 0 ≤ Real.log ((n : ℝ) + 2) :=
  Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

/-- `PathFacts` is monotone in its constant `C₁`. -/
theorem PathFacts.mono {ε C₀ C₁ C₁' : ℝ} (h : C₁ ≤ C₁') {Y : ℕ → Site d} {n : ℕ}
    (hY : PathFacts d ε C₀ C₁ Y n) : PathFacts d ε C₀ C₁' Y n := by
  have hL := mono_log_nonneg n
  refine ⟨hY.start, hY.step, hY.maxLoc, hY.maxRad, fun y hy => ?_, fun x hx => ?_,
    fun s t hst htn => ?_⟩
  · refine (hY.glob y hy).trans (mul_le_mul_of_nonneg_right h ?_)
    split_ifs
    · exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) hL
    · exact add_nonneg (Real.sqrt_nonneg _) hL
  · exact (hY.point x hx).trans (mul_le_mul_of_nonneg_right h
      (add_nonneg (Real.sqrt_nonneg _) hL))
  · exact (hY.vec s t hst htn).trans (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _))

/-- `LinOK` is monotone in its constant. -/
theorem LinOK.mono {ε C₁ C₁' : ℝ} (h : C₁ ≤ C₁') {Y : ℕ → Site d} {n : ℕ}
    (hY : LinOK d ε C₁ Y n) : LinOK d ε C₁' Y n := by
  intro s hs k hk
  refine (hY s hs k hk).trans (mul_le_mul_of_nonneg_right h ?_)
  exact add_nonneg (Real.sqrt_nonneg _) (Real.log_natCast_nonneg n)

/-- `eq:newton-convolution` and `eq:radial-convolution`: for `d ≥ 3` and the kernel
`χ(ζ) = (1 + |ζ|)^{2-2d}`, `(χ * U_D)(y) ≤ ‖χ‖₁ U_D^+(y)`. -/
def NewtonConv (d : ℕ) : Prop :=
  ∀ {ε : ℝ}, 0 ≤ ε → ∀ {D : Set (EuclideanSpace ℝ (Fin d))}, MeasurableSet D →
    Bornology.IsBounded D → ∀ y : EuclideanSpace ℝ (Fin d),
    ∫ ζ : EuclideanSpace ℝ (Fin d), (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) * potential d ε D (y - ζ)
      ≤ (∫ ζ : EuclideanSpace ℝ (Fin d), (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ))) *
        positivePotential d ε D y

/-! ### The geometry of `D_n` and its pieces -/

end CERW.Support.Outer.Radius
