import CERW.Support.Norm.ContactPotential
import CERW.Support.Norm.VectorBound
import CERW.Support.LocalTime.LatticeKernelFacts

/-!
# The contact estimate on the event of Section 5

The contact lemma of the revised paper (`lem:contact`) asserts `H = U_{D_n}(y₀) ≤ C r_n q_n` **on
the event of Section 5.1**, for all large `n`, at every contact point `y₀` (a point of the closure
of the complement of `D_n` with `Ψ(y₀) = inf_{y ∉ D_n} Ψ(y)`). The probability statement proved
earlier bounds only the failure set of the estimate itself, which may lie inside the event; this
module proves the localization.

The common event of Section 5.1 is the intersection of the sets on which hold: the three bounds of
Proposition 4.1 (`CoarseBounds`), the three estimates of Lemma 3.1 (`LocalBounds`), the vector
increment bound `eq:vector` (`VectorEstimate`), the local martingale bounds `eq:localmart` at all
lattice targets `|y| ≤ 3n` (`LocalMartEstimate`), the quadratic martingale bound
`eq:quadratic-coarse` (`QuadraticEstimate`), and the halfspace martingale bounds `eq:linear-mart`
for the two deterministic families of directions and all grid thresholds (`LinearEstimate`),
together with the typing of the model (`PathTyping`: the path starts at the origin and takes unit
steps, which holds almost surely). Each constituent is a literal predicate of a path; the constants
are parameters, chosen before the field of subgradients, the probability space and `n`.

* `contact_bound_of_event_inputs`: the deterministic inequality. For a path satisfying the
  typing, `CoarseBounds`, `LocalBounds` and `LocalMartEstimate` (the only constituents the contact
  proof consumes), every contact point satisfies `U_{D_n}(y₀) ≤ C r_n q_n`, with `C` and the
  large-`n` cutoff depending only on the dimension, the norm, the drift and the constants of those
  inputs. The quadratic, vector and halfspace constituents are not used.
* `Section5Event`: the literal event, the intersection of the constituents above.
* `LinearProducer`: the statement of the producer of the halfspace constituents, which is the
  statement of `exists_linear_martingale_bound` and is taken as a hypothesis of the composition, so
  that this module does not depend on the module that proves it.
* `exists_quadratic_producer`: the producer of the quadratic constituent `eq:quadratic-coarse`
  (the statement `QuadraticProducer`), proved here by stopping `𝒬` at the radii `1 ≤ k ≤ n + 1`.
* `measurableSet_section5Event`: the event is measurable when the positions of the walk are, since
  its constituents depend only on the path up to time `n`, a point of a countable type, and the
  typing is a countable intersection.
* `contact_on_section5Event`: the composition: the complement of the event has measure at most
  `C n^{-p}` (a union bound over the independent producers of the constituents), and on the event,
  for all large `n`, every contact point satisfies the contact bound.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.ContactEvent

open CERW CERW.Support.Statements CERW.Support.Norm.ContactShared
  CERW.Support.Norm.ContactAssembly

variable {d : ℕ}

/-! ## The scale `r_n`, the rate `q_n` and the constituents of the event -/

/-- The radius `r_n = ((d+1) n / (2 d ε |B_Ψ|))^{1/(d+1)}` of `eq:radius-norm`. -/
noncomputable def scale (d : ℕ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  (((d : ℝ) + 1) * n / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))

/-- The rate `q_n = √(log n / r_n)` for `d = 2` and `log n / r_n` for `d ≥ 3` of `eq:qn`. -/
noncomputable def contactRate (d : ℕ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  if d = 2 then Real.sqrt (Real.log n / scale d Ψ ε n) else Real.log n / scale d Ψ ε n

/-- The typing of the model: the path starts at the origin and takes unit steps. It holds almost
surely for the walk with a drift field. -/
def PathTyping (d : ℕ) (X : ℕ → Site d) : Prop :=
  X 0 = 0 ∧ ∀ j, X (j + 1) - X j ∈ unitSteps d

/-- The three bounds of Proposition 4.1 on a path `X` at time `n`, with constants `c`, `C`: the
size of the range, the largest local time and the largest radius are of order `r_n`. -/
def CoarseBounds (d : ℕ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε c C : ℝ) (X : ℕ → Site d)
    (n : ℕ) : Prop :=
  c * scale d Ψ ε n ^ d ≤ ((departureRange X n).card : ℝ) ∧
    ((departureRange X n).card : ℝ) ≤ C * scale d Ψ ε n ^ d ∧
    c * scale d Ψ ε n ≤ (maxLocalTime X n : ℝ) ∧ (maxLocalTime X n : ℝ) ≤ C * scale d Ψ ε n ∧
    c * scale d Ψ ε n ≤ maxRadius X n ∧ maxRadius X n ≤ C * scale d Ψ ε n

/-- The three estimates of Lemma 3.1 on a path `X` at time `n`, with constant `C`: the largest
local time, the local times on time intervals and the approximation of the local times by the
potential. -/
def LocalBounds (d : ℕ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε C : ℝ) (X : ℕ → Site d)
    (n : ℕ) : Prop :=
  (maxLocalTime X n : ℝ) ≤ C * ((departureRange X n).card : ℝ) ^ ((1 : ℝ) / d) +
      C * Real.log n ^ 2 ∧
    (∀ s t : ℕ, s < t → t ≤ n →
      (intervalMax X s t : ℝ) ≤ C * (freshCount X s t : ℝ) ^ ((1 : ℝ) / d) +
        C * Real.log n ^ 2) ∧
    ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
      |cellLocalTime X n y - normPotential d ε Ψ (cellSet X n) y| ≤
        C * Real.log n + C *
          (if d = 2 then Real.sqrt (maxLocalTime X n) * Real.log n
            else Real.sqrt (maxLocalTime X n * Real.log n))

/-- The vector bound `eq:vector` for the compensated position `Z_t = X_t + ε Σ_{j<t} I_j ξ(X_j)`:
`|Z_t - Z_s| ≤ C √((t - s) log n)` for all `0 ≤ s < t ≤ n`. -/
def VectorEstimate (d : ℕ) (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C : ℝ)
    (X : ℕ → Site d) (n : ℕ) : Prop :=
  ∀ s t : ℕ, s < t → t ≤ n →
    ‖CERW.Support.Norm.VectorBound.driftCompensated ε ξ X t -
        CERW.Support.Norm.VectorBound.driftCompensated ε ξ X s‖ ≤
      C * Real.sqrt (((t : ℝ) - s) * Real.log n)

/-- The local martingale bound `eq:localmart`, at every lattice target `|y| ≤ 3n`: for the Dynkin
martingale `𝓜^y` of `g_y = g(· - y)`, with `g` the lattice kernel, `|𝓜^y_n| ≤ C (√(W_y log n) +
log n)`, where `W_y = Σ_x ℓ_n(x) (1 + |x - y|)^{2-2d}`. -/
def LocalMartEstimate (d : ℕ) (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C : ℝ)
    (X : ℕ → Site d) (n : ℕ) : Prop :=
  ∀ y : Site d, euclidNorm y ≤ 3 * n →
    |dynkinMart (driftStepProb d ε ξ) (fun z => latticeKernel d (z - y)) X n| ≤
      C * (Real.sqrt ((∑ x ∈ departureRange X n,
          (localTime X n x : ℝ) * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ))) *
        Real.log n) + Real.log n)

/-- The quadratic martingale `𝒬_t = Σ_{j<t} 2 X_j · (X_{j+1} - X_j + ε I_j ξ(X_j))` of
`eq:quadratic`, where `I_j` marks a first departure. -/
noncomputable def quadraticMartingale (d : ℕ) (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (X : ℕ → Site d) (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range t, 2 * inner ℝ (toSpace (X j))
    (toSpace (X (j + 1)) - toSpace (X j) +
      ε • (if X j ∉ departureRange X j then ξ (X j) else 0))

/-- The quadratic martingale bound `eq:quadratic-coarse`: `|𝒬_n| ≤ C (R_out(n) + 1) √(n log n)`,
with `R_out(n) = max_{j ≤ n} |X_j|`. -/
def QuadraticEstimate (d : ℕ) (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C : ℝ)
    (X : ℕ → Site d) (n : ℕ) : Prop :=
  |quadraticMartingale d ε ξ X n| ≤ C * (maxRadius X n + 1) * Real.sqrt (n * Real.log n)

/-- The halfspace martingale bounds `eq:linear-mart` for a finite set `Q` of directions of length at
most `Λ_Ψ`, at the grid thresholds `a = k Λ_Ψ`, `0 ≤ k ≤ n`: for the Dynkin martingale `𝓜^{q,a}` of
`(q·x - a)_+`, `|𝓜^{q,a}_n| ≤ C (√(log n · Σ_{x : q·x > a - Λ_Ψ} ℓ_n(x)) + log n)`. -/
def LinearEstimate (d : ℕ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C : ℝ) (Q : Finset (EuclideanSpace ℝ (Fin d)))
    (X : ℕ → Site d) (n : ℕ) : Prop :=
  ∀ q ∈ Q, ∀ k : ℕ, k ≤ n →
    |dynkinMart (driftStepProb d ε ξ)
        (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) X n| ≤
      C * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange X n).filter
            (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
          (localTime X n z : ℝ)) + Real.log n)

/-- The first deterministic family of directions of Section 5.1: `Λ_Ψ u_x` for the lattice points
`0 < |x| ≤ n`, where `u_x = x / |x|`. -/
noncomputable def radialDirections (d : ℕ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (n : ℕ) :
    Finset (EuclideanSpace ℝ (Fin d)) :=
  ((LatticeProb.ballFinset d (n : ℝ)).filter (fun x => x ≠ 0)).image
    (fun x => (normMax Ψ / ‖toSpace x‖) • toSpace x)

/-- The second deterministic family of directions of Section 5.1: `Λ_Ψ u_{x - Π_n(x)}` for the
lattice points `|x| ≤ n` with `Ψ(x) > r_n`, where `Π_n` projects onto the closed convex ball
`{Ψ ≤ r_n}`; the projection enters as a selection `P` of nearest points of that ball. -/
noncomputable def projectionDirections (d : ℕ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (n : ℕ) (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Finset (EuclideanSpace ℝ (Fin d)) :=
  ((LatticeProb.ballFinset d (n : ℝ)).filter (fun x => scale d Ψ ε n < Ψ (toSpace x))).image
    (fun x => (normMax Ψ / ‖toSpace x - P (toSpace x)‖) • (toSpace x - P (toSpace x)))

/-! ## The deterministic contact inequality on the inputs of the event -/

/-- If `|a + m| ≤ c₁ L` and `|m| ≤ c₂ (s + L)`, with `c₁, s ≥ 0`, then `|a| ≤ (c₁ + c₂)(s + L)`:
the local martingale bound turns the decomposition `ℓ_n - U + 𝓜 = O(L)` into the pointwise bound on
`ℓ_n - U`. -/
private theorem abs_le_add_of_abs_add_le {a m L s c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁)
    (hs : 0 ≤ s) (h1 : |a + m| ≤ c₁ * L) (h2 : |m| ≤ c₂ * (s + L)) :
    |a| ≤ (c₁ + c₂) * (s + L) := by
  have h3 : |a| ≤ |a + m| + |m| := by
    calc |a| = |(a + m) - m| := by ring_nf
      _ ≤ |a + m| + |m| := abs_sub _ _
  have h4 : c₁ * L ≤ c₁ * (s + L) := mul_le_mul_of_nonneg_left (by linarith) hc₁
  calc |a| ≤ c₁ * L + c₂ * (s + L) := h3.trans (add_le_add h1 h2)
    _ ≤ c₁ * (s + L) + c₂ * (s + L) := by linarith
    _ = (c₁ + c₂) * (s + L) := by ring

/-- The cell modulus along a path: the cell set lies in the ball of radius `n + √d`, so the modulus
at radius `R = n + √d` gives `C₃ log (n + 2)` with `C₃ = C ε (1 + log (1 + √d))`. -/
private theorem cell_modulus_of_path (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {ε C_mod : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C_mod)
    (hmod : ∀ ε : ℝ, 0 ≤ ε → ∀ R : ℝ, 1 ≤ R →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → D ⊆ Metric.ball 0 R →
      ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R → ‖y - z‖ ≤ Real.sqrt d →
        |normPotential d ε Ψ D y - normPotential d ε Ψ D z| ≤ C_mod * ε * Real.log (R + 2))
    (X : ℕ → Site d) (n : ℕ) (hn : 2 ≤ n) (hXn : ∀ j, euclidNorm (X j) ≤ j) :
    ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * ((n : ℝ) + Real.sqrt d) →
      ‖y - z‖ ≤ Real.sqrt d →
      |normPotential d ε Ψ (cellSet X n) y - normPotential d ε Ψ (cellSet X n) z| ≤
        (C_mod * ε * (1 + Real.log (1 + Real.sqrt d))) * Real.log ((n : ℝ) + 2) := by
  intro y z hy hyz
  have hd1 : 1 ≤ d := by omega
  have hsq : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd1)
  have hball : cellSet X n ⊆ Metric.ball 0 ((n : ℝ) + Real.sqrt d) :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 X n).trans
      (Metric.ball_subset_ball (by
        linarith [CERW.Support.Norm.ContactShared.maxRadius_le_nat X n hXn]))
  have hR : (1 : ℝ) ≤ (n : ℝ) + Real.sqrt d := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1 := hmod ε hε _ hR (cellSet X n) (CERW.Support.Occupation.measurableSet_cellSet X n)
    hball y z hy hyz
  have hL1 : 1 ≤ Real.log ((n : ℝ) + 2) := CERW.Support.Law.one_le_log_add_two hn
  have hlog : Real.log ((n : ℝ) + Real.sqrt d + 2) ≤
      (1 + Real.log (1 + Real.sqrt d)) * Real.log ((n : ℝ) + 2) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2 : (n : ℝ) + Real.sqrt d + 2 ≤ (1 + Real.sqrt d) * ((n : ℝ) + 2) := by
      nlinarith
    calc Real.log ((n : ℝ) + Real.sqrt d + 2)
        ≤ Real.log ((1 + Real.sqrt d) * ((n : ℝ) + 2)) :=
          Real.log_le_log (by positivity) h2
      _ = Real.log (1 + Real.sqrt d) + Real.log ((n : ℝ) + 2) :=
          Real.log_mul (by positivity) (by positivity)
      _ ≤ (1 + Real.log (1 + Real.sqrt d)) * Real.log ((n : ℝ) + 2) := by
          have hl0 : 0 ≤ Real.log (1 + Real.sqrt d) :=
            Real.log_nonneg (by linarith)
          nlinarith
  have hCe : 0 ≤ C_mod * ε := mul_nonneg hC hε
  calc _ ≤ C_mod * ε * Real.log ((n : ℝ) + Real.sqrt d + 2) := h1
    _ ≤ C_mod * ε * ((1 + Real.log (1 + Real.sqrt d)) * Real.log ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hlog hCe
    _ = _ := by ring

/-- **The contact bound on the inputs of the event.** Let `Ψ` be a norm, `ε > 0`, and let
`c_co, C_co, C_loc, C_B` be the constants of the bounds of Proposition 4.1, of Lemma 3.1 and of the
local martingale bound. There are `C` and `n₀`, depending only on `d`, `Ψ`, `ε` and `C_co, C_loc,
C_B` (and not on `c_co`, the field `ξ`, the path, `n` or the contact point), such that for every
subgradient field `ξ` with `ξ 0 = 0`, every path with the typing of the model and every `n ≥ n₀`,
the bounds `CoarseBounds`, `LocalBounds` and `LocalMartEstimate` imply `U_{D_n}(y₀) ≤ C r_n q_n` at
**every** contact point `y₀`: a point of the closure of the complement of `D_n` with
`Ψ(y₀) = inf_{y ∉ D_n} Ψ(y)`.

The proof is the paper's: at an unvisited cell `z` whose closure contains `y₀` (with `|z| ≤ C r_n <
3n`), the local martingale bound, the pointwise decomposition and the cell modulus give
`H ≤ C (√(W_z log n) + log n)`, and the convolution bound closes the estimate (the planar case also
uses the bounds of Proposition 4.1 and the approximation of Lemma 3.1). -/
theorem contact_bound_of_event_inputs (hgeom : norm_potential_geometry)
    (hball : norm_ball_potential) (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε) (c_co C_co C_loc C_B : ℝ) (hC_co : 0 ≤ C_co)
    (hC_loc : 0 ≤ C_loc) (hC_B : 0 ≤ C_B) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n → PathTyping d X →
        CoarseBounds d Ψ ε c_co C_co X n → LocalBounds d Ψ ε C_loc X n →
        LocalMartEstimate d ε ξ C_B X n →
        ∀ y₀ : EuclideanSpace ℝ (Fin d), Ψ y₀ = normInnerRadius Ψ X n →
          y₀ ∈ closure (cellSet X n)ᶜ →
          normPotential d ε Ψ (cellSet X n) y₀ ≤ C * scale d Ψ ε n * contactRate d Ψ ε n := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨h, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  have hB : BregmanSumBound d Ψ := ContactBregman.bregmanSumBound_of hd hΨ
    (fun φ h1 h2 h3 => ContactWeakLap.inner_gradient_integral_nonpos hΨ h1 h2 h3)
    (ContactCellTest.cellTestBound hd hΨ)
  have hconv : ConvBound d Ψ ε := ContactConv.convBound hd hΨ hε hgeom hball
  obtain ⟨C_pt, hCpt, hpt⟩ :=
    ContactPointwise.exists_abs_localTime_sub_normPotential_add_driftDynkin_le.{0} hd hΨ hB hK
  obtain ⟨C_mod, hCmod, hmod⟩ := ContactModulus.exists_normPotential_cell_modulus hd hΨ
  have hC₁ : 0 ≤ C_pt * (1 + ε) + C_B := by positivity
  have hC₃ : 0 ≤ C_mod * ε * (1 + Real.log (1 + Real.sqrt d)) := by
    have : 0 ≤ Real.log (1 + Real.sqrt d) :=
      Real.log_nonneg (by linarith [Real.sqrt_nonneg (d : ℝ)])
    positivity
  have hV : 0 < normBallVolume Ψ := normBallVolume_pos' hd1 hΨ
  have hrpos : ∀ n : ℕ, 0 < n → 0 < scale d Ψ ε n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    exact Real.rpow_pos_of_pos (by positivity) _
  -- the pointwise bound on `ℓ_n - U` from the decomposition and the local martingale bound
  have hfine : ∀ (X : ℕ → Site d) (n : ℕ), 2 ≤ n → PathTyping d X →
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      LocalMartEstimate d ε ξ C_B X n →
      ∀ y : Site d, euclidNorm y ≤ 3 * n →
        |(localTime X n y : ℝ) - normPotential d ε Ψ (cellSet X n) (toSpace y)| ≤
          (C_pt * (1 + ε) + C_B) * (Real.sqrt ((∑ j ∈ Finset.range n,
            (1 + euclidNorm (X j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
              Real.log ((n : ℝ) + 2)) := by
    intro X n hn2 ⟨hX0, hsteps⟩ ξ hξ hξ0 hlm y hy
    have hnorm : ∀ j, euclidNorm (X j) ≤ j :=
      CERW.Support.Occupation.euclidNorm_le_of_steps X hX0 hsteps
    have hW : (∑ j ∈ Finset.range n, (1 + euclidNorm (X j - y)) ^ (2 - 2 * (d : ℝ))) =
        ∑ x ∈ departureRange X n,
          (localTime X n x : ℝ) * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)) :=
      CERW.Support.LocalTime.sum_range_eq_sum_localTime X n
        (fun x => (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)))
    have hW0 : 0 ≤ ∑ x ∈ departureRange X n,
        (localTime X n x : ℝ) * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (Nat.cast_nonneg _)
        (Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg (x - y)]) _)
    have hL0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hLL : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by linarith)
    have hmart : |CERW.Support.Drift.driftDynkin ε ξ (fun z => latticeKernel d (z - y))
          (fun j (_ : Unit) => X j) n ()| ≤
        C_B * (Real.sqrt ((∑ j ∈ Finset.range n,
          (1 + euclidNorm (X j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2)) := by
      rw [← CERW.Support.Drift.dynkinMart_driftStepProb_eq_driftDynkin hd1 ε ξ
        (fun z => latticeKernel d (z - y)) (fun j (_ : Unit) => X j) n ()]
      refine (hlm y hy).trans (mul_le_mul_of_nonneg_left (add_le_add ?_ hLL) hC_B)
      rw [hW]
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hLL hW0)
    exact abs_le_add_of_abs_add_le (by positivity) (Real.sqrt_nonneg _)
      (hpt ε hε.le ξ hξ hξ0 (fun j (_ : Unit) => X j) () hX0 hnorm n (by omega) y hy) hmart
  rcases Nat.lt_or_ge d 3 with hd3 | hd3
  · have hd2 : d = 2 := by omega
    obtain ⟨C_G, hCG, hG⟩ := ContactPlanar.contact_bound_two hd2 hΨ hε hconv
      (C_pt * (1 + ε) + C_B) C_loc (C_mod * ε * (1 + Real.log (1 + Real.sqrt d))) C_co C_co
      hC₁ hC_loc hC₃ hC_co hC_co
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 3 / (2 * (d : ℝ) * ε * normBallVolume Ψ) := ⟨_, rfl⟩
    have hapos : 0 < a := by
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      rw [ha]
      positivity
    have hrn : ∀ n : ℕ, scale d Ψ ε n = (a * (n : ℝ)) ^ ((1 : ℝ) / 3) := by
      intro n
      have h3 : (d : ℝ) + 1 = 3 := by
        rw [hd2]
        norm_num
      show (((d : ℝ) + 1) * n / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / ((d : ℝ) + 1)) = _
      rw [h3, ha]
      congr 1
      ring
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
      ((eventually_cube_root_scale hapos (3 * C_co) (6 * Real.sqrt d)).and
        (eventually_ge_atTop 2))
    refine ⟨2 * C_G, by positivity, n₀, ?_⟩
    intro ξ hξ hξ0 X n hn hty hcoarse hlocal hlm y₀ hy₀ hcl
    obtain ⟨⟨hr1, hrlog, hrlarge⟩, hn2⟩ := hn₀ n hn
    obtain ⟨hX0, hsteps⟩ := hty
    have hnorm : ∀ j, euclidNorm (X j) ≤ j :=
      CERW.Support.Occupation.euclidNorm_le_of_steps X hX0 hsteps
    obtain ⟨-, -, -, hM, -, hRad⟩ := hcoarse
    have hcrude : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ ≤ 2 * n →
        |cellLocalTime X n v - normPotential d ε Ψ (cellSet X n) v| ≤
          C_loc * Real.log n + C_loc * (Real.sqrt (maxLocalTime X n) * Real.log n) := by
      intro v hv
      have := hlocal.2.2 v hv
      rwa [if_pos hd2] at this
    have hmodω := cell_modulus_of_path hd hε.le hCmod hmod X n hn2 hnorm
    have hr1' : 1 ≤ scale d Ψ ε n := by
      rw [hrn n]
      exact hr1
    have hrlog' : Real.log ((n : ℝ) + 2) ^ 4 ≤ scale d Ψ ε n := by
      rw [hrn n]
      exact hrlog
    have hlarge : 3 * C_co * scale d Ψ ε n + 6 * Real.sqrt d ≤ n := by
      rw [hrn n]
      exact hrlarge
    have hU := hG X n (scale d Ψ ε n) hn2 hX0 hnorm hr1' hrlog' hlarge hM hRad
      (hfine X n hn2 ⟨hX0, hsteps⟩ ξ hξ hξ0 hlm) hcrude hmodω y₀ hy₀ hcl
    have hr := hrpos n (by omega)
    have hlogn := log_pos_of_two_le hn2
    have hL := log_add_two_le hn2
    have hsq : Real.sqrt (scale d Ψ ε n * Real.log ((n : ℝ) + 2)) ≤
        2 * Real.sqrt (scale d Ψ ε n * Real.log n) := by
      have h4 : scale d Ψ ε n * Real.log ((n : ℝ) + 2) ≤
          2 ^ 2 * (scale d Ψ ε n * Real.log n) := by
        have : scale d Ψ ε n * Real.log ((n : ℝ) + 2) ≤ scale d Ψ ε n * (2 * Real.log n) :=
          mul_le_mul_of_nonneg_left hL hr.le
        nlinarith [mul_nonneg hr.le hlogn.le]
      calc Real.sqrt (scale d Ψ ε n * Real.log ((n : ℝ) + 2))
          ≤ Real.sqrt (2 ^ 2 * (scale d Ψ ε n * Real.log n)) := Real.sqrt_le_sqrt h4
        _ = 2 * Real.sqrt (scale d Ψ ε n * Real.log n) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    have hsn : 0 ≤ Real.sqrt (scale d Ψ ε n * Real.log n) := Real.sqrt_nonneg _
    have hqn : contactRate d Ψ ε n = Real.sqrt (Real.log n / scale d Ψ ε n) := by
      rw [contactRate, if_pos hd2]
    rw [hqn]
    calc normPotential d ε Ψ (cellSet X n) y₀
        ≤ C_G * Real.sqrt (scale d Ψ ε n * Real.log ((n : ℝ) + 2)) := hU
      _ ≤ C_G * (2 * Real.sqrt (scale d Ψ ε n * Real.log n)) :=
          mul_le_mul_of_nonneg_left hsq hCG.le
      _ = 2 * C_G * Real.sqrt (scale d Ψ ε n * Real.log n) := by ring
      _ = 2 * C_G * (scale d Ψ ε n * Real.sqrt (Real.log n / scale d Ψ ε n)) := by
          rw [mul_sqrt_div_eq hr]
      _ = 2 * C_G * scale d Ψ ε n * Real.sqrt (Real.log n / scale d Ψ ε n) := by ring
  · obtain ⟨C_H, hCH, hH⟩ := ContactHigh.contact_bound_three_le hd3 hΨ hε hconv
      (C_pt * (1 + ε) + C_B) (C_mod * ε * (1 + Real.log (1 + Real.sqrt d))) hC₁ hC₃
    obtain ⟨n₁, hn₁⟩ := exists_nat_ge (4 * Real.sqrt d)
    refine ⟨2 * C_H, by positivity, max n₁ 2, ?_⟩
    intro ξ hξ hξ0 X n hn hty hcoarse hlocal hlm y₀ hy₀ hcl
    have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
    have hn4 : 4 * Real.sqrt d ≤ n :=
      hn₁.trans (by exact_mod_cast (le_max_left _ _).trans hn)
    obtain ⟨hX0, hsteps⟩ := hty
    have hnorm : ∀ j, euclidNorm (X j) ≤ j :=
      CERW.Support.Occupation.euclidNorm_le_of_steps X hX0 hsteps
    have hmodω := cell_modulus_of_path hd hε.le hCmod hmod X n hn2 hnorm
    have hU := hH X n hn2 hn4 hX0 hnorm
      (hfine X n hn2 ⟨hX0, hsteps⟩ ξ hξ hξ0 hlm) hmodω y₀ hy₀ hcl
    have hr := hrpos n (by omega)
    have hlogn := log_pos_of_two_le hn2
    have hL := log_add_two_le hn2
    have hqn : contactRate d Ψ ε n = Real.log n / scale d Ψ ε n := by
      rw [contactRate, if_neg (by omega)]
    rw [hqn]
    calc normPotential d ε Ψ (cellSet X n) y₀
        ≤ C_H * Real.log ((n : ℝ) + 2) := hU
      _ ≤ C_H * (2 * Real.log n) := mul_le_mul_of_nonneg_left hL hCH.le
      _ = 2 * C_H * (scale d Ψ ε n * (Real.log n / scale d Ψ ε n)) := by
          field_simp
      _ = 2 * C_H * scale d Ψ ε n * (Real.log n / scale d Ψ ε n) := by ring

/-! ## The common event of Section 5.1 -/

/-- The constants of the common event, fixed before the field of subgradients, the probability
space and `n`: `c_co, C_co` for Proposition 4.1, `C_loc` for Lemma 3.1, `C_vec` for `eq:vector`,
`C_mart` for `eq:localmart`, `C_quad` for `eq:quadratic-coarse` and `C_lin` for `eq:linear-mart`. -/
structure EventConstants where
  /-- The lower constant of Proposition 4.1. -/
  c_co : ℝ
  /-- The upper constant of Proposition 4.1. -/
  C_co : ℝ
  /-- The constant of Lemma 3.1. -/
  C_loc : ℝ
  /-- The constant of the vector bound `eq:vector`. -/
  C_vec : ℝ
  /-- The constant of the local martingale bound `eq:localmart`. -/
  C_mart : ℝ
  /-- The constant of the quadratic martingale bound `eq:quadratic-coarse`. -/
  C_quad : ℝ
  /-- The constant of the halfspace martingale bounds `eq:linear-mart`. -/
  C_lin : ℝ

/-- **The event of Section 5.1.** The set of sample points on which the walk has the typing of the
model and satisfies Proposition 4.1, Lemma 3.1, the vector bound `eq:vector`, the local martingale
bounds `eq:localmart`, the quadratic martingale bound `eq:quadratic-coarse`, and the halfspace
martingale bounds `eq:linear-mart` for the two deterministic families of directions
(`radialDirections` and `projectionDirections`, the latter for a selection `P` of nearest points
of `{Ψ ≤ r_n}`), at time `n`. -/
def Section5Event {Ω : Type*} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (K : EventConstants)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (X : ℕ → Ω → Site d) (n : ℕ) :
    Set Ω :=
  {ω | PathTyping d (fun j => X j ω) ∧
    CoarseBounds d Ψ ε K.c_co K.C_co (fun j => X j ω) n ∧
    LocalBounds d Ψ ε K.C_loc (fun j => X j ω) n ∧
    VectorEstimate d ε ξ K.C_vec (fun j => X j ω) n ∧
    LocalMartEstimate d ε ξ K.C_mart (fun j => X j ω) n ∧
    QuadraticEstimate d ε ξ K.C_quad (fun j => X j ω) n ∧
    LinearEstimate d Ψ ε ξ K.C_lin (radialDirections d Ψ n) (fun j => X j ω) n ∧
    LinearEstimate d Ψ ε ξ K.C_lin (projectionDirections d Ψ ε n P) (fun j => X j ω) n}

/-- `P` selects, for every point, the point of `{Ψ ≤ r}` nearest to it: it lies in the set and
satisfies the variational inequality of the Euclidean projection onto a convex set. -/
def IsNearestSelection (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (r : ℝ)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ y, Ψ (P y) ≤ r) ∧ ∀ y v, Ψ v ≤ r → inner ℝ (y - P y) (v - P y) ≤ 0

/-- The nearest point of a set is unique: two points of `{Ψ ≤ r}` satisfying the variational
inequality for `y` coincide. -/
theorem nearest_unique {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} {r : ℝ}
    {y z z' : EuclideanSpace ℝ (Fin d)} (hz : Ψ z ≤ r) (hz' : Ψ z' ≤ r)
    (hvar : ∀ v, Ψ v ≤ r → inner ℝ (y - z) (v - z) ≤ 0)
    (hvar' : ∀ v, Ψ v ≤ r → inner ℝ (y - z') (v - z') ≤ 0) : z = z' := by
  have h1 := hvar z' hz'
  have h2 := hvar' z hz
  have h3 : inner ℝ (y - z') (z - z') = -inner ℝ (y - z') (z' - z) := by
    rw [← inner_neg_right, neg_sub]
  have e : inner ℝ (z' - z) (z' - z) =
      inner ℝ (y - z) (z' - z) - inner ℝ (y - z') (z' - z) := by
    rw [← inner_sub_left]
    congr 1
    abel
  have h4 : inner ℝ (z' - z) (z' - z) ≤ 0 := by
    rw [e]
    linarith
  rw [real_inner_self_eq_norm_sq] at h4
  have h5 : ‖z' - z‖ = 0 := by nlinarith [norm_nonneg (z' - z)]
  exact (sub_eq_zero.1 (norm_eq_zero.1 h5)).symm

/-- The family `projectionDirections` does not depend on the choice of the selection: nearest
points are unique, so `Π_n` of the source is the selection. -/
theorem projectionDirections_eq_of_nearest (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ) (n : ℕ)
    {P P' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hP : IsNearestSelection Ψ (scale d Ψ ε n) P)
    (hP' : IsNearestSelection Ψ (scale d Ψ ε n) P') :
    projectionDirections d Ψ ε n P = projectionDirections d Ψ ε n P' := by
  have hPP : ∀ y, P y = P' y := fun y =>
    nearest_unique (hP.1 y) (hP'.1 y) (hP.2 y) (hP'.2 y)
  unfold projectionDirections
  refine Finset.image_congr fun x _ => ?_
  rw [hPP (toSpace x)]

/-! ## The producers of the constituents -/

/-- The producer of the halfspace martingale bounds `eq:linear-mart` for an arbitrary finite set of
directions of length at most `Λ_Ψ`: the statement of
`CERW.Support.Norm.exists_linear_martingale_bound`, the Freedman bound at the grid thresholds with
a union bound over the directions. It is taken as a hypothesis here, so that this module does not
depend on the module that proves it. -/
def LinearProducer : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}, IsNorm Ψ → ∀ {ε : ℝ}, 0 < ε →
    (∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) → ∀ {p : ℝ}, 0 < p →
    ∃ C : ℝ, 0 < C ∧ ∀ {ξ : Site d → EuclideanSpace ℝ (Fin d)},
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        {X : ℕ → Ω → Site d}, IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        ∀ Q : Finset (EuclideanSpace ℝ (Fin d)), (∀ q ∈ Q, ‖q‖ ≤ normMax Ψ) →
        μ {ω | ∃ q ∈ Q, ∃ k : ℕ, k ≤ n ∧
          C * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange (fun j => X j ω) n).filter
                (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
              (localTime (fun j => X j ω) n z : ℝ)) + Real.log n) <
            |dynkinMart (driftStepProb d ε ξ)
              (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0)
              (fun j => X j ω) n|} ≤
          ENNReal.ofReal (C * ((Q.card : ℝ) * ((n : ℝ) + 1)) * (n : ℝ) ^ (-p))

/-- The statement of the producer of the quadratic martingale bound `eq:quadratic-coarse`: for the
walk with a drift field, with probability at least `1 - C n^{-p}`,
`|𝒬_n| ≤ C (R_out(n) + 1) √(n log n)`, with `C` independent of the field. It is proved below as
`exists_quadratic_producer`. -/
def QuadraticProducer : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d) {ε : ℝ}, 0 < ε → ∀ {p : ℝ}, 0 < p →
    ∃ C : ℝ, 0 < C ∧ ∀ {ξ : Site d → EuclideanSpace ℝ (Fin d)},
      (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        {X : ℕ → Ω → Site d}, IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ QuadraticEstimate d ε ξ C (fun j => X j ω) n} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p))

/-! ## The families of directions: norm and cardinality -/

/-- For `Λ ≥ 0`, the vector `(Λ / ‖a‖) • a` has norm at most `Λ` (it is `0` for `a = 0`). -/
private theorem norm_scaled_le {Λ : ℝ} (hΛ : 0 ≤ Λ) (a : EuclideanSpace ℝ (Fin d)) :
    ‖(Λ / ‖a‖) • a‖ ≤ Λ := by
  rcases eq_or_ne a 0 with rfl | ha
  · simpa using hΛ
  · have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hΛ ha0.le)]
    exact (div_mul_cancel₀ Λ ha0.ne').le

/-- The directions `Λ_Ψ u_x` have length at most `Λ_Ψ`. -/
theorem norm_le_normMax_of_mem_radialDirections {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΛ : 0 ≤ normMax Ψ) {n : ℕ} {q : EuclideanSpace ℝ (Fin d)}
    (hq : q ∈ radialDirections d Ψ n) : ‖q‖ ≤ normMax Ψ := by
  unfold radialDirections at hq
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hq
  exact norm_scaled_le hΛ _

/-- The directions `Λ_Ψ u_{x - Π_n(x)}` have length at most `Λ_Ψ`. -/
theorem norm_le_normMax_of_mem_projectionDirections {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΛ : 0 ≤ normMax Ψ) {ε : ℝ} {n : ℕ}
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {q : EuclideanSpace ℝ (Fin d)} (hq : q ∈ projectionDirections d Ψ ε n P) :
    ‖q‖ ≤ normMax Ψ := by
  unfold projectionDirections at hq
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hq
  exact norm_scaled_le hΛ _

/-- Each of the two families has at most `(2n + 1)^d` directions. -/
theorem card_directions_le (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ) (n : ℕ)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    ((radialDirections d Ψ n).card : ℝ) ≤ (2 * (n : ℝ) + 1) ^ d ∧
      ((projectionDirections d Ψ ε n P).card : ℝ) ≤ (2 * (n : ℝ) + 1) ^ d := by
  have hball := LatticeProb.card_ballFinset_le d (R := (n : ℝ)) (Nat.cast_nonneg n)
  constructor
  · unfold radialDirections
    exact (Nat.cast_le.mpr (Finset.card_image_le.trans (Finset.card_filter_le _ _))).trans hball
  · unfold projectionDirections
    exact (Nat.cast_le.mpr (Finset.card_image_le.trans (Finset.card_filter_le _ _))).trans hball

/-- The arithmetic of the union bound: at most `2 (2n + 1)^d` directions and `n + 1` thresholds cost
at most `4 · 3^d n^{-p}` when each pair has probability `n^{-(p + d + 1)}`. -/
private theorem union_count_arith {C p : ℝ} (hC : 0 ≤ C) (d : ℕ) {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc : c ≤ 2 * (2 * (n : ℝ) + 1) ^ d) :
    C * (c * ((n : ℝ) + 1)) * (n : ℝ) ^ (-(p + d + 1)) ≤ (C * 4 * 3 ^ d) * (n : ℝ) ^ (-p) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hrp : 0 ≤ (n : ℝ) ^ (-(p + d + 1)) := Real.rpow_nonneg hnpos.le _
  have h1 : (2 * (n : ℝ) + 1) ^ d ≤ (3 * n) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  have h2 : c * ((n : ℝ) + 1) ≤ 2 * (3 ^ d * (n : ℝ) ^ d) * (2 * n) := by
    calc c * ((n : ℝ) + 1) ≤ (2 * (3 * (n : ℝ)) ^ d) * (2 * n) :=
          mul_le_mul (hc.trans (mul_le_mul_of_nonneg_left h1 (by norm_num)))
            (by linarith) (by positivity) (by positivity)
      _ = 2 * (3 ^ d * (n : ℝ) ^ d) * (2 * n) := by rw [mul_pow]
  have h3 : (n : ℝ) ^ (-(p + d + 1)) = (n : ℝ) ^ (-p) * ((n : ℝ) ^ (d + 1))⁻¹ := by
    rw [show -(p + d + 1) = -p + -((d + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hnpos, Real.rpow_neg hnpos.le ((d + 1 : ℕ) : ℝ), Real.rpow_natCast]
  have h4 : (n : ℝ) ^ d * n * ((n : ℝ) ^ (d + 1))⁻¹ = 1 := by
    rw [← pow_succ]
    exact mul_inv_cancel₀ (pow_ne_zero _ hnpos.ne')
  calc C * (c * ((n : ℝ) + 1)) * (n : ℝ) ^ (-(p + d + 1))
      ≤ C * (2 * (3 ^ d * (n : ℝ) ^ d) * (2 * n)) * (n : ℝ) ^ (-(p + d + 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC) hrp
    _ = (C * 4 * 3 ^ d) * (n : ℝ) ^ (-p) * ((n : ℝ) ^ d * n * ((n : ℝ) ^ (d + 1))⁻¹) := by
        rw [h3]
        ring
    _ = (C * 4 * 3 ^ d) * (n : ℝ) ^ (-p) := by rw [h4, mul_one]

/-- A set covered by six events of small probability and a null event has small probability. -/
private theorem measure_le_of_subset_union_six {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S E₁ E₂ E₃ E₄ E₅ E₆ N : Set Ω} {a₁ a₂ a₃ a₄ a₅ a₆ C : ℝ}
    (hS : S ⊆ E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅ ∪ E₆ ∪ N)
    (h₁ : μ E₁ ≤ ENNReal.ofReal a₁) (h₂ : μ E₂ ≤ ENNReal.ofReal a₂)
    (h₃ : μ E₃ ≤ ENNReal.ofReal a₃) (h₄ : μ E₄ ≤ ENNReal.ofReal a₄)
    (h₅ : μ E₅ ≤ ENNReal.ofReal a₅) (h₆ : μ E₆ ≤ ENNReal.ofReal a₆) (hN : μ N = 0)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha₄ : 0 ≤ a₄) (ha₅ : 0 ≤ a₅) (ha₆ : 0 ≤ a₆)
    (hC : a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ≤ C) : μ S ≤ ENNReal.ofReal C := by
  calc μ S ≤ μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅ ∪ E₆ ∪ N) := measure_mono hS
    _ ≤ μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅ ∪ E₆) + μ N := measure_union_le _ _
    _ = μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅ ∪ E₆) := by rw [hN, add_zero]
    _ ≤ μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅) + μ E₆ := measure_union_le _ _
    _ ≤ (μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄) + μ E₅) + μ E₆ := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ((μ (E₁ ∪ E₂ ∪ E₃) + μ E₄) + μ E₅) + μ E₆ :=
        add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
    _ ≤ (((μ (E₁ ∪ E₂) + μ E₃) + μ E₄) + μ E₅) + μ E₆ :=
        add_le_add (add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl) le_rfl
    _ ≤ ((((μ E₁ + μ E₂) + μ E₃) + μ E₄) + μ E₅) + μ E₆ :=
        add_le_add (add_le_add (add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl)
          le_rfl) le_rfl
    _ ≤ ((((ENNReal.ofReal a₁ + ENNReal.ofReal a₂) + ENNReal.ofReal a₃) + ENNReal.ofReal a₄) +
          ENNReal.ofReal a₅) + ENNReal.ofReal a₆ := by gcongr
    _ = ENNReal.ofReal (a₁ + a₂ + a₃ + a₄ + a₅ + a₆) := by
        rw [ENNReal.ofReal_add (by positivity) ha₆, ENNReal.ofReal_add (by positivity) ha₅,
          ENNReal.ofReal_add (by positivity) ha₄, ENNReal.ofReal_add (add_nonneg ha₁ ha₂) ha₃,
          ENNReal.ofReal_add ha₁ ha₂]
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC

/-! ## The producer of the quadratic constituent -/

section QuadraticProducer

open ProbabilityTheory Finset CERW.Support.Drift CERW.Support.Law

/-- A unit step changes the squared norm by `2 ⟪x, e⟫ + 1`. -/
private theorem euclidNorm_sq_add_unit (x e : Site d) (he : e ∈ unitSteps d) :
    euclidNorm (x + e) ^ 2 = euclidNorm x ^ 2 + 2 * inner ℝ (toSpace x) (toSpace e) + 1 := by
  have hto : toSpace (x + e) = toSpace x + toSpace e := by
    apply PiLp.ext
    intro i
    simp [toSpace_apply, Pi.add_apply, Int.cast_add]
  have he1 : euclidNorm e = 1 := CERW.Support.Law.euclidNorm_of_mem_unitSteps he
  have hnorm : ‖toSpace e‖ = 1 := by rw [norm_toSpace, he1]
  rw [← norm_toSpace (x + e), ← norm_toSpace x, hto, norm_add_sq_real, hnorm]
  ring

/-- The squared norm changes by at most `2 |x| + 1` under a unit step. -/
private theorem abs_sq_euclidNorm_add_le (x e : Site d) (he : e ∈ unitSteps d) :
    |euclidNorm (x + e) ^ 2 - euclidNorm x ^ 2| ≤ 2 * euclidNorm x + 1 := by
  have he1 : euclidNorm e = 1 := CERW.Support.Law.euclidNorm_of_mem_unitSteps he
  have hnorm : ‖toSpace e‖ = 1 := by rw [norm_toSpace, he1]
  have hinner : |inner ℝ (toSpace x) (toSpace e)| ≤ euclidNorm x := by
    calc |inner ℝ (toSpace x) (toSpace e)| ≤ ‖toSpace x‖ * ‖toSpace e‖ :=
          abs_real_inner_le_norm _ _
      _ = euclidNorm x := by rw [norm_toSpace, hnorm, mul_one]
  have hdiff : euclidNorm (x + e) ^ 2 - euclidNorm x ^ 2 =
      2 * inner ℝ (toSpace x) (toSpace e) + 1 := by
    rw [euclidNorm_sq_add_unit x e he]
    ring
  rw [hdiff]
  rw [abs_le] at hinner ⊢
  constructor <;> linarith [hinner.1, hinner.2]

/-- The quadratic martingale of the source is the Dynkin martingale of `|x|²`, along a path whose
steps are unit steps, in a field with `ξ 0 = 0`. -/
private theorem quadraticMartingale_eq_driftDynkin (hd : 1 ≤ d) {Ω : Type*} (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (hξ0 : ξ 0 = 0) (X : ℕ → Ω → Site d) (ω : Ω)
    (hsteps : ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d) (t : ℕ) :
    quadraticMartingale d ε ξ (fun j => X j ω) t =
      driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X t ω := by
  induction t with
  | zero => simp [quadraticMartingale]
  | succ t ih =>
    have hq : quadraticMartingale d ε ξ (fun j => X j ω) (t + 1) =
        quadraticMartingale d ε ξ (fun j => X j ω) t +
          2 * inner ℝ (toSpace (X t ω))
            (toSpace (X (t + 1) ω) - toSpace (X t ω) +
              ε • (if X t ω ∉ departureRange (fun j => X j ω) t then ξ (X t ω) else 0)) := by
      simp only [quadraticMartingale, sum_range_succ]
    set Iv : EuclideanSpace ℝ (Fin d) :=
      if X t ω ∉ departureRange (fun j => X j ω) t then ξ (X t ω) else 0 with hIv
    -- the mean of each coordinate of the next step
    have hcoord : ∀ k : Fin d, ∑ e ∈ unitSteps d,
        driftStepProb d ε ξ (fun j => X j ω) t e * ((e k : ℤ) : ℝ) = -(ε * Iv.ofLp k) := by
      intro k
      have h1 := driftNextMean_coord hd ε ξ (fun j => X j ω) t k
      have h2 : driftNextMean ε ξ (fun z : Site d => ((z k : ℤ) : ℝ)) (fun j => X j ω) t =
          ((X t ω k : ℤ) : ℝ) + ∑ e ∈ unitSteps d,
            driftStepProb d ε ξ (fun j => X j ω) t e * ((e k : ℤ) : ℝ) := by
        simp only [driftNextMean, Pi.add_apply, Int.cast_add, mul_add, sum_add_distrib]
        rw [← sum_mul, sum_driftStepProb hd ε ξ _ t, one_mul]
      have hterm : (if X t ω ≠ 0 ∧ X t ω ∉ (range t).image (fun j => X j ω) then
          ε * ξ (X t ω) k else 0) = ε * Iv.ofLp k := by
        by_cases h0 : X t ω = 0
        · simp [h0, hξ0, hIv, departureRange]
        · by_cases hdep : X t ω ∈ (range t).image (fun i => X i ω)
          · simp [hIv, departureRange, hdep]
          · simp [hIv, departureRange, hdep, h0]
      rw [h2, hterm] at h1
      linarith
    have hmean : driftNextMean ε ξ (fun z : Site d => euclidNorm z ^ 2) (fun j => X j ω) t =
        euclidNorm (X t ω) ^ 2 + 1 - 2 * ε * inner ℝ (toSpace (X t ω)) Iv := by
      have hsum : ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
          euclidNorm (X t ω + e) ^ 2 =
          ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
            ((euclidNorm (X t ω) ^ 2 + 1) + 2 * ∑ k : Fin d,
              ((X t ω k : ℤ) : ℝ) * ((e k : ℤ) : ℝ)) := by
        refine sum_congr rfl fun e he => ?_
        rw [euclidNorm_sq_add_unit _ _ he]
        have : inner ℝ (toSpace (X t ω)) (toSpace e) =
            ∑ k : Fin d, ((X t ω k : ℤ) : ℝ) * ((e k : ℤ) : ℝ) := by
          simp only [PiLp.inner_apply, toSpace_apply, RCLike.inner_apply, conj_trivial]
          exact sum_congr rfl fun k _ => mul_comm _ _
        rw [this]
        ring
      have hcomm : ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
          (∑ k : Fin d, ((X t ω k : ℤ) : ℝ) * ((e k : ℤ) : ℝ)) =
          ∑ k : Fin d, ((X t ω k : ℤ) : ℝ) * (-(ε * Iv.ofLp k)) := by
        simp only [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        rw [← hcoord k, mul_sum]
        refine sum_congr rfl fun e _ => ?_
        ring
      calc driftNextMean ε ξ (fun z : Site d => euclidNorm z ^ 2) (fun j => X j ω) t
          = ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
              euclidNorm (X t ω + e) ^ 2 := rfl
        _ = (euclidNorm (X t ω) ^ 2 + 1) *
              ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e +
            2 * ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
              (∑ k : Fin d, ((X t ω k : ℤ) : ℝ) * ((e k : ℤ) : ℝ)) := by
            rw [hsum, mul_sum, mul_sum, ← sum_add_distrib]
            refine sum_congr rfl fun e _ => ?_
            ring
        _ = euclidNorm (X t ω) ^ 2 + 1 - 2 * ε * inner ℝ (toSpace (X t ω)) Iv := by
            have hin : inner ℝ (toSpace (X t ω)) Iv =
                ∑ k : Fin d, ((X t ω k : ℤ) : ℝ) * Iv.ofLp k := by
              simp only [PiLp.inner_apply, toSpace_apply, RCLike.inner_apply, conj_trivial]
              exact sum_congr rfl fun k _ => mul_comm _ _
            have hs : ∑ k : Fin d, ((X t ω k : ℤ) : ℝ) * (-(ε * Iv.ofLp k)) =
                -(ε * ∑ k : Fin d, ((X t ω k : ℤ) : ℝ) * Iv.ofLp k) := by
              rw [mul_sum, ← sum_neg_distrib]
              exact sum_congr rfl fun k _ => by ring
            rw [sum_driftStepProb hd ε ξ _ t, hcomm, hs, hin]
            ring
    have hD : driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω =
        driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X t ω +
          (euclidNorm (X (t + 1) ω) ^ 2 -
            driftNextMean ε ξ (fun z : Site d => euclidNorm z ^ 2) (fun j => X j ω) t) := by
      have := driftDynkin_succ_sub ε ξ (fun z : Site d => euclidNorm z ^ 2) X t ω
      linarith
    have he := hsteps t
    have hX' : X (t + 1) ω = X t ω + (X (t + 1) ω - X t ω) := by abel
    have hto : toSpace (X (t + 1) ω) - toSpace (X t ω) = toSpace (X (t + 1) ω - X t ω) := by
      apply PiLp.ext
      intro i
      simp [toSpace_apply, Int.cast_sub]
    have hsq := euclidNorm_sq_add_unit (X t ω) (X (t + 1) ω - X t ω) he
    rw [← hX'] at hsq
    rw [hq, ih, hD, hmean, hto, hsq, inner_add_right, real_inner_smul_right]
    ring

/-- The indicator that the walk at time `j` is still inside the ball of radius `R`. -/
private noncomputable def quadBallIndicator (R : ℝ) {Ω : Type*}
    (X : ℕ → Ω → Site d) (j : ℕ) (ω : Ω) : ℝ :=
  if euclidNorm (X j ω) ≤ R then 1 else 0

/-- The Dynkin martingale of `|x|²` with its increments kept only while the walk is inside the
ball of radius `R`. -/
private noncomputable def truncatedQuad (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (R : ℝ)
    {Ω : Type*} (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range t, quadBallIndicator R X j ω *
    (driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
      driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X j ω)

private theorem quadBallIndicator_nonneg (R : ℝ) {Ω : Type*} (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : 0 ≤ quadBallIndicator R X j ω := by
  rw [quadBallIndicator]
  split_ifs <;> norm_num

private theorem quadBallIndicator_le_one (R : ℝ) {Ω : Type*} (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : quadBallIndicator R X j ω ≤ 1 := by
  rw [quadBallIndicator]
  split_ifs <;> norm_num

/-- The ball indicator is a function of the past path. -/
private theorem stronglyMeasurable_quadBallIndicator {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ n, Measurable (X n)) (R : ℝ) (j : ℕ) :
    StronglyMeasurable[pathFiltration hX j] (quadBallIndicator R X j) := by
  have h := stronglyMeasurable_comp_pastPath hX j
    (fun q : ((i : Iic j) → Site d) =>
      if euclidNorm (q ⟨j, Finset.mem_Iic.mpr le_rfl⟩) ≤ R then (1 : ℝ) else 0)
  exact h

private theorem truncatedQuad_zero (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (R : ℝ)
    {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) :
    truncatedQuad ε ξ R X 0 ω = 0 := by
  simp only [truncatedQuad, Finset.range_zero, Finset.sum_empty]

private theorem truncatedQuad_succ_sub (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (R : ℝ)
    {Ω : Type*} (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) :
    truncatedQuad ε ξ R X (t + 1) ω - truncatedQuad ε ξ R X t ω =
      quadBallIndicator R X t ω *
        (driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω -
          driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X t ω) := by
  simp only [truncatedQuad, Finset.sum_range_succ]
  ring


/-- The truncated Dynkin martingale of `|x|²`, clamped so that its increments are surely
bounded, has increments at most `2 (2 R + 1)`, conditional variances at most `(2 R + 1)²`, starts
at `0` and agrees almost surely with `𝒬` on the event that the walk stays in the ball of radius
`R` up to time `n`. -/
private theorem exists_clamped_quadratic_drift (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    {R : ℝ} (hR : 0 < R) (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsDriftCERW μ ε ξ X) :
    ∃ M : ℕ → Ω → ℝ, Martingale M (pathFiltration hX.measurable) μ ∧
      (∀ i ω, |M (i + 1) ω - M i ω| ≤ 2 * (2 * R + 1)) ∧
      (∀ j, μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | pathFiltration hX.measurable j] ≤ᵐ[μ]
        fun _ => (2 * R + 1) ^ 2) ∧
      (∀ ω, M 0 ω = 0) ∧
      ∀ᵐ ω ∂μ, (∀ j ≤ n, euclidNorm (X j ω) ≤ R) →
        M n ω = driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X n ω := by
  have hd1 : 1 ≤ d := by omega
  have hQmart : Martingale (driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X)
      (pathFiltration hX.measurable) μ :=
    martingale_driftDynkin hd1 hε hξ hX (fun z : Site d => euclidNorm z ^ 2)
  have hI_sm : ∀ j, StronglyMeasurable[pathFiltration hX.measurable j]
      (quadBallIndicator R X j) := fun j => stronglyMeasurable_quadBallIndicator hX.measurable R j
  have hQ'adp : StronglyAdapted (pathFiltration hX.measurable)
      (truncatedQuad ε ξ R X) := by
    intro t
    show StronglyMeasurable[pathFiltration hX.measurable t]
      (fun ω => ∑ j ∈ Finset.range t, quadBallIndicator R X j ω *
        (driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
          driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X j ω))
    refine Finset.stronglyMeasurable_fun_sum _ fun j hj => ?_
    have hjt : j + 1 ≤ t := Finset.mem_range.mp hj
    have hjt' : j ≤ t := le_of_lt hjt
    exact ((hI_sm j).mono ((pathFiltration hX.measurable).mono hjt')).mul
      (((hQmart.stronglyMeasurable (j + 1)).mono ((pathFiltration hX.measurable).mono hjt)).sub
        ((hQmart.stronglyMeasurable j).mono ((pathFiltration hX.measurable).mono hjt')))
  have hQ'int : ∀ t, Integrable (truncatedQuad ε ξ R X t) μ := by
    intro t
    have hterm : ∀ j ∈ Finset.range t, Integrable (fun ω => quadBallIndicator R X j ω *
        (driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
          driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X j ω)) μ := by
      intro j _
      refine Integrable.bdd_mul ((hQmart.integrable (j + 1)).sub (hQmart.integrable j))
        (((hI_sm j).mono ((pathFiltration hX.measurable).le j))).aestronglyMeasurable
        (c := 1) (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (quadBallIndicator_nonneg R X j ω)]
      exact quadBallIndicator_le_one R X j ω
    change Integrable (fun ω => ∑ j ∈ Finset.range t, quadBallIndicator R X j ω *
      (driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
        driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X j ω)) μ
    exact integrable_finsetSum (Finset.range t) hterm
  have hQ'cond : ∀ k, μ[truncatedQuad ε ξ R X (k + 1) - truncatedQuad ε ξ R X k
      | pathFiltration hX.measurable k] =ᵐ[μ] 0 := by
    intro k
    have hfun : truncatedQuad ε ξ R X (k + 1) - truncatedQuad ε ξ R X k =
        quadBallIndicator R X k * (driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X (k + 1) -
          driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X k) := by
      funext ω
      exact truncatedQuad_succ_sub ε ξ R X k ω
    rw [hfun]
    have hpull := condExp_stronglyMeasurable_mul_of_bound (μ := μ)
      ((pathFiltration hX.measurable).le k) (hI_sm k)
      ((hQmart.integrable (k + 1)).sub (hQmart.integrable k)) 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (quadBallIndicator_nonneg R X k ω)]
        exact quadBallIndicator_le_one R X k ω)
    have hcent : μ[driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X (k + 1) -
        driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X k | pathFiltration hX.measurable k]
        =ᵐ[μ] 0 := by
      have h3 := condExp_sub (hQmart.integrable (k + 1)) (hQmart.integrable k)
        (pathFiltration hX.measurable k)
      have h1 := hQmart.condExp_ae_eq (Nat.le_succ k)
      have h2 : μ[driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X k
          | pathFiltration hX.measurable k] =
          driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X k :=
        condExp_of_stronglyMeasurable ((pathFiltration hX.measurable).le k)
          (hQmart.stronglyMeasurable k) (hQmart.integrable k)
      filter_upwards [h3, h1] with ω e3 e1
      rw [e3, Pi.sub_apply, e1, h2, sub_self]
      rfl
    filter_upwards [hpull, hcent] with ω e1 e2
    rw [e1, Pi.mul_apply, e2, Pi.zero_apply, mul_zero]
  have hmartQ' : Martingale (truncatedQuad ε ξ R X) (pathFiltration hX.measurable) μ :=
    martingale_of_condExp_sub_eq_zero_nat hQ'adp hQ'int hQ'cond
  have hinc : ∀ i, ∀ᵐ ω ∂μ, |truncatedQuad ε ξ R X (i + 1) ω -
      truncatedQuad ε ξ R X i ω| ≤ 2 * (2 * R + 1) := by
    intro i
    filter_upwards [ae_abs_driftDynkin_succ_sub_le hd1 hε hξ hX
      (fun z : Site d => euclidNorm z ^ 2)] with ω hω
    rw [truncatedQuad_succ_sub]
    by_cases hb : euclidNorm (X i ω) ≤ R
    · have hI1 : quadBallIndicator R X i ω = 1 := by rw [quadBallIndicator, if_pos hb]
      rw [hI1, one_mul]
      exact hω i (2 * R + 1) fun e he => by
        have h1 := abs_sq_euclidNorm_add_le (X i ω) e he
        linarith
    · have hI0 : quadBallIndicator R X i ω = 0 := by rw [quadBallIndicator, if_neg hb]
      rw [hI0, zero_mul, abs_zero]
      positivity
  have hvarQ' : ∀ j, μ[fun ω => (truncatedQuad ε ξ R X (j + 1) ω -
      truncatedQuad ε ξ R X j ω) ^ 2 | pathFiltration hX.measurable j] ≤ᵐ[μ]
      fun _ => (2 * R + 1) ^ 2 := by
    intro j
    have hsquare : (fun ω => (truncatedQuad ε ξ R X (j + 1) ω -
        truncatedQuad ε ξ R X j ω) ^ 2) =ᵐ[μ]
        quadBallIndicator R X j * fun ω =>
          (driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
            driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X j ω) ^ 2 := by
      filter_upwards with ω
      rw [truncatedQuad_succ_sub, Pi.mul_apply, mul_pow, quadBallIndicator]
      split_ifs <;> ring
    refine (condExp_congr_ae hsquare).trans_le ?_
    have hIntDelta2 : Integrable (fun ω =>
        (driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
          driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X j ω) ^ 2) μ := by
      have hpath := integrable_path_next_drift hd1 hε hξ hX j
        (fun p z => (euclidNorm z ^ 2 - driftNextMean ε ξ (fun z : Site d => euclidNorm z ^ 2)
          (extendPath p) j) ^ 2)
      simpa only [driftDynkin_succ_sub, driftNextMean_pastPath] using hpath
    have hpull := condExp_stronglyMeasurable_mul_of_bound (μ := μ)
      ((pathFiltration hX.measurable).le j) (hI_sm j) hIntDelta2 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (quadBallIndicator_nonneg R X j ω)]
        exact quadBallIndicator_le_one R X j ω)
    filter_upwards [hpull, condExp_sq_driftDynkin_succ_sub_le hd1 hε hξ hX
      (fun z : Site d => euclidNorm z ^ 2) j] with ω e1 e2
    rw [e1, Pi.mul_apply]
    by_cases hb : euclidNorm (X j ω) ≤ R
    · have hI1 : quadBallIndicator R X j ω = 1 := by rw [quadBallIndicator, if_pos hb]
      rw [hI1, one_mul]
      refine e2.trans ?_
      calc ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun i => X i ω) j e *
            (euclidNorm (X j ω + e) ^ 2 - euclidNorm (X j ω) ^ 2) ^ 2
          ≤ ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun i => X i ω) j e * (2 * R + 1) ^ 2 := by
            refine sum_le_sum fun e he => mul_le_mul_of_nonneg_left ?_
              (driftStepProb_nonneg hε hξ _ j e)
            have h1 := abs_sq_euclidNorm_add_le (X j ω) e he
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
        _ = (2 * R + 1) ^ 2 := by
            rw [← sum_mul, sum_driftStepProb hd1 ε ξ _ j, one_mul]
    · have hI0 : quadBallIndicator R X j ω = 0 := by rw [quadBallIndicator, if_neg hb]
      rw [hI0, zero_mul]
      positivity
  obtain ⟨M, hMmart, hMinc, hM0, hMae⟩ :=
    CERW.Generic.Martingale.exists_martingale_clamp hmartQ'
      (b := 2 * (2 * R + 1)) (by positivity) hinc
  refine ⟨M, hMmart, hMinc, ?_, ?_, ?_⟩
  · intro j
    have hsq : (fun ω => (M (j + 1) ω - M j ω) ^ 2) =ᵐ[μ]
        fun ω => (truncatedQuad ε ξ R X (j + 1) ω -
          truncatedQuad ε ξ R X j ω) ^ 2 := by
      filter_upwards [hMae] with ω hω
      rw [hω (j + 1), hω j]
    exact (condExp_congr_ae hsq).trans_le (hvarQ' j)
  · intro ω
    rw [hM0 ω, truncatedQuad_zero]
  · have hQ'eq : ∀ ω, (∀ j ≤ n, euclidNorm (X j ω) ≤ R) →
        truncatedQuad ε ξ R X n ω =
          driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X n ω := by
      intro ω hball
      have hsum : truncatedQuad ε ξ R X n ω =
          ∑ j ∈ Finset.range n,
            (driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
              driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X j ω) := by
        simp only [truncatedQuad]
        refine sum_congr rfl fun j hj => ?_
        have hjn : j ≤ n := le_of_lt (Finset.mem_range.mp hj)
        have hI1 : quadBallIndicator R X j ω = 1 := by rw [quadBallIndicator, if_pos (hball j hjn)]
        rw [hI1, one_mul]
      rw [hsum, Finset.sum_range_sub
        (fun j => driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X j ω) n,
        driftDynkin_zero, sub_zero]
    filter_upwards [hMae] with ω hω hball
    rw [hω n, hQ'eq ω hball]

/-- The deterministic rearrangement: for the radius `R ≤ s + 1`, the Freedman threshold at bracket
`n (2 R + 1)²` and increment bound `2 (2 R + 1)` is at most `18 c (s + 1) √(n log n)`. -/
private theorem quad_det_arith {c s R : ℝ} {n : ℕ} (hc : 0 ≤ c) (hn : 2 ≤ n) (hs : 0 ≤ s)
    (hRs : R ≤ s + 1) (hR : 0 < R) :
    c * (Real.sqrt ((n : ℝ) * (2 * R + 1) ^ 2 * Real.log ((n : ℝ) + 2)) +
        2 * (2 * R + 1) * Real.log ((n : ℝ) + 2)) ≤
      18 * c * (s + 1) * Real.sqrt ((n : ℝ) * Real.log n) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  set ℓ : ℝ := Real.log (n : ℝ) with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos (by linarith)
  have hL2 : L ≤ 2 * ℓ := by
    have h1 : Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_pow] at h1
    simpa [hL, hℓ] using h1
  have hL0 : 0 ≤ L := by rw [hL]; exact Real.log_nonneg (by linarith)
  set S : ℝ := Real.sqrt ((n : ℝ) * ℓ) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hℓS : ℓ ≤ S := by
    apply Real.le_sqrt_of_sq_le
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n)
    nlinarith
  have hnL : Real.sqrt ((n : ℝ) * L) ≤ 2 * S := by
    calc Real.sqrt ((n : ℝ) * L) ≤ Real.sqrt (4 * ((n : ℝ) * ℓ)) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * S := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have hsq : Real.sqrt ((n : ℝ) * (2 * R + 1) ^ 2 * L) =
      (2 * R + 1) * Real.sqrt ((n : ℝ) * L) := by
    rw [show (n : ℝ) * (2 * R + 1) ^ 2 * L = (2 * R + 1) ^ 2 * ((n : ℝ) * L) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hsq]
  have h2R : 2 * R + 1 ≤ 3 * (s + 1) := by linarith
  have hinner : Real.sqrt ((n : ℝ) * L) + 2 * L ≤ 6 * S := by linarith
  have hnn : 0 ≤ Real.sqrt ((n : ℝ) * L) + 2 * L :=
    add_nonneg (Real.sqrt_nonneg _) (by linarith)
  calc c * ((2 * R + 1) * Real.sqrt ((n : ℝ) * L) + 2 * (2 * R + 1) * L)
      = c * ((2 * R + 1) * (Real.sqrt ((n : ℝ) * L) + 2 * L)) := by ring
    _ ≤ c * ((3 * (s + 1)) * (6 * S)) := by
        refine mul_le_mul_of_nonneg_left ?_ hc
        exact mul_le_mul h2R hinner hnn (by positivity)
    _ = 18 * c * (s + 1) * S := by ring

/-- The failure probability of one radius: `(clog₂ ⌈n (2 R + 1)²⌉ + 1) · 2 e^{-(p + 4) log (n + 2)}`
is at most `22 (n + 1)³ n^{-(p + 4)}` for `R = k + 1`, `k ≤ n`. -/
private theorem quad_prob_arith {p : ℝ} (hp : 0 < p) {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    (((Nat.clog 2 ⌈(n : ℝ) * (2 * ((k : ℝ) + 1) + 1) ^ 2⌉₊ : ℕ) : ℝ) + 1) *
        (2 * Real.exp (-((p + 4) * Real.log ((n : ℝ) + 2)))) ≤
      22 * ((n : ℝ) + 1) ^ 3 * (n : ℝ) ^ (-(p + 4)) := by
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
  set W : ℝ := (n : ℝ) * (2 * ((k : ℝ) + 1) + 1) ^ 2 with hW
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hX1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hWle : W ≤ 9 * ((n : ℝ) + 1) ^ 3 := by
    rw [hW]
    have h1 : 2 * ((k : ℝ) + 1) + 1 ≤ 3 * ((n : ℝ) + 1) := by linarith
    have h2 : (2 * ((k : ℝ) + 1) + 1) ^ 2 ≤ (3 * ((n : ℝ) + 1)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    calc (n : ℝ) * (2 * ((k : ℝ) + 1) + 1) ^ 2 ≤ ((n : ℝ) + 1) * (3 * ((n : ℝ) + 1)) ^ 2 :=
          mul_le_mul (by linarith) h2 (by positivity) (by positivity)
      _ = 9 * ((n : ℝ) + 1) ^ 3 := by ring
  have hceil : (⌈W⌉₊ : ℝ) ≤ 9 * ((n : ℝ) + 1) ^ 3 + 1 := by
    have h1 : (⌈W⌉₊ : ℝ) < W + 1 := Nat.ceil_lt_add_one hW0
    linarith
  have hclog : ((Nat.clog 2 ⌈W⌉₊ : ℕ) : ℝ) ≤ (⌈W⌉₊ : ℝ) := by
    exact_mod_cast Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hclog1 : ((Nat.clog 2 ⌈W⌉₊ : ℕ) : ℝ) + 1 ≤ 11 * ((n : ℝ) + 1) ^ 3 := by linarith
  have hexp : 2 * Real.exp (-((p + 4) * Real.log ((n : ℝ) + 2))) ≤
      2 * (n : ℝ) ^ (-(p + 4)) :=
    CERW.Generic.Martingale.two_mul_exp_neg_mul_log_le (K := p + 4) (by linarith) (n := n) hn
  calc (((Nat.clog 2 ⌈W⌉₊ : ℕ) : ℝ) + 1) * (2 * Real.exp (-((p + 4) * Real.log ((n : ℝ) + 2))))
      ≤ (11 * ((n : ℝ) + 1) ^ 3) * (2 * (n : ℝ) ^ (-(p + 4))) :=
        mul_le_mul hclog1 hexp (by positivity) (by positivity)
    _ = 22 * ((n : ℝ) + 1) ^ 3 * (n : ℝ) ^ (-(p + 4)) := by ring

/-- The union over the `n + 1` radii: `(n + 1) · 22 (n + 1)³ n^{-(p + 4)} ≤ 352 n^{-p}`. -/
private theorem quad_sum_arith {p : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) + 1) * (22 * ((n : ℝ) + 1) ^ 3 * (n : ℝ) ^ (-(p + 4))) ≤ 352 * (n : ℝ) ^ (-p) := by
  have h := CERW.Generic.Martingale.pow_mul_rpow_neg_le hn 4 p
  have h4 : (-(p + ((4 : ℕ) : ℝ))) = -(p + 4) := by norm_num
  rw [h4] at h
  calc ((n : ℝ) + 1) * (22 * ((n : ℝ) + 1) ^ 3 * (n : ℝ) ^ (-(p + 4)))
      = 22 * (((n : ℝ) + 1) ^ 4 * (n : ℝ) ^ (-(p + 4))) := by ring
    _ ≤ 22 * (2 ^ 4 * (n : ℝ) ^ (-p)) := by gcongr
    _ = 352 * (n : ℝ) ^ (-p) := by ring


/-- **The quadratic martingale bound `eq:quadratic-coarse`.** For every `p > 0` there is `C`
such that, for the walk with any field `ξ` of bounded drift, with `ξ 0 = 0`, and every `n ≥ 2`,
`μ(|𝒬_n| > C (R_out(n) + 1) √(n log n)) ≤ C n^{-p}`. The stopped martingales at the radii
`1 ≤ k ≤ n + 1` have increments at most `2 (2 k + 1)` and conditional variances at most
`(2 k + 1)²`; Freedman's inequality at dyadic brackets bounds each, a union over the radii bounds
all of them, and the least radius above the maximum of the path selects the one that agrees with
`𝒬`. -/
theorem exists_quadratic_producer : QuadraticProducer.{u} := by
  intro d hd ε hε p hp
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c, hc1, hc⟩ := CERW.Generic.Martingale.exists_dyadic_bound (K := p + 4) (by linarith)
  have hc0 : 0 ≤ c := by linarith
  refine ⟨18 * c + 352, by positivity, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hn1 : 1 ≤ n := by omega
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  choose M hMmart hMinc hMvar hM0 hMae using fun k : ℕ =>
    exists_clamped_quadratic_drift hd hε.le hξ (R := (k : ℝ) + 1) (by positivity) n hX
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  -- the failure probability of one radius
  have hper : ∀ k : ℕ, k ≤ n →
      μ {ω | c * (Real.sqrt ((n : ℝ) * (2 * ((k : ℝ) + 1) + 1) ^ 2 * L) +
          2 * (2 * ((k : ℝ) + 1) + 1) * L) < |M k n ω|} ≤
        ENNReal.ofReal (22 * ((n : ℝ) + 1) ^ 3 * (n : ℝ) ^ (-(p + 4))) := by
    intro k hk
    set R : ℝ := (k : ℝ) + 1 with hR
    have hRpos : 0 < R := by rw [hR]; positivity
    set b : ℝ := 2 * (2 * R + 1) with hb
    set W : ℝ := (n : ℝ) * (2 * R + 1) ^ 2 with hW
    set V : ℕ → Ω → ℝ := fun t _ => (t : ℝ) * (2 * R + 1) ^ 2 with hV
    have hbpos : 0 < b := by rw [hb]; positivity
    have hsq1 : (1 : ℝ) ≤ (2 * R + 1) ^ 2 := by nlinarith
    have hW1 : 1 ≤ W := by
      rw [hW]
      nlinarith
    have hVpred : ∀ j, StronglyMeasurable[pathFiltration hX.measurable j] (V (j + 1)) :=
      fun _ => stronglyMeasurable_const
    have hV0 : ∀ ω, V 0 ω = 0 := by
      intro ω
      simp only [hV]
      ring
    have hVmono : ∀ j ω, V j ω ≤ V (j + 1) ω := by
      intro j ω
      simp only [hV]
      have hnn : 0 ≤ (2 * R + 1) ^ 2 := sq_nonneg _
      push_cast
      nlinarith
    have hVdom : ∀ j, μ[fun ω => (M k (j + 1) ω - M k j ω) ^ 2 | pathFiltration hX.measurable j]
        ≤ᵐ[μ] fun ω => V (j + 1) ω - V j ω := by
      intro j
      refine (hMvar k j).trans ?_
      filter_upwards with ω
      have h : V (j + 1) ω - V j ω = (2 * R + 1) ^ 2 := by
        simp only [hV]
        push_cast
        ring
      rw [h]
    have hVW : ∀ ω, V (0 + n) ω - V 0 ω ≤ W := by
      intro ω
      rw [zero_add]
      have h : V n ω - V 0 ω = W := by
        simp only [hV, hW]
        ring
      rw [h]
    have hdy := hc (hMmart k) hVpred hV0 hVmono hVdom (b := b) hbpos 0 n
      (fun i _ _ ω => hMinc k i ω) (W := W) (L := L) hW1 hLpos (fun ω => hVW ω)
    refine le_trans (measure_mono ?_) (hdy.trans (ENNReal.ofReal_le_ofReal ?_))
    · intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have hVval : V (0 + n) ω - V 0 ω = W := by
        rw [zero_add]
        simp only [hV, hW]
        ring
      rw [hVval, max_eq_left hW1, zero_add, hM0 k ω, sub_zero]
      exact hω
    · exact quad_prob_arith hp hn1 hk
  -- the a.e. good set
  have hstart : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    rw [ae_iff]
    exact hX.start
  have hsteps : ∀ᵐ ω ∂μ, ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d :=
    ae_all_iff.mpr (ae_sub_mem_unitSteps_drift hd1 hε.le hξ hX)
  have hcut : ∀ᵐ ω ∂μ, ∀ k : ℕ, (∀ j ≤ n, euclidNorm (X j ω) ≤ (k : ℝ) + 1) →
      M k n ω = driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X n ω :=
    ae_all_iff.mpr fun k => (hMae k)
  have hsub : {ω | ¬ QuadraticEstimate d ε ξ (18 * c + 352) (fun j => X j ω) n} ≤ᵐ[μ]
      ⋃ k ∈ Finset.range (n + 1), {ω | c * (Real.sqrt ((n : ℝ) *
        (2 * ((k : ℝ) + 1) + 1) ^ 2 * L) + 2 * (2 * ((k : ℝ) + 1) + 1) * L) < |M k n ω|} := by
    filter_upwards [hstart, hsteps, hcut] with ω h0 hs hk hω
    have hω : (18 * c + 352) * (maxRadius (fun j => X j ω) n + 1) *
        Real.sqrt ((n : ℝ) * Real.log n) <
          |quadraticMartingale d ε ξ (fun j => X j ω) n| := not_le.mp hω
    set s : ℝ := maxRadius (fun j => X j ω) n with hsdef
    have hs0 : 0 ≤ s :=
      (LatticeProb.euclidNorm_nonneg _).trans
        (euclidNorm_le_maxRadius (fun j => X j ω) (Nat.zero_le n))
    have hsn : s ≤ n := CERW.Support.Occupation.maxRadius_le_of_steps (fun j => X j ω) h0 hs n
    set m : ℕ := ⌊s⌋₊ with hm
    have hms : (m : ℝ) ≤ s := Nat.floor_le hs0
    have hsm : s < (m : ℝ) + 1 := Nat.lt_floor_add_one s
    have hmn : m ≤ n := Nat.floor_le_of_le hsn
    have hball : ∀ j ≤ n, euclidNorm (X j ω) ≤ (m : ℝ) + 1 := fun j hj =>
      (euclidNorm_le_maxRadius (fun j => X j ω) hj).trans hsm.le
    refine Set.mem_iUnion₂.mpr ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hmn), ?_⟩
    simp only [Set.mem_setOf_eq]
    have hQ : quadraticMartingale d ε ξ (fun j => X j ω) n = M m n ω := by
      rw [hk m hball]
      exact quadraticMartingale_eq_driftDynkin hd1 ε ξ hξ0 X ω hs n
    rw [hQ] at hω
    refine lt_of_le_of_lt ?_ hω
    have hdet := quad_det_arith (c := c) (s := s) (R := (m : ℝ) + 1) (n := n) hc0 hn hs0
      (by linarith) (by positivity)
    refine hdet.trans ?_
    have hnn : 0 ≤ (s + 1) * Real.sqrt ((n : ℝ) * Real.log n) := by positivity
    nlinarith [hnn, hc0]
  calc μ {ω | ¬ QuadraticEstimate d ε ξ (18 * c + 352) (fun j => X j ω) n}
      ≤ μ (⋃ k ∈ Finset.range (n + 1), {ω | c * (Real.sqrt ((n : ℝ) *
          (2 * ((k : ℝ) + 1) + 1) ^ 2 * L) + 2 * (2 * ((k : ℝ) + 1) + 1) * L) < |M k n ω|}) :=
        measure_mono_ae hsub
    _ ≤ ∑ k ∈ Finset.range (n + 1), μ {ω | c * (Real.sqrt ((n : ℝ) *
          (2 * ((k : ℝ) + 1) + 1) ^ 2 * L) + 2 * (2 * ((k : ℝ) + 1) + 1) * L) < |M k n ω|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range (n + 1),
          ENNReal.ofReal (22 * ((n : ℝ) + 1) ^ 3 * (n : ℝ) ^ (-(p + 4))) :=
        Finset.sum_le_sum fun k hk => hper k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    _ = ENNReal.ofReal (((n : ℝ) + 1) *
          (22 * ((n : ℝ) + 1) ^ 3 * (n : ℝ) ^ (-(p + 4)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (p := (n : ℝ) + 1) (by positivity)]
        congr 1
        rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (352 * (n : ℝ) ^ (-p)) := ENNReal.ofReal_le_ofReal (quad_sum_arith hn1)
    _ ≤ ENNReal.ofReal ((18 * c + 352) * (n : ℝ) ^ (-p)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _)

end QuadraticProducer

/-! ## Measurability of the event -/

section Measurability

open Finset CERW.Support.Law

/-- The departure range up to a time at most `n + 1` depends only on the path up to time `n`. -/
private theorem departureRange_congr {x y : ℕ → Site d} {n m : ℕ} (h : ∀ j ≤ n, x j = y j)
    (hm : m ≤ n + 1) : departureRange x m = departureRange y m :=
  Finset.image_congr fun j hj => h j (by have := mem_range.mp hj; omega)

/-- The local times at a time at most `n + 1` depend only on the path up to time `n`. -/
private theorem localTime_congr {x y : ℕ → Site d} {n m : ℕ} (h : ∀ j ≤ n, x j = y j)
    (hm : m ≤ n + 1) : localTime x m = localTime y m := by
  funext z
  unfold localTime
  congr 1
  exact Finset.filter_congr fun j hj => by rw [h j (by have := mem_range.mp hj; omega)]

private theorem maxLocalTime_congr {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) :
    maxLocalTime x n = maxLocalTime y n := by
  unfold maxLocalTime
  rw [departureRange_congr h (Nat.le_succ n), localTime_congr h (Nat.le_succ n)]

private theorem maxRadius_congr {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) :
    maxRadius x n = maxRadius y n := by
  unfold maxRadius
  exact Finset.sup'_congr _ rfl fun j hj => by
    rw [h j (by have := mem_range.mp hj; omega)]

private theorem freshCount_congr {x y : ℕ → Site d} {n s t : ℕ} (h : ∀ j ≤ n, x j = y j)
    (ht : t ≤ n) : freshCount x s t = freshCount y s t := by
  unfold freshCount
  congr 1
  refine Finset.filter_congr fun j hj => ?_
  have hjt : j < t := (mem_Ico.mp hj).2
  rw [h j (by omega), departureRange_congr h (by omega : j ≤ n + 1)]

private theorem intervalMax_congr {x y : ℕ → Site d} {n s t : ℕ} (h : ∀ j ≤ n, x j = y j)
    (ht : t ≤ n) : intervalMax x s t = intervalMax y s t := by
  have himg : (Finset.Ico s t).image x = (Finset.Ico s t).image y :=
    Finset.image_congr fun j hj => h j (by have := (mem_Ico.mp hj).2; omega)
  have hloc : intervalLocalTime x s t = intervalLocalTime y s t := by
    funext z
    unfold intervalLocalTime
    congr 1
    exact Finset.filter_congr fun j hj => by
      rw [h j (by have := (mem_Ico.mp hj).2; omega)]
  unfold intervalMax
  rw [himg, hloc]

private theorem cellSet_congr {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) :
    cellSet x n = cellSet y n := by
  unfold cellSet
  rw [departureRange_congr h (Nat.le_succ n)]

private theorem cellLocalTime_congr {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) :
    cellLocalTime x n = cellLocalTime y n := by
  funext v
  unfold cellLocalTime
  rw [localTime_congr h (Nat.le_succ n)]

private theorem driftCompensated_congr {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    {x y : ℕ → Site d} {n t : ℕ} (h : ∀ j ≤ n, x j = y j) (ht : t ≤ n) :
    CERW.Support.Norm.VectorBound.driftCompensated ε ξ x t =
      CERW.Support.Norm.VectorBound.driftCompensated ε ξ y t := by
  unfold CERW.Support.Norm.VectorBound.driftCompensated
  rw [h t ht]
  congr 2
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjt : j < t := mem_range.mp hj
  rw [h j (by omega), departureRange_congr h (by omega : j ≤ n + 1)]

private theorem quadraticMartingale_congr {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) :
    quadraticMartingale d ε ξ x n = quadraticMartingale d ε ξ y n := by
  unfold quadraticMartingale
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j < n := mem_range.mp hj
  rw [h j (by omega), h (j + 1) (by omega), departureRange_congr h (by omega : j ≤ n + 1)]

private theorem dynkinMart_congr {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) (f : Site d → ℝ) :
    dynkinMart (driftStepProb d ε ξ) f x n = dynkinMart (driftStepProb d ε ξ) f y n := by
  unfold dynkinMart
  rw [h n le_rfl, h 0 (Nat.zero_le n)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j < n := mem_range.mp hj
  unfold stepMean
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [CERW.Support.Drift.driftStepProb_congr (fun i hi => h i (by omega)) e, h j (by omega)]

/-- The constituents of the event other than the typing depend only on the path up to time `n`. -/
private theorem constituents_congr (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (K : EventConstants)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ) {x y : ℕ → Site d}
    (h : ∀ j ≤ n, x j = y j) :
    (CoarseBounds d Ψ ε K.c_co K.C_co x n ∧ LocalBounds d Ψ ε K.C_loc x n ∧
      VectorEstimate d ε ξ K.C_vec x n ∧ LocalMartEstimate d ε ξ K.C_mart x n ∧
      QuadraticEstimate d ε ξ K.C_quad x n ∧
      LinearEstimate d Ψ ε ξ K.C_lin (radialDirections d Ψ n) x n ∧
      LinearEstimate d Ψ ε ξ K.C_lin (projectionDirections d Ψ ε n P) x n) ↔
    (CoarseBounds d Ψ ε K.c_co K.C_co y n ∧ LocalBounds d Ψ ε K.C_loc y n ∧
      VectorEstimate d ε ξ K.C_vec y n ∧ LocalMartEstimate d ε ξ K.C_mart y n ∧
      QuadraticEstimate d ε ξ K.C_quad y n ∧
      LinearEstimate d Ψ ε ξ K.C_lin (radialDirections d Ψ n) y n ∧
      LinearEstimate d Ψ ε ξ K.C_lin (projectionDirections d Ψ ε n P) y n) := by
  have hdep : departureRange x n = departureRange y n := departureRange_congr h (Nat.le_succ n)
  have hloc : localTime x n = localTime y n := localTime_congr h (Nat.le_succ n)
  have hmax : maxLocalTime x n = maxLocalTime y n := maxLocalTime_congr h
  have hrad : maxRadius x n = maxRadius y n := maxRadius_congr h
  have hcell : cellSet x n = cellSet y n := cellSet_congr h
  have hclt : cellLocalTime x n = cellLocalTime y n := cellLocalTime_congr h
  have hdyn : ∀ f : Site d → ℝ, dynkinMart (driftStepProb d ε ξ) f x n =
      dynkinMart (driftStepProb d ε ξ) f y n := dynkinMart_congr h
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_
    (and_congr ?_ ?_)))))
  · simp only [CoarseBounds, hdep, hmax, hrad]
  · simp only [LocalBounds, hdep, hmax, hcell, hclt]
    refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
    refine forall_congr' fun s => forall_congr' fun t => forall_congr' fun hst =>
      forall_congr' fun htn => ?_
    rw [intervalMax_congr h htn, freshCount_congr h htn]
  · unfold VectorEstimate
    refine forall_congr' fun s => forall_congr' fun t => forall_congr' fun hst =>
      forall_congr' fun htn => ?_
    rw [driftCompensated_congr h htn, driftCompensated_congr h (by omega : s ≤ n)]
  · simp only [LocalMartEstimate, hdep, hloc, hdyn]
  · simp only [QuadraticEstimate, quadraticMartingale_congr h, hrad]
  · simp only [LinearEstimate, hdep, hloc, hdyn]
  · simp only [LinearEstimate, hdep, hloc, hdyn]

/-- The event of Section 5.1 is measurable when the positions of the walk are: the typing is a
countable intersection of conditions on two consecutive positions, and the other constituents
depend only on the path up to time `n`, a point of a countable type. -/
theorem measurableSet_section5Event {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → Site d}
    (hX : ∀ j, Measurable (X j)) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (K : EventConstants)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    MeasurableSet (Section5Event Ψ ε ξ K P X n) := by
  set Pre : (ℕ → Site d) → Prop := fun x =>
    CoarseBounds d Ψ ε K.c_co K.C_co x n ∧ LocalBounds d Ψ ε K.C_loc x n ∧
      VectorEstimate d ε ξ K.C_vec x n ∧ LocalMartEstimate d ε ξ K.C_mart x n ∧
      QuadraticEstimate d ε ξ K.C_quad x n ∧
      LinearEstimate d Ψ ε ξ K.C_lin (radialDirections d Ψ n) x n ∧
      LinearEstimate d Ψ ε ξ K.C_lin (projectionDirections d Ψ ε n P) x n with hPre
  have h1 : Section5Event Ψ ε ξ K P X n =
      {ω | PathTyping d (fun j => X j ω)} ∩ {ω | Pre (fun j => X j ω)} := by
    ext ω
    simp only [Section5Event, hPre, Set.mem_setOf_eq, Set.mem_inter_iff]
  have h2 : {ω | Pre (fun j => X j ω)} = pastPath X n ⁻¹' {p | Pre (extendPath p)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact constituents_congr Ψ ε ξ K P n fun j hj => (extendPath_pastPath X hj ω).symm
  have h3 : MeasurableSet {ω | PathTyping d (fun j => X j ω)} := by
    have hset : {ω | PathTyping d (fun j => X j ω)} =
        X 0 ⁻¹' {0} ∩ ⋂ j : ℕ, (fun ω => (X (j + 1) ω, X j ω)) ⁻¹'
          {q : Site d × Site d | q.1 - q.2 ∈ unitSteps d} := by
      ext ω
      simp only [PathTyping, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_iInter]
    rw [hset]
    refine (hX 0 (measurableSet_singleton _)).inter (MeasurableSet.iInter fun j => ?_)
    exact ((hX (j + 1)).prodMk (hX j)) (Set.to_countable _).measurableSet
  rw [h1, h2]
  exact h3.inter (measurable_pastPath hX n (Set.to_countable _).measurableSet)

end Measurability

/-! ## The contact bound on the event, and its probability -/

/-- **The contact estimate on the event of Section 5.1.** Let `Ψ` be a norm in dimension `d ≥ 2`,
`ε > 0` with `ε Ψ(e_i) < 1/d`, and `p > 0`. There are constants `K` of the event, `C` and an
integer `n₀`, depending only on `d`, `Ψ`, `ε`, `p`, such that for every field `ξ` of subgradients
with `ξ 0 = 0`, every probability space carrying the walk with drift field `ξ`, every `n ≥ n₀` and
every selection `P` of the projection directions:

* the complement of the event `Section5Event` has probability at most `C n^{-p}`, and
* on the event, every contact point `y₀` (`Ψ(y₀) = inf_{y ∉ D_n} Ψ(y)` and `y₀` in the closure of
  the complement of `D_n`) satisfies `U_{D_n}(y₀) ≤ C r_n q_n`.

The inputs are the independent producers of the constituents: Proposition 4.1 and Lemma 3.1
(`hcoarse`, `hlocal`, whose constants precede `ξ`, the model and `n`), the vector bound and the
local martingale bound for the lattice kernel (proved in `VectorBound` and `ContactPotential`), the
halfspace martingale bounds for finite families (`hlin`) and the quadratic martingale bound
(`exists_quadratic_producer`), together with the lemmas on the potential of a norm ball (`hgeom`,
`hball`). The contact bound is the deterministic `contact_bound_of_event_inputs`, which uses only
the typing, the coarse bounds, Lemma 3.1 and `eq:localmart`; the vector, quadratic and halfspace
constituents belong to the event as in the source but are not consumed. -/
theorem contact_on_section5Event (hcoarse : norm_coarse_bounds.{u})
    (hlocal : norm_local_time_potential.{u}) (hlin : LinearProducer.{u})
    (hgeom : norm_potential_geometry) (hball : norm_ball_potential) (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ (K : EventConstants) (C : ℝ), 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
        ∀ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
          μ (Section5Event Ψ ε ξ K P X n)ᶜ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
          ∀ ω ∈ Section5Event Ψ ε ξ K P X n, ∀ y₀ : EuclideanSpace ℝ (Fin d),
            Ψ y₀ = normInnerRadius Ψ (fun j => X j ω) n →
            y₀ ∈ closure (cellSet (fun j => X j ω) n)ᶜ →
            normPotential d ε Ψ (cellSet (fun j => X j ω) n) y₀ ≤
              C * scale d Ψ ε n * contactRate d Ψ ε n := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hc0, -⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc0 (normMin_le_normMax hd1 hΨ)
  obtain ⟨c_co, C_co, hcc, hCc, hco⟩ := hcoarse hd Ψ hΨ ε hε hell p hp
  obtain ⟨C_loc, hCl, hloc⟩ := hlocal hd Ψ hΨ ε hε hell p hp
  obtain ⟨C_V, hCV, hvec⟩ :=
    CERW.Support.Norm.VectorBound.exists_driftCompensated_bound hd1 hε.le hp
  obtain ⟨h, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  obtain ⟨C_lm, hClm, hlm⟩ := ContactDynkin.exists_drift_local_mart hd hε.le hgrad hp
  obtain ⟨C_LM, hCLM, hLM⟩ := hlin hd hΨ hε hell (p := p + d + 1) (by positivity)
  obtain ⟨C_Q, hCQ, hQ⟩ := exists_quadratic_producer.{u} hd hε hp
  obtain ⟨C₀, hC₀, n₁, hdet⟩ := contact_bound_of_event_inputs hgeom hball hd hΨ hε c_co C_co
    C_loc (2 * C_lm) hCc.le hCl.le (by positivity)
  refine ⟨⟨c_co, C_co, C_loc, C_V, 2 * C_lm, C_Q, C_LM⟩,
    max (C_co + C_loc + C_V + C_lm + C_Q + C_LM * 4 * 3 ^ d) C₀,
    lt_max_of_lt_left (by positivity), max n₁ 2, le_max_right _ _, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn P
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hn1 : n₁ ≤ n := (le_max_left _ _).trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg hnR.le _
  have hξ' := drift_coord_le hΨ hε hell hξ hξ0
  have hN : μ {ω | ¬ PathTyping d (fun j => X j ω)} = 0 := by
    have hpath : ∀ᵐ ω ∂μ, PathTyping d (fun j => X j ω) := by
      have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
        rw [ae_iff]
        exact hX.start
      filter_upwards [h0, ae_all_iff.mpr
        (CERW.Support.Drift.ae_sub_mem_unitSteps_drift hd1 hε.le hξ' hX)] with ω h0 hs
      exact ⟨h0, hs⟩
    exact ae_iff.mp hpath
  have hE_co : μ {ω | ¬ CoarseBounds d Ψ ε c_co C_co (fun j => X j ω) n} ≤
      ENNReal.ofReal (C_co * (n : ℝ) ^ (-p)) := hco ξ hξ hξ0 μ X hX n hn2
  have hE_loc : μ {ω | ¬ LocalBounds d Ψ ε C_loc (fun j => X j ω) n} ≤
      ENNReal.ofReal (C_loc * (n : ℝ) ^ (-p)) := hloc ξ hξ hξ0 μ X hX n hn2
  have hE_vec := hvec hξ' hξ0 hX n hn2
  have hE_lm := hlm hξ' hX n hn2
  have hE_quad : μ {ω | ¬ QuadraticEstimate d ε ξ C_Q (fun j => X j ω) n} ≤
      ENNReal.ofReal (C_Q * (n : ℝ) ^ (-p)) := hQ hξ' hξ0 hX n hn2
  have hQnorm : ∀ q ∈ radialDirections d Ψ n ∪ projectionDirections d Ψ ε n P,
      ‖q‖ ≤ normMax Ψ := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact norm_le_normMax_of_mem_radialDirections hΛ.le hq
    · exact norm_le_normMax_of_mem_projectionDirections hΛ.le hq
  have hcard : (((radialDirections d Ψ n ∪ projectionDirections d Ψ ε n P).card : ℕ) : ℝ) ≤
      2 * (2 * (n : ℝ) + 1) ^ d := by
    obtain ⟨h1, h2⟩ := card_directions_le Ψ ε n P
    have := Finset.card_union_le (radialDirections d Ψ n) (projectionDirections d Ψ ε n P)
    have h3 : (((radialDirections d Ψ n ∪ projectionDirections d Ψ ε n P).card : ℕ) : ℝ) ≤
        ((radialDirections d Ψ n).card : ℝ) + ((projectionDirections d Ψ ε n P).card : ℝ) := by
      exact_mod_cast this
    linarith
  have hE_lin := (hLM hξ hξ0 hX n hn2 (radialDirections d Ψ n ∪ projectionDirections d Ψ ε n P)
    hQnorm).trans (ENNReal.ofReal_le_ofReal
      (union_count_arith (p := p) hCLM.le d (by omega) hcard))
  refine ⟨?_, ?_⟩
  · refine measure_le_of_subset_union_six (E₁ := {ω | ¬ CoarseBounds d Ψ ε c_co C_co
      (fun j => X j ω) n}) (E₂ := {ω | ¬ LocalBounds d Ψ ε C_loc (fun j => X j ω) n})
      (E₃ := {ω | ∃ s t : ℕ, s < t ∧ t ≤ n ∧ C_V * Real.sqrt (((t : ℝ) - s) * Real.log n) <
        ‖CERW.Support.Norm.VectorBound.driftCompensated ε ξ (fun j => X j ω) t -
          CERW.Support.Norm.VectorBound.driftCompensated ε ξ (fun j => X j ω) s‖})
      (E₄ := {ω | ∃ y : Site d, euclidNorm y ≤ 3 * n ∧
        C_lm * (Real.sqrt ((∑ j ∈ Finset.range n,
            (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log (n + 2)) +
          Real.log (n + 2)) <
        |CERW.Support.Drift.driftDynkin ε ξ (fun z => latticeKernel d (z - y)) X n ω|})
      (E₅ := {ω | ¬ QuadraticEstimate d ε ξ C_Q (fun j => X j ω) n})
      (E₆ := {ω | ∃ q ∈ radialDirections d Ψ n ∪ projectionDirections d Ψ ε n P, ∃ k : ℕ,
        k ≤ n ∧ C_LM * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange (fun j => X j ω) n).filter
              (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
            (localTime (fun j => X j ω) n z : ℝ)) + Real.log n) <
          |dynkinMart (driftStepProb d ε ξ)
            (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) (fun j => X j ω) n|})
      (N := {ω | ¬ PathTyping d (fun j => X j ω)}) ?_ hE_co hE_loc hE_vec hE_lm hE_quad
      hE_lin hN (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) ?_
    · intro ω hω
      by_contra hnot
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq] at hnot
      obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hnot
      apply hω
      simp only [Section5Event, Set.mem_setOf_eq]
      refine ⟨not_not.mp h7, not_not.mp h1, not_not.mp h2, ?_, ?_, not_not.mp h5, ?_, ?_⟩
      · intro s t hst htn
        exact not_lt.mp fun hlt => h3 ⟨s, t, hst, htn, hlt⟩
      · intro y hy
        have h4y := not_lt.mp fun hlt => h4 ⟨y, hy, hlt⟩
        rw [CERW.Support.Drift.dynkinMart_driftStepProb_eq_driftDynkin hd1 ε ξ _ X n ω]
        have hW : (∑ j ∈ Finset.range n, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) =
            ∑ x ∈ departureRange (fun j => X j ω) n,
              (localTime (fun j => X j ω) n x : ℝ) *
                (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)) :=
          CERW.Support.LocalTime.sum_range_eq_sum_localTime (fun j => X j ω) n
            (fun x => (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)))
        have hS0 : 0 ≤ ∑ j ∈ Finset.range n, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ)) :=
          Finset.sum_nonneg fun j _ =>
            Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg (X j ω - y)]) _
        have hL0 := log_pos_of_two_le hn2
        have hL := log_add_two_le hn2
        have hsq : Real.sqrt ((∑ j ∈ Finset.range n,
            (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) ≤
            2 * Real.sqrt ((∑ j ∈ Finset.range n,
              (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log n) := by
          have h4' : (∑ j ∈ Finset.range n,
              (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2) ≤
              2 ^ 2 * ((∑ j ∈ Finset.range n,
                (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log n) := by
            have := mul_le_mul_of_nonneg_left hL hS0
            nlinarith [mul_nonneg hS0 hL0.le]
          calc _ ≤ Real.sqrt (2 ^ 2 * ((∑ j ∈ Finset.range n,
                (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log n)) :=
                Real.sqrt_le_sqrt h4'
            _ = 2 * Real.sqrt _ := by
                rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
        show _ ≤ 2 * C_lm * (Real.sqrt ((∑ x ∈ departureRange (fun j => X j ω) n,
            (localTime (fun j => X j ω) n x : ℝ) *
              (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ))) * Real.log n) + Real.log n)
        rw [← hW]
        calc _ ≤ C_lm * (Real.sqrt ((∑ j ∈ Finset.range n,
              (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
                Real.log ((n : ℝ) + 2)) := h4y
          _ ≤ C_lm * (2 * Real.sqrt ((∑ j ∈ Finset.range n,
              (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log n) +
                2 * Real.log n) :=
              mul_le_mul_of_nonneg_left (add_le_add hsq hL) hClm.le
          _ = 2 * C_lm * (Real.sqrt ((∑ j ∈ Finset.range n,
              (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log n) +
                Real.log n) := by ring
      · intro q hq k hk
        exact not_lt.mp fun hlt => h6 ⟨q, Finset.mem_union_left _ hq, k, hk, hlt⟩
      · intro q hq k hk
        exact not_lt.mp fun hlt => h6 ⟨q, Finset.mem_union_right _ hq, k, hk, hlt⟩
    · calc C_co * (n : ℝ) ^ (-p) + C_loc * (n : ℝ) ^ (-p) + C_V * (n : ℝ) ^ (-p) +
          C_lm * (n : ℝ) ^ (-p) + C_Q * (n : ℝ) ^ (-p) + C_LM * 4 * 3 ^ d * (n : ℝ) ^ (-p)
          = (C_co + C_loc + C_V + C_lm + C_Q + C_LM * 4 * 3 ^ d) * (n : ℝ) ^ (-p) := by ring
        _ ≤ max (C_co + C_loc + C_V + C_lm + C_Q + C_LM * 4 * 3 ^ d) C₀ * (n : ℝ) ^ (-p) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hnp
  · intro ω hω y₀ hy₀ hcl
    obtain ⟨hty, hcoω, hlocω, -, hlmω, -, -, -⟩ := hω
    have hU := hdet ξ hξ hξ0 (fun j => X j ω) n hn1 hty hcoω hlocω hlmω y₀ hy₀ hcl
    have hV : 0 < normBallVolume Ψ := normBallVolume_pos' hd1 hΨ
    have hr : 0 < scale d Ψ ε n := by
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      exact Real.rpow_pos_of_pos (by positivity) _
    have hq : 0 ≤ contactRate d Ψ ε n := by
      unfold contactRate
      split_ifs
      · exact Real.sqrt_nonneg _
      · exact div_nonneg (log_pos_of_two_le hn2).le hr.le
    exact hU.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le) hq)

end CERW.Support.Norm.ContactEvent
