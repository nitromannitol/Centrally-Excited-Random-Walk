# Pre-freeze refute-first audit (independent fresh instance)

* **Target:** the transient `scratch/Anchors.lean`, sha256
  `0ca9ad7c017455d2c70060404c71549bb2d3036e28624ddad1be9d52b5ea2e66`. It holds 7 theorems with
  `by sorry` bodies and the External.
* **Vocabulary:** `CERW/Model/*` at commit `7c2689b`.
* **Procedure:** `lean-statement-audit`, refute-first, read-only, with transient probes that were
  deleted afterwards.

## Machine evidence produced by the auditor

* **A0.** A copy of the target compiles; the only warnings are the 7 `sorry` warnings. The
  consumption prototypes elaborate.
* **A1.** The auditor wrote an independent reconstruction of all 8 declarations from the tex, with
  every cast spelled out (`((d:ℝ)+1)`, `2*(d:ℝ)-1`, `(-1:ℝ)/12`, …) and its own definitions of
  a, N, L, Q, the event `Good`, the Hausdorff rate, λ_n and e_n. Each reconstruction is closed by
  exactly the frozen export (`Iff.rfl` for the External), so the elaborated types match. No hidden
  ℕ-division or ℕ-subtraction.
* **A2: definition probes, all compiling.**
  * ℓ_n is a sum of indicators.
  * `srwHeat 2 1 (unit 0) = 1/4` and `srwHeat 2 1 (e0+e1) = 0`.
  * On the path 0, e0, 0, e0, …: `stepProb` at time 0 is 1/4 (origin, SRW); at time 1 it is
    1/4 − ε/2 for +e0 and 1/4 + ε/2 for −e0 (first departure); at time 3 it is 1/4 (revisit, SRW).
  * From `IsCERW` alone: P(X0=0, X1=e0, X2=2e0) = ofReal(1/4)·ofReal(1/4 − ε/2).
  * The cell is half-open: its left endpoint is in, its right endpoint is out.
  * `#print axioms exists_isCERW` gives `[propext, Classical.choice, Quot.sound]`.
  * `toSphere_apply_univ` gives total mass dω_d.
* **A3.** `summable_srwHeat (3 ≤ d)` has clean axioms, and `srwGreen d M x → srwGreenInf d x`: in
  d ≥ 3 the Green function is a genuine sum, not the junk `tsum`.
* **Numerics.**
  * The constant chain dΓ(d/2)/((d−2)π^{d/2}) = 2/((d−2)V_d), V_d the unit-ball volume, holds for
    d = 3..10 to within 1e-16; at d = 3 both are 3/(2π).
  * Planar partial sums Σ_{j<M}(p_j(0) − p_j(x)) up to M = 1600 converge for both parities:
    (1,0) → 1.000000, (1,1) → 4/π, (2,0) → 4 − 8/π.
  * For |x| ≤ 10.4, (value − (2/π)log|x| − (2γ+log 8)/π)·|x|² stays within ±0.1, consistent
    with O(|x|^{-2}).

## Verdicts

| declaration | verdict | EXCESS | notes |
|---|---|---|---|
| `CERW.External.LatticePotentialKernel` | PASS (TRUE statement) | n/a | d ≥ 3: Lawler–Limic Thm 4.3.1 (line 7468), with the ball-volume constant. d = 2: Thm 4.4.4 (line 8243) and the partial-sum definition after (4.15) (line 8052); the limit exists for every x. eq:gradient and (P−I)b = 1_{0} are derived, not assumed |
| `CERW.Frozen.ball_shape` | PASS | 0 | SOURCE 7, TYPING 3, RULED 3. ∀ᵐ precedes ∀η and ∀x (cerw.tex:142); open balls; sup → 0 in the eventual form (R-5) |
| `CERW.Frozen.fluctuation_bounds` | PASS | 0 | C, n₀ after (d, ε, p), before Ω (R-1); casts confirmed by A1; the ENNReal sum is equivalent to the real inequality; second conjunct ∃C ∀ᵐ ∀ᶠ |
| `CERW.Frozen.hausdorff_bound` | PASS | 0 | rates re-derived; both sets nonempty. **CONCERN:** the planar remark is encoded one-sided |
| `CERW.Frozen.local_time_potential` | PASS | 0 | C_d before ε (R-15); λ_n and e_n as displayed; ‖y‖ ≤ 2n in ℝ |
| `CERW.Frozen.potential_geometry` | PASS | 0 | the toSphere normalization checks out; no Bochner junk; Borel vs Lebesgue measurability is immaterial |
| `CERW.Frozen.radial_test` | PASS | 0 | ℕ-valued r₀ is equivalent to a real one; r − b_d > b_d > 0; the shell filter is exhaustive |
| `CERW.Frozen.coarse_bounds` | PASS | 0 | six non-strict inequalities; one c, one C |

**Definition audit.** For all 21 definitions below: BODY_MATCH OK, PUBLIC_CARRIER OK,
WELL_DEFINEDNESS N/A_LITERAL, CHARACTERIZATION N/A_LITERAL, CHOICE_INDEPENDENCE N/A,
DEFINITION_VERDICT PASS. The definitions are `firstStep`, `srwStep`, `stepProb`, `IsCERW`,
`localTime`, `departureRange`, `visitedRange`, `maxLocalTime`, `maxRadius`, `freshCount`,
`intervalLocalTime`, `intervalMax`, `shellMax`, `cell`, `cellSet`, `cellLocalTime`, `potential`,
`tail`, `unitBallVolume`, `toSpace` and `unitDir`.

**Junk values.** None can make a clause vacuous or false:
* every `/` and `-` elaborates in ℝ;
* `log` is taken at arguments ≥ 1 or ≥ 2;
* division by N only at n ≥ 1;
* every rpow base is ≥ 0;
* `toReal` of finite volumes only;
* every Bochner integral is integrable;
* `Finset.sup` of an empty set is the true value;
* no `sSup`;
* every `ofReal` argument is ≥ 0.

## DEFECTs

None.

## CONCERN for the author (ruling requested in `ledger/approval/PHASE-B.md`)

The planar remark "the inner-radius error in the plane is at most Cn^{1/6}√log(n+2) in lattice
units" is encoded one-sided, as `B(0, aN − Cn^{1/6}√L) ∩ ℤ² ⊆ A_n`. Read two-sided, it also
asserts that the inner radius is at most `aN + Cn^{1/6}√L`. That is true, since eq:inradius is
two-sided, but the draft does not state it.

## NOTEs

* The constants C are chosen per sample-space universe u. This is harmless: the law does not
  depend on u, and the existence witness lives in `Type`, transported through `ULift`.
* Borel vs Lebesgue measurability of D in lem:geometry does not matter: U_D and F depend only on
  the a.e. class of D.
