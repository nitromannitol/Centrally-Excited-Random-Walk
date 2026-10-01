# Feasibility: proving `CERW.External.MartingaleCLT` (Hall-Heyde Cor. 3.1) from Mathlib + CERW

Checked against `CERW/External/MartingaleCLT.lean:20` (HEAD 9217e0b; the statement and `CERW.predBracket`
(`CERW/Model/Bracket.lean:16`) are unchanged since 9d4a3ff). Mathlib 81a5d257, LatticeProb 4bdbaa4, Lean 4.32.0.
Probe: `scratch/externals/CltProbe.lean`, exit status 0 (section 5). Machine-checked prototypes:
`scratch/externals/CltPrototypes.lean`, exit 0 under `-DmaxHeartbeats=100000`, axioms `[propext, Classical.choice, Quot.sound]`.
Existing drafts of this project live in the gitignored `wip/clt/` and `wip/plan/martingale-clt-plan.md`; I re-ran them
(statuses in the table). The plan is sound; this note re-derives it independently, fixes two defects and shortens G2.

## 1. Route (paper proof, adapted to the Lean statement)

Source. Statement: Hall-Heyde (1980) Cor. 3.1 with constant `eta^2 = v`. Technique: characteristic function with a
predictable truncation and an exponential compensator (the classical conditional-ch.f. argument; cf. Hall-Heyde Ch. 3,
Helland 1982). I did not have the books; the argument below is self-contained, its analytic core (E3, E4, H2, the
exp-Lipschitz bound) is machine-checked, and the remaining steps are routine and were checked by hand. It is NOT
McLeish's product route (needs the realized bracket) and NOT Lindeberg replacement (needs an independent Gaussian family).

Fix a row `n`, `M_k = S_k / s_n`, `D_k = M_{k+1} - M_k`, `sigma_k = E[D_k^2 | F_k]`, `V_k = sum_{j<k} max(sigma_j,0)`
(pathwise nondecreasing, `V_{k+1}` is `F_k`-measurable, `V_k =ae predBracket`), `c = v+1`, `g_k = 1{V_{k+1} <= c}`
(`bracketIndicator`), `X_k = g_k D_k`, `Mc_k = sum_{j<k} X_j` (`predictableStop`), `q_k = E[X_k^2 | F_k] =ae g_k sigma_k`,
`Q_n = sum_{k<n} q_k`, `Y_k = exp(i t Mc_k + t^2 Q_k / 2)`.
1. (F1-F3) `E[X_k|F_k]=0`; `Q_n <= c` a.e.; `Lindeberg_k(X) <= Lindeberg_k(M)`. Only `L^2` is used, never an increment bound.
2. (E1,E2) `|e^{iy} - 1 - iy + y^2/2| <= 4 min(|y|^3, y^2)` for all real `y`; `|e^a(1-a) - 1| <= a^2 e^a / 2` for `a >= 0`.
3. (E3) A bounded `F_k`-measurable complex `W` satisfies `E[W f] = E[W E[f|F_k]]` for real integrable `f`.
4. (E4) One step: `|E[W (e^{itX} e^{t^2 q/2} - 1)]| <= K e^{t^2 c/2} (t^4/8 E[q^2] + 4(delta |t|^3 E[X^2] + t^2 E[X^2 1{|X|>delta}]))`.
   Write `e^{itX} = 1 + itX - t^2 X^2/2 + r`, `a = t^2 q / 2`; the `X` term and the `a - t^2 X^2/2` term vanish by E3, the rest is E1, E2.
5. (G1a,b,c) `Y_{k+1} - Y_k = Y_k (e^{itX_k} e^{t^2 q_k/2} - 1)`, `Y_0 = 1`, `|Y_k| <= e^{t^2 c/2}`. Telescope, apply E4 at each `k`, and use
   `q_k <= delta^2 + L'_k`, `sum L'_k <= min(lind, c)`: `|E Y_n - 1| <= e^{t^2 c} (t^4/8 c (delta^2 + iota) + 4(delta |t|^3 c + t^2 iota))`,
   `iota = E min(lind_delta, c)`.
6. (G2, simplified relative to the plan) Let `p = P(eta < |V_n - v|)`, `0 < eta <= 1`, `Z = e^{t^2 v/2} e^{itM_n} - Y_n`. On `{|V_n - v| <= eta}` one has
   `V_n <= c`, so `Mc_n = M_n` (`predictableStop_eq_of_le`) and `Q_n = V_n`, hence `|Z| <= e^{t^2 c/2} (t^2/2) eta` by `|e^y - e^x| <= e^A |y - x|`.
   Elsewhere `|Z| <= 2 e^{t^2 c/2}`. So `|E e^{itM_n} - e^{-t^2 v/2}| <= |E Y_n - 1| + e^{t^2 c/2} (t^2 eta/2 + 2p)`. The constancy of `v` is used exactly here
   (`e^{t^2 v/2}` leaves the integral). The truncation cost is the `2p` term, so no Slutsky step is needed
   (`tendstoInDistribution_of_tendstoInMeasure_sub` exists but would add a row-wise CLT for the stopped array).
7. (J,K) `iota_n(delta) -> 0` because `min(lind_n, c)` is `>= 0` a.e., `<= c`, and `-> 0` in measure (bounded convergence in measure, E7);
   `p_n(eta) -> 0` is the bracket hypothesis. Given `eps`, choose `delta, eta` small, then `n` large: `E e^{itM^n_n} -> e^{-t^2 v/2}` for every `t`.
8. (H2) Levy (`tendsto_iff_tendsto_charFun`) + `charFun_gaussianReal` give `TendstoInDistribution _ atTop id (fun _ => mu) (gaussianReal 0 v)`.
9. (H3) Rows `M^n_k = S_k / s_n`: `Martingale.smul`, `condExp_smul` for `predBracket(S)/s_n^2`, `sub_div` for the Lindeberg term.

Edge cases. `v = 0`: no case split (`charFun_gaussianReal` holds for every `v : NNReal`; the limit is `dirac 0`; `c = 1`, bound unchanged).
`s n` need not tend to infinity: each row is treated separately and only the two hypotheses at time `n` are used. `S 0 = 0` gives `Mc_0 = 0`
and `Mc_n = M_n` on the good set. `n = 0`: empty sums. No filtration nesting or stable convergence is needed because `v` is a constant.
No `IsStoppingTime`/`stoppedProcess` API is used: the CERW indicator form already has adaptedness, the martingale property and the agreement lemma.

## 2. Packets (dependency order; "wip" = draft in `wip/clt`, compiled by me)

Notation: E1..H3 as in the plan. "new" = lines still to write. Names are indexed with file:line in section 6.

| # | File (under `CERW/Generic/Martingale/CLT/`) | Lean sketch | Names used | new | risk |
|---|---|---|---|---|---|
| A | `ExpBounds` (E1,E2) | `norm_cexp_I_sub_taylor_le : forall y:R, ‖cexp(y*I) - (1+y*I-y^2/2)‖ <= 4*min (abs(y)^3) (y^2)`; `abs_exp_mul_one_sub_sub_one_le : 0<=a -> abs(exp a*(1-a)-1) <= a^2/2*exp a` | Complex.exp_bound, Complex.norm_exp_ofReal_mul_I, Real.one_sub_le_exp_neg, Real.sum_le_exp_of_nonneg | 0 (wip 115 lines, exit 0) | low |
| B | `CondPullOut` (E3,E7) | `integral_mul_ofReal_eq_integral_mul_condExp : m<=m0 -> Integrable f mu -> StronglyMeasurable[m] W -> (ae ‖W‖<=K) -> ∫ W*f = ∫ W*condExp[f ; m]`; `tendsto_integral_of_tendstoInMeasure_of_bounded : (0<=f n<=C ae) -> f ->0 in meas -> ∫ f n -> 0` | condExp_stronglyMeasurable_bilin_of_bound, integral_condExp, integral_congr_ae, tendstoInMeasure_iff_measureReal_norm, integral_mono_of_nonneg | ~3 (wip 97 lines, exit 1: see below) | low |
| C | `Truncation` (F1,F2,F3) | `pathBracket` monotone/predictable/`=ae predBracket`; `condExp[g D ; F_k]=0`, `condExp[(gD)^2 ; F_k]=g condExp[D^2 ; F_k]`; `sum_k condExp[(gD)^2 ; F_k] <= c` a.e., truncated Lindeberg term `<=` original | bracketIndicator, predictableStop, stronglyMeasurable_bracketIndicator, sum_bracketIndicator_mul_le, condExp_increment_eq_zero, condExp_stronglyMeasurable_mul_of_bound, condExp_nonneg, condExp_mono, MemLp.integrable_sq, CERW.predBracket | 0 (wip 248 lines, exit 0) | low |
| D | `ArrayForm` (H2,H3) | `tendstoInDistribution_gaussianReal_of_tendsto_integral_cexp : (forall n, AEMeasurable (X n) mu) -> (forall t, ∫ cexp(t*X n*I) -> cexp(-(t^2*v/2))) -> TendstoInDistribution X atTop id (fun _ => mu) (gaussianReal 0 v)`; `martingaleCLT_of_arrayCLT : ArrayCLT -> MartingaleCLT` | ProbabilityMeasure.tendsto_iff_tendsto_charFun, charFun_apply_real, integral_map, Measure.map_id, charFun_gaussianReal, TendstoInDistribution, Martingale.smul, condExp_smul, TendstoInMeasure.congr, TendstoInMeasure.congr_left | ~25 (wip 101 lines, exit 0 with one `sorry` = last goal of H2; my 20-line proof of H2 is in `CltPrototypes`) | low |
| E | `StepBound` (E4) | `norm_integral_step_le : (E1 E2 E3 as hypotheses) -> m<=m0 -> MemLp X 2 mu -> condExp[X ; m]=ae 0 -> StronglyMeasurable[m] W -> (ae ‖W‖<=K) -> (ae condExp[X^2 ; m]<=c) -> 0<=delta -> ‖∫ W*(cexp(t*X*I)*cexp(t^2*condExp[X^2 ; m]/2)-1)‖ <= K*exp(t^2*c/2)*(...)` | condExp_nonneg, stronglyMeasurable_condExp, integrable_condExp, Integrable.bdd_mul, Integrable.ofReal, Integrable.mono', norm_integral_le_of_norm_le, integral_add, integral_sub, integral_const_mul, Complex.ofReal_exp, MemLp.integrable_sq | ~190 (proved in `CltPrototypes`, 170 lines + 2 helpers) | low (done) |
| F | `CompensatorShape` (G1a) | `Y_succ_sub : Y (k+1)-Y k = Y k*(cexp(t*X_k*I)*cexp(t^2*q_k/2)-1)` and `Y 0 = 1`; `stronglyMeasurable_Y : StronglyMeasurable[ℱ k] (Y k)`; `norm_Y_le : ae, k<=n -> ‖Y k‖ <= exp(t^2*c/2)` given `sum_{j<n} q_j<=c`, `q_j>=0` ae | stronglyAdapted_predictableStop, predictableStop_succ_sub, stronglyMeasurable_condExp, condExp_nonneg, Complex.norm_exp | ~100 | med |
| G | `LindebergSums` (G1b, real only) | `sum_integral_sq_condVar_le : sum_k ∫ q_k^2 <= c*(delta^2+iota)`; `sum_integral_sq_le : sum_k ∫ X_k^2 <= c`; `sum_integral_tail_le : sum_k ∫ X_k^2 1{delta<abs(X_k)} <= iota` | integral_condExp, condExp_add, condExp_const, condExp_mono, condExp_nonneg, integral_mono_ae, integral_finsetSum, Integrable.mono' | ~130 | med |
| H | `CompensatedBound` (G1) | `norm_integral_Y_sub_one_le : (Martingale M, L2, M 0=0) -> ‖∫ cexp(t*Mc n*I + t^2/2*sum q) - 1‖ <= exp(t^2*c)*(t^4/8*(c*(delta^2+iota)) + 4*(delta*abs(t)^3*c + t^2*iota))` (exact `CompensatedCexpBoundStatement`) | E, F, G; MemLp.mono, integral_finsetSum, norm_integral_le_integral_norm, Finset.sum_range_sub (core) | ~90 | med |
| I | `CharFunBound` (G2) | `abs_exp_sub_exp_le : x<=A -> y<=A -> abs(exp y-exp x) <= exp A*abs(y-x)` (proved in `CltPrototypes`); `norm_integral_cexp_sub_le : 0<=v -> 0<delta -> 0<eta<=1 -> ‖∫ cexp(t*M n*I) - cexp(-(t^2*v/2))‖ <= (G1 bound with c=v+1) + exp(t^2*c/2)*(t^2*eta/2 + 2*mu.real{eta<abs(predBracket-v)})` | H, C, predictableStop_eq_of_le, bracketIndicator_of_le, norm_integral_le_of_norm_le, measure_mono_ae, Complex.norm_exp, Real.add_one_le_exp | ~170 (+40 proved) | med-high |
| J | `LindebergInMeasure` (H1a) | `tendsto_integral_min_lind : lind_n -> 0 in measure -> ∫ min(lind_n,c) -> 0`; `tendsto_measureReal_bracket : TendstoInMeasure ... -> mu.real{eta<abs(predBracket_n - v)} -> 0` | B (E7), condExp_nonneg, measure_mono_ae, tendstoInMeasure_iff_measureReal_norm | ~60 | low-med |
| K | `ArrayCharFun` (H1) | `ArrayCharFunTendstoStatement` (rows `M n`; for all `t`, `∫ cexp(t*M n n*I) -> cexp(-(t^2*v/2))`) by an `eps`/`delta`/`eta` argument from I and J | I, J; Metric.tendsto_nhds | ~80 | med-low |
| L | `Assembly` (glue) | `martingaleCLT_holds : CERW.External.MartingaleCLT.{u} := martingaleCLT_of_arrayCLT (fun .. => tendstoInDistribution_gaussianReal_of_tendsto_integral_cexp .. (arrayCharFun_tendsto ..))`; unify the duplicate `lind`/`pathBracket` defs of `Truncation` and `Interfaces` | D, K | ~30 | low |

Defects found in the existing drafts. (i) `wip/clt/CondPullOut.lean:36` fails ("expected `∂?m`"): with `{m0} {m}` both local instances, `Measure Ω` picks the
LAST one, `m`. Declare `{m m0 : MeasurableSpace Ω}` (as Mathlib's `PullOut.lean` does) and E3 compiles (14 lines, `CltPrototypes`).
(ii) The plan's G2 carries `2p + e^{t^2 c}(...) + e^{t^2 c/2}(t^2/2)(eta + c p)` (needs `E|Q_n - v|`); step 6 above gives the shorter bound that
packet I states. The plan's G2 is also true; either may be chosen, but the shorter one is mine and is NOT yet machine-checked beyond its two analytic ingredients.

## 3. Missing pieces (no usable Mathlib / LatticeProb / CERW support)

1. Any martingale CLT or conditional characteristic function bound: absent from Mathlib (only the i.i.d. CLT `tendstoInDistribution_inv_sqrt_mul_sum`,
   independent summands) and LatticeProb. `LatticeProb.Prob.Freedman` is a template (real exponential, bounded increments: `condExp_one_add_linear_quadratic`,
   `integral_exp_sub_condQvar_le_one`), not reusable. `LatticeProb/Prob/WeightedCLT.lean` (`charFun_second_order`, `norm_prod_sub_prod_le_sum`, ...) is the
   independent-array product route and has NO compiled olean at this pin (`import LatticeProb.Prob.WeightedCLT` fails), so nothing from it is cited.
   `taylorWithinEval_charFun_two_zero` is for unconditional laws only: unusable in the conditional step.
2. Third-order Taylor bound for `e^{iy}` valid for all real `y`: Mathlib has only `Complex.exp_bound` for `|x| <= 1`; the case `|y|>1` is done by hand (packet A, done).
3. Bounded convergence in measure (`0 <= f_n <= C`, `f_n -> 0` in measure `=> ∫ f_n -> 0`): Mathlib has Vitali (`tendsto_Lp_finite_of_tendstoInMeasure`,
   needs `UnifIntegrable`) but no direct lemma; packet B proves it by hand in ~40 lines (compiles in wip).
4. Complex-weight pull-out: Mathlib's `condExp_mul_of_stronglyMeasurable_left` is real-valued; the bilinear version
   `condExp_stronglyMeasurable_bilin_of_bound` with `B : C ->L[R] R ->L[R] C` covers it (E3, verified).
5. A packaged `charFun` convergence => `TendstoInDistribution` for a Gaussian limit: not in Mathlib; 20 lines (H2, verified, includes `v = 0`).
6. The compensator estimate itself (packets F, G, H, I): all new. No `TendstoInMeasure` squeeze lemma exists; packet J uses `measure_mono_ae` by hand.
7. Pathwise-monotone bracket (`pathBracket`): `CERW.predBracket` is only a.e. nonnegative, and `predictableStop_eq_of_le` needs a pathwise monotone `V`,
   hence `max(.,0)` (packet C, done). Nothing in `CERW/Support` is reusable: every `predBracket` lemma there is `private` and specific to the walk.

## 4. Verdict

FEASIBLE. 12 packets (A..L). Done or nearly done: A, C (complete drafts), E (complete prototype), B and D (about 30 lines of fixes). New lines still to write:
about 880 (E 190, F 100, G 130, H 90, I 170, J 60, K 80, L 30, B/D 28); with the existing drafts the final library is about 1450 lines
(range 1200 to 1800). Critical path: F -> H -> I -> K -> L, about 470 lines in sequence (G runs in parallel with F; E is done).
Estimated sequence of waves: wave 1 {A, B, C, D, F, G} (independent given the `Interfaces` statements), wave 2 {H}, wave 3 {I, J}, wave 4 {K, L}.

Riskiest step: packet I (G2). It combines (a) the a.e. identification `Q_n = V_n` on the good set for all `k < n` simultaneously (F2 plus
`bracketIndicator_of_le` plus `condExp_nonneg`), (b) `predictableStop_eq_of_le` with the pathwise hypotheses, (c) an indicator bound over a set defined by a
condExp-valued function with `mu.real` conversions, and (d) the final algebra with `e^{-t^2 v/2}`; its statement is new and the largest context in the file.
Second: packets G/H (sums of conditional expectations; keep nlinarith out of large contexts, use explicit `mul_le_mul` terms as in the project memory).
The local analytic core (E1-E4, H2, the exp-Lipschitz bound) is no longer a risk: it compiles with clean axioms.

## 5. Probe

`scratch/externals/CltProbe.lean` imports `CERW.External.MartingaleCLT`, `CERW.Generic.Martingale.FreedmanEvent`, `LatticeProb.Prob.Freedman` and the
Mathlib files for every cited name and `#check`s all 79 of them. Command (repo root):
`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false scratch/externals/CltProbe.lean`. Exit status: 0, no output other than the `#check` lines.
`scratch/externals/CltPrototypes.lean`: same flags plus `-DmaxHeartbeats=100000`, exit status 0. No tracked file was edited and no `lake build` was run.

## 6. Name index (file:line of the declaration; `M:` = `.lake/packages/mathlib/Mathlib/`, `L:` = `.lake/packages/lattice-probability/LatticeProb/`)

CERW: `CERW.External.MartingaleCLT` CERW/External/MartingaleCLT.lean:20; `CERW.predBracket` CERW/Model/Bracket.lean:16;
in `CERW/Generic/Martingale/FreedmanEvent.lean`: `bracketIndicator` 25, `predictableStop` 30, `bracketIndicator_of_le` 52, `bracketIndicator_of_lt` 58,
`stronglyMeasurable_bracketIndicator` 64, `predictableStop_succ_sub` 77, `predictableStop_eq_of_le` 83, `sum_bracketIndicator_mul_le` 100,
`condExp_increment_eq_zero` 120, `integrable_predictableStop` 134, `stronglyAdapted_predictableStop` 158, `martingale_predictableStop` 173
(all in namespace `CERW.Generic.Martingale`).

LatticeProb (templates only): `LatticeProb.condExp_one_add_linear_quadratic` L:Prob/Freedman.lean:32; `condQvar` 114; `integral_exp_sub_condQvar_le_one` 168.

Mathlib, convergence and Gaussian: `TendstoInDistribution` M:MeasureTheory/Function/ConvergenceInDistribution.lean:64;
`tendstoInDistribution_of_tendstoInMeasure_sub` same file:172; `ProbabilityMeasure.tendsto_iff_tendsto_charFun` M:MeasureTheory/Measure/LevyConvergence.lean:214;
`charFun_apply_real` M:MeasureTheory/Measure/CharacteristicFunction/Basic.lean:130; `taylorWithinEval_charFun_two_zero` .../CharacteristicFunction/TaylorExpansion.lean:126;
`ProbabilityTheory.charFun_gaussianReal` M:Probability/Distributions/Gaussian/Real.lean:485; `gaussianReal_zero_var` same file:229;
`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum` M:Probability/CentralLimitTheorem.lean:79; `integral_map` M:MeasureTheory/Integral/Bochner/Basic.lean:1043;
`Measure.map_id` M:MeasureTheory/Measure/Map.lean:193; `TendstoInMeasure` M:MeasureTheory/Function/ConvergenceInMeasure.lean:57;
`tendstoInMeasure_iff_measureReal_norm` same file:129; `TendstoInMeasure.congr` 183; `TendstoInMeasure.congr_left` 187;
`measure_mono_ae` M:MeasureTheory/OuterMeasure/AE.lean:260; `tendsto_Lp_finite_of_tendstoInMeasure` M:MeasureTheory/Function/UniformIntegrable.lean:565.

Mathlib, conditional expectation (`M:MeasureTheory/Function/ConditionalExpectation/`): in `Basic.lean`: `condExp_of_stronglyMeasurable` 142, `condExp_const` 147,
`condExp_congr_ae` 201, `stronglyMeasurable_condExp` 187, `integrable_condExp` 222, `integral_condExp` 236, `condExp_add` 292, `condExp_smul` 317, `condExp_sub` 335,
`condExp_mono` 486, `condExp_nonneg` 495; in `PullOut.lean`: `condExp_stronglyMeasurable_bilin_of_bound` 85, `condExp_stronglyMeasurable_mul_of_bound` 260.

Mathlib, martingales (`M:Probability/Martingale/Basic.lean`): `Martingale` 53, `Martingale.stronglyMeasurable` 88, `Martingale.condExp_ae_eq` 92, `Martingale.integrable` 97,
`Martingale.smul` 123, `martingale_of_condExp_sub_eq_zero_nat` 504; `IsStoppingTime` M:Probability/Process/Stopping.lean:75, `stoppedProcess` same file:824 (unused).

Mathlib, integrals (`M:MeasureTheory/Integral/Bochner/Basic.lean` unless noted): `integral_add` 237, `integral_finsetSum` 246, `integral_sub` 261, `integral_const_mul` 288,
`integral_congr_ae` 299, `integral_mono_ae` 627, `integral_mono_of_nonneg` 639, `norm_integral_le_integral_norm` 934, `norm_integral_le_of_norm_le` 947;
`Integrable.bdd_mul` M:MeasureTheory/Function/L1Space/Integrable.lean:1065, `Integrable.mono'` same file:100, `Integrable.ofReal` 1107;
`Integrable.of_bound` M:MeasureTheory/Integral/IntegrableOn.lean:171; `MemLp.integrable_sq` M:MeasureTheory/Function/L2Space.lean:42;
`MemLp.mono` M:MeasureTheory/Function/LpSeminorm/Basic.lean:508.

Mathlib, other: `Finset.sum_range_sub` M:Algebra/BigOperators/Group/Finset/Basic.lean:896 (additive form of the telescoping-product lemma), `Metric.tendsto_nhds` M:Topology/MetricSpace/Pseudo/Defs.lean:891.

Mathlib, exponentials: `Complex.exp_bound` M:Analysis/Complex/Exponential.lean:375, `Complex.ofReal_exp` 189, `Real.sum_le_exp_of_nonneg` 246, `Real.add_one_le_exp` 631,
`Real.one_sub_le_exp_neg` 639, `Complex.norm_exp_ofReal` 708; `Complex.norm_exp` M:Analysis/Complex/Trigonometric.lean:983, `Complex.norm_exp_ofReal_mul_I` same file:950.
