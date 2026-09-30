# Unconsumed public theorems

This file lists the public theorems under `CERW` that are not in the dependency closure of the
anchor proofs. The closure follows theorem statements and proofs. Its roots are the Support proofs
of the seven anchors, the one-sided Hausdorff variant, and the kernel bridges `kernelFacts_two` and
`kernelFacts_ge_three`. Equation lemmas are excluded. There are 25 such theorems.

* **Definition guards (8), kept by design.** Each pins a definition against a junk value.
  * `CERW.Support.Guards.departureRange_zero`
  * `CERW.Support.Guards.visitedRange_zero`
  * `CERW.Support.Guards.sum_localTime`
  * `CERW.Support.Guards.firstStep_three_four`
  * `CERW.Support.Guards.unitBallVolume_two`
  * `CERW.Support.Guards.unitBallVolume_three`
  * `CERW.Support.Guards.limitRadius_spec`
  * `CERW.Support.Guards.exists_cerw_realization`
* **Non-vacuity witness (1), kept by design.** `CERW.Support.Law.exists_isCERW` shows that
  `IsCERW` has a model for every `0 ≤ ε < 1/d`.
* **Model API (12), kept.** These are small facts about the definitions:
  * `card_unitSteps`, `condExp_next`, `exists_abs_le_of_euclidNorm_le`, `sum_firstStep_smul`,
    `sum_srwStep_smul`, `toSpace_eq_sum_unit`, `toSpace_neg` and `pathFiltration.congr_simp` in
    `CERW.Support.Law`;
  * `freshCount_le`, `maxLocalTime_le` and `maxRadius_le_of_steps` in `CERW.Support.Occupation`;
  * `CERW.mem_cell_iff`.
* **Superseded route (4), candidates for removal before the freeze.**
  * `CERW.Generic.Lattice.sum_finset_rpow_one_sub_le`
  * `CERW.Generic.Newton.integrable_sphere_of_integrable`
  * `CERW.Generic.Young.log_sub_log_mem_Icc`
  * `CERW.Generic.Young.rpow_neg_sub_mem_Icc`
