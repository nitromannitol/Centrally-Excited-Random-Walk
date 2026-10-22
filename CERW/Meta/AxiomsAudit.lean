import CERW.MainTheorems

/-!
# Axiom closure of the paper's statements

These commands print the kernel axiom closure of each registered source theorem
and each main theorem restatement. The statement gates check the allowed closure.
-/

#print axioms CERW.LimitShapes.limit_shape
#print axioms CERW.LimitShapes.fluctuation_rates
#print axioms CERW.LimitShapes.sharp_radii
#print axioms CERW.LimitShapes.sharp_radii_lil
#print axioms CERW.LimitShapes.sharp_bulk
#print axioms CERW.LimitShapes.sharp_width
#print axioms CERW.LimitShapes.norm_shape
#print axioms CERW.LimitShapes.norm_ball_potential
#print axioms CERW.LimitShapes.freedman_bound
#print axioms CERW.LimitShapes.cell_gradient
#print axioms CERW.LimitShapes.norm_coarse_bounds
#print axioms CERW.LimitShapes.norm_shape_rates
#print axioms CERW.LimitShapes.layer_potential
#print axioms CERW.LimitShapes.inner_radius
#print axioms CERW.LimitShapes.outer_radius
#print axioms CERW.LimitShapes.near_far
#print axioms CERW.LimitShapes.moment_fluctuations
#print axioms CERW.LimitShapes.fixed_site_centering
#print axioms CERW.LimitShapes.site_fluctuations
#print axioms CERW.LimitShapes.exp_deviation
#print axioms CERW.LimitShapes.bulk_profile
#print axioms CERW.LimitShapes.log_lower_bounds
#print axioms CERW.LimitShapes.norm_local_time_potential
#print axioms CERW.LimitShapes.contact_potential
#print axioms CERW.LimitShapes.separated_brackets
#print axioms CERW.MainTheorems.limit_shape
#print axioms CERW.MainTheorems.fluctuation_rates
#print axioms CERW.MainTheorems.sharp_radii
#print axioms CERW.MainTheorems.sharp_radii_lil
#print axioms CERW.MainTheorems.sharp_bulk
#print axioms CERW.MainTheorems.sharp_width
#print axioms CERW.MainTheorems.norm_shape

#print axioms CERW.LimitShapes.DynkinBounds.exists_dynkin_freedman_bound
#print axioms CERW.LimitShapes.ShiftedSquare.exists_squareKernel_step_bound
#print axioms CERW.LimitShapes.KernelEvents.exists_localMartingaleBound
#print axioms CERW.LimitShapes.KernelEvents.exists_squareMartingaleBound
#print axioms CERW.LimitShapes.distance_crossing_bound
#print axioms CERW.LimitShapes.exists_common_event
#print axioms CERW.LimitShapes.contact_potential_on_common_event
#print axioms CERW.LimitShapes.Crossing.Probability.distanceCrossingBound_mono
#print axioms CERW.LimitShapes.CommonEvent.stopped_quadratic_bound_of_coarse
#print axioms CERW.LimitShapes.ContactEvent.contactRate_nonneg
#print axioms CERW.LimitShapes.ExitStopping.exit_norm_le
#print axioms CERW.LimitShapes.ExitStopping.stoppedQuadratic_eq_sum_range_min
#print axioms CERW.LimitShapes.QuadraticStopping.stoppedQuadratic_succ_sub
#print axioms CERW.LimitShapes.QuadraticStopping.abs_stoppedQuadratic_increment_le
#print axioms CERW.LimitShapes.RadiusEvents.outer_on_event
#print axioms CERW.LimitShapes.QuadraticDynkin.stronglyAdapted_quadratic
#print axioms CERW.LimitShapes.QuadraticDynkin.martingale_quadratic
#print axioms CERW.LimitShapes.StoppedQuadraticMartingale.stoppedQuadratic_congr
#print axioms CERW.LimitShapes.StoppedQuadraticMartingale.stronglyAdapted_stoppedQuadratic
#print axioms CERW.LimitShapes.StoppedQuadraticMartingale.martingale_stoppedQuadratic
#print axioms CERW.LimitShapes.QuadraticStopping.abs_stoppedQuadratic_increment_le_normMax
#print axioms CERW.LimitShapes.SquareDynkin.squareKernel_stepMean
#print axioms CERW.LimitShapes.SquareDynkin.squareKernel_dynkin_identity
#print axioms CERW.LimitShapes.EuclideanEvent.exists_euclidean_event
#print axioms CERW.LimitShapes.RadiusEvents.radius_bounds_on_event

#print axioms CERW.LimitShapes.QuadraticProbability.exists_stopped_quadratic_tail
#print axioms CERW.LimitShapes.separated_brackets_on_euclidean_event
