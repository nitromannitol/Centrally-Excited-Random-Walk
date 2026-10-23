import CERW

/-!
# Elaborated types of the frozen statements

The statement hashes in `ledger/oct13.yaml` pin the text of each frozen block. This check pins
the elaborated type of each export registered there and of each theorem of
`CERW/MainTheorems.lean`, with every binder, instance and universe parameter, so that a section
variable or other context outside a frozen block cannot change a statement unnoticed. Each entry
records the 64-bit hash and the length of the fully explicit printed type, and the universe
parameters. Run with `lake env lean tools/FrozenTypes.lean` after `lake build`. After an approved
change of statement, replace the entry by the value the check prints.
-/

open Lean in
run_cmd do
  let expected : Array (Name × UInt64 × Nat × List Name) := #[
    (``CERW.LimitShapes.limit_shape, 8435425723614314236, 29700, [`u]),
    (``CERW.LimitShapes.fluctuation_rates, 7595970576983438552, 58778, [`u]),
    (``CERW.LimitShapes.sharp_radii, 13792085775717561909, 28808, [`u]),
    (``CERW.LimitShapes.sharp_radii_lil, 12038755092376208021, 28999, [`u]),
    (``CERW.LimitShapes.sharp_bulk, 626799424558210261, 28414, [`u]),
    (``CERW.LimitShapes.sharp_width, 7976022896914299232, 32922, [`u]),
    (``CERW.LimitShapes.norm_shape, 4885596237841293665, 7978, [`u]),
    (``CERW.LimitShapes.norm_ball_potential, 1585751764467792010, 1160, []),
    (``CERW.LimitShapes.freedman_bound, 6657303426485752047, 2595, [`u]),
    (``CERW.LimitShapes.cell_gradient, 11802856189424210834, 31964, []),
    (``CERW.LimitShapes.norm_coarse_bounds, 2734997155722000138, 7858, [`u]),
    (``CERW.LimitShapes.norm_shape_rates, 15477099319829793672, 14157, [`u]),
    (``CERW.LimitShapes.layer_potential, 5102984238789070075, 2169, []),
    (``CERW.LimitShapes.inner_radius, 11130119929618956960, 55488, [`u]),
    (``CERW.LimitShapes.outer_radius, 11012028247759243261, 28590, [`u]),
    (``CERW.LimitShapes.near_far, 89890988665239453, 53290, []),
    (``CERW.LimitShapes.moment_fluctuations, 1995923146566628308, 37191, [`u]),
    (``CERW.LimitShapes.fixed_site_centering, 8915430330247964240, 28789, [`u]),
    (``CERW.LimitShapes.site_fluctuations, 16916458140291290869, 50663, [`u]),
    (``CERW.LimitShapes.exp_deviation, 3178691819322210499, 10215, [`u]),
    (``CERW.LimitShapes.bulk_profile, 5079562416031365477, 30220, [`u]),
    (``CERW.LimitShapes.log_lower_bounds, 3901999970211679902, 32383, [`u]),
    (``CERW.LimitShapes.norm_local_time_potential, 14234023717245230487, 6550, [`u]),
    (``CERW.LimitShapes.contact_potential, 13102144208337238619, 4643, []),
    (``CERW.LimitShapes.separated_brackets, 12756596395304876025, 36121, []),
    (``CERW.LimitShapes.distance_crossing_bound, 4903395844735546571, 4295, [`u]),
    (``CERW.LimitShapes.exists_common_event, 11886190267889282060, 5260, [`u]),
    (``CERW.LimitShapes.contact_potential_on_common_event, 311891241794458366, 7575, [`u]),
    (``CERW.LimitShapes.separated_brackets_on_euclidean_event, 7811155747937722285, 37005, [`u]),
    (``CERW.MainTheorems.limit_shape, 13629748971628152765, 29462, [`u]),
    (``CERW.MainTheorems.fluctuation_rates, 17260779497693808517, 58341, [`u]),
    (``CERW.MainTheorems.sharp_radii, 11635643947328707590, 28553, [`u]),
    (``CERW.MainTheorems.sharp_radii_lil, 3325739106838446400, 28759, [`u]),
    (``CERW.MainTheorems.sharp_bulk, 192986005634019636, 28270, [`u]),
    (``CERW.MainTheorems.sharp_width, 11611135184704867710, 32327, [`u]),
    (``CERW.MainTheorems.norm_shape, 8168576230479964865, 7754, [`u])
  ]
  let mut changed : Nat := 0
  for (n, h, len, us) in expected do
    let ci ← getConstInfo n
    let s := ci.type.dbgToString
    unless s.hash == h && s.length == len && ci.levelParams == us do
      changed := changed + 1
      logError m!"{n}: elaborated type changed; now ({s.hash}, {s.length}, {ci.levelParams})"
  logInfo m!"{expected.size} elaborated types checked, {changed} changed"
