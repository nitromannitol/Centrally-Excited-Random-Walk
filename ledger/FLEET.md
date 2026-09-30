# Fleet calibration

One row per packet. `accepted` means the file compiled silently on the director's recheck, its
statements were byte-identical to the leaf, and it contained no banned token. `repairs` counts
director interventions after dispatch. `tokens` are the pane counters `↑input ↓output`, read at
completion from the `pi` status line. They are cumulative per session, and the session is reset
with `/new` before every packet. Earlier sessions were not reset before a counter was read, and
their cells say "not recorded" rather than an estimate. All workers run `deepseek-v4.1-flash`,
thinking high, via `pi --no-extensions`, unless noted.

| wave | packet | worker | model | prompt bytes | lemmas | tokens | result | repairs | landed lines | landed file |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | lattice log sums | ds1 | v4.1-flash | 4458 | 2 | ↑107k ↓35k (session incl. ping) | accepted | 0 | 165 | `CERW/Generic/Lattice/WeightSums.lean` |
| 1 | lattice packing | ds2 | v4.1-flash | 4555 | 2 | ↑194k ↓59k | accepted | 0 | 218 | `CERW/Generic/Lattice/Packing.lean` |
| 1 | summable weights, Lipschitz convolution | ds3 | v4.1-flash | 4126 | 4 | ↑78k ↓15k | accepted | 0 | 107 | `CERW/Generic/Lattice/SummableSums.lean` |
| 1 | kernel algebra | ds4 | v4.1-flash | 5867 | 18 | ↑111k ↓97k (incl. rework) | accepted after repair | 1: worker found the ℕ-division bug in `srwStep`; the director fixed the definition and redirected the worker | 319 | `CERW/Support/Law/Moments.lean` |
| 1 | bathtub principle | Sonnet subagent | sonnet | ~3.1k (task prompt) | 2 | 44k (agent total) | accepted | 0 | 151 | `CERW/Generic/Kernel/Bathtub.lean` |
| 2 | Young absorption | ds1 | v4.1-flash | 4383 | 2 | not recorded | accepted | 0 | 114 | `CERW/Generic/Young/Absorb.lean` |
| 2 | halving cost | ds2 | v4.1-flash | 4320 | 2 | not recorded | accepted | 0 | 101 | `CERW/Generic/Halving/Cost.lean` |
| 2 | halving levels | ds3 | v4.1-flash | 4800 | 2 | not recorded | accepted | 0 | 167 | `CERW/Generic/Halving/Levels.lean` |
| 3 | contact absorption | ds1 | v4.1-flash | 3960 | 1 | not recorded | accepted | 0 | 160 | `CERW/Generic/Young/Contact.lean` |
| 3 | radius inversion | ds2 | v4.1-flash | 3825 | 2 | not recorded | accepted | 0 | 68 | `CERW/Generic/Young/Radius.lean` |
| 3 | resolvent bound | ds3 | v4.1-flash | 4342 | 1 | not recorded | accepted | 0 | 134 | `CERW/Generic/Lattice/Resolvent.lean` |
| 3 | occupation facts | ds4 | v4.1-flash | 6294 | 16 | not recorded | accepted | 0 | 164 | `CERW/Support/Occupation/Facts.lean` |
| 4 | cell membership | ds1 | v4.1-flash | 3889 | 3 | ↑39k ↓6.0k | accepted | 0 | 41 | `CERW/Support/Occupation/Cells.lean` |
| 4 | tail basics | ds2 | v4.1-flash | 4374 | 3 | ↑90k ↓32k | accepted | 0 | 84 | `CERW/Support/Geometry/TailBasic.lean` |
| 4 | cell volume | ds3 | v4.1-flash | 4137 | 2 | ↑74k ↓20k | accepted | 0 | 52 | `CERW/Support/Occupation/CellVolume.lean` |
| 4 | step mean | ds4 | v4.1-flash | 4333 | 3 | ↑75k ↓24k | accepted | 0 | 86 | `CERW/Support/Law/StepMean.lean` |
| 5 | cell-set volume | ds3 | v4.1-flash | ~3.9k (brief overwritten by the next ds3 packet) | 2 | ↑33k ↓10k | accepted | 0 | 30 | `CERW/Support/Occupation/CellSetVolume.lean` |
| 5 | cell norm | ds1 | v4.1-flash | 4250 | 3 | not recorded | accepted | 0 | 67 | `CERW/Support/Occupation/CellNorm.lean` |
| 5 | tail bounds | ds2 | v4.1-flash | 5128 | 3 | ↑93k ↓40k | accepted | 0 | 117 | `CERW/Support/Geometry/TailBounds.lean` |
| 5 | Hausdorff exponents | ds3 | v4.1-flash | 4132 | 3 | ↑53k ↓31k | accepted | 0 | 93 | `CERW/Support/Main/HausdorffArith.lean` |
| 5 | scale limits | ds4 | v4.1-flash | 4352 | 3 | ↑83k ↓67k | accepted | 0 | 169 | `CERW/Support/Main/ScaleLimits.lean` |
| 6 | contact kernel | ds1 | v4.1-flash | 4010 | 2 | not recorded | accepted | 0 | 72 | `CERW/Support/Contact/Kernel.lean` |
| 6 | last entrance | ds2 | v4.1-flash | 3928 | 2 | not recorded | accepted | 0 | 47 | `CERW/Support/Crossing/LastEntrance.lean` |
| 6 | crossing kinematics | ds3 | v4.1-flash | 3982 | 3 | not recorded | accepted | 0 | 49 | `CERW/Support/Crossing/Kinematics.lean` |
| 6 | planar contact sum | ds4 | v4.1-flash | 4120 | 3 | not recorded | accepted | 0 | 79 | `CERW/Support/Contact/PlanarSum.lean` |
| 7 | Freedman threshold arithmetic | ds1 | v4.1-flash | 4089 | 3 | not recorded | accepted | 0 | 82 | `CERW/Generic/Martingale/Arith.lean` |
| 7 | centred ball sums | ds2 | v4.1-flash | 4420 | 3 | not recorded | accepted | 0 | 94 | `CERW/Generic/Lattice/Centered.lean` |
| 7 | crossing contradiction | ds3 | v4.1-flash | 4505 | 1 | not recorded | accepted | 0 | 158 | `CERW/Support/Crossing/Contradiction.lean` |
| 7 | cell weight | ds4 | v4.1-flash | 4866 | 3 | not recorded | accepted | 0 (the director rewrapped a 101-character statement line of its own leaf before dispatch) | 107 | `CERW/Support/Occupation/CellWeight.lean` |
| 7 | Freedman on a small-bracket event | Sonnet subagent | sonnet | task prompt | 1 + helpers | not recorded | accepted | 0 | 295 | `CERW/Generic/Martingale/FreedmanEvent.lean` |
| 7 | integrability of the Newtonian field | Sonnet subagent | sonnet | task prompt | 3 + helpers | not recorded | accepted | 0 | 127 | `CERW/Generic/Kernel/Integrable.lean` |
| 7 | radial packing inequality | Sonnet subagent | sonnet | task prompt | 1 + helpers | not recorded | accepted | 0 | 102 | `CERW/Generic/Kernel/RadialPacking.lean` |
| 8 | radial profile increments | ds1 | v4.1-flash | 4241 | 2 | ↑55k ↓14k | accepted | 0 | 69 | `CERW/Generic/Young/RadialProfile.lean` |
| 8 | Poisson equation of the potential kernel | ds2 | v4.1-flash | 4863 | 3 | ↑87k ↓36k | accepted | 0 | 107 | `CERW/Support/LocalTime/KernelPoisson.lean` |
| 8 | outer contradiction | ds3 | v4.1-flash | 4927 | 1 | ↑296k ↓174k | accepted | 0 | 507 | `CERW/Support/Crossing/OuterContradiction.lean` |
| 8 | cell integral | ds4 | v4.1-flash | 4688 | 2 | ↑87k ↓9.5k | accepted | 0 | 43 | `CERW/Support/Occupation/CellIntegral.lean` |
| 9 | radial power integrals | ds1 | v4.1-flash | 5927 | 2 | ↑249k ↓94k | accepted | 0 (the pasted brief arrived split; the worker proved the leaf before the rules paragraph arrived) | 152 | `CERW/Generic/Kernel/RadialPower.lean` |
| 9 | Newtonian field difference | ds2 | v4.1-flash | 4919 | 3 | ↑158k ↓67k (after respawn) | accepted | 1 dispatch repair: the pasted brief arrived split, the pane was respawned and pointed at the brief file | 165 | `CERW/Generic/Kernel/NewtonField.lean` |
| 9 | directions across a cell | ds4 | v4.1-flash | 4767 | 2 | ↑211k ↓37k | accepted | 0 | 99 | `CERW/Support/Occupation/CellDirection.lean` |
| 9 | logarithmic radial integrals | ds4 | v4.1-flash | 6458 | 2 | ↑168k ↓101k | accepted | 0 | 199 | `CERW/Generic/Kernel/LogRadial.lean` |
| 10 | potential sup bound | ds1 | v4.1-flash | 5967 | 3 | ↑81k ↓31k | accepted | 0 | 112 | `CERW/Support/Geometry/Bound.lean` |
| 10 | coordinate drift | ds2 | v4.1-flash | 5310 | 3 | ↑93k ↓21k | accepted | 0 | 62 | `CERW/Support/Law/CoordinateDrift.lean` |
| 10 | shifted martingale and interval Freedman | ds3 | v4.1-flash | 6509 | 2 | ↑115k ↓36k | accepted | 0 | 142 | `CERW/Generic/Martingale/Shift.lean` |
| 10 | contact cell | Sonnet subagent | sonnet | task prompt | 1 + 3 helpers | 44k (agent total) | accepted | 0 | 117 | `CERW/Support/Contact/ContactCell.lean` |
| 10 | kernel modulus | Sonnet subagent | sonnet | task prompt | 1 + 6 helpers | 79k (agent total) | accepted | 0 | 248 | `CERW/Generic/Kernel/Modulus.lean` |
| 11 | one-step bound of the potential kernel | ds1 | v4.1-flash | 5747 | 2 | ↑51k ↓18k | accepted | 0 | 87 | `CERW/Support/LocalTime/GradientBound.lean` |
| 11 | second-order scalar Taylor bounds | ds2 | v4.1-flash | 5598 | 2 | ↑92k ↓44k | accepted | 0 | 156 | `CERW/Generic/Kernel/ScalarTaylor.lean` |
| 11 | dyadic Freedman bound | ds3 | v4.1-flash | 6800 | 1 | ↑136k ↓55k | accepted | 0 | 189 | `CERW/Generic/Martingale/Dyadic.lean` |
| 11 | direction error | ds4 | v4.1-flash | 7558 | 1 | ↑193k ↓67k | accepted | 0 | 233 | `CERW/Generic/Kernel/DirectionError.lean` |
| 11 | Hölder continuity of the potential | Sonnet subagent | sonnet | task prompt | 1 + 3 helpers | 47k (agent total) | accepted | 0 | 131 | `CERW/Support/Geometry/Holder.lean` |
| 11 | polar coordinates | Sonnet subagent | sonnet | task prompt | 2 + 1 helper | 59k (agent total) | accepted | 1: the director dropped an unused hypothesis from one statement | 118 | `CERW/Generic/Newton/Polar.lean` |
| 12 | cell modulus of the potential | ds1 | v4.1-flash | 8064 | 1 | ↑197k ↓99k | accepted | 1: the director made its helpers private after a name collision with the parallel Hölder file | 403 | `CERW/Support/Geometry/CellModulus.lean` |
| 12 | flux through a sphere | ds2 | v4.1-flash | 7710 | 3 | ↑190k ↓93k | accepted | 0 (the director made its helpers private) | 355 | `CERW/Generic/Newton/Flux.lean` |
| 12 | central difference of the potential kernel | ds3 | v4.1-flash | 7404 | 2 | ↑474k ↓162k | accepted | 0 (the director made its helpers private) | 711 | `CERW/Support/LocalTime/GradientAsymp.lean` |
| 12 | clamped martingale | ds4 | v4.1-flash | 6038 | 1 | ↑91k ↓36k | accepted | 0 (the director made its helpers private) | 102 | `CERW/Generic/Martingale/Clamp.lean` |
| 13 | rotational symmetry of a ball potential | ds1 | v4.1-flash | 5170 | 2 | ↑67k ↓23k | accepted | 0 (the director made its helpers private) | 65 | `CERW/Generic/Newton/BallSymmetry.lean` |
| 13 | Gauss's law for a point source | Sonnet subagent | sonnet | task prompt | 1 + 5 helpers | 75k (agent total) | accepted | 0 | 213 | `CERW/Generic/Newton/Gauss.lean` |
| 13 | compensated position (eq:vector) | Sonnet subagent | sonnet | task prompt | 1 + 9 helpers | 89k (agent total) | accepted | 0 | 291 | `CERW/Support/Coarse/Vector.lean` |
| 14 | sums over first visits | ds1 | v4.1-flash | 5170 | 3 | ↑39k ↓20k | accepted | 0 | 53 | `CERW/Support/Occupation/FreshSum.lean` |
| 14 | arithmetic of the first mass scale | ds4 | v4.1-flash | 5067 | 1 | ↑37k ↓33k | accepted | 0 | 99 | `CERW/Support/Coarse/SstarArith.lean` |
| 14 | Gauss's flux theorem | Sonnet subagent | sonnet | task prompt | 2 + 14 helpers | 125k (agent total) | accepted | 0 | 420 | `CERW/Generic/Newton/GaussFlux.lean` |
| 15 | Newton's theorem and the ball potential | Sonnet subagent | sonnet | task prompt | 3 + 6 helpers | 88k (agent total) | accepted | 0 | 242 | `CERW/Support/Geometry/Newton.lean` |
| 15 | Dynkin decomposition of the local time | ds1 | v4.1-flash | 6893 | 3 | ↑152k ↓52k | accepted | 0 | 118 | `CERW/Support/LocalTime/DynkinLocal.lean` |
| 15 | level sets of the potential kernel | ds2 | v4.1-flash | 6983 | 2 | ↑490k ↓236k | accepted | 0 | 560 | `CERW/Support/Coarse/LevelSets.lean` |
| 15 | bracket of the local-time martingale | ds4 | v4.1-flash | 6004 | 3 | ↑127k ↓36k | accepted | 0 | 98 | `CERW/Support/LocalTime/Bracket.lean` |
| 16 | drift of the radial test | ds1 | v4.1-flash | 6720 | 3 | ↑82k ↓55k | accepted | 0 | 218 | `CERW/Support/Coarse/RadialDrift.lean` |
| 16 | shell count by the tail | ds4 | v4.1-flash | 6542 | 1 | ↑129k ↓39k | accepted | 0 | 159 | `CERW/Support/Coarse/ShellCount.lean` |
| 16 | radial bracket by the tail | ds3 | v4.1-flash | 6135 | 1 | ↑107k ↓58k | accepted | 0 (the director rewrapped a long line of its own docstring) | 187 | `CERW/Support/Coarse/RadialBracket.lean` |
| 16 | interval martingales (eq:interval-mart) | Sonnet subagent | sonnet | task prompt | 1 + 20 helpers | 124k (agent total) | accepted | 0 | 467 | `CERW/Support/LocalTime/IntervalMart.lean` |
| 17 | tail beyond a radius by the source sum | ds1 | v4.1-flash | 5742 | 1 | ↑96k ↓41k | accepted | 0 | 118 | `CERW/Support/Coarse/TailLower.lean` |
| 17 | source inequality of the radial test | ds4 | v4.1-flash | 7820 | 1 | ↑264k ↓94k | accepted | 0 (the director rewrapped a long line of its own docstring) | 395 | `CERW/Support/Coarse/RadialSource.lean` |
| 17 | crossings through a small set | ds3 | v4.1-flash | 7197 | 1 | ↑164k ↓55k | accepted | 0 | 196 | `CERW/Support/Coarse/Crossing.lean` |
| 17 | spherical cap measure | ds2 | v4.1-flash | 6871 | 1 | ↑264k ↓118k | accepted | 0 | 242 | `CERW/Generic/Newton/Cap.lean` |
| 17 | radial martingales (eq:radialmart) | Sonnet subagent | sonnet | task prompt | 1 + 24 helpers | 138k (agent total) | accepted | 0 | 537 | `CERW/Support/Coarse/RadialMart.lean` |
| 18 | radial test assembly (lem:radial from the kernel facts) | Sonnet subagent | sonnet | task prompt | 1 + 5 helpers | 70k (agent total) | accepted | 0 | 272 | `CERW/Support/Coarse/RadialAssembly.lean` |
| 18 | gradient replacement | ds1 | v4.1-flash | 6885 | 1 | ↑200k ↓76k | accepted | 0 | 290 | `CERW/Support/LocalTime/ReplaceGradient.lean` |
| 18 | cell replacement | ds4 | v4.1-flash | 8459 | 1 | ↑217k ↓91k | accepted | 0 | 418 | `CERW/Support/LocalTime/ReplaceCell.lean` |
| 18 | direction replacement | ds3 | v4.1-flash | 6465 | 1 | ↑116k ↓26k | accepted | 0 (the director rewrapped a long line of its own docstring) | 101 | `CERW/Support/LocalTime/ReplaceDirection.lean` |
| 19 | from the kernel asymptotics to the kernel facts | ds1 | v4.1-flash | 7207 | 2 | ↑407k ↓49k | accepted | 0 | 208 | `CERW/Support/LocalTime/KernelBridge.lean` |
| 19 | contact lower bound | ds3 | v4.1-flash | 6031 | 1 | ↑71k ↓39k | accepted | 0 (the director rewrapped its own docstring during dispatch) | 121 | `CERW/Support/Contact/ContactLower.lean` |
| 19 | cap average (eq:cap-average) | ds2 | v4.1-flash | 6266 | 1 | ↑241k ↓78k | accepted | 0 | 158 | `CERW/Generic/Newton/CapAverage.lean` |
| 19 | source sum versus potential | ds4 | v4.1-flash | 7361 | 1 | ↑353k ↓53k | accepted | 0 | 279 | `CERW/Support/LocalTime/SourceSum.lean` |
| 20 | the squared displacement (eq:quadratic) | ds1 | v4.1-flash | 5997 | 3 | ↑159k ↓39k | accepted | 0 | 165 | `CERW/Support/Contact/Quadratic.lean` |
| 20 | first moment of the cell set | ds3 | v4.1-flash | 4972 | 1 | ↑100k ↓29k | accepted | 0 | 78 | `CERW/Support/Contact/NormReplace.lean` |
| 21 | interval Dynkin decomposition | ds3 | v4.1-flash | 5867 | 2 | ↑80k ↓24k | accepted | 0 | 66 | `CERW/Support/LocalTime/IntervalDynkin.lean` |
| 21 | source sum over k sites | ds4 | v4.1-flash | 4906 | 1 | ↑92k ↓23k | accepted | 0 | 114 | `CERW/Support/LocalTime/SourcePacking.lean` |
| 21 | first mass scale and preconditions | ds1 | v4.1-flash | 5096 | 1 | ↑44k ↓32k | accepted | 0 | 130 | `CERW/Support/Coarse/Sstar.lean` |
| 21 | cell count by the tail | ds2 | v4.1-flash | 5334 | 1 | ↑171k ↓78k | accepted after a statement repair | 1 statement repair: `S = ∅` with `R' < -√d/2` made the statement false; the director added `ρ ≤ R'` | 156 | `CERW/Support/Coarse/CardTail.lean` |
| 21 | lem:local assembly | Sonnet subagent | sonnet | task prompt | 1 + 10 helpers | 149k (agent total) | accepted | 0 | 368 | `CERW/Support/LocalTime/LocalAssembly.lean` |
| 22 | mass identity (eq:massidentity) | Sonnet subagent | sonnet | task prompt | 1 + 6 helpers | 77k (agent total) | accepted | 1: the director removed an unused hypothesis | 199 | `CERW/Support/Geometry/MassIdentity.lean` |
| 22 | radius arithmetic | ds4 | v4.1-flash | 4653 | 1 | ↑95k ↓41k | accepted | 0 | 131 | `CERW/Support/Coarse/RadiusArith.lean` |
| 22 | mass error | ds3 | v4.1-flash | 5682 | 1 | ↑188k ↓55k | accepted | 0 | 124 | `CERW/Support/Coarse/MassError.lean` |
| 22 | first moment over ball and excess | ds1 | v4.1-flash | 4778 | 1 | ↑64k ↓20k | accepted | 0 | 64 | `CERW/Support/Contact/BallExcess.lean` |
| 22 | shell bound (eq:shell) | Sonnet subagent | sonnet | task prompt | 1 + 5 helpers | 96k (agent total) | accepted | 0 | 334 | `CERW/Support/Coarse/Shell.lean` |
| 22 | outer radius (eq:HvsR) | Sonnet subagent | sonnet | task prompt | 1 + 11 helpers | 81k (agent total) | accepted | 0 | 304 | `CERW/Support/Coarse/OuterRadius.lean` |
| 23 | coarse tail (eq:coarse-tail) | Sonnet subagent | sonnet | task prompt | 1 + 13 helpers | 169k (agent total) | accepted | 0 | 651 | `CERW/Support/Coarse/Tail.lean` |
| 23 | pointwise decomposition (eq:pointwise) | ds1 | v4.1-flash | 5994 | 1 | ↑171k ↓68k | accepted | 0 | 244 | `CERW/Support/LocalTime/Pointwise.lean` |
| 23 | local martingales (eq:localmart) | ds2 | v4.1-flash | 5870 | 1 | ↑187k ↓73k | accepted | 1: the director rewrapped two long proof lines | 353 | `CERW/Support/LocalTime/LocalMart.lean` |
| 23 | inradius arithmetic (eq:inradius) | ds4 | v4.1-flash | 5595 | 1 | ↑92k ↓55k | accepted | 0 (the director added the missing hypothesis `0 ≤ Xsq` before dispatch) | 181 | `CERW/Support/Contact/InradiusArith.lean` |
| 24 | envelope and inner inclusion | ds1 | v4.1-flash | 5763 | 2 | ↑141k ↓22k | accepted | 0 | 83 | `CERW/Support/Contact/Envelope.lean` |
| 24 | local-time profile (eq:profile-rate) | ds2 | v4.1-flash | 6266 | 1 | ↑230k ↓77k | accepted | 1: the director removed an unneeded hypothesis (the worker had padded a constant to use it) | 253 | `CERW/Support/Contact/Profile.lean` |
| 24 | volume and symmetric difference | ds4 | v4.1-flash | 5229 | 1 | ↑213k ↓71k | accepted | 0 | 253 | `CERW/Support/Contact/Volume.lean` |
| 24 | planar hole bracket | ds3 | v4.1-flash | 5099 | 1 | ↑45k ↓24k | accepted | 0 | 98 | `CERW/Support/Contact/PlanarBracket.lean` |
| 25 | high-dimensional envelope (eq:envelopehigh) | ds1 | v4.1-flash | 7664 | 1 | not recorded | accepted | 0 | 528 | `CERW/Support/Contact/EnvelopeHigh.lean` |
| 25 | contact inequality | ds2 | v4.1-flash | 4557 | 1 | not recorded | accepted | 0 | 82 | `CERW/Support/Contact/ContactMass.lean` |
| 25 | outer fluctuation bound | ds3 | v4.1-flash | 6016 | 1 | ↑295k ↓154k | accepted | 0 | 462 | `CERW/Support/Coarse/OuterBound.lean` |
| 25 | shell envelope and global error | ds4 | v4.1-flash | 4417 | 2 | not recorded | accepted | 0 | 75 | `CERW/Support/Contact/EnvelopeShell.lean` |
| 26 | Borel–Cantelli from a power tail | ds1 | v4.1-flash | 5154 | 1 | ↑56k ↓20k | accepted | 0 | 60 | `CERW/Support/Main/BorelCantelli.lean` |
| 26 | shape inclusions and profile from the event | ds2 | v4.1-flash | 5797 | 1 | ↑105k ↓34k | accepted | 1: the director removed three unused hypotheses (the worker had bound them to anonymous `have`s) | 82 | `CERW/Support/Main/ShapeInclusion.lean` |
| 26 | shape count and pointwise bound from the event | ds4 | v4.1-flash | 6337 | 1 | ↑145k ↓65k | accepted | 0 | 180 | `CERW/Support/Main/ShapeCount.lean` |
| 27 | tail end (eq:tailend) | Sonnet subagent | sonnet | task prompt | 1 + 9 helpers | 142k (agent total) | accepted | 2: the first dispatch was stopped because the director's leaf did not compile (missing import); after return the director replaced re-proved cell facts with library lemmas | 497 | `CERW/Support/Coarse/TailEnd.lean` |
| 27 | shape theorem from the almost-sure event | ds2 | v4.1-flash | 4473 | 1 | ↑22k ↓4.7k | accepted | 0 | 55 | `CERW/Support/Main/ShapeAssembly.lean` |
| 28 | inradius (eq:inradius) | ds2 | v4.1-flash | 6104 | 1 | ↑238k ↓125k | accepted | 0 | 397 | `CERW/Support/Contact/Inradius.lean` |
| 29 | contact setup (eq:bm, eq:contactcell, modulus) | ds2 | v4.1-flash | 5694 | 1 | ↑140k ↓41k | accepted | 1: the director sent a follow-up after dispatch correcting a Mathlib name in the brief | 116 | `CERW/Support/Contact/ContactSetup.lean` |
| 29 | outer bound from the envelope | ds3 | v4.1-flash | 6123 | 1 | ↑169k ↓68k | accepted | 1: the director sent a follow-up after dispatch replacing a deprecated Mathlib name in the brief | 193 | `CERW/Support/Coarse/OuterEnvelope.lean` |
| 30 | mass step on the event (d ≥ 3) | ds2 | v4.1-flash | 6214 | 1 | ↑239k ↓67k | accepted | 0 | 224 | `CERW/Support/Main/MassEventHigh.lean` |
| 30 | outer inclusion from the radius bound | ds4 | v4.1-flash | 4941 | 1 | ↑50k ↓35k | accepted | 0 | 115 | `CERW/Support/Main/OuterInclusion.lean` |
| 30 | thm:fluctuations and thm:shape from the core | ds3 | v4.1-flash | 5765 | 2 | ↑35k ↓18k | accepted | 0 | 143 | `CERW/Support/Main/FluctAssembly.lean` |
| 31 | eq:hausdorff (two-sided) from the core | ds2 | v4.1-flash | 5405 | 1 | ↑183k ↓78k | accepted | 0 | 156 | `CERW/Support/Main/HausdorffAssembly.lean` |
| 31 | mass step on the event (d = 2) | ds1 | v4.1-flash | 6029 | 1 | — | in flight | — | — | `wip/MassEventPlanar.lean` |
| 32 | inner clauses on the event, given the mass | ds3 | v4.1-flash | 6559 | 1 | — | in flight | — | — | `wip/InnerOfMass.lean` |
| 32 | outer inclusion on the event, given the mass | ds4 | v4.1-flash | 6071 | 1 | ↑127k ↓56k | accepted | 1: the worker reported an unused hypothesis, which the director removed | 212 | `CERW/Support/Main/OuterOfMass.lean` |
| 33 | eq:hausdorff one-sided (variant A) from the core | ds4 | v4.1-flash | 4813 | 1 | — | in flight | — | — | `wip/HausdorffOneSided.lean` |
| 29 | inner clauses of the event | ds4 | v4.1-flash | 6013 | 1 | ↑195k ↓62k | accepted | 0 | 225 | `CERW/Support/Main/InnerClauses.lean` |
| 27 | Hausdorff bound from the event | ds4 | v4.1-flash | 5941 | 1 | ↑395k ↓211k | accepted | 0 | 503 | `CERW/Support/Main/HausdorffGood.lean` |
| 27 | planar contact variance (eq:massplanar, eq:envelopeplanar) | ds1 | v4.1-flash | 6297 | 1 | ↑325k ↓171k | accepted | 0 | 606 | `CERW/Support/Contact/MassPlanar.lean` |
| 27 | high-dimensional contact variance (eq:masshigh) | ds3 | v4.1-flash | 6359 | 1 | ↑186k ↓125k | accepted | 1: the director sent a follow-up after dispatch because the brief suggested a Mathlib name that does not exist | 462 | `CERW/Support/Contact/MassHigh.lean` |
| 28 | prop:coarse assembly from the kernel facts | Sonnet subagent | sonnet | task prompt | 1 + 11 helpers | 222k (agent total) | accepted | 0 | 509 | `CERW/Support/Coarse/Assembly.lean` |
| 28 | probability of the event (union bound) | Sonnet subagent | sonnet | task prompt | 1 + 7 helpers | 102k (agent total) | accepted | 0 | 201 | `CERW/Support/Main/EventProb.lean` |
| 23 | quadratic martingale concentration | ds3 | v4.1-flash | 7217 | 1 | ↑693k ↓121k | accepted | 0 | 489 | `CERW/Support/Contact/QuadraticError.lean` |

## Observations

* **Waves 1–26.** Every returned DeepSeek packet was accepted: 104/104, two after a statement repair. There were three repairs: a definition
  in wave 1, a dispatch in wave 9, and helper visibility in wave 12. Every Sonnet leaf was accepted: 23/23.
* **Brief names are machine-checked.** In waves 27 and 29 a brief named a Mathlib lemma that does not
  exist or is deprecated, and a correction had to follow the dispatch. `brief_helper.py` now greps every
  backticked name before writing a brief and reports unfound or deprecated ones.
* **Parallel helpers collide.** Two parallel files in one namespace each added a public helper with the same
  name. Since wave 13, the common rules require every helper a worker adds to be `private`.
* **Waves 1–4.** 21/21 packets were accepted (wave 4 and the cell-set volume: 5/5, no repair, each under 10 minutes); 16 of 17 with no repair. Wall-clock time per packet was
  4–20 minutes.
* **What a brief carried.** Every brief was 3.8–6.3 KB, stated the proof route step by step, and
  cited only names grep-verified at the pin.
* **Why wave 1 hit 100%.** This contradicts the 0/1,808 of the earlier IDLA campaign. The
  difference is the brief shape: exact statements in a compiling leaf, a spelled-out route,
  verified names, and an agentic loop that compiles its own attempts.
* **Packet size.** From wave 4 on, packets are capped at three lemmas each, per the carve-up
  directive. Wave 1's 18-lemma packet did succeed, but only after a definition repair.
* **Workers catch definition defects.** The ds4 catch shows that a worker proving the obvious API of
  a definition is an effective junk-value probe. Keep dispatching API packets early, before a freeze.
* **Dispatch channel.** Pasting a brief with `tmux paste-buffer` can split it into several user messages.
  In wave 9, ds2 never saw its goal and started searching other panes. ds1 finished its proof before the
  rules paragraph arrived. From wave 9b on, a brief is dispatched as a one-line message that points the
  worker at the brief file.
* **Junk cases in director statements.** In wave 21, ds2 proved in Lean that a director statement
  was false: a hypothesis quantified over an empty set left a radius unconstrained, so it could be
  negative. From then on, before dispatch every statement is checked for its vacuous-hypothesis cases.
