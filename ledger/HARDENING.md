# Heartbeat margin

Every library file compiles at Lean's default budget of 200000 heartbeats. This file tracks the
files where some declaration needs more than half of that, 100000. Those files are fragile against
changes in Mathlib or the toolchain.

Each file becomes one packet. The packet makes the file compile at `-DmaxHeartbeats=100000`
without changing any public declaration. The measurement compiles every file under `CERW/`
except the aggregators. The first measurement found 154 of 168 passing, and the 14 below did not.

**Final measurement: all 168 files compile at `-DmaxHeartbeats=100000`.** Every packet kept every
public declaration and its docstring byte-identical and changed only proof bodies and private
helpers. After each landing, `check_axioms` passed on all eight frozen nodes.

| file | status |
|---|---|
| `CERW/Support/Contact/MassPlanar.lean` | done |
| `CERW/Support/Contact/EnvelopeHigh.lean` | done |
| `CERW/Support/Contact/MassHigh.lean` | done |
| `CERW/Support/Contact/InradiusArith.lean` | done |
| `CERW/Generic/Newton/Cap.lean` | done |
| `CERW/Generic/Young/Absorb.lean` | done |
| `CERW/Support/Coarse/OuterBound.lean` | done |
| `CERW/Support/Coarse/OuterRadius.lean` | done |
| `CERW/Support/Coarse/Shell.lean` | done |
| `CERW/Support/Coarse/Tail.lean` | done |
| `CERW/Support/Contact/QuadraticError.lean` | done |
| `CERW/Support/LocalTime/GradientAsymp.lean` | done |
| `CERW/Support/LocalTime/LocalAssembly.lean` | done |
| `CERW/Support/Main/MassEventPlanar.lean` | done |
