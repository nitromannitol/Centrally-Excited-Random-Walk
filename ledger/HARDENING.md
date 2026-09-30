# Heartbeat margin

Every library file compiles at Lean's default budget of 200000 heartbeats. This file tracks the
files where some declaration needs more than half of that, 100000. Those files are fragile against
changes in Mathlib or the toolchain.

Each file becomes one packet. The packet makes the file compile at `-DmaxHeartbeats=100000`
without changing any public declaration. The measurement compiles every file under `CERW/`
except the aggregators: 154 of 168 pass, and the 14 below do not.

| file | status |
|---|---|
| `CERW/Support/Contact/MassPlanar.lean` | done |
| `CERW/Support/Contact/EnvelopeHigh.lean` | in flight |
| `CERW/Support/Contact/MassHigh.lean` | done |
| `CERW/Support/Contact/InradiusArith.lean` | done |
| `CERW/Generic/Newton/Cap.lean` | in flight |
| `CERW/Generic/Young/Absorb.lean` | in flight |
| `CERW/Support/Coarse/OuterBound.lean` | in flight |
| `CERW/Support/Coarse/OuterRadius.lean` | queued |
| `CERW/Support/Coarse/Shell.lean` | queued |
| `CERW/Support/Coarse/Tail.lean` | queued |
| `CERW/Support/Contact/QuadraticError.lean` | queued |
| `CERW/Support/LocalTime/GradientAsymp.lean` | queued |
| `CERW/Support/LocalTime/LocalAssembly.lean` | queued |
| `CERW/Support/Main/MassEventPlanar.lean` | queued |
