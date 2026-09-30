"""The checker harness, and the meta-check that makes a green meaningful.

BEST_PRACTICES.md §3 new-gate 5: *every checker asserts it processed at least
one node and that its paper regex matched the `source_pin.file` stem.*

Nine checkers across four repos — two of them released — exited 0 having
processed nothing, because a vendored copy still carried another repo's paper
name in a regex. A checker that reports `OK (0 statements)` is not a passing
checker; it is a checker that did not run. `Result.done()` makes that a
failure by construction, so a future copy-paste cannot reintroduce the class.
"""

from __future__ import annotations

import sys
import traceback
from dataclasses import dataclass, field


@dataclass
class Result:
    """What one checker did. `processed` is the meta-check's subject."""

    name: str
    processed: int = 0
    total: int = 0
    failures: list = field(default_factory=list)
    notes: list = field(default_factory=list)
    # A checker with genuinely nothing to do (a repo with no External nodes,
    # say) sets this with a reason, and the meta-check is waived for it.
    vacuous_ok: str | None = None

    def fail(self, msg: str) -> None:
        self.failures.append(msg)

    def note(self, msg: str) -> None:
        self.notes.append(msg)

    def count(self, n: int = 1) -> None:
        self.processed += n

    def done(self) -> int:
        """Print the verdict and return the exit code.

        Exit 2 is reserved for the meta-check so a vacuous pass is
        distinguishable from an ordinary failure in CI logs.
        """
        for f in self.failures:
            print(f"  FAIL  {f}")
        for n in self.notes:
            print(f"  note  {n}")

        if self.processed == 0 and self.vacuous_ok is None:
            print(
                f"{self.name}: META-CHECK FAILED — processed 0 items"
                + (f" of {self.total} available" if self.total else "")
                + ". A checker that inspects nothing does not pass. This is"
                " almost always a paper-name or path constant that does not"
                " match this repo; the package derives those from"
                " ledger/manifest.yaml, so check source_pin.file."
            )
            return 2
        if self.processed == 0:
            print(f"{self.name}: OK (nothing to do — {self.vacuous_ok})")
            return 0
        if self.failures:
            print(f"{self.name}: FAILED ({len(self.failures)} problem(s); "
                  f"{self.processed} item(s) inspected)")
            return 1
        tail = f"/{self.total}" if self.total and self.total != self.processed else ""
        print(f"{self.name}: OK ({self.processed}{tail} item(s) inspected)")
        return 0


def run(name: str, fn, *args, **kwargs) -> int:
    """Run a checker body, converting an exception into a hard failure.

    Fail closed: a checker that crashes has not passed.
    """
    res = Result(name=name)
    try:
        fn(res, *args, **kwargs)
    except Exception as exc:  # noqa: BLE001 — fail closed on anything
        print(f"  FAIL  {type(exc).__name__}: {exc}")
        traceback.print_exc(file=sys.stderr)
        print(f"{name}: FAILED (checker raised; treated as a failure)")
        return 1
    return res.done()
