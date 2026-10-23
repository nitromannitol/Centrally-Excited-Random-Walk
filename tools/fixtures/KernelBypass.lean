import Lean

/-!
# A declaration that skipped the kernel

This module is not part of the library. It installs the theorem `KernelBypass.falseProof : False`
with kernel checking disabled, and `tools/replay_kernel.sh` checks that the kernel replay
rejects it.
-/

open Lean in
set_option debug.skipKernelTC true in
run_cmd Lean.Elab.Command.liftCoreM <| addDecl (.thmDecl {
  name := `KernelBypass.falseProof
  levelParams := []
  type := mkConst ``False
  value := mkConst ``True.intro })
