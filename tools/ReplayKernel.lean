import Lean.Replay

/-!
# Kernel replay of the library

`lake env lean --run tools/ReplayKernel.lean CERW LatticeProb` collects the modules in the import
closure of the module `CERW` whose names begin with `CERW` or `LatticeProb`, imports the other
modules they import (Mathlib and the core library), and replays every declaration of the
collected modules, private ones included, through the Lean kernel in that environment.  A
declaration that was added with kernel checking disabled, or whose compiled form differs from
what the kernel accepts, makes the replay fail.

The module loading follows `leanchecker` of the Lean toolchain (`src/lean/LeanChecker.lean`),
which instead checks each module, and every module whose name it prefixes, in a separate
environment at the same time.
-/

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let roots := args.map String.toName
  let some start := roots.head? | throw <| IO.userError "no module given"
  let inRoots (m : Name) : Bool := roots.contains m.getRoot
  let mut queue := #[start]
  let mut collected : NameSet := NameSet.empty.insert start
  let mut imports : Array Import := #[]
  let mut seen : NameSet := {}
  let mut consts : Std.HashMap Name ConstantInfo := {}
  let mut counts : Std.HashMap Name Nat := {}
  while !queue.isEmpty do
    let m := queue.back!
    queue := queue.pop
    counts := counts.insert m.getRoot (counts.getD m.getRoot 0 + 1)
    let mFile ← findOLean m
    unless (← mFile.pathExists) do
      throw <| IO.userError s!"object file '{mFile}' of module {m} does not exist"
    let mut fnames := #[mFile]
    let sFile := OLeanLevel.server.adjustFileName mFile
    if (← sFile.pathExists) then
      fnames := fnames.push sFile
      let pFile := OLeanLevel.private.adjustFileName mFile
      if (← pFile.pathExists) then
        fnames := fnames.push pFile
    let parts ← readModuleDataParts fnames
    if h : parts.size = 0 then throw <| IO.userError s!"failed to read module data of {m}" else
    for i in parts[0].1.imports do
      if inRoots i.module then
        unless collected.contains i.module do
          collected := collected.insert i.module
          queue := queue.push i.module
      else if !seen.contains i.module then
        imports := imports.push i
        seen := seen.insert i.module
    -- The last ("most private") part subsumes the others.
    for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
      consts := consts.insert name ci
  let (_, s) ← importModulesCore imports |>.run
  let env ← finalizeImport s imports {} 0 false false (isModule := true)
  discard <| env.replay consts
  for r in roots.eraseDups do
    IO.println s!"{counts.getD r 0} modules of {r}"
  IO.println s!"{consts.size} declarations replayed in the kernel"
  return 0
