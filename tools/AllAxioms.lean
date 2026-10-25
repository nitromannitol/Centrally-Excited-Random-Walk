module

public import CERW

@[expose] public section

/-!
# Axiom closures of all production declarations

Every declaration in a module of the library `CERW`, private and auxiliary declarations
included, depends on no axiom beyond `propext`, `Classical.choice` and `Quot.sound`, and no
module of the library declares an axiom. A use of `sorry` would appear here as `sorryAx`.
Every file under `CERW/` must be a module imported by `CERW`, so that none escapes the scan.
Run from the repository root with `lake env lean tools/AllAxioms.lean` after `lake build`.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let files ← System.FilePath.walkDir "CERW"
  let sources := files.filter (·.extension == some "lean")
  if sources.size < 100 then
    throwError m!"only {sources.size} source files found under CERW/"
  for f in sources do
    let m := (f.withExtension "").components.foldl Name.str Name.anonymous
    unless mods.contains m do
      logError m!"{f} is not imported by CERW, so its declarations escape this check"
  let decls := env.constants.fold (init := #[]) fun acc name ci =>
    match env.getModuleIdxFor? name with
    | some idx => if (mods[idx.toNat]!).getRoot == `CERW then acc.push (name, ci) else acc
    | none => acc
  if decls.size < 1000 then
    throwError m!"only {decls.size} declarations found in CERW modules"
  let mut bad : Nat := 0
  for (name, ci) in decls do
    if ci matches .axiomInfo _ then
      bad := bad + 1
      logError m!"{name} is an axiom"
    let extra := (← collectAxioms name).filter fun a =>
      a != ``propext && a != ``Classical.choice && a != ``Quot.sound
    unless extra.isEmpty do
      bad := bad + 1
      logError m!"{name} depends on {extra}"
  logInfo m!"{sources.size} source files and {decls.size} declarations of CERW modules checked, {bad} violations"
