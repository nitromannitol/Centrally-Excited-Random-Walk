import CERW

/-!
# Elaborated types of the frozen statements

The statement hashes in `ledger/oct13.yaml` pin the text of each frozen block. This check pins
what each export registered there, and each theorem of `CERW/MainTheorems.lean`, means after
elaboration. For each such declaration it writes an unambiguous serialization of its type, with
escaped names, binder kinds, de Bruijn indices and universe levels, followed by the type and
value of every definition and the type of every other declaration of the libraries `CERW` and
`LatticeProb` that the type reaches. Mathlib is pinned by `lake-manifest.json`. The files go to
`.lake/frozen-types/`, and `tools/check_frozen_types.py` compares their SHA-256 digests with
`tools/frozen-types.sha256`. Run from the repository root with
`lake env lean tools/FrozenTypes.lean` after `lake build`.
-/

open Lean

namespace CERW.FrozenTypes

/-- Append an unambiguous serialization of `e`. -/
partial def ser (e : Expr) : StateM String Unit := do
  let out (s : String) : StateM String Unit := modify (· ++ s)
  let bi : BinderInfo → String
    | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"
  match e with
  | .bvar i => out s!"#{i}"
  | .fvar f => out s!"(fvar {f.name.toString})"
  | .mvar m => out s!"(mvar {m.name.toString})"
  | .sort u => out s!"(sort {u})"
  | .const n us => out s!"(const {n.toString (escape := true)} {us})"
  | .app f a => do out "(app "; ser f; out " "; ser a; out ")"
  | .lam _ t b k => do out s!"(lam {bi k} "; ser t; out " "; ser b; out ")"
  | .forallE _ t b k => do out s!"(pi {bi k} "; ser t; out " "; ser b; out ")"
  | .letE _ t v b nd => do out s!"(let {nd} "; ser t; out " "; ser v; out " "; ser b; out ")"
  | .lit (.natVal n) => out s!"(nat {n})"
  | .lit (.strVal s) => out s!"(str {repr s})"
  | .mdata _ e => ser e
  | .proj s i e => do out s!"(proj {s.toString (escape := true)} {i} "; ser e; out ")"

/-- The serialization of a declaration and of the project declarations its type reaches. -/
def closure (env : Environment) (root : Name) : Except String String := do
  let some ci := env.find? root | throw s!"missing {root}"
  let project (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx => let r := (env.header.moduleNames[idx.toNat]!).getRoot
                  r == `CERW || r == `LatticeProb
    | none => false
  let mut seen : NameSet := {}
  let mut todo : Array Name := ci.type.getUsedConstants
  let mut parts : Array (String × String) := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n || !project n then continue
    seen := seen.insert n
    let some c := env.find? n | throw s!"missing {n}"
    let exprs : List Expr := match c with
      | .defnInfo d => [d.type, d.value]
      | .opaqueInfo d => [d.type, d.value]
      | .inductInfo d => d.type :: (d.ctors.filterMap fun k => (env.find? k).map (·.type))
      | _ => [c.type]
    let s := (exprs.forM ser).run "" |>.2
    parts := parts.push (n.toString (escape := true), s!"{c.levelParams} {s}")
    for e in exprs do
      todo := todo ++ e.getUsedConstants
  let head := (ser ci.type).run "" |>.2
  let body := (parts.qsort (fun a b => a.1 < b.1)).foldl
    (fun acc p => acc ++ s!"\n{p.1} {p.2}") ""
  return s!"{root.toString (escape := true)} {ci.levelParams} {head}{body}\n"

end CERW.FrozenTypes

open Lean CERW.FrozenTypes in
run_cmd do
  let env ← getEnv
  let ledger ← IO.FS.lines "ledger/oct13.yaml"
  let exports := ledger.filterMap fun l =>
    (l.trimAsciiStart.toString.dropPrefix? "export: ").map (·.toString.trimAscii.toString.toName)
  let main := (← IO.FS.lines "CERW/MainTheorems.lean").filterMap fun l =>
    (l.dropPrefix? "theorem ").map fun r =>
      (`CERW.MainTheorems ++ ((r.toString.splitOn " ").head!.toName))
  let roots := exports ++ main
  if exports.size != 29 || main.size != 7 then
    throwError m!"expected 29 exports and 7 main theorems, found {exports.size} and {main.size}"
  IO.FS.createDirAll ".lake/frozen-types"
  for r in roots do
    match closure env r with
    | .ok s => IO.FS.writeFile s!".lake/frozen-types/{r}.txt" s
    | .error msg => throwError msg
  logInfo m!"{roots.size} serializations written to .lake/frozen-types"
