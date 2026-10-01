import Lake

open Lake DSL

package «centrally-excited-random-walk» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "4bdbaa4b05ca02163aacea948cfc385be6bb61b6"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

/-- The comparator audit surface (`Audit/*/Challenge.lean`, `Audit/*/Solution.lean`).
Deliberately **not** a default target: it builds only on demand (`lake build Audit`), so the
ordinary project build is unchanged. -/
lean_lib «CERWAudit» where
  globs := #[.submodules `CERWAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

@[default_target]
lean_lib «CERW» where
  globs := #[.andSubmodules `CERW]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]
