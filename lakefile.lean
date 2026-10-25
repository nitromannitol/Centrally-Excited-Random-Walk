import Lake

open Lake DSL

package «centrally-excited-random-walk» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "7e229549ff3b35ff8e7bb30bb96d4a193a292864"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

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
