Files in `extras/` are not part of the `ErdosLean` build. Each one builds against a specific
formal-conjectures commit named in its header.

- `Erdos177OptimalGrowth.lean`: builds against formal-conjectures PR #6756 at commit 0b725ba8
  (import `FormalConjectures.ErdosProblems.«177»`). It proves that `IsOptimalGrowth H` holds for no `H`.
