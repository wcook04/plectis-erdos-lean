# Cubic-rate irrationality for reciprocal sums

This release snapshot contains the complete local proof closure for the thirteen
declarations in [the E243_01 Comparator configuration](PalomarCorpus/E243_01/comparator.json).
Its principal theorem concerns positive strictly increasing zero-indexed integer
sequences with the stated cubic-rate limit and a HasSum witness for the reciprocal
series. The selected supporting statements cover integer-tail reduction, primitive
gcd structure, square specialisation, scale twelve, forbidden words modulo seven
and regular-rate extraction. Erdős problem #243 remains open.

All substantive proof bodies are present locally. The mathematical source comes
from `wcook04/plectis-erdos-lean` commit `6bc4913c4ca42ac48829ad2d89985f8516361cb5`. The only mathematical-source
changes introduce Lean's module visibility syntax; all thirteen theorem headers
and every proof body are unchanged. Statement is regenerated from Challenge by
its existing source owner. The canonical full corpus remains the authority for
other entries.

Build with the pinned Lean toolchain and Mathlib dependency:

```sh
lake exe cache get
lake build Solutions
```

Challenge contains thirteen deliberate theorem placeholders; the Solution closure
contains no placeholders. Compilation, axiom audit, Comparator, independent-kernel,
rendering and registry outcomes are separate commit-specific evidence. This source
snapshot does not claim Palomar acceptance, human review or a solution of the
unrestricted Erdős problem.

The manifest binds the frozen authority and every included payload digest. It does
not include itself in its content digest.
