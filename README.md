# Infinite rank of the three-prime running-LCM kernel

This release snapshot contains the complete local proof closure for the thirteen
declarations in [the E269_02 Comparator configuration](PalomarCorpus/E269_02/comparator.json).
For pairwise distinct primes, the selected rational running-LCM kernel has nonzero
square minors of every order and no finite rational separated representation.
The same injective row and column maps work for every fixed third exponent.
Supporting statements give the exact threshold-column rank formula, a two-by-two
example at 2,3,5, two-prime separation and the four-base dyadic recurrence for the
actual 2,3,5 sum. The uniform approximation result concerns the rescaled real carry
matrix; it is not a lower bound for the original summable kernel. Infinite kernel
rank does not prove irrationality of the three-prime running-LCM series. The
stronger E269_08 modular-minor selection is outside this configuration.

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
unrestricted Erdős problem. Existing consented receiving requests remain separate.

The manifest binds the frozen authority and every included payload digest. It does
not include itself in its content digest.
