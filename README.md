# An explicit rational-base irrationality region for Zudilin's Lambert series

This release snapshot contains the complete local proof closure for the twenty-five
declarations in [the E1049_01 Comparator configuration](PalomarCorpus/E1049_01/comparator.json).
For coprime natural integers a > b > 0 satisfying b^mu < a, the selected threshold
theorems prove irrationality of the Lambert value F(a/b). The exponent mu is the
exact reciprocal of the contour constant defined in Challenge. The selection
includes irrationality at 31/4 and every positive integer power, associated
irrationality-exponent bounds, and checked supporting constants and enclosures.
The region excludes 3/2. The later sharp fixed-base asymptotic and all-rank Hankel
results are outside this configuration. The unrestricted rational-base problem
remains open.

All substantive proof bodies are present locally. The mathematical source comes
from `wcook04/plectis-erdos-lean` commit `6bc4913c4ca42ac48829ad2d89985f8516361cb5`. The only mathematical-source
changes introduce Lean's module visibility syntax; all twenty-five theorem headers
and every proof body are unchanged. Statement is regenerated from Challenge by
its existing source owner. The canonical full corpus remains the authority for
other entries.

Build with the pinned Lean toolchain and Mathlib dependency:

```sh
lake exe cache get
lake build Solutions
```

Challenge contains twenty-five deliberate theorem placeholders; the Solution closure
contains no placeholders. Compilation, axiom audit, Comparator, independent-kernel,
rendering and registry outcomes are separate commit-specific evidence. This source
snapshot does not claim Palomar acceptance, human review or a solution of the
unrestricted Erdős problem.

The manifest binds the frozen authority and every included payload digest. It does
not include itself in its content digest.
