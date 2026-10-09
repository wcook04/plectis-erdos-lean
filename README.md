# Carry and divisor-channel criteria for the factorial-minus-one reciprocal series

This release snapshot contains the complete local proof closure for the six
declarations in [the E68_05 Comparator configuration](PalomarCorpus/E68_05/comparator.json).
For the sum of reciprocals of n! - 1 over n at least two, the selected statements
characterize irrationality by cofinal failures of exact factorial-carry or
divisibility conditions. A companion-orbit statement characterizes rationality
by eventual congruences. The selection also gives divisor-channel coordinates,
a finite gcd moment certificate with its stated prime-interval hypotheses,
and a sufficient complementary-tail criterion under its explicit cofinal
certificate hypothesis. These structural criteria do not prove irrationality
of the series or certify the paper's large computed denominator exclusions.

All substantive proof bodies are present locally. The mathematical source comes
from `wcook04/plectis-erdos-lean` commit `6bc4913c4ca42ac48829ad2d89985f8516361cb5`. The only mathematical-source
changes introduce Lean's module visibility syntax; all six theorem headers
and every proof body are unchanged. Statement is regenerated from Challenge by
its existing source owner. The canonical full corpus remains the authority for
other entries. Historical registered receiving sources remain separate.

Build with the pinned Lean toolchain and Mathlib dependency:

```sh
lake exe cache get
lake build Solutions
```

Challenge contains six deliberate theorem placeholders; the Solution closure
contains no placeholders. Compilation, axiom audit, Comparator, independent-kernel,
rendering and registry outcomes are separate commit-specific evidence. This source
snapshot does not claim Palomar acceptance, human review or a solution of the
unrestricted Erdős problem. It performs no new intake or registration.

The manifest binds the frozen authority and every included payload digest. It does
not include itself in its content digest.
