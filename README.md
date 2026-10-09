# Uniform sparse rationalisation of dyadic series

This release snapshot contains the complete local proof closure for the eleven
declarations in [the E251_01 Comparator configuration](PalomarCorpus/E251_01/comparator.json).
The selected results concern sparse congruence-preserving corrections to dyadic
series, uniform control of finite block distributions, exact finite prime-to-gap
summation identities with their endpoint, and dyadic-tail rationality criteria.
They do not assert that corrected positions are prime or that the original prime
series is irrational. Erdős problem #251 remains open.

All substantive proof bodies are present locally. The mathematical source comes
from `wcook04/plectis-erdos-lean` commit `6bc4913c4ca42ac48829ad2d89985f8516361cb5`. The only mathematical-source
changes introduce Lean's module visibility syntax; all eleven theorem headers
and every proof body are unchanged. Statement is regenerated from Challenge by
its existing source owner. The canonical full corpus remains the authority for
other entries.

Build with the pinned Lean toolchain and Mathlib dependency:

```sh
lake exe cache get
lake build Solutions
```

Challenge contains eleven deliberate theorem placeholders; the Solution closure
contains no placeholders. Compilation, axiom audit, Comparator, independent-kernel,
rendering and registry outcomes are separate commit-specific evidence. This source
snapshot does not claim Palomar acceptance, human review or a solution of the
unrestricted Erdős problem.

The manifest binds the frozen authority and every included payload digest. It does
not include itself in its content digest.
