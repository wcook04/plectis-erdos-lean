# All-base bases and integral relations for the totient kernel

This release snapshot contains the complete local proof closure for the five declarations in
[the E249_29 Comparator configuration](PalomarCorpus/E249_29/comparator.json).
It proves exact finite-level bases and integral relation normal forms for the totient kernel.
It also includes a full dyadic basis and an affine independence theorem, with the prior work
of Greg Martin, Michael Coons and others credited in the entry metadata.
Erdős problem #249's irrationality question remains open.

All substantive Lean proof bodies are present in this snapshot. The source comes from the
full corpus at commit `6bc4913c4ca42ac48829ad2d89985f8516361cb5` in `wcook04/plectis-erdos-lean`.
The mathematical-source changes introduce Lean's module visibility syntax and replace
only the retainedChannel and fullRetainedChannel index-bound proofs with explicit Nat
arithmetic terms. Channel levels, residues and five selected theorem statements are
unchanged. Statement is regenerated from Challenge. A small exported Init-only pair
passes the pinned structural Comparator algorithm; full-source official verification
remains commit-specific and separate.
The canonical full corpus remains the authority for the other entries.

Build with the pinned Lean toolchain and Mathlib dependency:

```sh
lake exe cache get
lake build Solutions
```

The Challenge contains five deliberate theorem placeholders. The Solution closure contains
no placeholders. Compilation, axiom audit, Comparator, independent-kernel and registry outcomes
are separate, commit-specific evidence; this README does not claim a Palomar acceptance.

The snapshot manifest binds the frozen authority, every included source file and its digest.
The manifest does not include itself in its content digest.
