# Erdős 249 proof in the receiving Formal Conjectures environment

`FC249Repair` assembles the exact `Erdos249.erdos_249.variants.rational_dyadic_observable`
statement carried by Formal Conjectures #6579 at `e6bf75a53ef0655241873e5f12427fb6b4695de5`.
The bridge derives the statement from the original dyadic-observable classification.
This receiving-environment port remains unverified until the native workflow passes.

This package uses receiving Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
The original Lean 4.29.1 package remains at `verification/FC249RationalObservable`.
`source-binding.json` records the old proof pin and receiving target.

Build with `lake build FC249Repair` from this directory. The bridge includes
`#print axioms` for the final declaration. Compilation and an axiom audit are
separate from receiving identity certification.

Receiving identity requires exporting the actual immutable Formal Conjectures
module in an independent workspace before compiling this proof, then running
Comparator on both exported declarations and their definitions. A Challenge
copied into this package would not establish that boundary.
