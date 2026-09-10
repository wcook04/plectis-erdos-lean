# Erdős #249: totient rigidity theorems

One exact prime law plus an `o(n)` error forces `g = φ`. The exact even
doubling laws plus eventual congruence modulo every integer also force
`g = φ`. The compared theorems are
`one_prime_law_and_little_o_forces_totient`, `totient_prime_mul_of_dvd`,
`totient_prime_mul_of_not_dvd`, `even_law_and_eventual_congruence_forces_totient`,
`totient_two_mul_of_odd`, and `totient_two_mul_of_even`.

These are rigidity no-gos for weaker rational controls, not a solution of
Erdős #249.

The Challenge imports only Mathlib. The Solution imports
`ErdosProblems.Erdos249.PrefixValuationAndControlRigidity` and transports
the source proofs. NanoDa is enabled; permitted axioms are `propext`,
`Quot.sound`, and `Classical.choice`.

`lakefile.toml` registration remains for the integrating agent. No submission
has occurred; novelty is unassessed.
