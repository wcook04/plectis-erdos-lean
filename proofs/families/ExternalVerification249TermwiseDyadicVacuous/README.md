# Erdős #249: termwise dyadic window is vacuous

The termwise hypothesis `2^t ∣ φ(N+t)` can never beat the size budget
`v·(N+t+2)`, because `2^t ≤ φ(N+t) < N+t`. The compared theorem is
`termwise_dyadic_window_vacuous`. This is a no-go for the termwise dyadic
window, not a solution of Erdős #249.

The Challenge imports only Mathlib. The Solution imports
`ErdosProblems.Erdos249.PrefixValuationAndControlRigidity` and cites the
source theorem. NanoDa is enabled; permitted axioms are `propext`,
`Quot.sound`, and `Classical.choice`.

`lakefile.toml` registration remains for the integrating agent. No submission
has occurred; novelty is unassessed.
