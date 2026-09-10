# ExternalVerification257FourNinthsRepairWindows

A natural sequence in the square-root strip cannot strictly increase through a
window of length `2 * sqrt K + 12`. Specialising to the `4/9` greedy defect
gives exact equivalences between membership of `4/9` in the Mersenne
achievement set, cofinal one-step repairs, and a repair in every explicit
square-root window. One certified window of strict increases excludes the
target.

These are target-specific equivalences. They do not prove that the repair
producer holds. They are not `ExternalVerification257FourNinthsTetraprime`.
Erdős Problem 257 remains open.

`Challenge.lean` imports only Mathlib. `Solution.lean` imports
`ErdosProblems.Erdos257.BatchReturnSynthesis` and cites the four source
theorems.
