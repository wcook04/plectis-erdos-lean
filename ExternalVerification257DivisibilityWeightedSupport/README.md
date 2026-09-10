# ExternalVerification257DivisibilityWeightedSupport

A finite prime-weighted cost on an infinite support excluding zero forces
irrationality of the reciprocal-Mersenne series at that base, and a finite
binary weighted cost on a host forces all-base hereditary irrationality of every
infinite subset. This is the long-record weighted claim, not a universal
infinite-support theorem. Erdős Problem 257 remains open.

`Challenge.lean` imports only Mathlib and restates `DivisibilityWeightedClaim`
together with the definitions in its unfolding. `Solution.lean` imports
`ErdosProblems.Erdos257.PaperCompleteR8.WeightedReturn` and cites
`divisibilityWeightedClaim`.

## Files

| File | Role |
|---|---|
| `Challenge.lean` | Mathlib-only restatement with one `sorry` body. |
| `Solutions/ExternalVerification257DivisibilityWeightedSupport.lean` | Source transport. |
| `comparator.json` | Compared theorem name and permitted axioms. |
| `AxiomAudit.lean` | `#print axioms` over the compared theorem. |
