# Dyadic support-observation summability

After weighting each observation length by the reciprocal of its conductor,
the dyadic incomplete-period masses are summable. Finite dyadic sums obey
the majorant `2 Q ∑ weightedObservationTerm`, and the sliding window mean
from `M` to `2M` vanishes as `M → ∞`. Unweighted atom costs need not be
summable.

The Challenge imports only Mathlib and restates `supportObservationMass` and
`weightedObservationTerm` in the same classical form as the source. The
Solution transports the three source endpoints from
`ErdosProblems.Erdos257.WeightedSupportLimits`. These estimates do not settle
Erdős #257.

`lakefile.toml` registration remains for the integrating agent.
Comparator replay and Palomar submission are not claimed.
