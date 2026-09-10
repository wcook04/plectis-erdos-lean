# An Archimedean cap

Integer-polynomial pairs with positive quadratic degree and decay rates, a nonnegative height-rate bound, and eventual nonvanishing at each real x>1 satisfy sigma/(sigma+delta)<=1/2. Actual-degree denominator-cleared forms tend to zero whenever log(b)/log(a) lies strictly below that ratio. The Challenge states every asymptotic hypothesis directly and defines the polynomial remainder, degree and coefficient norm using only Mathlib.

This matches the current short paper res:archimedean-cap. Allowing o(n²) height when h=0 and finitely many zero remainders strengthens the literal paper hypotheses. No rational-base polynomial supply, equality-case conclusion, or irrationality follows. The original cap source is compiled and axiom-audited. The added no-decay source and extended wrapper are uncompiled; axiom audit, Comparator replay and negative control for the extension remain pending. Novelty is unassessed; no submission occurred.

The second declaration repeats the maximum-coefficient height bound of `LongCapHypotheses` literally, alongside the same degree upper bound and eventual nonvanishing and two-sided remainder rate at every real x>1. For natural a,b with 1≤b and b<a<b², it asserts that the actual-degree cleared forms do not tend to zero. It assumes no limit for degree/n² and asserts neither divergence nor irrationality. `maxCoefficient` is defined independently using the finite polynomial support; the positive Solution transports the exact canonical theorem. The Challenge imports only Mathlib and has the two intended theorem placeholders.

The excluded decay concerns the undivided forms `b^d_n * Lambda_n(a/b)`. It does not exclude base-dependent content division or other irrationality methods outside the all-base hypotheses.

`comparator-nodecay-negative-mismatch.json` selects only
`cleared_below_square_not_tendsto_zero`. Its separate
`NoDecayNegativeSolution` module deliberately supplies `True` under that name.
Acceptance of this control requires the exact diagnostic
`Challenge and solution theorem statement do not match: 'Erdos249257.ExternalVerification1049ArchimedeanCap.cleared_below_square_not_tendsto_zero'`,
with a nonzero semantic-rejection exit, not a timeout or compilation failure.
The original cap mismatch cannot serve as evidence for this selection.

This new negative module awaits focused elaboration and supported Comparator
replay. The current public six-entry replay contains only the original cap
selection; it provides no NoDecay replay evidence. The expanded positive
configuration and this dedicated negative must be published and replayed
against the same future immutable commit. No submission is implied.
