# Plectis Erdős Lean

### 19 Lean-verified theorem families across eight open Erdős problems

**Will Cook · human-led, AI-assisted mathematical research and formalisation · Lean 4 / Mathlib**

Lead results: irrationality for every reciprocal-summable support and every integer base (Erdős #257); explicit 21/320 floor for the positive rank-one Möbius Mersenne cone (Erdős #249); exact three-prime running-LCM identity and infinite kernel rank (Erdős #269); checked kernels for three completely solved polynomial families (Erdős #1041); exact countermodel to coarse gap-profile irrationality routes (Erdős #251).

Each entry states an exact theorem, proves it in Lean against Mathlib, prints the axioms
it depends on, and records its mathematical consequence, its proof boundary and the
remaining open step. The unrestricted parent problems remain open; this repository does
not close any of them.

Problems covered: #68, #243, #249, #251, #257, #269, #1041, #1049.

This repository is the Lean surface of the Plectis programme: <https://wcook04.github.io/plectis/>. The papers behind each entry, the eight problem pages and the further verified work outside this release are indexed at <https://wcook04.github.io/plectis/maths/>.

## Start here

### Erdős #257: irrationality for every reciprocal-summable support and every integer base

For every infinite set A of exponents whose reciprocal sum converges and every integer base b at least two, the series with terms 1/(b^a - 1) supported on A is irrational. The theorem settles the whole reciprocal-summable support regime at once and uniformly in the base, with no pairwise-coprimality, periodicity, density or powerful-support hypothesis, and with the zero exponent normalised to zero by real division. Any counterexample to the universal Erdős Problem 257 must therefore be supported on a set whose reciprocal sum diverges. The mechanism produces close returns of shifted binary support atoms from an LCM-prefix orbit-mean argument, transfers them to every radix through a uniform pointwise inequality bounding the base-b atom displacement by twice the binary one, and closes with an exact radix integer orbit. Erdős proved the pairwise-coprime case at base two and stated that pairwise coprimality can be removed by a more complicated argument without printing that argument; the base-two proof here is an independent reconstruction, the passage to every integer base is a local strengthening, and no theorem-priority claim is made and no identification with Erdős's omitted argument is asserted. The audience is analytic number theorists working on irrationality of Mersenne-type reciprocal subseries. Reciprocal-divergent supports are untouched, so the universal Erdős Problem 257 remains open.

Boundary. The compared result states that every infinite reciprocal-summable support A gives an irrational reciprocal-power subseries at every integer base at least two. The zero exponent is normalized to zero by real division. No pairwise-coprimality, periodicity, density, or powerful-support hypothesis is assumed. Challenge.lean contains the deliberate Comparator specification sorry; the proof-bearing Solution.lean and its imported source theorem are sorry-free. The atom comparison and close-return producer are subordinate proof mechanisms rather than extra results.

Source: [`ExternalVerification257ReciprocalSupport/`](ExternalVerification257ReciprocalSupport/), configuration `ExternalVerification257ReciprocalSupport/comparator.json`.

### Erdős #249: explicit 21/320 floor for the positive rank-one Möbius Mersenne cone

Write Θ₂ for the Möbius Mersenne rung, the sum of μ(d)/(2^d - 1)^2 over d at least 1, write t_Y(r) for its first Y atoms at exponent r, and set Q(e,Y) = t_Y(e+2)^2 / t_Y(2e+2) on the admissible range e at least 1 and Y at least 4. Every admissible Q(e,Y) exceeds Θ₂ by more than 21/320, and the value Q(1,5) at the five-atom first-depth kernel is attained at no other admissible pair. The unit-fraction boundary is settled exactly: 1/16 is a valid uniform floor for the gap and 1/15 fails at an admissible pair, so 1/16 is the largest unit fraction bounding the gap from below. The floor survives mixing, since for every nonempty finite family of admissible pairs with positive weights the weighted mean of the quotients still exceeds Θ₂ + 21/320, so no positive combination of rank-one blocks approaches Θ₂. Any rational representation Q(e,Y) = p/q with q at least 1 gives the explicit bound |qΘ₂ - p| > 21q/320, a rational linear-form obstruction of the kind used in irrationality measures for lacunary Möbius sums. Exact evaluation of the finite Möbius Mersenne prefixes combines with a uniform interval bound to reduce the two-parameter admissible family to a finite comparison, and the family is first presented in this development with its novelty unassessed. Signed cancellation and genuinely coupled higher-rank constructions lie outside every statement here, so Erdős Problem 249 remains open.

Boundary. Six compared declarations expose the unique minimizer, explicit strict floor, sharp unit-fraction boundary, positive-mixture closure, and rational-linear-form consequence. Challenge.lean contains six intentional Comparator specification sorries.

Source: [`ExternalVerification249RankOneSharpFloor/`](ExternalVerification249RankOneSharpFloor/), configuration `ExternalVerification249RankOneSharpFloor/comparator.json`.

### Erdős #269: exact three-prime running-LCM identity and infinite kernel rank

For pairwise distinct primes p, q, r and every nonzero x, the least common multiple of all smooth numbers p^i q^j r^k at most x equals the product of the three maximal pure prime powers below x. The reciprocal-height kernel K(i,j,k) built from that identity is constant on every logarithmic cell, and the first m positive jump values across the three prime channels number exactly 3m. Every finite exponent box sums to the height-fibre normal form, the sum over genuine running-LCM heights of the fibre cardinality divided by the height, and a multiplicative shell of width factor r inside a sorted exponent budget j satisfies 9 times its cardinality at most (j+3)^2. For every order n there are injective index families giving a nonsingular n by n minor of K uniformly in the remaining exponent layer, so K has infinite rank and no finite separable representation K(i,j,k) = sum over l < d of f_l(i) G_l(j,k) exists for any d. The smallest 2,3,5 rectangle has determinant exactly -1/15. Three distinct primes keep the three logarithm floors independent, which is what makes the running-LCM identity exact and the minors nonsingular in every order, and it removes every method that would evaluate the three-prime sum by finitely many separated factors. Priority for the three-prime structure has not been established, none of the seven theorems yields irrationality or transcendence, and Erdős #269 remains open.

Boundary. Seven compared theorems expose the exact running-LCM identity, logarithmic cell constancy, exact jump count, height-fibre normal form, quadratic shell multiplicity, exact rank-two minor, and the composite arbitrary-order-minor/no-finite-separation theorem. Challenge.lean contains seven deliberate specification sorries; the proof-bearing Solution imports the checked source.

Source: [`ExternalVerification269ThreePrimeStructure/`](ExternalVerification269ThreePrimeStructure/), configuration `ExternalVerification269ThreePrimeStructure/comparator.json`.

### Erdős #1041: checked kernels for three completely solved polynomial families

The accompanying ordinary mathematics completely solves three structured families of Erdős #1041: collinear root configurations in every degree, the primitive sparse quintics, and translated cubic quotient fibres in every degree 3q with q at least two. This configuration verifies in Lean the three load-bearing kernels of those solutions, and only those three. For every degree n at least two, a monic polynomial of degree n vanishing at -1 and 1, with n-1 increasing interior nodes in the closed interval and values alternating in sign along them, has one node at which the absolute value is at most 2^-(n-1) times cos(pi/2n)^-n. Five real disk coordinates satisfying the first three rotated Newton moments for r strictly between 0 and 2 contain two distinct indices whose tail energy is strictly below one, and three roots in the open unit disc admit one complete radial spoke along which their monic cubic stays inside the closed unit lemniscate. Each family solution is reduced to a single finite inequality, so the delicate step in the geometry of polynomial sublevel sets is the part submitted for checking. The alternation argument sits in the classical Chebyshev context, a bounded search found no earlier form of the quintic selector, and priority is unresolved. Affine transport, the final selection, and the surrounding analytic assembly are ordinary proofs rather than Lean-checked conclusions, and the unrestricted problem is untouched.

Boundary. Three exact Lean endpoints support three ordinary solved polynomial families. They do not state the ordinary assembly or unrestricted #1041.

Source: [`ExternalVerification1041SolvedFamilies/`](ExternalVerification1041SolvedFamilies/), configuration `ExternalVerification1041SolvedFamilies/comparator.json`.

### Erdős #251: exact countermodel to coarse gap-profile irrationality routes

The explicit digit word g(n) = 2(n^2 + 4n + 2) and the explicit rational orbit T(n) = 2(n + 4)^2 satisfy the dyadic tail recurrence T(N + 1) = 2 T(N) - g(N + 1) at every index. The word is positive, even and strictly increasing, hence unbounded and nonperiodic; every fixed tail shift T(N + h) - T(N) is an integer for every h and every N; and every difference of consecutive digits past the first term is at least fourteen, so it is never 2 or -2. The construction is an exact countermodel, and it eliminates every argument that would force the adjacent small-mismatch producer out of positivity, parity, polynomial growth, unboundedness, nonperiodicity, the dyadic recurrence and integrality at every fixed shift taken together. The mechanism is that an integer-valued quadratic orbit turns all-shift integrality into a polynomial identity over the integers while the word has constant second difference, so its adjacent differences grow linearly and clear the small window from the outset. The readers are number theorists working on the irrationality of the dyadic prime-gap series; priority for the construction has not been assessed. The orbit is not the actual consecutive-prime-gap orbit, so the theorem does not decide Erdős Problem 251.

Boundary. The single compared theorem states the complete exact countermodel: its quadratic digit word is positive, even, and strictly increasing; it obeys the dyadic recurrence with the explicit rational orbit; every fixed shift is integral; and every adjacent difference avoids plus-or-minus two. Challenge.lean has the one intentional Comparator specification sorry; the proof-bearing Solution.lean and imported source theorems are sorry-free.

Source: [`ExternalVerification251PolynomialShiftCountermodel/`](ExternalVerification251PolynomialShiftCountermodel/), configuration `ExternalVerification251PolynomialShiftCountermodel/comparator.json`.

## Every entry in this release

| Problem | Result | Entry |
| --- | --- | --- |
| #68 | Erdős #68: explicit cubic radius floor for simultaneous factorial channel cancellation | [`ExternalVerification68ChannelRadius`](ExternalVerification68ChannelRadius/) |
| #243 | Erdős #243: exclusion of eventually periodic negative-magnitude orbits | [`ExternalVerification243PeriodicNegativeOrbit`](ExternalVerification243PeriodicNegativeOrbit/) |
| #249 | Erdős #249: unconditional clean prime anchors in the binary cyclotomic layers | [`ExternalVerification249BinaryCyclotomicAnchors`](ExternalVerification249BinaryCyclotomicAnchors/) |
| #249 | Erdős #249: explicit 21/320 floor for the positive rank-one Möbius Mersenne cone | [`ExternalVerification249RankOneSharpFloor`](ExternalVerification249RankOneSharpFloor/) |
| #251 | Erdős #251: exact rational-tail collapse for the actual prime-gap dyadic series | [`ExternalVerification251ActualPrimeGapTail`](ExternalVerification251ActualPrimeGapTail/) |
| #251 | Erdős #251: exact countermodel to coarse gap-profile irrationality routes | [`ExternalVerification251PolynomialShiftCountermodel`](ExternalVerification251PolynomialShiftCountermodel/) |
| #257 | Erdős #257: exact multiplicative-order noncollapse at every integer base | [`ExternalVerification257FinitePeriodNoncollapse`](ExternalVerification257FinitePeriodNoncollapse/) |
| #257 | Erdős #257: rational values force unbounded integer tail orbits and mass lower bounds | [`ExternalVerification257RationalTailRigidity`](ExternalVerification257RationalTailRigidity/) |
| #257 | Erdős #257: irrationality for every reciprocal-summable support and every integer base | [`ExternalVerification257ReciprocalSupport`](ExternalVerification257ReciprocalSupport/) |
| #269 | Erdős #269: exact three-prime running-LCM identity and infinite kernel rank | [`ExternalVerification269ThreePrimeStructure`](ExternalVerification269ThreePrimeStructure/) |
| #1041 | Erdős #1041: global two-root critical proximity and exact straight-line obstructions | [`ExternalVerification1041CriticalGeometry`](ExternalVerification1041CriticalGeometry/) |
| #1041 | Erdős #1041: strict lemniscate containment of trinomial root spokes | [`ExternalVerification1041CyclicTrinomialFiber`](ExternalVerification1041CyclicTrinomialFiber/) |
| #1041 | Erdős #1041: strict length budget below two for quotient-fibre root lifts | [`ExternalVerification1041QuarticQuotientFiber`](ExternalVerification1041QuarticQuotientFiber/) |
| #1041 | Erdős #1041: checked kernels for three completely solved polynomial families | [`ExternalVerification1041SolvedFamilies`](ExternalVerification1041SolvedFamilies/) |
| #1041 | Erdős #1041: coefficient and energy criteria forcing two safe tetranomial spokes | [`ExternalVerification1041TetranomialSpokes`](ExternalVerification1041TetranomialSpokes/) |
| #1049 | Erdős #1049: exact first transformed Zudilin row and the 2^64 < 3^41 < 2^65 bracket | [`ExternalVerification1049AdelicHeightBridge`](ExternalVerification1049AdelicHeightBridge/) |
| #1049 | Erdős #1049: sharp rectangular Hermite–Padé threshold no-go with unique equality point | [`ExternalVerification1049HermitePadeNoGo`](ExternalVerification1049HermitePadeNoGo/) |
| #1049 | Erdős #1049: prime support forces the sharp 1/q gap in q-Apéry linear forms | [`ExternalVerification1049PrimeSupportSelectors`](ExternalVerification1049PrimeSupportSelectors/) |
| #1049 | Erdős #1049: no coordinatewise denominator clearing at the rational base 3/2 | [`ExternalVerification1049RationalBaseBarrier`](ExternalVerification1049RationalBaseBarrier/) |

## Reading an entry

Each entry contains the same five core files.

- `Challenge.lean` states the theorem for a reviewer and does not prove it.
- `Solution.lean` proves it. A `sorry` here would be fatal and there is none.
- `AxiomAudit.lean` prints the axioms each selected declaration depends on.
- `comparator.json` is the configuration a registry submission names.
- `formalization.yaml` records scope, sources, attribution and known divergences.

## What this repository does not establish

A Lean proof establishes that the Solution proves the theorem the Challenge states,
on the axioms the audit prints. It does not establish that a result is new, that it
is important, or that anyone has reviewed it. Where the literature does not settle
novelty, the metadata records novelty as unassessed and makes no priority claim.
No human mathematical peer review is claimed for any entry in this release.

## Authorship

Will Cook is the human author and responsible maintainer.
AI systems assisted with mathematical exploration, proof search, formalisation and
Lean engineering. The author selected the public claims, reviewed their stated
boundaries and accepts responsibility for every statement in this repository.

## Citation

Cite this repository through `CITATION.cff`, at the commit you read.

## Build

```sh
lake exe cache get
lake build
```
