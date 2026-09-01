# Problems, and where each one is stuck

This repository is a corpus to work in. Clone it, choose a live mathematical
obstruction below, and either prove it, falsify the route that is proposed for it,
or improve the machinery that makes the result checkable. Every section names the
strongest theorem the release carries for that problem, the exact unresolved step,
and the smallest contribution that would move it.

The unrestricted parent problems are open. Sections run in the order a reader meets
them in `README.md`.

## Erdős #257

**The question.** Prove irrationality of sum_{n in A} 1/(2^n-1) for every infinite support A.

**What the release proves.** ExternalVerification257ReciprocalSupport proves that for every infinite exponent set A whose reciprocal sum converges and every integer base b at least two, the series with terms 1/(b^a - 1) supported on A is irrational, with no coprimality, periodicity, density or powerful-support hypothesis.

**Where it is stuck.** Every candidate counterexample support now has divergent reciprocal sum, and the surviving fatal branch at the rational target 1/21 is consistent with a permanent affine supercapacity regime, so no theorem forces the cofinal closed returns that would decide membership.

**Smallest useful contribution** (proof). Formalise the 1/3 certificate lemma as an inequality chain of roughly two hundred lines, after which finite certificates decide an individual support and rational-target pair.

**Entries.**

- [`ExternalVerification257ReciprocalSupport/`](ExternalVerification257ReciprocalSupport/), irrationality for every reciprocal-summable support and every integer base.
- [`ExternalVerification257FinitePeriodNoncollapse/`](ExternalVerification257FinitePeriodNoncollapse/), exact multiplicative-order noncollapse at every integer base.
- [`ExternalVerification257RationalTailRigidity/`](ExternalVerification257RationalTailRigidity/), rational values force unbounded integer tail orbits and mass lower bounds.

```sh
lake build ExternalVerification257ReciprocalSupport Solutions.ExternalVerification257ReciprocalSupport
lake build ExternalVerification257FinitePeriodNoncollapse Solutions.ExternalVerification257FinitePeriodNoncollapse
lake build ExternalVerification257RationalTailRigidity Solutions.ExternalVerification257RationalTailRigidity
```

## Erdős #249

**The question.** Prove that the binary totient series sum_{n>=1} phi(n)/2^n is irrational.

**What the release proves.** ExternalVerification249RankOneSharpFloor proves that every admissible rank-one quotient exceeds the Möbius Mersenne rung by more than 21/320, that the minimum is attained at a unique admissible pair, and that 1/16 is the largest unit fraction bounding the gap from below.

**Where it is stuck.** Irrationality of the binary totient series is equivalent in Lean to a residue-gap supply statement, that for every c and every positive odd v there exists H > 0 divisible by phi(v) whose canonical totient-block residue modulo (2^H - 1)/v lies in the central interval of radius c + H + 1, and no construction supplies that H.

**Smallest useful contribution** (literature). Test whether the Padé construction of Duverney and Tachiya for Lambert series survives a bounded non-periodic Möbius weight, and record the exact step at which it fails.

**Entries.**

- [`ExternalVerification249RankOneSharpFloor/`](ExternalVerification249RankOneSharpFloor/), explicit 21/320 floor for the positive rank-one Möbius Mersenne cone.
- [`ExternalVerification249BinaryCyclotomicAnchors/`](ExternalVerification249BinaryCyclotomicAnchors/), unconditional clean prime anchors in the binary cyclotomic layers.

```sh
lake build ExternalVerification249RankOneSharpFloor Solutions.ExternalVerification249RankOneSharpFloor
lake build ExternalVerification249BinaryCyclotomicAnchors Solutions.ExternalVerification249BinaryCyclotomicAnchors
```

## Erdős #269

**The question.** Prove irrationality in the first unresolved support case with three distinct prime generators.

**What the release proves.** ExternalVerification269ThreePrimeStructure proves the exact three-prime running-LCM identity, that the reciprocal-height kernel is constant on every logarithmic cell with exactly 3m jump values across the first m positive jumps, and that the kernel admits injective minors of every order, so it has no finite separable representation.

**Where it is stuck.** The normalised infinite dyadic shell tail either reaches an exact integral state or returns cofinally at distance at least 1/31 from every integer, and excluding the exact-integral-state branch is the unresolved step.

**Smallest useful contribution** (proof). Prove in Lean the telescoping identity that the sum over primes p of (p - 1) times the sum over n of 1/H(p^n) equals 1, where H is the running LCM height, which is a one-line difference identity and is absent from the corpus.

**Entries.**

- [`ExternalVerification269ThreePrimeStructure/`](ExternalVerification269ThreePrimeStructure/), exact three-prime running-LCM identity and infinite kernel rank.

```sh
lake build ExternalVerification269ThreePrimeStructure Solutions.ExternalVerification269ThreePrimeStructure
```

## Erdős #1041

**The question.** If a monic polynomial f(z)=product_i(z-z_i) has all roots in the open unit disk, prove that two roots can be joined by a curve of length less than 2 contained in the open lemniscate |f|<1.

**What the release proves.** ExternalVerification1041FirstMergeCriticalValueSeparation proves the exact all-degree critical-value separation thresholds C(n, 4) < 1 for every n at least 3, C(n, 3) < 1 for every n at least 4, and C(n, 2) < 1 for every n at least 6, where C(n, S) = (1 + S)^(2/n) log(S/(S - 1)), together with the sign-free consumer that a squared length at most 4 C(n, S) with C(n, S) < 1 forces length strictly below 2.

**Where it is stuck.** The sharp constant is settled in every degree only under the critical-spectrum separation hypothesis, and the two surviving unconditional routes are the componentwise combined-charge lemma, that every nontrivial connected component C of the admissible critical forest satisfies the sum over edges e in C of D_e + K_e being at least 0, and the covering statement COVER, that for monic g with roots in the closed unit disk there is a level lambda in [mu, 1] and a compact connected subset Gamma of the first-merge component of {|g| <= lambda} carrying two roots with every point of Gamma within intrinsic distance 1 of a root.

**Smallest useful contribution** (computation). Re-run the degree-five moment computation with directed rounding rather than IEEE double arithmetic, which converts the fifth arithmetic-mean strengthening into a certificate-backed statement and opens the sixth.

**Entries.**

- [`ExternalVerification1041FirstMergeCriticalValueSeparation/`](ExternalVerification1041FirstMergeCriticalValueSeparation/), exact all-degree critical-value separation thresholds and a sign-free first-merge length bound.
- [`ExternalVerification1041SolvedFamilies/`](ExternalVerification1041SolvedFamilies/), checked kernels for three completely solved polynomial families.
- [`ExternalVerification1041CriticalGeometry/`](ExternalVerification1041CriticalGeometry/), global two-root critical proximity and exact straight-line obstructions.
- [`ExternalVerification1041CyclicTrinomialFiber/`](ExternalVerification1041CyclicTrinomialFiber/), strict lemniscate containment of trinomial root spokes.
- [`ExternalVerification1041QuarticQuotientFiber/`](ExternalVerification1041QuarticQuotientFiber/), strict length budget below two for quotient-fibre root lifts.
- [`ExternalVerification1041TetranomialSpokes/`](ExternalVerification1041TetranomialSpokes/), coefficient and energy criteria forcing two safe tetranomial spokes.

```sh
lake build ExternalVerification1041FirstMergeCriticalValueSeparation Solutions.ExternalVerification1041FirstMergeCriticalValueSeparation
lake build ExternalVerification1041SolvedFamilies Solutions.ExternalVerification1041SolvedFamilies
lake build ExternalVerification1041CriticalGeometry Solutions.ExternalVerification1041CriticalGeometry
lake build ExternalVerification1041CyclicTrinomialFiber Solutions.ExternalVerification1041CyclicTrinomialFiber
lake build ExternalVerification1041QuarticQuotientFiber Solutions.ExternalVerification1041QuarticQuotientFiber
lake build ExternalVerification1041TetranomialSpokes Solutions.ExternalVerification1041TetranomialSpokes
```

## Erdős #251

**The question.** Prove irrationality of the dyadic series built from consecutive prime gaps.

**What the release proves.** ExternalVerification251PolynomialShiftCountermodel exhibits the explicit digit word g(n) = 2(n^2 + 4n + 2) with orbit T(n) = 2(n + 4)^2, which satisfies the dyadic tail recurrence at every index, is positive, even, strictly increasing, unbounded and nonperiodic, has every fixed tail shift integral, and has every adjacent difference past the first term at least fourteen.

**Where it is stuck.** The remaining producer is the cofinal adjacent small mismatch, that for each fixed h at least 1 and every N0 there is an index N at least N0 at which T(N+h) - T(N) and T(N+h+1) - T(N+1) both lie strictly between -1 and 1 while g(N+h+1) differs from g(N+1).

**Smallest useful contribution** (proof). Prove in Lean that the countermodel series sums to 32 as a tsum, which currently rests on a computed ratio bound of 25/32.

**Entries.**

- [`ExternalVerification251PolynomialShiftCountermodel/`](ExternalVerification251PolynomialShiftCountermodel/), exact countermodel to coarse gap-profile irrationality routes.
- [`ExternalVerification251ActualPrimeGapTail/`](ExternalVerification251ActualPrimeGapTail/), exact rational-tail collapse for the actual prime-gap dyadic series.

```sh
lake build ExternalVerification251PolynomialShiftCountermodel Solutions.ExternalVerification251PolynomialShiftCountermodel
lake build ExternalVerification251ActualPrimeGapTail Solutions.ExternalVerification251ActualPrimeGapTail
```

## Erdős #68

**The question.** Prove that the Erdős #68 factorial-denominator series is irrational.

**What the release proves.** ExternalVerification68CompanionOrbitBoundary proves that the series is rational exactly when floor(m! C) is congruent to -2 modulo m for all sufficiently large m, where C is the sum over n at least 2 of 1/(n!(n! - 1)), and irrational exactly when that residue is missed cofinally, with the same equivalence at every real base point.

**Where it is stuck.** No producer supplies the cofinal residue misses, and exact computation of the strict-successor carries through m = 300000 gives only a finite denominator exclusion for any displayed rational representation.

**Smallest useful contribution** (computation). Extend the exact carry computation beyond m = 300000 and account for the odd-index pattern that has held from index 23 through 300000, since a Lean-checked consumer converts cofinally many non-unit carries into irrationality.

**Entries.**

- [`ExternalVerification68CompanionOrbitBoundary/`](ExternalVerification68CompanionOrbitBoundary/), companion-orbit rationality boundary.
- [`ExternalVerification68ChannelRadius/`](ExternalVerification68ChannelRadius/), explicit cubic radius floor for simultaneous factorial channel cancellation.

```sh
lake build ExternalVerification68CompanionOrbitBoundary Solutions.ExternalVerification68CompanionOrbitBoundary
lake build ExternalVerification68ChannelRadius Solutions.ExternalVerification68ChannelRadius
```

## Erdős #243

**The question.** Under a_{n+1}/a_n^2 -> 1 and rational reciprocal sum, force eventual Sylvester recurrence.

**What the release proves.** ExternalVerification243PeriodicNegativeOrbit proves that for every offset N, every period h > 0 and every positive drift M, positivity of the negative-magnitude sequence together with e_n < a_n on the tail, the exact recurrence and the shape equation D_n + e_n = (a_n - 1) C_n are contradictory, so no eventually periodic negative-magnitude orbit with positive drift carries a rational value.

**Where it is stuck.** The surviving signed-state obstruction is cofinally unbounded negative excursions in the exact dynamic cocycle, and the decisive producer is a global negative-mass, cumulative-LCM or repair-payment theorem.

**Smallest useful contribution** (proof). Formalise the bridge from Koizumi, Irrationality of the reciprocal sum of doubly exponential sequences, arXiv:2504.05933, INTEGERS 26 (2026), A28, so that bounded-negative rigidity becomes a statement about Erdős #243 itself under one added hypothesis.

**Entries.**

- [`ExternalVerification243PeriodicNegativeOrbit/`](ExternalVerification243PeriodicNegativeOrbit/), exclusion of eventually periodic negative-magnitude orbits.

```sh
lake build ExternalVerification243PeriodicNegativeOrbit Solutions.ExternalVerification243PeriodicNegativeOrbit
```

## Erdős #1049

**The question.** Determine irrationality of the rational-base Lambert values, with 3/2 as the first resistant explicit base.

**What the release proves.** ExternalVerification1049HermitePadeNoGo proves that on the admissible region rho at least 0 and sigma at least 1 + rho the rectangular two-function threshold of the explicit exponent model is at most 1/2 - 1/pi^2, with equality exactly at rho = 0 and sigma = 1.

**Where it is stuck.** At the base 3/2 the homogenisation ceiling caps every content lane on the fixed diagonal at a > b^2, rank two fails the model even at zero clearing, rank three would require kappa_3 < 0.10721, and no construction supplies a family, integrality, nonvanishing or remainder estimate.

**Smallest useful contribution** (infrastructure). Add the power-certificate compiler, which is Lean-checked and already present in the public source, to the comparator configuration of the entry that consumes it.

**Entries.**

- [`ExternalVerification1049HermitePadeNoGo/`](ExternalVerification1049HermitePadeNoGo/), sharp rectangular Hermite–Padé threshold no-go with unique equality point.
- [`ExternalVerification1049AdelicHeightBridge/`](ExternalVerification1049AdelicHeightBridge/), exact first transformed Zudilin row and the 2^64 < 3^41 < 2^65 bracket.
- [`ExternalVerification1049PrimeSupportSelectors/`](ExternalVerification1049PrimeSupportSelectors/), prime support forces the sharp 1/q gap in q-Apéry linear forms.
- [`ExternalVerification1049RationalBaseBarrier/`](ExternalVerification1049RationalBaseBarrier/), no coordinatewise denominator clearing at the rational base 3/2.

```sh
lake build ExternalVerification1049HermitePadeNoGo Solutions.ExternalVerification1049HermitePadeNoGo
lake build ExternalVerification1049AdelicHeightBridge Solutions.ExternalVerification1049AdelicHeightBridge
lake build ExternalVerification1049PrimeSupportSelectors Solutions.ExternalVerification1049PrimeSupportSelectors
lake build ExternalVerification1049RationalBaseBarrier Solutions.ExternalVerification1049RationalBaseBarrier
```

## How a contribution is checked

**Comparator statement parity.** Comparator compares the Challenge statement against the Solution declaration of the same name. A contribution is checked when the Solution proves the theorem the Challenge states, with the statement unchanged.

**Axiom budget.** Each entry's AxiomAudit prints the axioms every selected declaration depends on. A contribution that introduces sorryAx, or an axiom outside the audited budget, is not checked.

**Novelty.** Palomar does not certify novelty. Where the literature does not settle novelty, the metadata records it as unassessed and makes no priority claim.

Before any of that, run the build once so the baseline is green.

```sh
lake exe cache get
lake build
```
