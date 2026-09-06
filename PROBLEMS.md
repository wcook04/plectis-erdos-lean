# Problems, and where each one is stuck

This repository is a corpus to work in. Clone it, choose a live mathematical
obstruction below, and either prove it, falsify the route that is proposed for it,
or improve the machinery that makes the result checkable. Every section names the
strongest theorem the release carries for that problem, the exact unresolved step,
and the smallest contribution that would move it.

The unrestricted parent problems are open. Sections run in the order a reader meets
them in `README.md`.

Two public repositories carry this work, with different roles. wcook04/plectis-erdos-lean is the Plectis Palomar release corpus (Palomar release corpus, 21 Comparator entries, eight problems), a release projection of the private corpus; the reviewed claim registry stays in wcook04/plectis-lean-erdos249-257 at one commit. wcook04/plectis-lean-erdos249-257 is the Plectis public formal-mathematics corpus: the reviewed claim registry (docs/claims.json), the declaration atlas and the papers live there, and this release repository is its Comparator and Palomar projection at one commit. A packaged Comparator entry is a review unit, never a theorem, a curated claim, or a problem. Entry counts never compose with declaration counts from the other corpus.

## Erdős #257

**The question.** Prove irrationality of sum_{n in A} 1/(2^n-1) for every infinite support A.

**What the release proves.** ExternalVerification257ReciprocalSupport proves that for every infinite exponent set A whose reciprocal sum converges and every integer base b at least two, the series with terms 1/(b^a - 1) supported on A is irrational, with no coprimality, periodicity, density or powerful-support hypothesis.

**Where it is stuck.** Every candidate counterexample support now has divergent reciprocal sum, and the surviving fatal branch at the rational target 1/21 is consistent with a permanent affine supercapacity regime, so no theorem forces the cofinal closed returns that would decide membership.

**Smallest useful contribution** (proof). Formalise the 1/3 certificate lemma as an inequality chain of roughly two hundred lines, after which finite certificates decide an individual support and rational-target pair.

**Strongest genuine longitudinal theorem.** Finite divisibility-weighted mass implies hereditary all-base irrationality, including explicit reciprocal-divergent short-gap supports..

Finite divisibility-weighted mass implies hereditary all-base irrationality, including explicit reciprocal-divergent short-gap supports.

Evidence: ordinary_proof. Prior art: unassessed, no audit date.

Routes: no Lean package in this release; paper label `sec:eight-return-extensions`; public entry not_packaged.

**Best standalone structural theorem.** achievement-set topology and exact volume dichotomy.

A supported Mersenne achievement set is the set of reals coded by binary strings whose support lies in a fixed set J of allowed digit positions, where digit position k contributes the Mersenne weight 1 / (2^(k+1) - 1). Two declarations are compared. The first is a measure no-go on rational fibres. If 0 is not in J and the sum of 1 / (2^m - 1) over m in J is a rational number, the achievement set supported on J has Lebesgue measure zero. Positive-measure selection over a rational fibre is excluded by that measure-zero conclusion. An exceptional null point stays unexcluded. In that first declaration the set J indexes exponents in the hypothesis and digit positions in the conclusion. The second declaration classifies the whole family, with no hypothesis on J. The supported digit map is injective, its range is compact, its range is nowhere dense, the range is perfect whenever J is infinite, and the Lebesgue measure of the range satisfies an exact dichotomy: when the omitted digit positions form a finite set F the measure is the reciprocal of 2^|F|, and when infinitely many digit positions are omitted the measure is zero. Both statements are proved for the literal Mathlib-only definitions repeated in the Challenge module. The compared declarations establish no irrationality of any infinite Mersenne subseries, and Erdős Problem 257 remains open.

Evidence: lean_kernel_checked. Prior art: classical_input_disclosed, no audit date; antecedent Kakeya (1914) and Kovač-Tao Remark 4.1 own compact/perfect/totally disconnected/nowhere dense; the exact measure dichotomy is presented as added.

Routes: source [`ExternalVerification257AchievementSetGeometry/`](ExternalVerification257AchievementSetGeometry/), proof `Solutions.ExternalVerification257AchievementSetGeometry`, package `ExternalVerification257AchievementSetGeometry/comparator.json`; no paper label; public entry reserve.

**Strongest unresolved producer** (`contradict_twenty_one_permanent_affine_supercapacity`). Contradict the exact permanent affine-supercapacity regime forced by TwentyOneFatalAlignedBranch. Commit bad43508 proves that any unbounded sequence of closed canonical rows s_R<=2^R already gives the compactness decay required for 1/21 membership, so the fatal branch must eventually satisfy 2^R<s_R at every rank. Combined with commit f23727a, the boundary coin is then always taken: support appends R+1 and the scalar follows one literal affine recurrence with no residual Boolean branch. Commit 73f417a additionally proves that an aligned crossing from exact saturation into strict supercapacity must occur at R=3a+2 and omit a canonical ancestor at a+1 or 2(a+1). This restricts one entrance mechanism but does not show that the fatal branch enters late from exact saturation or contradict the regime after entry. One direct producer is an arbitrarily deep closed return, or any checked consequ…

**Failed approaches and falsifiers.**

- Any counterexample support must have divergent reciprocal sum; every candidate support with summable reciprocals is now excluded at every integer base.
- Powerful supports as an independent contribution: subsumed by the reciprocal-summable theorem and removed from public lanes.
- The 4/9 modulus-84 2-3-7 causal producer: false despite explaining all eight observed repair-gap rescues.
- The actual modulus-420 tetraprime repair producer is false at arbitrarily large prime cofactors. EightReturnSynthesis.md section 3 supplies the proof from an exact 80-anchor selected prefix and Dirichlet; the new audit gives jumps >=2 and causal-margin failures >=3. This supersedes the earlier fifty-million finite survival evidence. Unrestricted cofinal repairs remain open.
- Finite checks do not settle cofinal repairs or universal #257. Complete Lean formalization is separate from this ordinary proof.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 257` against the frontier.

**Entries.**

- [`ExternalVerification257ReciprocalSupport/`](ExternalVerification257ReciprocalSupport/), irrationality for every reciprocal-summable support and every integer base.
- [`ExternalVerification257AchievementSetGeometry/`](ExternalVerification257AchievementSetGeometry/), rational-fibre null theorem and supported Mersenne achievement-set geometry.
- [`ExternalVerification257FinitePeriodNoncollapse/`](ExternalVerification257FinitePeriodNoncollapse/), exact multiplicative-order noncollapse at every integer base.
- [`ExternalVerification257RationalTailRigidity/`](ExternalVerification257RationalTailRigidity/), rational values force unbounded integer tail orbits and mass lower bounds.

```sh
lake build ExternalVerification257ReciprocalSupport Solutions.ExternalVerification257ReciprocalSupport
lake build ExternalVerification257AchievementSetGeometry Solutions.ExternalVerification257AchievementSetGeometry
lake build ExternalVerification257FinitePeriodNoncollapse Solutions.ExternalVerification257FinitePeriodNoncollapse
lake build ExternalVerification257RationalTailRigidity Solutions.ExternalVerification257RationalTailRigidity
```

## Erdős #251

**The question.** Prove irrationality of the dyadic series built from consecutive prime gaps.

**What the release proves.** ExternalVerification251PolynomialShiftCountermodel exhibits the explicit digit word g(n) = 2(n^2 + 4n + 2) with orbit T(n) = 2(n + 4)^2, which satisfies the dyadic tail recurrence at every index, is positive, even, strictly increasing, unbounded and nonperiodic, has every fixed tail shift integral, and has every adjacent difference past the first term at least fourteen.

**Where it is stuck.** The remaining producer is the cofinal adjacent small mismatch, that for each fixed h at least 1 and every N0 there is an index N at least N0 at which T(N+h) - T(N) and T(N+h+1) - T(N+1) both lie strictly between -1 and 1 while g(N+h+1) differs from g(N+1).

**Smallest useful contribution** (proof). Supply the h = 1 cofinal adjacent-small-mismatch producer from actual consecutive-prime arithmetic. Coarse gap properties cannot supply it (the polynomial countermodel), the measured event density of 0.0042 to 0.0082 over 6.8 million primes is finite evidence only, and a Lean-checked consumer converts the producer into irrationality.

**Strongest genuine longitudinal theorem.** None. No genuine climb: the rational-tail normal form is pinned to one located obstruction, the free-pair producer with the shift offset free; the coarse-gap route is refuted as a proposal by an explicit countermodel rather than closed; and the denominator exclusions q >= 2^589 and q > 10^12040 are finite (longitudinal_truth_2026_09_01 section 1).

**Best standalone structural theorem.** Free-pair lattice and the equivalence of irrationality with cofinal free-pair nonintegrality.

(F) with converse: for any integer-digit dyadic tail recurrence, at and beyond an odd-denominator state with reduced denominator d, T_M - T_N is an integer iff N == M mod orderOf(2 : ZMod d); the offset M - N is free. Every rational-valued orbit therefore has a cutoff N0 and a positive modulus t with T_M - T_N in Z iff M == N mod t beyond N0 (exists_free_pair_lattice), in particular the rational candidate tail of every proposed rational value S of the prime-gap series. (P) is formalised as CofinalFreePairNonintegral T: for every t > 0 and every cutoff there are N, M beyond the cutoff with N == M mod t and T_M - T_N not an integer. Lean proves Irrational (T 0) <-> (P) for every real integer-digit dyadic tail orbit, that (P) is equivalent to the fixed-offset criterion CofinalNonintegralTailShifts, and, with the real tail primeGapRealTail N = 2^(N+1) sum_k g_(k+N+1)/2^(k+N+2) satisfying the recurrence with the actual prime gaps as digits and primeGapRealTail 0 = 2S - 1, that Irrational S <-> CofinalFreePairNonintegral primeGapRealTail for the actual consecutive-prime-gap series S.

Evidence: lean_kernel_checked. Prior art: new, audited 2026-09-02; antecedent J.-C. Schlage-Puchta, The irrationality of some number theoretical series, arXiv:1105.1451 (Theorem 2 (periodic base-b digit expansions); Theorem 3 (linear independence for S_k = sum p_n^k / n!)).

Routes: no Lean package in this release; no paper label; public entry not_packaged.

**Strongest unresolved producer** (`cofinal_adjacent_small_mismatch`). For each fixed h >= 1 and every N0, produce N >= N0 such that both actual tail shifts T_(N+h)-T_N and T_(N+h+1)-T_(N+1) lie strictly between -1 and 1 while g_(N+h+1) != g_(N+1). The checked finite consumer then excludes eventual integrality of the h-shift.

**Failed approaches and falsifiers.**

- Coarse gap properties (positive, even, increasing, unbounded, nonperiodic): the word g_n = 2(n^2+4n+2) satisfies all of them, has rational value 32, and never produces an adjacent small mismatch. This refutes the proposal that those properties suffice; the density measurement over 6,841,648 primes shows the event does occur in the actual primes, so the countermodel does not transfer to them.
- Bounded additive perturbation invariance: raising every gap by at most M while preserving its residue modulo M and any prescribed prefix already makes the sum rational, so no size-and-residue gap theorem invariant under that perturbation can suffice.
- Data-dependent affine cylinder escape and its fixed-lattice replacement: both are proved equivalent to the non-eventual-integrality they were introduced to derive, so neither is an independent producer.
- State compression by word repetition alone: the margin is recorded so the lane is not re-walked, and the exchanged-summation bound makes equal-tail pairs abundant for free, which leaves nonintegrality as the whole difficulty.
- Liouville-flavoured attacks: the certified expansion has irrationality-exponent witness 2.0007.
- The equivalence relocates the burden to the free-pair condition; it supplies no free pair for the actual prime-gap tail.
- The measurement that supports the condition is finite: over 1,270,607 primes below 2e7 every residue class modulo every t up to 20 carries witnesses into the last usable index window, and uniformity in t and in the cutoff is missing.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 251` against the frontier.

**Entries.**

- [`ExternalVerification251PolynomialShiftCountermodel/`](ExternalVerification251PolynomialShiftCountermodel/), exact countermodel to coarse gap-profile irrationality routes.
- [`ExternalVerification251KernelDenominatorFloor/`](ExternalVerification251KernelDenominatorFloor/), kernel-decided denominator floor for the prime-gap dyadic series.
- [`ExternalVerification251ActualPrimeGapTail/`](ExternalVerification251ActualPrimeGapTail/), exact rational-tail collapse for the actual prime-gap dyadic series.
- [`ExternalVerification251BoundedPerturbationCountermodel/`](ExternalVerification251BoundedPerturbationCountermodel/), bounded-perturbation countermodel anchored at the actual prime gaps.
- [`ExternalVerification251FreePairEquivalence/`](ExternalVerification251FreePairEquivalence/), free-pair equivalence for the actual prime-gap dyadic series.
- [`ExternalVerification251PrimeGapIdentity/`](ExternalVerification251PrimeGapIdentity/), unconditional prime-gap reformulation of the dyadic prime series.

```sh
lake build ExternalVerification251PolynomialShiftCountermodel Solutions.ExternalVerification251PolynomialShiftCountermodel
lake build ExternalVerification251KernelDenominatorFloor Solutions.ExternalVerification251KernelDenominatorFloor
lake build ExternalVerification251ActualPrimeGapTail Solutions.ExternalVerification251ActualPrimeGapTail
lake build ExternalVerification251BoundedPerturbationCountermodel Solutions.ExternalVerification251BoundedPerturbationCountermodel
lake build ExternalVerification251FreePairEquivalence Solutions.ExternalVerification251FreePairEquivalence
lake build ExternalVerification251PrimeGapIdentity Solutions.ExternalVerification251PrimeGapIdentity
```

## Erdős #249

**The question.** Prove that the binary totient series sum_{n>=1} phi(n)/2^n is irrational.

**What the release proves.** ExternalVerification249RankOneSharpFloor proves that every admissible rank-one quotient exceeds the Möbius Mersenne rung by more than 21/320, that the minimum is attained at a unique admissible pair, and that 1/16 is the largest unit fraction bounding the gap from below.

**Where it is stuck.** Irrationality of the binary totient series is equivalent in Lean to a residue-gap supply statement, that for every c and every positive odd v there exists H > 0 divisible by phi(v) whose canonical totient-block residue modulo (2^H - 1)/v lies in the central interval of radius c + H + 1, and no construction supplies that H.

**Smallest useful contribution** (literature). Test whether the Padé construction of Duverney and Tachiya for Lambert series survives a bounded non-periodic Möbius weight, and record the exact step at which it fails.

**Strongest genuine longitudinal theorem.** None. No genuine climb: rationality is forced into a tempered carry of dyadic rank ≥ 2^e−1 against the proved kernel rank 2^e+1, plus finite exclusions; no producer supplies the residue-gap H (longitudinal_truth_2026_09_01 §1).

**Best standalone structural theorem.** explicit odd-core basis, full-span equality, canonical finite normal form, and exact ranks.

The two zero-residue base channels and one odd-residue channel at each positive dyadic level form a linearly independent spanning family for all dyadic sections of Euler's totient. The complete family through level e has the same span as the duplicate-free canonical truncation and exact rank 2^e+1. This unconditional structural theorem does not prove irrationality of the binary totient series.

Evidence: lean_kernel_checked. Prior art: extends, audited 2026-09-02; antecedent M. Coons, (Non)Automaticity of number theoretic functions, J. Theor. Nombres Bordeaux 22 (2010), no. 2, 339-352 (Theorem 3.2, proof printed p. 349; k-kernel definition in Section 1).

Routes: source [`ExternalVerification249DyadicTotientKernel/`](ExternalVerification249DyadicTotientKernel/), proof `Solutions.ExternalVerification249DyadicTotientKernel`, package `ExternalVerification249DyadicTotientKernel/comparator.json`; no paper label; public entry reserve.

**Strongest unresolved producer** (`totient_specific_moving_dyadic_escape`). Prove FullMersenneCanonicalBasepointResidueGapSupply, the Lean-equivalent arithmetic normal form: for every c and positive odd v, find H>0 divisible by phi(v) such that the canonical residue (-totientBlock(H,c)) mod ((2^H-1)/v) lies in the central interval of radius c+H+1. On the pure-dyadic axis, the Lean-checked signed error E_H=totientBlock(H,c)-k(2^H-1) obeys E_(H+1)=2E_H+phi(c+H+1)-k while the nearest quotient k stays fixed. Exact computation through c<=1000000 finds delay nineteen at c=490794, ruling out caps through seventeen. Pointwise legal-letter methods, the constant-two mode, sublinear errors, and every eventually affine linear-scale error are eliminated. Actual prime positions cofinally force linear excursions; more directionally, if the successor remains upper-trapped then 4E_H+p+phi(p+1)<=4+3k, so any permanent trap is cofinally bottom-locked immediately before large prim…

**Failed approaches and falsifiers.**

- Uniform bounds ‖v·2^c·S‖ ≥ c^{−A}: impossible for irrational S because odd multiples of 2^c S are dense mod 1.
- Coprime restriction with Stern-Brocot splitting and geometric decay: the visible-lattice sum ∑_{gcd(a,b)=1} 1/(2^{a+b}−1) equals exactly 1, so it cannot force irrationality.
- Positive rank-one Schur blocks: every admissible quotient sits at least 21/320 above Θ₂ (unique minimiser (1,5)).
- Nonnegative Stieltjes representations of the Möbius-Mersenne ladder: strict log-concavity at every rung.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 249` against the frontier.

**Entries.**

- [`ExternalVerification249RankOneSharpFloor/`](ExternalVerification249RankOneSharpFloor/), sharp minimiser and explicit 21/320 floor for the positive rank-one Möbius Mersenne cone.
- [`ExternalVerification249ResidueClassTotientSeries/`](ExternalVerification249ResidueClassTotientSeries/), irrationality of fixed-resolution observables of the totient word.
- [`ExternalVerification249BinaryCyclotomicAnchors/`](ExternalVerification249BinaryCyclotomicAnchors/), unconditional clean prime anchors in the binary cyclotomic layers.
- [`ExternalVerification249DyadicTotientKernel/`](ExternalVerification249DyadicTotientKernel/), complete dyadic totient-kernel structure.
- [`ExternalVerification249MobiusMersenneLadderStructure/`](ExternalVerification249MobiusMersenneLadderStructure/), no finite linear recurrence for the Möbius-Mersenne power ladder, and its separation from the literal Möbius-Lambert ladder.
- [`ExternalVerification249ParityPerturbedRationalControl/`](ExternalVerification249ParityPerturbedRationalControl/), a parity-perturbed rational control for the binary totient series.

```sh
lake build ExternalVerification249RankOneSharpFloor Solutions.ExternalVerification249RankOneSharpFloor
lake build ExternalVerification249ResidueClassTotientSeries Solutions.ExternalVerification249ResidueClassTotientSeries
lake build ExternalVerification249BinaryCyclotomicAnchors Solutions.ExternalVerification249BinaryCyclotomicAnchors
lake build ExternalVerification249DyadicTotientKernel Solutions.ExternalVerification249DyadicTotientKernel
lake build ExternalVerification249MobiusMersenneLadderStructure Solutions.ExternalVerification249MobiusMersenneLadderStructure
lake build ExternalVerification249ParityPerturbedRationalControl Solutions.ExternalVerification249ParityPerturbedRationalControl
```

## Erdős #269

**The question.** Prove irrationality in the first unresolved support case with three distinct prime generators.

**What the release proves.** ExternalVerification269ThreePrimeStructure proves the exact three-prime running-LCM identity, that the reciprocal-height kernel is constant on every logarithmic cell with exactly 3m jump values across the first m positive jumps, and that the kernel admits injective minors of every order, so it has no finite separable representation.

**Where it is stuck.** The normalised infinite dyadic shell tail either reaches an exact integral state or returns cofinally at distance at least 1/31 from every integer, and excluding the exact-integral-state branch is the unresolved step.

**Smallest useful contribution** (proof). Prove in Lean the telescoping identity that the sum over primes p of (p - 1) times the sum over n of 1/H(p^n) equals 1, where H is the running LCM height, which is a one-line difference identity and is absent from the corpus.

**Strongest genuine longitudinal theorem.** None. No genuine climb: a two-branch reduction on the actual orbit (B = 1 corner decidable per index and refuted to 6000; B > 1 corner a lattice statement certified to 10^105), the rank phase transition, and q > 10^6768; the LCM identity and two-prime transcendence are Steve Fan's (longitudinal_truth_2026_09_01 §1, prior_art_adjudication_2026_09_02 §4).

**Best standalone structural theorem.** exact running-LCM identity, logarithmic-cell constancy, exact jump count, height-fibre normal form, quadratic shell bound, arbitrary-order nonsingular minors, and no finite exact separation.

The running-LCM kernel is K(i,j,k) = 1 / (p^a q^b r^c) with a, b, c the Nat.log exponents of N = p^i q^j r^k in the bases p, q, r. Eight declarations are compared. The strongest is stated for arbitrary generators. For natural numbers p, q, r each greater than 1 such that no positive integer multiple of logb r p is an integer and no positive integer multiple of logb r q is an integer, and for every order n, there are injective index families I, J from Fin n to the naturals whose n by n minor det K(I a, J b, k) is nonzero simultaneously for every value of the third exponent k. Distinct primes satisfy that independence hypothesis: for primes p, q, r with p different from r and q different from r, the same uniform nonsingular minors exist at every order, and for every d there is no representation K(i,j,k) = sum over l < d of f_l(i) G_l(j,k) by finitely many separated factors. That pair carries no hypothesis relating p and q. For pairwise distinct primes p, q, r and every nonzero x, the least common multiple of all smooth numbers p^i q^j r^k at most x equals p^(log_p x) q^(log_q x) r^(log_r x), the product of the three maximal pure prime powers below x. For pairwise distinct primes p, q, r the first m positive jump values across the three prime channels number exactly 3m. Two declarations hold for arbitrary natural generators with no hypothesis at all: K is constant on every logarithmic cell, and the sum of K over a finite exponent box equals the sum over the genuine running-LCM heights of the fibre cardinality divided by the height. A multiplicative shell of width factor r inside a sorted exponent budget hp at most hq at most hr summing to j satisfies 9 times its cardinality at most (j+3)^2, on the hypotheses that r is positive and the shell width hi is at most r times lo. The smallest 2, 3, 5 kernel rectangle has determinant exactly -1/15. The running-LCM factorisation identity for every finite prime set, and the two-prime case in which the series factorises and is transcendental by Hecke and Mahler, are due to Steve Fan (erdosproblems.com/269 comment, 26 June 2026), who also records that the factorisation does not extend to three or more primes. The identity theorem here formalises his identity at three primes, and the rank statements are the addition. Priority for the rank statements is unassessed. None of the eight declarations yields irrationality or transcendence, and Erdős #269 remains open.

Evidence: lean_kernel_checked. Prior art: new, audited 2026-09-02; antecedent Steve Fan, comment on erdosproblems.com/269, 05:22 on 26 June 2026 (the general-k running-LCM identity, the two-prime factorisation S = S_1 S_2, and transcendence via Hecke-Mahler; closing sentence "This argument does not seem to generalize immediately to |P| >= 3, since S does not factor nicely in the first place.").

Routes: source [`ExternalVerification269ThreePrimeStructure/`](ExternalVerification269ThreePrimeStructure/), proof `Solutions.ExternalVerification269ThreePrimeStructure`, package `ExternalVerification269ThreePrimeStructure/comparator.json`; no paper label; public entry launch_core.

**Strongest unresolved producer** (`exclude_exact_integral_dyadic_tails`). Exclude every exact integral state of the genuine normalized source tail X_a=H(2^a)T_a/2. Lean proves that this orbit either has such a state or returns cofinally 1/31-far from all integers. The denominator-one automaton remains the direct arithmetic representation, but the exact a=2295 source word kills every uniform three-transition post-clear proof, and exact left-null certificates now eliminate every direct phase-conditioned source potential of total degree at most two. Analyze longer surviving error cones through a genuinely nonlocal all-scale invariant, prove that an integral carry would force a finite-degree source potential, or move to nonpolynomial/unbounded-memory structure.

**Failed approaches and falsifiers.**

- Finite separated-factor decompositions of the three-prime kernel: nonsingular minors exist at every order uniformly in the third layer.
- Adamczewski-Bugeaud stammering criterion: measured simultaneous-approximation exponents fall to ≈ 1.007 while the criterion needs exponent 1 for both slopes at the same denominator; Dirichlet supplies only 1/2.
- Finite Farey boxes and lattice first-hit screens: a measured square-root law with no cofinal quantifier.
- Leading minors are not a witness of infinite rank: row three is 1/120 times row zero for j ≤ 3 and the proportionality fails at j = 4, so index selection is essential.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 269` against the frontier.

**Entries.**

- [`ExternalVerification269ThreePrimeStructure/`](ExternalVerification269ThreePrimeStructure/), exact three-prime running-LCM identity and infinite kernel rank.
- [`ExternalVerification269WindowEscapeEquivalence/`](ExternalVerification269WindowEscapeEquivalence/), the cofinal local-window escape is equivalent to irrationality of the three-prime running-LCM value.
- [`ExternalVerification269ActualShellOrbit/`](ExternalVerification269ActualShellOrbit/), actual dyadic shell orbit, exact recurrence and integral-or-far escape.

```sh
lake build ExternalVerification269ThreePrimeStructure Solutions.ExternalVerification269ThreePrimeStructure
lake build ExternalVerification269WindowEscapeEquivalence Solutions.ExternalVerification269WindowEscapeEquivalence
lake build ExternalVerification269ActualShellOrbit Solutions.ExternalVerification269ActualShellOrbit
```

## Erdős #68

**The question.** Prove that the Erdős #68 factorial-denominator series is irrational.

**What the release proves.** ExternalVerification68CompanionOrbitBoundary proves that the series is rational exactly when floor(m! C) is congruent to -2 modulo m for all sufficiently large m, where C is the sum over n at least 2 of 1/(n!(n! - 1)), and irrational exactly when that residue is missed cofinally, with the same equivalence at every real base point.

**Where it is stuck.** No producer supplies the cofinal residue misses, and exact computation of the strict-successor carries through m = 300000 gives only a finite denominator exclusion for any displayed rational representation.

**Smallest useful contribution** (computation). Extend the exact carry computation beyond m = 300000 and account for the odd-index pattern that has held from index 23 through 300000, since a Lean-checked consumer converts cofinally many non-unit carries into irrationality.

**Strongest genuine longitudinal theorem.** None. No genuine climb: the corpus holds finite exclusions (q > 10^12039, q ∤ 299999!), exact equivalences, and route ceilings; the target never entered through the cofinal statement (longitudinal_truth_2026_09_01 §1).

**Best standalone structural theorem.** quantitative square-subsequence channel-radius lower bound, exclusion of eventual three-halves upper bounds, and exact failure of little-o decay.

A channel is an index d at least 2 carrying the modulus d! - 1, obtained by reweighting each factorial term of the series so that the powers of d! divide out; the channel test at d compares that reweighted integer with the factorial moment modulo d! - 1. Six declarations are compared. The sharpest is explicit: for every t at least 2^32 and all natural numbers M and R with M positive, M divisible by the least common multiple of d! - 1 over 2 ≤ d ≤ 2t^2, and M < (R+1)! - 1, the support radius satisfies 3t^3 < 2(R+1). The same hypotheses imposed from t = 4096 onwards give t^3 < 8(R+1), which is the explicit bound available on 4096 ≤ t < 2^32. Imposing each hypothesis set at every large t gives the sequence forms: no radius function can eventually satisfy 2(R(t)+1) ≤ 3t^3, no radius function can eventually satisfy 8(R(t)+1) ≤ t^3, and R(t)+1 is not o(t^3). The sixth declaration evaluates the finite logarithmic constraint that produces these bounds at the value R+1 = (16/9)t^3 and proves that for every t at least 4 the constraint is satisfied there. That declaration bounds no support radius. It establishes that the logarithmic constraint alone does not force a lower bound at the constant 16/9, while the constant proved on this subsequence is 3/2. The subcubic range is closed on the square subsequence D = 2t^2, since every finite channel system meeting the hypotheses carries support radius above (3/2)t^3. The nontrivial input is a finite lower estimate for the channel least common multiple, in which consecutive numbers d! - 1 are combined while their pairwise gcd losses are counted explicitly, and a Stirling bound converts that estimate into the cubic radius. This theorem family is the first presentation recorded in the development and its novelty is unassessed. The divisibility and factorial bounds remain hypotheses, so the irrationality question in Erdős Problem 68 is untouched, and the remaining problem is to derive those hypotheses from the factorial-gap series and to prove that the required channels vanish.

Evidence: lean_kernel_checked. Prior art: unassessed, no audit date.

Routes: source [`ExternalVerification68ChannelRadius/`](ExternalVerification68ChannelRadius/), proof `Solutions.ExternalVerification68ChannelRadius`, package `ExternalVerification68ChannelRadius/comparator.json`; no paper label; public entry launch_core.

**Strongest unresolved producer** (`cofinal_exact_prefix_strict_successor_miss`). Prove that cofinally many integers m fail m | strictFacTopRat(factorialGapPrefix(m),m); Lean proves this is exactly equivalent to Erdős #68. The new full-constant coordinate is an analytically equivalent version of the same producer: for C=sum_{n>=2}1/(n!(n!-1))=S-e+2, prove floor(m!C) not congruent to -2 modulo m cofinally. Lean checks the pointwise equivalence between that residue and the canonical digit d_m(C)=m-2, while the infinite-tail equivalence is recorded analytically. Prime-index misses and the fixed-k two-stage prime-power criterion remain sufficient special cases, but primes are no longer part of the exact frontier statement.

**Failed approaches and falsifiers.**

- One-owner closing route: killed because log lcm_{n≤N}(n!−1) ≫ N^{4/3} log N eventually dominates log((N!)²).
- Koepf-Schmersau floor criterion at the natural clearing scale p_n = lcm(k!−1): its tail hypothesis fails from n ≥ 4.
- Rank-two producer: reclassified as a smoothness exclusion, not an irrationality route; the CF bound already discharges grid size n ≤ 1.
- Square-subsequence logarithmic constraint: provably cannot pass the sharp constant 4√2/9 (Lean sharp_radius_satisfies_square_log_constraint).

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 68` against the frontier.

**Entries.**

- [`ExternalVerification68CompanionOrbitBoundary/`](ExternalVerification68CompanionOrbitBoundary/), companion-orbit rationality boundary.
- [`ExternalVerification68ChannelRadius/`](ExternalVerification68ChannelRadius/), explicit cubic radius floor for simultaneous factorial channel cancellation.
- [`ExternalVerification68PrimeUnitTranslator/`](ExternalVerification68PrimeUnitTranslator/), remote factorial-grid kernels reduced by an exact prime unit translator.

```sh
lake build ExternalVerification68CompanionOrbitBoundary Solutions.ExternalVerification68CompanionOrbitBoundary
lake build ExternalVerification68ChannelRadius Solutions.ExternalVerification68ChannelRadius
lake build ExternalVerification68PrimeUnitTranslator Solutions.ExternalVerification68PrimeUnitTranslator
```

## Erdős #1049

**The question.** Determine irrationality of the rational-base Lambert values, with 3/2 as the first resistant explicit base.

**What the release proves.** ExternalVerification1049HermitePadeNoGo proves that on the admissible region rho at least 0 and sigma at least 1 + rho the rectangular two-function threshold of the explicit exponent model is at most 1/2 - 1/pi^2, with equality exactly at rho = 0 and sigma = 1.

**Where it is stuck.** At the base 3/2 the homogenisation ceiling caps every content lane on the fixed diagonal at a > b^2, rank two fails the model even at zero clearing, rank three would require kappa_3 < 0.10721, and no construction supplies a family, integrality, nonvanishing or remainder estimate.

**Smallest useful contribution** (infrastructure). Add the power-certificate compiler, which is Lean-checked and already present in the public source, to the comparator configuration of the entry that consumes it.

**Strongest genuine longitudinal theorem.** F(a/b) is irrational on the region b^μ < a, μ = 2.46497868…; 31/4 is the first new base.

THEOREM A (region). Let a > b >= 1 be coprime integers with b^mu < a, mu = C_1/C_0 = 2.464978683574975037454488275535521581878..., equivalently log b / log a < theta* = 1/mu = 0.40568302138406054101566030557693017464819107867787.... Then F(a/b) = sum_{m>=1} 1/((a/b)^m - 1) is irrational. In the normalisation of Zudilin 2016 Sec. 2 (p = r/s, log|r| > c log|s|) the constant is c = mu, the irrationality-exponent bound of Zudilin 2004 Theorem 1 itself. Consequences: the strip s^mu < r < s^{mu_BV} (mu_BV = 2 pi^2/(pi^2-2) = 2.508284761994...) of bases beyond Bundschuh-Vaananen 1994 Theorem 2 is infinite; new bases with s <= 12 are 31/4; 53/5, 54/5, 56/5; 83/6, 85/6, 89/6; 122/7,...,131/7 (9 bases); 169/8,...,183/8 (odd r, 8 bases); 15, 12, 37, 17 bases for s = 9, 10, 11, 12; none for s = 2, 3. 31/4 is the new base of smallest denominator and smallest numerator. Among coprime a/b with a <= 60 the region has 137 members; closest misses 52/5 (theta = 0.407324), 51/5, 29/4 (0.411694); tightest members 53/5 (margin 0.000313), 31/4 (0.001985), 54/5.

THEOREM B. F(31/4) is irrational, and so is F((31/4)^r) for every integer r >= 1. Here log 4 / log 31 = 0.4036981731... < 81/200 < theta*, 4^mu = 30.4835... < 31 < 4^{mu_BV} = 32.3696..., so 31/4 lies outside the Bundschuh-Vaananen region and inside Theorem A's; it is the first base (smallest denominator and numerator) beyond the published region.

Evidence: ordinary_proof. ordinary complete proof citing Zudilin 2004 Lemmas 1, 2 and 7 (published lemmas); not kernel-checked, not published, no independent review; the finite part θ* > 81/200 (zudilinJ ≥ 77.6, C_0 > 88371/400) and the 31/4 parameter facts are Lean-checked; an adversarial pass on the region theorem is pending. Prior art: extends, audited 2026-09-02; antecedent P. Bundschuh and K. Vaananen, Arithmetical investigations of a certain infinite product, Compositio Math. 91 (1994), 175-199 (Theorem 2, second half (alpha = -1 case), printed p. 177; identification L_q(alpha) with the q-harmonic series also p. 177).

Routes: no Lean package in this release; no paper label; public entry not_packaged.

**Best standalone structural theorem.** Exact q-order N(N−1)(2N−1)/6 and leading coefficient (N!)²(N+1)!/2^N of Zudilin's normalized Hankel determinant.

For every rank N, Zudilin's normalized Hankel determinant V_N^* at x = z = 1 has q-order exactly N(N−1)(2N−1)/6 and leading coefficient exactly (N!)²(N+1)!/2^N, where Zudilin 2016 §4 proves only the inequality ord_q V_N^* ≥ N(N−1)(2N−1)/6. Exactness is verified by exact integer power-series computation for 1 ≤ N ≤ 7; the general-N argument is ordinary mathematics whose Lean formalisation covers the first transformed row in every column and the closed-form assembly, with rows j ≥ 2 and the determinant identification open.

Evidence: ordinary_proof. mixed: exact computation N ≤ 7, ordinary all-rank proof, partial Lean (row 1 in every column, assembly identities); any public statement must carry that qualification. Prior art: extends, audited 2026-09-02; antecedent W. Zudilin, On the irrationality of generalized q-logarithm, Res. Number Theory 2 (2016), Art. 15, arXiv:1601.02688 (Section 4 (source.tex lines 278-305): "the q-expansion of V_n^* starts from at least q^{n(n-1)(2n-1)/6}").

Routes: no Lean package in this release; paper labels `res:zudilin-sharp-qorder`, `sec:hankel-order`; public entry not_packaged.

**Strongest unresolved producer** (`three_halves_pade_height_gap`). The fixed-prime route is conditional, not an unconditional closure of step 1. The finite harmonic descent gives J_5={4,20,24} by the two-line descent lemma plus an empty level-three check, with eps=v_5(3^2-2^2)=1 and loss blocks [8,9],[40,41],[48,49]. If the all-level q-Apery monodromy/continuity premise (M)/(C5) holds, the weighted transfer gives 5 | B_j for every j >= 50 and hence a window gcd divisible by 5^(1+floor(log_5(s/2))) for every start s >= 50. The premise is certified only at N<=3 and over the finite indices recorded in FixedPrimeInfiniteTailProof.md, so the available evidence does not prove an all-index q-Apery denominator tail or unconditionally close the window-divisor substep. No first-appearance prime, factoring of 3^s-2^s, or effective form of Boyd's heuristic is needed under that explicit conditional premise. Conditional fixed-tail data also exist at p=13 (j>=676), 1…

**Failed approaches and falsifiers.**

- Scalar q-Apéry Padé family at 3/2: quantitatively dead by a fixed positive proportion at every index, with the shortfall in closed form.
- Rectangular two-function Hermite-Padé thresholds: at most 1/2 − 1/π² on the whole admissible cone ρ ≥ 0, σ ≥ 1 + ρ, with equality only at (0,1).
- Scalar content and scalar-plus-border extraction from Zudilin's Hankel determinant: neither can meet the required charge (Lean).
- Outward scalar diagonal evaluation: the homogenisation ceiling caps every content lane on the fixed diagonal at a > b².
- The theorem says nothing about F(3/2) (θ = 0.630930, gap 0.225247 above θ*), negative bases, or any base with b^μ ≥ a.
- Theorem C (Archimedean cap) shows no p-uniform Padé-type family reaches any base with b² ≥ a, so 3/2 needs a base-dependent smallness exponent, content constraints, or rank ≥ 3.
- The conditional Lean statement's row hypothesis is discharged only for rows j = 0, 1, 2; rows j >= 3 are open, so the all-rank Lean statement is not unconditional.
- The exact computation covers N <= 7 only.
- Closing the hidden-cubic-decay hope is a statement about the determinant's order and does not decide irrationality at 3/2.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 1049` against the frontier.

**Entries.**

- [`ExternalVerification1049HermitePadeNoGo/`](ExternalVerification1049HermitePadeNoGo/), sharp rectangular Hermite–Padé threshold no-go with unique equality point.
- [`ExternalVerification1049RationalBaseContour/`](ExternalVerification1049RationalBaseContour/), the rational-base contour of Zudilin's (14,12,14;27) forms.
- [`ExternalVerification1049AdelicHeightBridge/`](ExternalVerification1049AdelicHeightBridge/), exact first transformed Zudilin row and the 2^64 < 3^41 < 2^65 bracket.
- [`ExternalVerification1049PrimeSupportSelectors/`](ExternalVerification1049PrimeSupportSelectors/), sharp rational gaps for integral linear forms and the exterior-determinant height tradeoff.
- [`ExternalVerification1049RationalBaseBarrier/`](ExternalVerification1049RationalBaseBarrier/), no coordinatewise denominator clearing at the rational base 3/2.

```sh
lake build ExternalVerification1049HermitePadeNoGo Solutions.ExternalVerification1049HermitePadeNoGo
lake build ExternalVerification1049RationalBaseContour Solutions.ExternalVerification1049RationalBaseContour
lake build ExternalVerification1049AdelicHeightBridge Solutions.ExternalVerification1049AdelicHeightBridge
lake build ExternalVerification1049PrimeSupportSelectors Solutions.ExternalVerification1049PrimeSupportSelectors
lake build ExternalVerification1049RationalBaseBarrier Solutions.ExternalVerification1049RationalBaseBarrier
```

## Erdős #243

**The question.** Under a_{n+1}/a_n^2 -> 1 and rational reciprocal sum, force eventual Sylvester recurrence.

**What the release proves.** ExternalVerification243PeriodicNegativeOrbit proves that for every offset N, every period h > 0 and every positive drift M, positivity of the negative-magnitude sequence together with e_n < a_n on the tail, the exact recurrence and the shape equation D_n + e_n = (a_n - 1) C_n are contradictory, so no eventually periodic negative-magnitude orbit with positive drift carries a rational value.

**Where it is stuck.** The surviving signed-state obstruction is cofinally unbounded negative excursions in the exact dynamic cocycle, and the decisive producer is a global negative-mass, cumulative-LCM or repair-payment theorem.

**Smallest useful contribution** (proof). Formalise the bridge from Koizumi, Irrationality of the reciprocal sum of doubly exponential sequences, arXiv:2504.05933, INTEGERS 26 (2026), A28, so that bounded-negative rigidity becomes a statement about Erdős #243 itself under one added hypothesis.

**Strongest genuine longitudinal theorem.** bounded-negative complete rigidity and eventual Sylvester recurrence.

Clearing denominators in the rational case of Erdős Problem 243 produces an exact integer orbit: multipliers a n greater than 1 drive C (n+1) + D n = a n * C n and D (n+1) = a n * D n, and the centred error is E n = D n - (a n - 1) * C n. The compared theorem proves complete rigidity of the bounded-negative branch of that orbit. An eventual one-sided lower bound -B ≤ E n on the centred error, together with division-free normalized vanishing K * Int.natAbs (E n) < C n at every scale K, forces two conclusions at once: the centred error is exactly zero from some index onward, and the multipliers satisfy the exact Sylvester recurrence a (n+1) = a n ^ 2 - a n + 1 from some index onward. The second conclusion is the Sylvester recurrence itself, which is the target shape for this dynamics, so the theorem reaches that endpoint inside the stated regime. The hypothesis list contains no periodicity assumption, no eventual periodicity assumption, and no sign condition on the centred error, so the statement covers aperiodic orbits and orbits whose centred error changes sign infinitely often. The normalized-vanishing hypothesis is stated division-free over the natural numbers, so the theorem consumes no real-analytic input. Eventual strict centring Int.natAbs (E n) < C n is the K = 1 instance of normalized vanishing and is absorbed into that hypothesis. The proof runs a natural-tail descent on the eventually nonnegative branch and a gcd-stabilisation and scale-reduction obstruction on the recurring bounded-negative branch, then composes the resulting zero-defect statement with the algebraic step that turns a vanishing centred state into the Sylvester successor. The exact recurrence, the one-sided lower bound, and normalized vanishing are hypotheses of the theorem. No declaration in this package produces them for an arbitrary orbit, orbits with cofinally unbounded negative centred error lie outside the statement, and Erdős Problem 243 remains open.

Evidence: lean_kernel_checked. Prior art: extends, audited 2026-09-02; antecedent J. Koizumi, arXiv:2504.05933, Proposition 19(2) and Corollary 20(2) (Badea) (as above).

Routes: source [`ExternalVerification243BoundedNegativePartRigidity/`](ExternalVerification243BoundedNegativePartRigidity/), proof `Solutions.ExternalVerification243BoundedNegativePartRigidity`, package `ExternalVerification243BoundedNegativePartRigidity/comparator.json`; no paper label; public entry reserve.

**Best standalone structural theorem.** CRT bounded-rise barrier: a slowly rising natural state cannot avoid an infinite pairwise-coprime modulus family at every strict rise.

A natural state tending to infinity with upward increments bounded by B cannot, at every strict rise, avoid all earlier members of an infinite pairwise-coprime modulus family. The proof uses B old moduli, a shifted consecutive CRT block, and the first crossing; avoidance away from strict rises is not assumed.

No exact reduced tail u_(n+1)+v_n=a_n*u_n, v_(n+1)=a_n*v_n with gcd(u_n,v_n)=1 can have u_n tend to infinity while u_(n+1)<=u_n+B for a fixed positive B. Reduced exactness forces pairwise-coprime multipliers and permanent whole-modulus avoidance; a shifted CRT block and first-crossing argument give the contradiction.

Evidence: lean_kernel_checked. Prior art: new, audited 2026-09-02; antecedent J. Koizumi, arXiv:2504.05933, Lemma 15 (the modular recurrence e_n == d_n (mod c_n), c_{n+1} = c_n - e_n).

Routes: no Lean package in this release; no paper label; public entry not_packaged.

**Strongest unresolved producer** (`exclude_aperiodic_negative_state_orbits`). Attack the sole remaining signed-state obstruction, now quantified: any counterexample has negative excursions with -E_n > (1 - delta) log2 log2 C_n infinitely often for every delta > 0 (slow_negative_part_rigidity, counterexample_loglog_negative_excursions), with divergent normalised negative mass and with every multiplier overlap gcd(a_n, D_n) bounded by the next negative magnitude. Coprimality-only arguments are capped at O(log C_n) rises, so the producer must use the congruence E_n = D_n (mod C_n) or a second landing mechanism. Attack the sole remaining signed-state obstruction: cofinally unbounded negative excursions in the exact dynamic cocycle. Corrected unit-field propagation kills the factor-35 branch, forces eight cofinal returns on (31,-10) at factor 41, and forces four more on its (41,-20) child at factor 61. The exact formerly inert factor-25 continuation is now 1061100/292…

**Failed approaches and falsifiers.**

- Finite-prefix rules: arbitrary finite deviations can precede an exact Sylvester tail.
- Eventually periodic and eventually constant negative orbits: excluded unconditionally, so a counterexample must have aperiodic unbounded negative excursions.
- Working at the 1/n rate: the critical constant-negative template sits exactly at the boundary of Koizumi's rate theorem.
- Avoidance away from strict rises is not assumed, and the barrier alone does not force eventual Sylvester recurrence.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 243` against the frontier.

**Entries.**

- [`ExternalVerification243PeriodicNegativeOrbit/`](ExternalVerification243PeriodicNegativeOrbit/), exclusion of eventually periodic negative-magnitude orbits.
- [`ExternalVerification243BoundedNegativePartRigidity/`](ExternalVerification243BoundedNegativePartRigidity/), bounded-negative-part rigidity for reciprocal-tail dynamics.
- [`ExternalVerification243BoundedRiseReducedTail/`](ExternalVerification243BoundedRiseReducedTail/), exclusion of bounded-rise reduced tails.

```sh
lake build ExternalVerification243PeriodicNegativeOrbit Solutions.ExternalVerification243PeriodicNegativeOrbit
lake build ExternalVerification243BoundedNegativePartRigidity Solutions.ExternalVerification243BoundedNegativePartRigidity
lake build ExternalVerification243BoundedRiseReducedTail Solutions.ExternalVerification243BoundedRiseReducedTail
```

## Erdős #1041

**The question.** If a monic polynomial f(z)=product_i(z-z_i) has all roots in the open unit disk, prove that two roots can be joined by a curve of length less than 2 contained in the open lemniscate |f|<1.

**What the release proves.** ExternalVerification1041FirstMergeCriticalValueSeparation proves the exact all-degree critical-value separation thresholds C(n, 4) < 1 for every n at least 3, C(n, 3) < 1 for every n at least 4, and C(n, 2) < 1 for every n at least 6, where C(n, S) = (1 + S)^(2/n) log(S/(S - 1)), together with the sign-free consumer that a squared length at most 4 C(n, S) with C(n, S) < 1 forces length strictly below 2.

**Where it is stuck.** The sharp constant is settled in every degree only under the critical-spectrum separation hypothesis, and the two surviving unconditional routes are the componentwise combined-charge lemma, that every nontrivial connected component C of the admissible critical forest satisfies the sum over edges e in C of D_e + K_e being at least 0, and the covering statement COVER, that for monic g with roots in the closed unit disk there is a level lambda in [mu, 1] and a compact connected subset Gamma of the first-merge component of {|g| <= lambda} carrying two roots with every point of Gamma within intrinsic distance 1 of a root.

**Smallest useful contribution** (computation). Re-run the degree-five moment computation with directed rounding rather than IEEE double arithmetic, which converts the fifth arithmetic-mean strengthening into a certificate-backed statement and opens the sixth.

**Strongest genuine longitudinal theorem.** Unconditional all-degree regime: least critical value at most 13/25, via the circle-slice angular packing floor.

{'op': 'substring_replace', 'find': 'Certificate: full mode (step 1/400, 12 grid areas, 14 radii per dual, 7 arities, 126 certified duals, 13.5 minutes) X_cert = 317881444799/500000000000 < 0.6357629 and (13/25) exp(X_cert) < 1; quick mode (101 s) certifies 51/100 with X_cert < 0.664374.', 'replace': 'Certificate: full mode (step 1/400, 18 area-table levels, 14 radii per dual, 7 arities, 126 certified duals, single initial lower area 1e-6, about 13.5 minutes) X_cert = 635762889599/1000000000000 < 0.6357629 and (13/25) exp(X_cert) < 1; quick mode certifies 51/100 with X_cert = 664373027131/1000000000000 < 0.664374.'}

Evidence: ordinary_proof. elementary hyperbolic packing lemma (disjoint balls cut disjoint arcs from every circle about the observer) with an LP-proposed, exactly-disposed dual floor; full-mode exact rational certificate X_cert < 0.6357629 (13.5 min) and quick-mode 51/100 (101 s, conductor replayed rc=0); conductor read the lemma, the dual and the checker's branch-and-bound sup bound; not Lean-checked, not independently reviewed. Prior art: unassessed, no audit date.

Routes: no Lean package in this release; no paper label; public entry not_packaged.

**Best standalone structural theorem.** sharp all-degree collinear root-diameter theorem with equality configurations, complete primitive sparse quintic, and translated cubic quotient fibres.

The accompanying ordinary mathematics completely solves three structured families of Erdős #1041: collinear root configurations in every degree, the primitive sparse quintics, and translated cubic quotient fibres in every degree 3q with q at least two. This configuration verifies in Lean the three load-bearing kernels of those solutions, and only those three. For every degree n at least two, a monic polynomial of degree n vanishing at -1 and 1, with n-1 increasing interior nodes in the closed interval and values alternating in sign along them, has one node at which the absolute value is at most 2^-(n-1) times cos(pi/2n)^-n. Five real disk coordinates satisfying the first three rotated Newton moments for r strictly between 0 and 2 contain two distinct indices whose tail energy is strictly below one, and three roots in the open unit disc admit one complete radial spoke along which their monic cubic stays inside the closed unit lemniscate. Each family solution is reduced to a single finite inequality, so the delicate step in the geometry of polynomial sublevel sets is the part submitted for checking. The alternation argument sits in the classical Chebyshev context, a bounded search found no earlier form of the quintic selector, and priority is unresolved. Affine transport, the final selection, and the surrounding analytic assembly are ordinary proofs rather than Lean-checked conclusions, and the unrestricted problem is untouched.

Evidence: lean_kernel_checked. Prior art: unknown, no audit date; antecedent The alternation argument sits in the classical Chebyshev context; a bounded search found no earlier form of the quintic selector (entry metadata).

Routes: source [`ExternalVerification1041SolvedFamilies/`](ExternalVerification1041SolvedFamilies/), proof `Solutions.ExternalVerification1041SolvedFamilies`, package `ExternalVerification1041SolvedFamilies/comparator.json`; paper labels `thm:sharp-collinear-diameter`, `prop:sharp-collinear-chebyshev-comparator`, `thm:primitive-quintic-two-tail`, `prop:primitive-quintic-two-tail-energy-selector`, `thm:translated-cubic-quotient-fibres`, `lem:cubic-safe-root-spoke`, `bdry:solved-polynomial-families`, `rem:sharp-collinear-formal-boundary`, `rem:primitive-quintic-formal-boundary`, `rem:cubic-quotient-formal-boundary`; public entry launch_core.

**Strongest unresolved producer** (`one_root_covering_of_the_first_merge_component`). Prove (COVER): for monic g with roots in the closed unit disk there is a level lambda in [mu,1] and a compact CONNECTED subset Gamma of the first-merge component of {|g| <= lambda} carrying two roots, such that every point of Gamma lies within intrinsic distance 1 of a root of g, paths being allowed to run in the whole component. By visibility_overlap_reduction_to_a_one_root_statement this settles Erdos #1041, with no separate length obligation. Take Gamma as SMALL as possible and the ambient as LARGE as possible: the cheapest Gamma is the descending Newton branch pair from c*, on which the covering was measured in its strongest form -- straight segments at level 1 -- with zero uncovered points over 26 scored rows at 283 points per arc, at least 155 overlap points per row, and worst overlap length 1.90422 against a budget of 2. Two guards are mandatory: the level is NOT monotone, so nev…

**Failed approaches and falsifiers.**

- Universal scalar saddle-wall thresholds T ≤ 2√2(βγ)^{1/2n}: false for the actual wall of (z²−a²)(z²+b²).
- Least-critical nearest-pair hub selectors: refuted in the quartic fixed-pair no-go (CEGMQuarticFixedPairNoGo.md).
- Separate critical contours for resolved critical stars: a negative result for the monodromy route.
- The shtuka tree-budget proposition: the Cassini level-length tail 4(√(a²+a) − a) falls below the root distance 2a for a > 4/5 (recorded countermodel, not re-derived on 2026-09-02).
- The consecutive-gap angular budget is proved empty; the mechanism cannot pass mu ~ 0.545 with any arity floor; the exterior energy has no failure-derived floor.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 1041` against the frontier.

**Entries.**

- [`ExternalVerification1041FirstMergeCriticalValueSeparation/`](ExternalVerification1041FirstMergeCriticalValueSeparation/), exact all-degree critical-value separation thresholds and a sign-free first-merge length bound.
- [`ExternalVerification1041CriticalGeometry/`](ExternalVerification1041CriticalGeometry/), global two-root critical proximity and exact straight-line obstructions.
- [`ExternalVerification1041CollinearChord/`](ExternalVerification1041CollinearChord/), straight-chord selection from quantitative collinear critical-gap data.
- [`ExternalVerification1041CyclicTrinomialFiber/`](ExternalVerification1041CyclicTrinomialFiber/), sublevel containment of trinomial root spokes.
- [`ExternalVerification1041DiskFamilySeparation/`](ExternalVerification1041DiskFamilySeparation/), uniform disk-family critical-value separation thresholds and a sign-free connector-length bound.
- [`ExternalVerification1041QuarticQuotientFiber/`](ExternalVerification1041QuarticQuotientFiber/), strict length budget below two for quotient-fibre root lifts.
- [`ExternalVerification1041SolvedFamilies/`](ExternalVerification1041SolvedFamilies/), checked kernels for three completely solved polynomial families.
- [`ExternalVerification1041TetranomialSpokes/`](ExternalVerification1041TetranomialSpokes/), coefficient and energy criteria forcing two safe tetranomial spokes.

```sh
lake build ExternalVerification1041FirstMergeCriticalValueSeparation Solutions.ExternalVerification1041FirstMergeCriticalValueSeparation
lake build ExternalVerification1041CriticalGeometry Solutions.ExternalVerification1041CriticalGeometry
lake build ExternalVerification1041CollinearChord Solutions.ExternalVerification1041CollinearChord
lake build ExternalVerification1041CyclicTrinomialFiber Solutions.ExternalVerification1041CyclicTrinomialFiber
lake build ExternalVerification1041DiskFamilySeparation Solutions.ExternalVerification1041DiskFamilySeparation
lake build ExternalVerification1041QuarticQuotientFiber Solutions.ExternalVerification1041QuarticQuotientFiber
lake build ExternalVerification1041SolvedFamilies Solutions.ExternalVerification1041SolvedFamilies
lake build ExternalVerification1041TetranomialSpokes Solutions.ExternalVerification1041TetranomialSpokes
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
