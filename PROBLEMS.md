# Problems, and where each one is stuck

This repository is a corpus to work in. Clone it, choose a live mathematical
obstruction below, and either prove it, falsify the route that is proposed for it,
or improve the machinery that makes the result checkable. Every section names the
strongest theorem the release carries for that problem, the exact unresolved step,
and the smallest contribution that would move it.

The unrestricted parent problems are open. Sections run in the order a reader meets
them in `README.md`.

Two public repositories carry this work, with different roles. wcook04/plectis-erdos-lean is the Plectis Palomar release corpus (Palomar release corpus: eight problem-level Palomar entries under PalomarCorpus/E* selecting 317 theorems, over 38 launch family entries, eight problems), a release projection of the private corpus; the reviewed claim registry stays in wcook04/plectis-lean-erdos249-257 at one commit. wcook04/plectis-lean-erdos249-257 is the Plectis public formal-mathematics corpus: the reviewed claim registry (docs/claims.json), the declaration atlas and the papers live there, and this release repository is its Comparator and Palomar projection at one commit. A packaged Comparator entry is a review unit, never a theorem, a curated claim, or a problem. Entry counts never compose with declaration counts from the other corpus.

## Erdős #257

**The question.** Prove irrationality of sum_{n in A} 1/(2^n-1) for every infinite support A.

**Best substantive result.** Finite prime-part weighted mass gives fixed-base irrationality, and finite binary weighted mass on a host gives hereditary irrationality at every integer base at least two for every infinite subhost. Beyond that checked class, an ordinary delayed-gluing theorem constructs a reciprocal-divergent hereditary all-base irrational host outside every finite mixture of the weighted and strengthened-cover classes, even after finite unions of fixed dilates of prime powers and finite modifications.

**What this achieves.** The weighted theorem is a complete Lean-checked sufficient class with explicit reciprocal-divergent short-gap examples, so it goes strictly beyond the classical reciprocal-summable regime. Delayed gluing then proves that the current finite sufficient-class taxonomy is not the end of the method. The sub-log-star theorem remains a separate quantitative route: rational p/q forces a positive liminf lower bound for reciprocal mass, and this criterion is incomparable with weighted mass rather than a weaker corollary.

**Remaining boundary.** Universal Erdős 257 and the rational targets 1/2 and 1/21 remain open. The weighted, cover, prime-power, sub-log-star, mixed, and delayed-gluing results cover proper support classes or freely constructed hosts. The reciprocal-summable theorem proves by an independent argument the coprimality-free extension Erdős stated without printing a proof; the statement is his, and no identification with his omitted argument is asserted. The arbitrary prime-power result uses Tao-Teräväinen's correlation theorem and has unverified priority for its arbitrary-selection extension.

Evidence: lean_kernel_checked. Routes: compared in the Palomar entry `PalomarCorpus/E257` as `DivisibilityWeightedSupport.divisibilityWeightedClaim`; proof source [`WeightedReturn.lean`](ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean); paper label `eq:weighted-return`; public entry PalomarCorpus/E257.

**Strongest genuine longitudinal theorem.** Finite divisibility-weighted mass implies hereditary all-base irrationality, including explicit reciprocal-divergent short-gap supports..

Finite prime-part weighted mass gives fixed-base irrationality and, at binary weighted mass, hereditary irrationality for every infinite subhost at every integer base at least two.

Evidence: lean_kernel_checked. Prior art: unassessed, no audit date.

Routes: compared in the Palomar entry `PalomarCorpus/E257` as `DivisibilityWeightedSupport.divisibilityWeightedClaim`; proof source [`WeightedReturn.lean`](ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean); paper label `eq:weighted-return`; public entry PalomarCorpus/E257.

**Best standalone structural theorem.** achievement-set topology and exact volume dichotomy.

A supported Mersenne achievement set is the set of reals coded by binary strings whose support lies in a fixed set J of allowed digit positions, where digit position k contributes the Mersenne weight 1 / (2^(k+1) - 1). The original support and rational-fibre declarations are retained. The first is a measure no-go on rational fibres. If 0 is not in J and the sum of 1 / (2^m - 1) over m in J is a rational number, the achievement set supported on J has Lebesgue measure zero. Positive-measure selection over a rational fibre is excluded by that measure-zero conclusion. An exceptional null point stays unexcluded. In that first declaration the set J indexes exponents in the hypothesis and digit positions in the conclusion. The second declaration classifies the whole family, with no hypothesis on J. The supported digit map is injective, its range is compact, its range is nowhere dense, the range is perfect whenever J is infinite, and the Lebesgue measure of the range satisfies an exact dichotomy: when the omitted digit positions form a finite set F the measure is the reciprocal of 2^|F|, and when infinitely many digit positions are omitted the measure is zero. Both statements are proved for the literal Mathlib-only definitions repeated in the Challenge module. The compared declarations establish no irrationality of any infinite Mersenne subseries, and Erdős Problem 257 remains open. The extended selection also includes the full achievement geometry with exact span and relative-density bounds, a finite-prefix nonmembership criterion with an explicit tail upper bound, and exclusion of the entire interval (2/3,1). These do not imply universal subseries irrationality.

Evidence: lean_kernel_checked. Prior art: classical_input_disclosed, no audit date; antecedent Kakeya (1914) and Kovač-Tao Remark 4.1 own compact/perfect/totally disconnected/nowhere dense; the exact measure dichotomy is presented as added.

Routes: source [`ExternalVerification257AchievementSetGeometry/`](ExternalVerification257AchievementSetGeometry/), proof `Solutions.ExternalVerification257AchievementSetGeometry`, package `ExternalVerification257AchievementSetGeometry/comparator.json`; proof source [`MersenneSubseriesRigidity.lean`](ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean); no paper label; public entry launch_core.

**Strongest unresolved producer** (`contradict_twenty_one_permanent_affine_supercapacity`). Contradict the exact permanent affine-supercapacity regime forced by TwentyOneFatalAlignedBranch. Commit bad43508 proves that any unbounded sequence of closed canonical rows s_R<=2^R already gives the compactness decay required for 1/21 membership, so the fatal branch must eventually satisfy 2^R<s_R at every rank. Combined with commit f23727a, the boundary coin is then always taken: support appends R+1 and the scalar follows one literal affine recurrence with no residual Boolean branch. Commit 73f417a additionally proves that an aligned crossing from exact saturation into strict supercapacity must occur at R=3a+2 and omit a canonical ancestor at a+1 or 2(a+1). This restricts one entrance mechanism but does not show that the fatal branch enters late from exact saturation or contradict the regime after entry. …

**Failed approaches and falsifiers.**

- Any counterexample support must have divergent reciprocal sum; every candidate support with summable reciprocals is now excluded at every integer base.
- Powerful supports as an independent contribution: subsumed by the reciprocal-summable theorem and removed from public lanes.
- The 4/9 modulus-84 2-3-7 causal producer: false despite explaining all eight observed repair-gap rescues.
- The actual modulus-420 tetraprime repair producer is false at arbitrarily large prime cofactors. EightReturnSynthesis.md section 3 supplies the proof from an exact 80-anchor selected prefix and Dirichlet; the new audit gives jumps >=2 and causal-margin failures >=3. This supersedes the earlier fifty-million finite survival evidence. Unrestricted cofinal repairs remain open.
- A theorem for finite-prime weighted supports does not cover an arbitrary infinite support or decide the fixed rational targets.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 257` against the frontier.

**What the release proves.** ExternalVerification257ReciprocalSupport proves that for every infinite exponent set A whose reciprocal sum converges and every integer base b at least two, the series with terms 1/(b^a - 1) supported on A is irrational, with no coprimality, periodicity, density or powerful-support hypothesis.

**Where it is stuck.** Every candidate counterexample support now has divergent reciprocal sum, and the surviving fatal branch at the rational target 1/21 is consistent with a permanent affine supercapacity regime, so no theorem forces the cofinal closed returns that would decide membership.

**Smallest useful contribution** (proof). Formalise the 1/3 certificate lemma as an inequality chain of roughly two hundred lines, after which finite certificates decide an individual support and rational-target pair.

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

## Erdős #249

**The question.** Prove that the binary totient series sum_{n>=1} phi(n)/2^n is irrational.

**Best substantive result.** If S = sum_(n>=1) phi(n)/2^n is not irrational, then there are v > 0 and an integral tempered carry u for phi such that, for every e, the rational span of its canonical depth-e carry sections has rank at least 2^e - 1, while the same carry is eventually periodic modulo v with one fixed positive period.

**What this achieves.** Hypothetical rationality is converted into two simultaneous rigid consequences: exponential all-level section-rank growth and a uniform modular period. This exposes a concrete incompatibility to prove and is more informative than an exact Mersenne-residue reformulation of irrationality.

**Remaining boundary.** No theorem turns eventual periodicity modulo v into finite rational rank, so no contradiction or irrationality theorem follows. The carry-rank route's priority remains unassessed.

Evidence: lean_kernel_checked. Routes: packaged privately, not in this release; proof source [`TotientTailCarryPeriod.lean`](Erdos257PeriodNoncollapse/TotientTailCarryPeriod.lean); proof source [`TotientCarryKernelRigidity.lean`](Erdos257PeriodNoncollapse/TotientCarryKernelRigidity.lean); proof source [`GenericTailOrbitRigidity.lean`](Erdos257PeriodNoncollapse/GenericTailOrbitRigidity.lean); no paper label; public entry reserve.

**Best standalone structural theorem.** explicit odd-core basis, full-span equality, canonical finite normal form, and exact ranks.

The two zero-residue base channels and one odd-residue channel at each positive dyadic level form a linearly independent spanning family for all dyadic sections of Euler's totient. The complete family through level e has the same span as the duplicate-free canonical truncation and exact rank 2^e+1. This unconditional structural theorem does not prove irrationality of the binary totient series.

Evidence: lean_kernel_checked. Prior art: extends, audited 2026-09-02; antecedent M. Coons, (Non)Automaticity of number theoretic functions, J. Theor. Nombres Bordeaux 22 (2010), no. 2, 339-352 (Theorem 3.2, proof printed p. 349; k-kernel definition in Section 1).

Routes: source [`ExternalVerification249DyadicTotientKernel/`](ExternalVerification249DyadicTotientKernel/), proof `Solutions.ExternalVerification249DyadicTotientKernel`, package `ExternalVerification249DyadicTotientKernel/comparator.json`; proof source [`TotientMahlerDefect.lean`](Erdos257PeriodNoncollapse/TotientMahlerDefect.lean); no paper label; public entry launch_core.

**Strongest unresolved producer** (`totient_specific_moving_dyadic_escape`). Prove FullMersenneCanonicalBasepointResidueGapSupply, the Lean-equivalent arithmetic normal form: for every c and positive odd v, find H>0 divisible by phi(v) such that the canonical residue (-totientBlock(H,c)) mod ((2^H-1)/v) lies in the central interval of radius c+H+1. On the pure-dyadic axis, the Lean-checked signed error E_H=totientBlock(H,c)-k(2^H-1) obeys E_(H+1)=2E_H+phi(c+H+1)-k while the nearest quotient k stays fixed. Exact computation through c<=1000000 finds delay nineteen at c=490794, ruling out caps through seventeen. Pointwise legal-letter methods, the constant-two mode, sublinear errors, and every eventually affine linear-scale error are eliminated. Actual prime positions cofinally force linear excursions; …

**Failed approaches and falsifiers.**

- Uniform bounds ‖v·2^c·S‖ ≥ c^{−A}: impossible for irrational S because odd multiples of 2^c S are dense mod 1.
- Coprime restriction with Stern-Brocot splitting and geometric decay: the visible-lattice sum ∑_{gcd(a,b)=1} 1/(2^{a+b}−1) equals exactly 1, so it cannot force irrationality.
- Positive rank-one Schur blocks: every admissible quotient sits at least 21/320 above Θ₂ (unique minimiser (1,5)).
- Nonnegative Stieltjes representations of the Möbius-Mersenne ladder: strict log-concavity at every rung r at least 1.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 249` against the frontier.

**What the release proves.** ExternalVerification249RankOneSharpFloor proves that every admissible rank-one quotient exceeds the Möbius Mersenne rung by more than 21/320, that the minimum is attained at a unique admissible pair, and that 1/16 is the largest unit fraction bounding the gap from below.

**Where it is stuck.** Irrationality of the binary totient series is equivalent in Lean to a residue-gap supply statement, that for every c and every positive odd v there exists H > 0 divisible by phi(v) whose canonical totient-block residue modulo (2^H - 1)/v lies in the central interval of radius c + H + 1, and no construction supplies that H.

**Smallest useful contribution** (literature). Test whether the Padé construction of Duverney and Tachiya for Lambert series survives a bounded non-periodic Möbius weight, and record the exact step at which it fails.

**Entries.**

- [`ExternalVerification249RankOneSharpFloor/`](ExternalVerification249RankOneSharpFloor/), sharp minimiser and explicit 21/320 floor for the positive rank-one Möbius Mersenne cone.
- [`ExternalVerification249ResidueClassTotientSeries/`](ExternalVerification249ResidueClassTotientSeries/), irrationality of fixed-resolution observables of the totient word.
- [`ExternalVerification249BinaryCyclotomicAnchors/`](ExternalVerification249BinaryCyclotomicAnchors/), unconditional clean prime anchors in the binary cyclotomic layers.
- [`ExternalVerification249DyadicTotientKernel/`](ExternalVerification249DyadicTotientKernel/), complete dyadic totient-kernel structure.
- [`ExternalVerification249MobiusMersenneLadderStructure/`](ExternalVerification249MobiusMersenneLadderStructure/), no finite linear recurrence for the Möbius-Mersenne power ladder, and its separation from the literal Möbius-Lambert ladder.
- [`ExternalVerification249ParityPerturbedRationalControl/`](ExternalVerification249ParityPerturbedRationalControl/), a parity-perturbed rational control for the binary totient series.
- [`ExternalVerification249TotientKernelBasis/`](ExternalVerification249TotientKernelBasis/), all-base totient kernel dimension, canonical basis and relation module.

```sh
lake build ExternalVerification249RankOneSharpFloor Solutions.ExternalVerification249RankOneSharpFloor
lake build ExternalVerification249ResidueClassTotientSeries Solutions.ExternalVerification249ResidueClassTotientSeries
lake build ExternalVerification249BinaryCyclotomicAnchors Solutions.ExternalVerification249BinaryCyclotomicAnchors
lake build ExternalVerification249DyadicTotientKernel Solutions.ExternalVerification249DyadicTotientKernel
lake build ExternalVerification249MobiusMersenneLadderStructure Solutions.ExternalVerification249MobiusMersenneLadderStructure
lake build ExternalVerification249ParityPerturbedRationalControl Solutions.ExternalVerification249ParityPerturbedRationalControl
lake build ExternalVerification249TotientKernelBasis Solutions.ExternalVerification249TotientKernelBasis
```

## Erdős #251

**The question.** Prove irrationality of the dyadic series built from consecutive prime gaps.

**Best substantive result.** For h >= 2, the number of indices n < N with g_(n+h) - g_n = r is bounded, up to the explicit factor H+1, by a large-span term and the count of an explicit separated four-prime configuration. The stated quadruple-sieve estimate would therefore force zero density of these shifted-gap coincidences.

**What this achieves.** This converts an actual-prime shifted-gap obstruction into a concrete four-prime counting problem, discharging the combinatorial encoding and large-span contribution instead of merely introducing an actual-tail state. It gives analytic number theory a named remaining input.

**Remaining boundary.** The quadruple-sieve estimate is an explicit unproved hypothesis, the h=1 case degenerates, and zero density of exact shifted-gap matches is not yet connected to the tail-smallness event needed to contradict rationality. Erdős #251 remains open.

Evidence: lean_kernel_checked. Routes: compared in the Palomar entry `PalomarCorpus/E251`; no paper label; public entry PalomarCorpus/E251.

**Best standalone structural theorem.** A rational logarithmic dyadic word with small digits recurring in every residue class and PNT-scale cumulative growth.

Explicit synthetic positive even logarithmically bounded digits, 2 and 4 recurring in every index residue, cofinal unboundedness, nonperiodicity, strictly increasing odd positions with N log N asymptotic, dyadic sum 6 and integral tail shifts. No primality assertion or counterexample to Erdos251. For all t>0,r<t,N, there are i,j>=N congruent to r mod t with digits2and4. Every positive shift fails to be an eventual period. Every N,h>=0 has integral complete-tail difference. The pointwise bound is4 log(n+1)+24 and position/(N logN) tends to1.

Evidence: lean_kernel_checked. The focused build passed with unchanged proof inputs and the three endpoint axiom audits are clean; the theorem is selected by the Palomar entry `PalomarCorpus/E251`, whose Comparator replay runs in `.github/workflows/palomar-replay.yml`. Prior art: unassessed, audited 2026-09-02; antecedent Vjeko Kovač posted a telescoping countermodel of the same broad species for the neighbouring conjecture printed under #251 in April 2026; priority for this exact every-residue logarithmic form is unassessed..

Routes: compared in the Palomar entry `PalomarCorpus/E251`; no paper label; public entry PalomarCorpus/E251.

**Strongest unresolved producer** (`cofinal_adjacent_small_mismatch`). For each fixed h >= 1 and every N0, produce N >= N0 such that both actual tail shifts T_(N+h)-T_N and T_(N+h+1)-T_(N+1) lie strictly between -1 and 1 while g_(N+h+1) != g_(N+1). The checked finite consumer then excludes eventual integrality of the h-shift. The quantifier is every positive h, not only h=1. Digit mismatch and smallness are a joint event. A preferred unproved substitute is a positive finite phase-variance lower bound V_t(X,L) on the schedule t=lcm(1..floor(log log X)), L~(1+ε)log_2 log X (PhaseVarianceLab.md); that lower bound is not proved. r5 sparse rationalisation preserves all unnormalised blocks of length o(log log X) and therefore does not supply this joint event; a distinguishing actual-prime estimate must exceed the block-change error or use a longer window. r6 residue-feedback / sharp δ_* construction is a stronger countermodel in the polylogarithmic regime; …

**Failed approaches and falsifiers.**

- Coarse gap properties (positive, even, increasing, unbounded, nonperiodic): the word g_n = 2(n²+4n+2) satisfies all of them, has rational value 32, and never produces an adjacent small mismatch.
- State compression by word repetition alone: the margin is recorded so the lane is not re-walked.
- Liouville-flavoured attacks: a finite continued-fraction expansion yields a local exponent-style witness 2.0007, which is not an irrationality-exponent theorem.
- The word is synthetic and is not the consecutive-prime-gap word; it supplies no actual-prime theorem and does not decide Erdős #251.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 251` against the frontier.

**What the release proves.** ExternalVerification251PolynomialShiftCountermodel exhibits the explicit digit word g(n) = 2(n^2 + 4n + 2) with orbit T(n) = 2(n + 4)^2, which satisfies the dyadic tail recurrence at every index, is positive, even, strictly increasing, unbounded and nonperiodic, has every fixed tail shift integral, and has every adjacent difference past the first term at least fourteen.

**Where it is stuck.** The remaining producer is the cofinal adjacent small mismatch, that for each fixed h at least 1 and every N0 there is an index N at least N0 at which T(N+h) - T(N) and T(N+h+1) - T(N+1) both lie strictly between -1 and 1 while g(N+h+1) differs from g(N+1).

**Smallest useful contribution** (proof). Supply the h = 1 cofinal adjacent-small-mismatch producer from actual consecutive-prime arithmetic. Coarse gap properties cannot supply it (the polynomial countermodel), and the measured event density of 0.0042 to 0.0082 over 6.8 million primes is finite evidence only. Establishing the adjacent-small-mismatch condition for h=1 would settle one useful case of the open producer. The full tail-shift route to irrationality requires the corresponding condition for every fixed positive h; the h=1 case alone does not complete it.

**Entries.**

- [`ExternalVerification251PolynomialShiftCountermodel/`](ExternalVerification251PolynomialShiftCountermodel/), exact countermodel to coarse gap-profile irrationality routes.
- [`ExternalVerification251PrimeGapIdentity/`](ExternalVerification251PrimeGapIdentity/), unconditional prime-gap reformulation of the dyadic prime series.
- [`ExternalVerification251ActualPrimeGapTail/`](ExternalVerification251ActualPrimeGapTail/), exact rational-tail collapse for the actual prime-gap dyadic series.
- [`ExternalVerification251BoundedPerturbationCountermodel/`](ExternalVerification251BoundedPerturbationCountermodel/), bounded-perturbation countermodel anchored at the actual prime gaps.
- [`ExternalVerification251FreePairEquivalence/`](ExternalVerification251FreePairEquivalence/), free-pair equivalence for the actual prime-gap dyadic series.
- [`ExternalVerification251KernelDenominatorFloor/`](ExternalVerification251KernelDenominatorFloor/), kernel-decided denominator floor for the prime-gap dyadic series.

```sh
lake build ExternalVerification251PolynomialShiftCountermodel Solutions.ExternalVerification251PolynomialShiftCountermodel
lake build ExternalVerification251PrimeGapIdentity Solutions.ExternalVerification251PrimeGapIdentity
lake build ExternalVerification251ActualPrimeGapTail Solutions.ExternalVerification251ActualPrimeGapTail
lake build ExternalVerification251BoundedPerturbationCountermodel Solutions.ExternalVerification251BoundedPerturbationCountermodel
lake build ExternalVerification251FreePairEquivalence Solutions.ExternalVerification251FreePairEquivalence
lake build ExternalVerification251KernelDenominatorFloor Solutions.ExternalVerification251KernelDenominatorFloor
```

## Erdős #1049

**The question.** Determine irrationality of the rational-base Lambert values, with 3/2 as the first resistant explicit base.

**Best substantive result.** For coprime integers a>b>=1 with b^mu<a, mu=2.464978683574975..., the Lambert value F(a/b) is irrational. In particular F(31/4) and F((31/4)^r) are irrational for every r>=1.

**What this achieves.** This is an endpoint irrationality theorem on an infinite rational-base strip beyond the published Bundschuh-Vaananen threshold, with 31/4 an explicit new base. The repository's contribution is the rational homogenisation, positivity and limit argument, explicit constant, and consequences. Zudilin owns the hypergeometric forms and Lemma 7, Bundschuh-Vaananen own the earlier rational-height framework, and Zudilin 2016 announced the shape with an unspecified constant.

**Remaining boundary.** The region theorem is an ordinary complete proof citing published lemmas, not a kernel-checked theorem. Its finite Lean support must be split: ZudilinHeightRegion has source-backed checked subregion facts, while RationalBaseContour's former build receipt is absent and remains reported prior. The theorem does not reach F(3/2), negative bases, or bases outside the region. Independent specialist review remains open; the internal adversary is complete and the theorem survived it.

Evidence: ordinary_proof. Routes: no dedicated comparator entry in this release; proof source [`RationalBaseContour.lean`](ErdosProblems/Erdos1049/RationalBaseContour.lean); proof source [`ZudilinHeightRegion.lean`](ErdosProblems/Erdos1049/ZudilinHeightRegion.lean); no paper label; public entry not_packaged.

**Strongest genuine longitudinal theorem.** F(a/b) is irrational on the region b^mu < a, mu = 2.46497868...; 31/4 is the first new base.

THEOREM A (region). Let a > b >= 1 be coprime integers with b^mu < a, mu = C_1/C_0 = 2.464978683574975037454488275535521581878..., equivalently log b / log a < theta* = 1/mu = 0.40568302138406054101566030557693017464819107867787.... Then F(a/b) = sum_{m>=1} 1/((a/b)^m - 1) is irrational. In the normalisation of Zudilin 2016 Sec. 2 (p = r/s, log|r| > c log|s|) the constant is c = mu, the irrationality-exponent bound of Zudilin 2004 Theorem 1 itself. Consequences: the strip s^mu < r < s^{mu_BV} (mu_BV = 2 pi^2/(pi^2-2) = 2.508284761994...) of bases beyond Bundschuh-Vaananen 1994 Theorem 2 is infinite; new bases with s <= 12 are 31/4; 53/5, 54/5, 56/5; 83/6, 85/6, 89/6; 122/7,...,131/7 (9 bases); 169/8,...,183/8 (odd r, 8 bases); 15, 12, 37, 17 bases for s = 9, 10, 11, 12; none for s = 2, 3. 31/4 is the new base of smallest denominator and smallest numerator. Among coprime a/b with a <= 60 the region has 137 members; closest misses 52/5 (theta = 0.407324), 51/5, 29/4 (0.411694); tightest members 53/5 (margin 0.000313), 31/4 (0.001985), 54/5.

THEOREM B. F(31/4) is irrational, and so is F((31/4)^r) for every integer r >= 1. Here log 4 / log 31 = 0.4036981731... < 81/200 < theta*, 4^mu = 30.4835... < 31 < 4^{mu_BV} = 32.3696..., so 31/4 lies outside the Bundschuh-Vaananen region and inside Theorem A's; it is the first base (smallest denominator and numerator) beyond the published region.

Evidence: ordinary_proof. Ordinary complete proof citing Zudilin 2004 Lemma 7 in its polynomial reading together with the inputs of that lemma's proof: Lemma 3, Lemma 4's exponent (16), Lemma 5, and identities (9)-(11). Lemmas 1 and 2 are not in the final citation set. The analytic theorem is not kernel-checked. ZudilinHeightRegion supplies source-backed Lean checks of the 81/200 power certificate and subregion membership. RationalBaseContour contains the stronger contour declarations, but its former build and axiom receipt is not present on the audited surface, so that verification remains reported prior. The independent 2026-09-02 adversary checked eight attack points; Theorems A and B survived.. Prior art: extends, audited 2026-09-02; antecedent P. Bundschuh and K. Vaananen, Arithmetical investigations of a certain infinite product, Compositio Math. 91 (1994), 175-199 (Theorem 2, second half (alpha = -1 case), printed p. 177; identification L_q(alpha) with the q-harmonic series also p. 177).

Routes: no dedicated comparator entry in this release; proof source [`RationalBaseContour.lean`](ErdosProblems/Erdos1049/RationalBaseContour.lean); proof source [`ZudilinHeightRegion.lean`](ErdosProblems/Erdos1049/ZudilinHeightRegion.lean); no paper label; public entry not_packaged.

**Best standalone structural theorem.** The q-order N(N-1)(2N-1)/6 and the leading coefficient (N!)^2(N+1)!/2^N of Zudilin's normalized Hankel determinant at every rank.

For every rank N, Zudilin's normalized Hankel determinant V_N^* at x=z=1 has q-order N(N-1)(2N-1)/6 and leading coefficient (N!)^2(N+1)!/2^N. The normalized moments and the determinant are Zudilin's construction (Acta Arith. 111 (2004); Res. Number Theory 2 (2016), Art. 15), and Zudilin 2016, Section 4, proves that the q-order is at least N(N-1)(2N-1)/6. The Lean proof in [`AllRow/Producer.lean`](ErdosProblems/Erdos1049/AllRow/Producer.lean) supplies the initial monomial of every transformed row and composes it with the determinant deduction in [`ZudilinSharpHankelCoefficient.lean`](ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean); exact integer power-series computation agrees at ranks 1 through 7.

Evidence: lean_kernel_checked. The two statements are compared in [`PalomarCorpus/E1049`](PalomarCorpus/E1049/) against a Challenge that restates the normalized moments, the Hankel matrix and its determinant over Mathlib alone, and they depend on the axioms propext, Classical.choice and Quot.sound only. Prior art audited 2026-09-02; antecedent W. Zudilin, On the irrationality of generalized q-logarithm, Res. Number Theory 2 (2016), Art. 15, arXiv:1601.02688 (Section 4 (source.tex lines 278-305): "the q-expansion of V_n^* starts from at least q^{n(n-1)(2n-1)/6}").

Routes: Comparator entry [`PalomarCorpus/E1049`](PalomarCorpus/E1049/) as `PalomarCorpus.E1049.AdelicHeightBridge.zudilinSharpHankelOrderAndCoeff_all` and `PalomarCorpus.E1049.AdelicHeightBridge.coeff_zudilinNormalizedHankelDet_all_rat`; proof source [`AllRow/Producer.lean`](ErdosProblems/Erdos1049/AllRow/Producer.lean); paper labels `res:zudilin-sharp-qorder`, `sec:hankel-order`.

**Strongest unresolved producer** (`three_halves_pade_height_gap`). The fixed-prime route is conditional, not an unconditional closure of step 1. The finite harmonic descent gives J_5={4,20,24} by the two-line descent lemma plus an empty level-three check, with eps=v_5(3^2-2^2)=1 and loss blocks [8,9],[40,41],[48,49]. If the all-level q-Apery monodromy/continuity premise (M)/(C5) holds, the weighted transfer gives 5 | B_j for every j >= 50 and hence a window gcd divisible by 5^(1+floor(log_5(s/2))) for every start s >= 50. The premise is certified only at N<=3 and over the finite indices recorded in FixedPrimeInfiniteTailProof.md, so the available evidence does not prove an all-index q-Apery denominator tail or unconditionally close the window-divisor substep. No first-appearance prime, factoring of 3^s-2^s, or effective form of Boyd's heuristic is needed under that explicit conditional premise. …

**Failed approaches and falsifiers.**

- Scalar q-Apery Pade family at 3/2: quantitatively dead by a fixed positive proportion at every index, with the shortfall in closed form.
- Rectangular two-function Hermite-Pade thresholds: at most 1/2-1/pi^2 on the whole admissible cone rho>=0, sigma>=1+rho, with equality only at (0,1).
- Scalar content and scalar-plus-border extraction from Zudilin's Hankel determinant: neither can meet the required charge under the proved class assumptions.
- Changing Van Assche's outward scalar evaluation alone leaves a positive forced-clearing main term at 3/2; clearing-supported primitive common content remains the precise scalar escape hatch.
- The theorem says nothing about F(3/2), where theta = 0.6309297536 and the gap above theta* is about 0.225247, about negative bases, or about bases with b^mu >= a.
- The Archimedean cap applies only under its stated base-uniform degree, coefficient-height, nonvanishing, and remainder hypotheses; it is not a universal obstruction to every Pade construction.
- Equality rules out free analytic gain from a higher normalized q-order only. Arithmetic denominator extraction and different determinant or integral models remain open.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 1049` against the frontier.

**What the release proves.** ExternalVerification1049HermitePadeNoGo proves that on the admissible region rho at least 0 and sigma at least 1 + rho the rectangular two-function threshold of the explicit exponent model is at most 1/2 - 1/pi^2, with equality exactly at rho = 0 and sigma = 1.

**Where it is stuck.** At the base 3/2 the homogenisation ceiling caps every content lane on the fixed diagonal at a > b^2, rank two fails the model even at zero clearing, rank three would require kappa_3 < 0.10721, and no construction supplies a family, integrality, nonvanishing or remainder estimate.

**Smallest useful contribution** (infrastructure). Add the power-certificate compiler, which is Lean-checked and already present in the public source, to the comparator configuration of the entry that consumes it.

**Entries.**

- [`ExternalVerification1049HermitePadeNoGo/`](ExternalVerification1049HermitePadeNoGo/), sharp rectangular Hermite–Padé threshold no-go with unique equality point.
- [`ExternalVerification1049AdelicHeightBridge/`](ExternalVerification1049AdelicHeightBridge/), exact first transformed Zudilin row and the 2^64 < 3^41 < 2^65 bracket.
- [`ExternalVerification1049PrimeSupportSelectors/`](ExternalVerification1049PrimeSupportSelectors/), sharp rational gaps for integral linear forms and the exterior-determinant height tradeoff.
- [`ExternalVerification1049RationalBaseBarrier/`](ExternalVerification1049RationalBaseBarrier/), no coordinatewise denominator clearing at the rational base 3/2.
- [`ExternalVerification1049RationalBaseContour/`](ExternalVerification1049RationalBaseContour/), the rational-base contour of Zudilin's (14,12,14;27) forms.

```sh
lake build ExternalVerification1049HermitePadeNoGo Solutions.ExternalVerification1049HermitePadeNoGo
lake build ExternalVerification1049AdelicHeightBridge Solutions.ExternalVerification1049AdelicHeightBridge
lake build ExternalVerification1049PrimeSupportSelectors Solutions.ExternalVerification1049PrimeSupportSelectors
lake build ExternalVerification1049RationalBaseBarrier Solutions.ExternalVerification1049RationalBaseBarrier
lake build ExternalVerification1049RationalBaseContour Solutions.ExternalVerification1049RationalBaseContour
```

## Erdős #1041

**The question.** If a monic polynomial f(z)=product_i(z-z_i) has all roots in the open unit disk, prove that two roots can be joined by a curve of length less than 2 contained in the open lemniscate |f|<1.

**Best substantive result.** For every degree n>=3, a monic polynomial with distinct zeros on a circle of radius rho<=2^(-1/n) has an adjacent-root straight chord of length less than 2 entirely inside |f|<1.

**What this achieves.** This proves the original path-and-containment conclusion on an infinite all-degree geometric class, extending the corpus to cases beginning at degree five and an admissible radius tending to one with the degree. It is not an exact reformulation or an open reduction. The concyclic radius theorem and the configuration-free least-critical-value theorem cover incomparable regimes, so the latter remains visible rather than being described as subsumed.

**Remaining boundary.** The concyclic theorem is an ordinary proof, not Lean-checked or independently reviewed, and assumes the displayed radius bound. Its sharp arc constant cannot reach arbitrary radii below one at fixed degree; the full concyclic case and unrestricted Erdős 1041 remain open. The self-inversive realification is classical, and priority for the combined theorem has not been searched.

Evidence: ordinary_proof. Routes: no dedicated comparator entry in this release; no paper label; public entry not_packaged.

**Strongest genuine longitudinal theorem.** An adjacent-root chord in the open lemniscate for every concyclic root set of radius at most 2^(-1/n).

For a monic polynomial of degree n >= 3 with distinct zeros on a circle of radius rho, some adjacent-root chord has length at most 2 rho sin(pi/n) and maximum modulus strictly below 2 rho^n. Thus rho <= 2^(-1/n) gives a path of length less than 2 inside |f| < 1. Repeated roots are immediate; degree two follows directly for roots in the open unit disk. The all-degree arc comparison is sharp with constant 2; the stronger conjectured chord constant is not part of the theorem.

Evidence: ordinary_proof. Complete ordinary alternation and chord-domination argument in ConcyclicAlternation.md. The exact rational witnesses and PASS computation receipt corroborate the calculation but are not the all-degree proof. No Lean formalisation or independent review is asserted.. Prior art: unassessed, no audit date; antecedent Self-inversive realification is classical Schur-Cohn material; comparison with z^n-c is the circle analogue of Chebyshev comparison..

Routes: no dedicated comparator entry in this release; no paper label; public entry not_packaged.

**Best standalone structural theorem.** sharp all-degree collinear root-diameter theorem with equality configurations, complete primitive sparse quintic, and translated cubic quotient fibres.

The accompanying ordinary mathematics completely solves three structured families of Erdős #1041: collinear root configurations in every degree, the primitive sparse quintics, and translated cubic quotient fibres in every degree 3q with q at least two. This configuration verifies in Lean the three load-bearing kernels of those solutions, and only those three. For every degree n at least two, a monic polynomial of degree n vanishing at -1 and 1, with n-1 increasing interior nodes in the closed interval and values alternating in sign along them, has one node at which the absolute value is at most 2^-(n-1) times cos(pi/2n)^-n. Five real disk coordinates satisfying the first three rotated Newton moments for r strictly between 0 and 2 contain two distinct indices whose tail energy is strictly below one, and three roots in the open unit disc admit one complete radial spoke along which their monic cubic stays inside the closed unit lemniscate. Each family solution is reduced to a single finite inequality, so the delicate step in the geometry of polynomial sublevel sets is the part submitted for checking. The alternation argument sits in the classical Chebyshev context, a bounded search found no earlier form of the quintic selector, and priority is unresolved. Affine transport, the final selection, and the surrounding analytic assembly are ordinary proofs rather than Lean-checked conclusions, and the unrestricted problem is untouched.

Evidence: lean_kernel_checked. Prior art: unknown, no audit date; antecedent The alternation argument sits in the classical Chebyshev context; a bounded search found no earlier form of the quintic selector (entry metadata).

Routes: source [`ExternalVerification1041SolvedFamilies/`](ExternalVerification1041SolvedFamilies/), proof `Solutions.ExternalVerification1041SolvedFamilies`, package `ExternalVerification1041SolvedFamilies/comparator.json`; proof source [`SharpCollinearChebyshev.lean`](ErdosProblems/Erdos1041/SharpCollinearChebyshev.lean); proof source [`PrimitiveQuinticInteriorTail.lean`](ErdosProblems/Erdos1041/PrimitiveQuinticInteriorTail.lean); proof source [`CubicQuotientFiberCase.lean`](ErdosProblems/Erdos1041/CubicQuotientFiberCase.lean); paper labels `thm:sharp-collinear-diameter`, `prop:sharp-collinear-chebyshev-comparator`, `thm:primitive-quintic-two-tail`, `prop:primitive-quintic-two-tail-energy-selector`, `thm:translated-cubic-quotient-fibres`, `lem:cubic-safe-root-spoke`, `bdry:solved-polynomial-families`, `rem:sharp-collinear-formal-boundary`, `rem:primitive-quintic-formal-boundary`, `rem:cubic-quotient-formal-boundary`; public entry launch_core.

**Strongest unresolved producer** (`one_root_covering_of_the_first_merge_component`). Prove (COVER): for monic g with roots in the closed unit disk there is a level lambda in [mu,1] and a compact CONNECTED subset Gamma of the first-merge component of {|g| <= lambda} carrying two roots, such that every point of Gamma lies within intrinsic distance 1 of a root of g, paths being allowed to run in the whole component. By visibility_overlap_reduction_to_a_one_root_statement this settles Erdos #1041, with no separate length obligation. Take Gamma as SMALL as possible and the ambient as LARGE as possible: the cheapest Gamma is the descending Newton branch pair from c*, on which the covering was measured in its strongest form -- straight segments at level 1 -- with zero uncovered points over 26 scored rows at 283 points per arc, at least 155 overlap points per row, and worst overlap length 1.90422 against a budget of 2. …

**Failed approaches and falsifiers.**

- Universal scalar saddle-wall thresholds T ≤ 2√2(βγ)^{1/2n}: false for the actual wall of (z²−a²)(z²+b²).
- Least-critical nearest-pair hub selectors: refuted in the quartic fixed-pair no-go (CEGMQuarticFixedPairNoGo.md).
- Separate critical contours for resolved critical stars: a negative result for the monodromy route.
- The shtuka tree-budget proposition: the Cassini level-length tail 4(√(a²+a) − a) falls below the root distance 2a for a > 4/5 (recorded countermodel, not re-derived on 2026-09-02).
- The sharp arc bound does not reach arbitrary radii below one; neither the regular-polygon conjectured chord constant nor the unrestricted path problem is proved.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 1041` against the frontier.

**What the release proves.** ExternalVerification1041FirstMergeCriticalValueSeparation proves the exact all-degree critical-value separation thresholds C(n, 4) < 1 for every n at least 3, C(n, 3) < 1 for every n at least 4, and C(n, 2) < 1 for every n at least 6, where C(n, S) = (1 + S)^(2/n) log(S/(S - 1)), together with the sign-free consumer that a squared length at most 4 C(n, S) with C(n, S) < 1 forces length strictly below 2.

**Where it is stuck.** The sharp constant is settled in every degree only under the critical-spectrum separation hypothesis, and the two surviving unconditional routes are the componentwise combined-charge lemma, that every nontrivial connected component C of the admissible critical forest satisfies the sum over edges e in C of D_e + K_e being at least 0, and the covering statement COVER, that for monic g with roots in the closed unit disk there is a level lambda in [mu, 1] and a compact connected subset Gamma of the first-merge component of {|g| <= lambda} carrying two roots with every point of Gamma within intrinsic distance 1 of a root.

**Smallest useful contribution** (computation). Re-run the degree-five moment computation with directed rounding rather than IEEE double arithmetic, which converts the fifth arithmetic-mean strengthening into a certificate-backed statement and opens the sixth.

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

## Erdős #243

**The question.** Under a_{n+1}/a_n^2 -> 1 and rational reciprocal sum, force eventual Sylvester recurrence.

**Best substantive result.** For an exact cleared-tail orbit C_(n+1) + D_n = a_n C_n and D_(n+1) = a_n D_n with centred error E_n = D_n - (a_n - 1) C_n, if a_n > 1, C_n > 0, E_n is eventually bounded below, and for every K one eventually has K |E_n| < C_n, then E_n = 0 eventually and a_(n+1) = a_n^2 - a_n + 1 eventually.

**What this achieves.** This reaches the Sylvester endpoint throughout the bounded-negative regime while allowing infinitely many sign changes. It narrows every surviving counterexample to cofinally unbounded negative excursions instead of merely renaming the target.

**Remaining boundary.** The original hypotheses are not known to force an eventual lower bound on E_n, so Erdős #243 remains open. Badea and Koizumi supply the eventual-nonnegative antecedent; the bounded-negative form widens that sign condition to negative visits of bounded depth while adding normalised vanishing, and the local prior-art audit records only medium confidence in the exact coordinate comparison.

Evidence: lean_kernel_checked. Routes: source [`ExternalVerification243BoundedNegativePartRigidity/`](ExternalVerification243BoundedNegativePartRigidity/), proof `Solutions.ExternalVerification243BoundedNegativePartRigidity`, package `ExternalVerification243BoundedNegativePartRigidity/comparator.json`; proof source [`ReciprocalTailRigidity.lean`](ErdosProblems/Erdos243/ReciprocalTailRigidity.lean); no paper label; public entry launch_core.

**Strongest genuine longitudinal theorem.** bounded-negative complete rigidity and eventual Sylvester recurrence.

Clearing denominators in the rational case of Erdős Problem 243 produces an exact integer orbit: multipliers a n greater than 1 drive C (n+1) + D n = a n * C n and D (n+1) = a n * D n, and the centred error is E n = D n - (a n - 1) * C n. The compared theorem proves complete rigidity of the bounded-negative branch of that orbit. An eventual one-sided lower bound -B ≤ E n on the centred error, together with division-free normalized vanishing K * Int.natAbs (E n) < C n at every scale K, forces two conclusions at once: the centred error is exactly zero from some index onward, and the multipliers satisfy the exact Sylvester recurrence a (n+1) = a n ^ 2 - a n + 1 from some index onward. The second conclusion is the Sylvester recurrence itself, which is the target shape for this dynamics, so the theorem reaches that endpoint inside the stated regime. The hypothesis list contains no periodicity assumption, no eventual periodicity assumption, and no sign condition on the centred error, so the statement covers aperiodic orbits and orbits whose centred error changes sign infinitely often. The normalized-vanishing hypothesis is stated division-free over the natural numbers, so the theorem consumes no real-analytic input. Eventual strict centring Int.natAbs (E n) < C n is the K = 1 instance of normalized vanishing and is absorbed into that hypothesis. The proof runs a natural-tail descent on the eventually nonnegative branch and a gcd-stabilisation and scale-reduction obstruction on the recurring bounded-negative branch, then composes the resulting zero-defect statement with the algebraic step that turns a vanishing centred state into the Sylvester successor. The exact recurrence, the one-sided lower bound, and normalized vanishing are hypotheses of the theorem. No declaration in this package produces them for an arbitrary orbit, orbits with cofinally unbounded negative centred error lie outside the statement, and Erdős Problem 243 remains open.

Evidence: lean_kernel_checked. Prior art: extends, audited 2026-09-02; antecedent J. Koizumi, arXiv:2504.05933, Proposition 19(2) and Corollary 20(2) (Badea) (as above).

Routes: source [`ExternalVerification243BoundedNegativePartRigidity/`](ExternalVerification243BoundedNegativePartRigidity/), proof `Solutions.ExternalVerification243BoundedNegativePartRigidity`, package `ExternalVerification243BoundedNegativePartRigidity/comparator.json`; proof source [`ReciprocalTailRigidity.lean`](ErdosProblems/Erdos243/ReciprocalTailRigidity.lean); no paper label; public entry launch_core.

**Best standalone structural theorem.** CRT bounded-rise barrier: a slowly rising natural state cannot avoid an infinite pairwise-coprime modulus family at every strict rise.

A natural state tending to infinity with upward increments bounded by B cannot, at every strict rise, avoid all earlier members of an infinite pairwise-coprime modulus family. The proof uses B old moduli, a shifted consecutive CRT block, and the first crossing; avoidance away from strict rises is not assumed.

No exact reduced tail u_(n+1)+v_n=a_n*u_n, v_(n+1)=a_n*v_n with gcd(u_n,v_n)=1 can have u_n tend to infinity while u_(n+1)<=u_n+B for a fixed positive B. Reduced exactness forces pairwise-coprime multipliers and permanent whole-modulus avoidance; a shifted CRT block and first-crossing argument give the contradiction.

Evidence: lean_kernel_checked. Prior art: new, audited 2026-09-02; antecedent J. Koizumi, arXiv:2504.05933, Lemma 15 (the modular recurrence e_n == d_n (mod c_n), c_{n+1} = c_n - e_n).

Routes: no dedicated comparator entry in this release; no paper label; public entry not_packaged.

**Strongest unresolved producer** (`exclude_aperiodic_negative_state_orbits`). Attack the sole remaining signed-state obstruction, now quantified: any counterexample has negative excursions with -E_n > (1 - delta) log2 log2 C_n infinitely often for every delta > 0 (slow_negative_part_rigidity, counterexample_loglog_negative_excursions), with divergent normalised negative mass and with every multiplier overlap gcd(a_n, D_n) bounded by the next negative magnitude. Coprimality-only arguments are capped at O(log C_n) rises, so the producer must use the congruence E_n = D_n (mod C_n) or a second landing mechanism. Attack the sole remaining signed-state obstruction: cofinally unbounded negative excursions in the exact dynamic cocycle. Corrected unit-field propagation kills the factor-35 branch, forces eight cofinal returns on (31,-10) at factor 41, and forces four more on its (41,-20) child at factor 61. …

**Failed approaches and falsifiers.**

- Finite-prefix rules: arbitrary finite deviations can precede an exact Sylvester tail.
- Eventually periodic and eventually constant negative orbits: excluded unconditionally, so a counterexample must have aperiodic unbounded negative excursions.
- Working at the 1/n rate: the critical constant-negative template sits exactly at the boundary of Koizumi's rate theorem.
- Avoidance away from strict rises is not assumed, and the barrier alone does not force eventual Sylvester recurrence.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 243` against the frontier.

**What the release proves.** ExternalVerification243PeriodicNegativeOrbit proves that for every offset N, every period h > 0 and every positive drift M, positivity of the negative-magnitude sequence together with e_n < a_n on the tail, the exact recurrence and the shape equation D_n + e_n = (a_n - 1) C_n are contradictory, so no eventually periodic negative-magnitude orbit with positive drift carries a rational value.

**Where it is stuck.** The surviving signed-state obstruction is cofinally unbounded negative excursions in the exact dynamic cocycle, and the decisive producer is a global negative-mass, cumulative-LCM or repair-payment theorem.

**Smallest useful contribution** (proof). Formalise the bridge from Koizumi, Irrationality of the reciprocal sum of doubly exponential sequences, arXiv:2504.05933, INTEGERS 26 (2026), A28, so that bounded-negative rigidity becomes a statement about Erdős #243 itself under one added hypothesis.

**Entries.**

- [`ExternalVerification243PeriodicNegativeOrbit/`](ExternalVerification243PeriodicNegativeOrbit/), exclusion of eventually periodic negative-magnitude orbits.
- [`ExternalVerification243ProtectedEpochEnergy/`](ExternalVerification243ProtectedEpochEnergy/), protected-epoch record energy from reusable odd-prime barriers.
- [`ExternalVerification243BoundedNegativePartRigidity/`](ExternalVerification243BoundedNegativePartRigidity/), bounded-negative-part rigidity for reciprocal-tail dynamics.
- [`ExternalVerification243BoundedRiseReducedTail/`](ExternalVerification243BoundedRiseReducedTail/), exclusion of bounded-rise reduced tails.
- [`ExternalVerification243RecordIncrementBarrier/`](ExternalVerification243RecordIncrementBarrier/), unit record-increment rigidity under arbitrary cancellation.
- [`ExternalVerification243SaturatedSquareTransport/`](ExternalVerification243SaturatedSquareTransport/), saturated square transport across one primitive cancellation and the exact reach of its Legendre defect.
- [`ExternalVerification243SlowRiseBarrier/`](ExternalVerification243SlowRiseBarrier/), slow-rise exclusion for reduced exact reciprocal tails.
- [`ExternalVerification243TwoModulusRecordCut/`](ExternalVerification243TwoModulusRecordCut/), the two-modulus record cut and its sharpness at jump five.

```sh
lake build ExternalVerification243PeriodicNegativeOrbit Solutions.ExternalVerification243PeriodicNegativeOrbit
lake build ExternalVerification243ProtectedEpochEnergy Solutions.ExternalVerification243ProtectedEpochEnergy
lake build ExternalVerification243BoundedNegativePartRigidity Solutions.ExternalVerification243BoundedNegativePartRigidity
lake build ExternalVerification243BoundedRiseReducedTail Solutions.ExternalVerification243BoundedRiseReducedTail
lake build ExternalVerification243RecordIncrementBarrier Solutions.ExternalVerification243RecordIncrementBarrier
lake build ExternalVerification243SaturatedSquareTransport Solutions.ExternalVerification243SaturatedSquareTransport
lake build ExternalVerification243SlowRiseBarrier Solutions.ExternalVerification243SlowRiseBarrier
lake build ExternalVerification243TwoModulusRecordCut Solutions.ExternalVerification243TwoModulusRecordCut
```

## Erdős #68

**The question.** Prove that the Erdős #68 factorial-denominator series is irrational.

**Best substantive result.** Lean proves that L_N=lcm_{2<=n<=N}(n!-1) satisfies liminf log L_N/(N^(3/2) log N) at least 2 sqrt(2)/3, strictly improving the former 4/3 lower exponent. For the original series, Lean also proves that any rational branch forces the strict successors N_m to satisfy N_m=m N_{m-1}; consequently every fixed positive modulus divides all sufficiently late N_m, so infinitely many failures modulo one fixed modulus already imply irrationality.

**What this achieves.** The 3/2 theorem is the strongest unconditional standalone theorem in the #68 corpus and decisively closes the full-LCM or one-owner clearing route. Multiplicative successor rigidity is the strongest useful target-directed reduction: it changes the remaining sufficient task from the moving-modulus condition m divides N_m to failure of one congruence chosen in advance, with parity as the simplest case.

**Remaining boundary.** Erdős 68 remains open. L_N is a common denominator, not a reduced denominator, and the 3/2 lower bound obstructs a proof architecture rather than proving irrationality. The fixed-modulus theorem proves no cofinal failures; the observed odd density is finite heuristic evidence only. Exact carry and companion-orbit equivalences transfer the target without simplifying it. The polynomial-perturbation extension is ordinary mathematics with only its gcd identity Lean checked.

Evidence: lean_kernel_checked. Routes: no dedicated comparator entry in this release; no paper label; public entry not_packaged.

**Best standalone structural theorem.** Lean-checked 3/2 lower growth for lcm_{2<=n<=N}(n!-1).

Let L_N = lcm_{2 <= n <= N}(n!-1), represented in Lean by channelLCM N. Then liminf_{N -> infinity} log L_N/(N^(3/2) log N) is at least 2 sqrt(2)/3.

Evidence: lean_kernel_checked. The parent compile receipt records rc=0 for PaperCompleteGcdSegment, PaperCompleteAsymptotics, and PaperCompleteLiminf at their current source hashes, and an axiom audit of exactly [propext, Classical.choice, Quot.sound]. The source header saying uncompiled is stale. The public checkout contains byte-identical proof files under the same Mathlib revision, although its prose and claim registry have not consumed the receipt.. Prior art: extends, audited 2026-09-12; antecedent The former claim used Garaev-Luca-Shparlinski Theorem 12 to derive log L_N >> N^(4/3) log N. The checked terminal-block argument proves the stronger exponent 3/2 and constant 2 sqrt(2)/3 without upgrading the old GLS theorem itself..

Routes: no dedicated comparator entry in this release; no paper label; public entry not_packaged.

**Strongest unresolved producer** (`cofinal_exact_prefix_strict_successor_miss`). Prove that cofinally many integers m fail m | strictFacTopRat(factorialGapPrefix(m),m); Lean proves this is exactly equivalent to Erdős #68. The new full-constant coordinate is an analytically equivalent version of the same producer: for C=sum_{n>=2}1/(n!(n!-1))=S-e+2, prove floor(m!C) not congruent to -2 modulo m cofinally. Lean checks the pointwise equivalence between that residue and the canonical digit d_m(C)=m-2, while the infinite-tail equivalence is recorded analytically. Prime-index misses and the fixed-k two-stage prime-power criterion remain sufficient special cases, but primes are no longer part of the exact frontier statement. UPDATE 2026-09-07 (batch erdos_revision_packets_r5_20260907): unrestricted channel-moment ideals are now finitely determined for each fixed D, with exact mu_D through D=24. That algebraic normalisation does not supply cofinal m not dividing Z_m. …

**Failed approaches and falsifiers.**

- Full-LCM/one-owner clearing: the checked bound liminf log L_N/(N^(3/2) log N) >= 2 sqrt(2)/3 eventually dominates log((N!)^2); it concerns the common denominator, not the reduced denominator.
- Koepf-Schmersau floor criterion at the natural clearing scale p_n = lcm(k!−1): its tail hypothesis fails from n ≥ 4.
- Rank-two producer: reclassified as a smoothness exclusion, not an irrationality route; the CF bound already discharges grid size n ≤ 1.
- Square-subsequence logarithmic constraint: provably cannot pass the sharp constant 4√2/9 in the cancellation-depth coordinate D = 2t^2, which is the radius (16/9)t^3 of the Lean hypothesis (Lean sharp_radius_satisfies_square_log_constraint).
- L_N is a common denominator, not the reduced denominator of a rational representation of the series.
- The estimate obstructs full-LCM clearing because L_N times the positive tail grows; it does not prove irrationality.
- The constant is optimal only for the coarse terminal-block estimate, not asserted to be the true LCM asymptotic constant.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 68` against the frontier.

**What the release proves.** ExternalVerification68CompanionOrbitBoundary proves that the series is rational exactly when floor(m! C) is congruent to -2 modulo m for all sufficiently large m, where C is the sum over n at least 2 of 1/(n!(n! - 1)), and irrational exactly when that residue is missed cofinally, with the same equivalence at every real base point.

**Where it is stuck.** No producer supplies the cofinal residue misses, and exact computation of the strict-successor carries through m = 300000 gives only a finite denominator exclusion for any displayed rational representation.

**Smallest useful contribution** (computation). Extend the exact carry computation beyond m = 300000 and account for the odd-index pattern that has held from index 23 through 300000, since a Lean-checked consumer converts cofinally many non-unit carries into irrationality.

**Entries.**

- [`ExternalVerification68CompanionOrbitBoundary/`](ExternalVerification68CompanionOrbitBoundary/), companion-orbit rationality boundary.
- [`ExternalVerification68ChannelRadius/`](ExternalVerification68ChannelRadius/), explicit cubic radius floor for simultaneous factorial channel cancellation.
- [`ExternalVerification68PrimeUnitTranslator/`](ExternalVerification68PrimeUnitTranslator/), remote factorial-grid kernels reduced by an exact prime unit translator.

```sh
lake build ExternalVerification68CompanionOrbitBoundary Solutions.ExternalVerification68CompanionOrbitBoundary
lake build ExternalVerification68ChannelRadius Solutions.ExternalVerification68ChannelRadius
lake build ExternalVerification68PrimeUnitTranslator Solutions.ExternalVerification68PrimeUnitTranslator
```

## Erdős #269

**The question.** Prove irrationality in the first unresolved support case with three distinct prime generators.

**Best substantive result.** Lean constructs the literal infinite {2,3,5} dyadic-shell tail, proves its exact affine recurrence with radix in {2,6,10,30}, and proves that the unscaled normalized state either hits an integer or returns cofinally at distance at least 1/31 from every integer. Separately, an ordinary decoding theorem proves irrationality of every coordinate fibre for {2,3,5}, and of largest-prime fibres for every finite prime set with at least two elements.

**What this achieves.** The shell-orbit theorem closes the former abstract-tail, digit-identification, and summability gaps on the actual series, so a genuine bounded-radix theorem now applies to the literal object. The fibre theorem is the strongest unconditional positive irrationality result adjacent to the problem and uses a different mechanism: bounded digit-one tails decode their radix word, while irrational logarithmic means forbid eventual periodicity.

**Remaining boundary.** No three-prime repeated-series irrationality or transcendence theorem is proved. The shell dichotomy by itself treats the unscaled integer-state branch and does not exclude rational denominators greater than one. The all-denominator carry/window statement is Lean-checked but exactly equivalent to the target, so it is an exact reformulation and route no-go rather than a reduction to an easier theorem. Fibre irrationality does not combine to irrationality of the repeated series; Sigma_2 + 2 Sigma_3 + 4 Sigma_5 = 1 is the explicit warning. Steve Fan has priority for the two-prime result and the running-height telescope inputs; the fibre theorem's novelty is unverified.

Evidence: lean_kernel_checked. Routes: source [`ExternalVerification269ActualShellOrbit/`](ExternalVerification269ActualShellOrbit/), proof `Solutions.ExternalVerification269ActualShellOrbit`, package `ExternalVerification269ActualShellOrbit/comparator.json`; proof source [`DyadicShellSummability.lean`](ErdosProblems/Erdos269/DyadicShellSummability.lean); no paper label; public entry launch_core.

**Best standalone structural theorem.** exact running-LCM identity, logarithmic-cell constancy, exact jump count, height-fibre normal form, quadratic shell bound, arbitrary-order nonsingular minors, and no finite exact separation.

The running-LCM kernel is K(i,j,k) = 1 / (p^a q^b r^c) with a, b, c the Nat.log exponents of N = p^i q^j r^k in the bases p, q, r. Eight declarations are compared. The strongest is stated for arbitrary generators. For natural numbers p, q, r each greater than 1 such that no positive integer multiple of logb r p is an integer and no positive integer multiple of logb r q is an integer, and for every order n, there are injective index families I, J from Fin n to the naturals whose n by n minor det K(I a, J b, k) is nonzero simultaneously for every value of the third exponent k. Distinct primes satisfy that independence hypothesis: for primes p, q, r with p different from r and q different from r, the same uniform nonsingular minors exist at every order, and for every d there is no representation K(i,j,k) = sum over l < d of f_l(i) G_l(j,k) by finitely many separated factors with rational-valued f_l and G_l. That pair carries no hypothesis relating p and q. For pairwise distinct primes p, q, r and every nonzero x, the least common multiple of all smooth numbers p^i q^j r^k at most x equals p^(log_p x) q^(log_q x) r^(log_r x), the product of the three maximal pure prime powers below x. For pairwise distinct primes p, q, r the first m positive jump values across the three prime channels number exactly 3m. Two declarations hold for arbitrary natural generators with no hypothesis at all: K is constant on every logarithmic cell, and the sum of K over a finite exponent box equals the sum over the genuine running-LCM heights of the fibre cardinality divided by the height. A multiplicative shell of width factor r inside a sorted exponent budget hp at most hq at most hr summing to j satisfies 9 times its cardinality at most (j+3)^2, on the hypotheses that r is positive and the shell width hi is at most r times lo. The smallest 2, 3, 5 kernel rectangle has determinant exactly -1/15. The running-LCM factorisation identity for every finite prime set, and the two-prime case in which the series factorises and is transcendental by Hecke and Mahler, are due to Steve Fan (erdosproblems.com/269 comment, 26 June 2026), who also records that the factorisation does not extend to three or more primes. The identity theorem here formalises his identity at three primes, and the rank statements are the addition. Priority for the rank statements is unassessed. None of the eight declarations yields irrationality or transcendence, and Erdős #269 remains open.

Evidence: lean_kernel_checked. Prior art: new, audited 2026-09-02; antecedent Steve Fan, comment on erdosproblems.com/269, 05:22 on 26 June 2026 (the general-k running-LCM identity, the two-prime factorisation S = S_1 S_2, and transcendence via Hecke-Mahler; closing sentence "This argument does not seem to generalize immediately to |P| >= 3, since S does not factor nicely in the first place.").

Routes: source [`ExternalVerification269ThreePrimeStructure/`](ExternalVerification269ThreePrimeStructure/), proof `Solutions.ExternalVerification269ThreePrimeStructure`, package `ExternalVerification269ThreePrimeStructure/comparator.json`; proof source [`ThreePrimeRunningLcm.lean`](ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean); proof source [`KernelCarryRank.lean`](ErdosProblems/Erdos269/KernelCarryRank.lean); no paper label; public entry launch_core.

**Strongest unresolved producer** (`exclude_exact_integral_dyadic_tails`). For every positive B coprime to 30 and every a>=1, prove that the actual normalised state B X_a is nonintegral. Clearing and the rationality-to-reduced-carry bridge make this equivalent to irrationality of the {2,3,5} series; it is not a strictly stronger producer. The B=1 corner (integral X_a) is included but is not the whole target. Lean proves that the unscaled orbit either hits an integer or returns cofinally 1/31-far from all integers. The denominator-one automaton remains a direct B=1 representation, but the exact a=2295 source word kills every uniform three-transition post-clear proof, and exact left-null certificates eliminate every direct phase-conditioned source potential of total degree at most two. The registered onset in the manuscript remains u+1+2v+3w until a sharper onset is independently checked. …

**Failed approaches and falsifiers.**

- Finite separated-factor decompositions of the three-prime kernel: nonsingular minors exist at every order uniformly in the third layer.
- Adamczewski-Bugeaud stammering criterion: measured simultaneous-approximation exponents fall to ≈ 1.007 while the criterion needs exponent 1 for both slopes at the same denominator; Dirichlet supplies only 1/2.
- Finite Farey boxes and lattice first-hit screens: a measured square-root law with no cofinal quantifier.
- Leading minors are not a witness of infinite rank: row three is 1/120 times row zero for j ≤ 3 and the proportionality fails at j = 4, so index selection is essential.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 269` against the frontier.

**What the release proves.** ExternalVerification269ThreePrimeStructure proves the exact three-prime running-LCM identity, that the reciprocal-height kernel is constant on every logarithmic cell with exactly 3m jump values across the first m positive jumps, and that the kernel admits injective minors of every order, so it has no finite separable representation with rational-valued factors.

**Where it is stuck.** The normalised infinite dyadic shell tail either reaches an exact integral state or returns cofinally at distance at least 1/31 from every integer, and excluding the exact-integral-state branch is the unresolved step.

**Smallest useful contribution** (proof). Prove in Lean the telescoping identity that the sum over primes p of (p - 1) times the sum over n of 1/H(p^n) equals 1, where H is the running LCM height, which is a one-line difference identity and is absent from the corpus.

**Entries.**

- [`ExternalVerification269ThreePrimeStructure/`](ExternalVerification269ThreePrimeStructure/), exact three-prime running-LCM identity and infinite kernel rank.
- [`ExternalVerification269ActualShellOrbit/`](ExternalVerification269ActualShellOrbit/), actual dyadic shell orbit, exact recurrence and integral-or-far escape.
- [`ExternalVerification269WindowEscapeEquivalence/`](ExternalVerification269WindowEscapeEquivalence/), the cofinal local-window escape is equivalent to irrationality of the three-prime running-LCM value.

```sh
lake build ExternalVerification269ThreePrimeStructure Solutions.ExternalVerification269ThreePrimeStructure
lake build ExternalVerification269ActualShellOrbit Solutions.ExternalVerification269ActualShellOrbit
lake build ExternalVerification269WindowEscapeEquivalence Solutions.ExternalVerification269WindowEscapeEquivalence
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
