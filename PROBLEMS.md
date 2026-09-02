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

**Strongest genuine longitudinal theorem.** irrationality for every infinite reciprocal-summable support at every integer base.

For every infinite set A of exponents whose reciprocal sum converges and every integer base b at least two, the series with terms 1/(b^a - 1) supported on A is irrational. The theorem settles the whole reciprocal-summable support regime at once and uniformly in the base, with no pairwise-coprimality, periodicity, density or powerful-support hypothesis, and with the zero exponent normalised to zero by real division. Any counterexample to the universal Erdős Problem 257 must therefore be supported on a set whose reciprocal sum diverges. The mechanism produces close returns of shifted binary support atoms from an LCM-prefix orbit-mean argument, transfers them to every radix through a uniform pointwise inequality bounding the base-b atom displacement by twice the binary one, and closes with an exact radix integer orbit. Erdős (1968) proved the pairwise-coprime reciprocal-summable case for every integer base t at least two and stated that pairwise coprimality is superfluous by a more complicated argument he did not print; this formalization proves that stated extension, in every integer base, by an independent argument. No theorem-priority claim is made and no identification with Erdős's omitted argument is asserted. The audience is analytic number theorists working on irrationality of Mersenne-type reciprocal subseries. Reciprocal-divergent supports are untouched, so the universal Erdős Problem 257 remains open.

Evidence: lean_kernel_checked. Prior art: matched_to_stated_extension_strictly_stronger_than_printed_theorem, audited 2026-09-02; antecedent P. Erdős, On the irrationality of certain series, Math. Student 36 (1968), 222-226: printed theorem for pairwise-coprime reciprocal-summable supports at every integer base t ≥ 2; the removal of coprimality is stated without proof.

Routes: source [`ExternalVerification257ReciprocalSupport/`](ExternalVerification257ReciprocalSupport/), proof `Solutions.ExternalVerification257ReciprocalSupport`, package `ExternalVerification257ReciprocalSupport/comparator.json`; paper labels `res:reciprocal-support`, `bdry:reciprocal-support`, `sec:reciprocal-support`; public entry launch_core.

**Best standalone structural theorem.** achievement-set topology and exact volume dichotomy.

For every set J of allowed binary Mersenne coordinates, the supported digit map is injective and has compact nowhere-dense range; the range is perfect when J is infinite. Its Lebesgue measure is exactly 2^(-|F|) when J omits the finite set F, and zero when the omitted coordinates are infinite. This support-uniform geometric classification does not prove universal Mersenne-subseries irrationality or solve Erdős Problem 257.

Evidence: lean_kernel_checked. Prior art: classical_input_disclosed, no audit date; antecedent Kakeya (1914) and Kovač-Tao Remark 4.1 own compact/perfect/totally disconnected/nowhere dense; the exact measure dichotomy is presented as added.

Routes: packaged privately, not in this release; no paper label; public entry reserve.

**Strongest unresolved producer** (`contradict_twenty_one_permanent_affine_supercapacity`). Contradict the exact permanent affine-supercapacity regime forced by TwentyOneFatalAlignedBranch. Commit bad43508 proves that any unbounded sequence of closed canonical rows s_R<=2^R already gives the compactness decay required for 1/21 membership, so the fatal branch must eventually satisfy 2^R<s_R at every rank. Combined with commit f23727a, the boundary coin is then always taken: support appends R+1 and the scalar follows one literal affine recurrence with no residual Boolean branch. Commit 73f417a additionally proves that an aligned crossing from exact saturation into strict supercapacity must occur at R=3a+2 and omit a canonical ancestor at a+1 or 2(a+1). This restricts one entrance mechanism but does not show that the fatal branch enters late from exact saturation or contradict the regime after entry. One direct producer is an arbitrarily deep closed return, or any checked consequ…

**Failed approaches and falsifiers.**

- Any counterexample support must have divergent reciprocal sum; every candidate support with summable reciprocals is now excluded at every integer base.
- Powerful supports as an independent contribution: subsumed by the reciprocal-summable theorem and removed from public lanes.
- The 4/9 modulus-84 2-3-7 causal producer: false despite explaining all eight observed repair-gap rescues.
- Any counterexample to universal #257 must have divergent reciprocal sum; the theorem says nothing about divergent supports.
- Kovač-Tao Thm 2.3 constructs rational sums only with m ≥ 2 distinct bases and divergent reciprocal mass; no conflict.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 257` against the frontier.

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

**Strongest genuine longitudinal theorem.** None. No genuine climb: rationality is forced into a tempered carry of dyadic rank ≥ 2^e−1 against the proved kernel rank 2^e+1, plus finite exclusions; no producer supplies the residue-gap H (longitudinal_truth_2026_09_01 §1).

**Best standalone structural theorem.** explicit odd-core basis, full-span equality, canonical finite normal form, and exact ranks.

The two zero-residue base channels and one odd-residue channel at each positive dyadic level form a linearly independent spanning family for all dyadic sections of Euler's totient. The complete family through level e has the same span as the duplicate-free canonical truncation and exact rank 2^e+1. This unconditional structural theorem does not prove irrationality of the binary totient series.

Evidence: lean_kernel_checked. Prior art: extends, audited 2026-09-02; antecedent M. Coons, (Non)Automaticity of number theoretic functions, J. Theor. Nombres Bordeaux 22 (2010), no. 2, 339-352 (Theorem 3.2, proof printed p. 349; k-kernel definition in Section 1).

Routes: packaged privately, not in this release; no paper label; public entry reserve.

**Strongest unresolved producer** (`totient_specific_moving_dyadic_escape`). Prove FullMersenneCanonicalBasepointResidueGapSupply, the Lean-equivalent arithmetic normal form: for every c and positive odd v, find H>0 divisible by phi(v) such that the canonical residue (-totientBlock(H,c)) mod ((2^H-1)/v) lies in the central interval of radius c+H+1. On the pure-dyadic axis, the Lean-checked signed error E_H=totientBlock(H,c)-k(2^H-1) obeys E_(H+1)=2E_H+phi(c+H+1)-k while the nearest quotient k stays fixed. Exact computation through c<=1000000 finds delay nineteen at c=490794, ruling out caps through seventeen. Pointwise legal-letter methods, the constant-two mode, sublinear errors, and every eventually affine linear-scale error are eliminated. Actual prime positions cofinally force linear excursions; more directionally, if the successor remains upper-trapped then 4E_H+p+phi(p+1)<=4+3k, so any permanent trap is cofinally bottom-locked immediately before large prim…

**Failed approaches and falsifiers.**

- Uniform bounds ‖v·2^c·S‖ ≥ c^{−A}: impossible for irrational S because odd multiples of 2^c S are dense mod 1.
- Coprime restriction with Stern-Brocot splitting and geometric decay: the visible-lattice sum ∑_{gcd(a,b)=1} 1/(2^{a+b}−1) equals exactly 1, so it cannot force irrationality.
- Positive rank-one Schur blocks: every admissible quotient sits at least 21/320 above Θ₂ (unique minimiser (1,5)).
- Nonnegative Stieltjes representations of the Möbius-Mersenne ladder: strict log-concavity at every rung.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 249` against the frontier.

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

**Strongest genuine longitudinal theorem.** None. No genuine climb: a two-branch reduction on the actual orbit (B = 1 corner decidable per index and refuted to 6000; B > 1 corner a lattice statement certified to 10^105), the rank phase transition, and q > 10^6768; the LCM identity and two-prime transcendence are Steve Fan's (longitudinal_truth_2026_09_01 §1, prior_art_adjudication_2026_09_02 §4).

**Best standalone structural theorem.** exact running-LCM identity, logarithmic-cell constancy, exact jump count, height-fibre normal form, quadratic shell bound, arbitrary-order nonsingular minors, and no finite exact separation.

For pairwise distinct primes p, q, r and every nonzero x, the least common multiple of all smooth numbers p^i q^j r^k at most x equals the product of the three maximal pure prime powers below x. The reciprocal-height kernel K(i,j,k) built from that identity is constant on every logarithmic cell, and the first m positive jump values across the three prime channels number exactly 3m. Every finite exponent box sums to the height-fibre normal form, the sum over genuine running-LCM heights of the fibre cardinality divided by the height, and a multiplicative shell of width factor r inside a sorted exponent budget j satisfies 9 times its cardinality at most (j+3)^2. For every order n there are injective index families giving a nonsingular n by n minor of K uniformly in the remaining exponent layer, so K has infinite rank and no finite separable representation K(i,j,k) = sum over l < d of f_l(i) G_l(j,k) exists for any d. The smallest 2,3,5 rectangle has determinant exactly -1/15. Three distinct primes keep the three logarithm floors independent, which is what makes the running-LCM identity exact and the minors nonsingular in every order, and it removes every method that would evaluate the three-prime sum by finitely many separated factors. The running-LCM factorisation identity for every finite prime set, and the two-prime case in which the series factorises and is transcendental by Hecke and Mahler, are due to Steve Fan (erdosproblems.com/269 comment, 26 June 2026), who also records that the factorisation does not extend to three or more primes; the identity theorem here formalises his identity at three primes, and the rank statements are the addition. Priority for the rank statements has not been established, none of the seven theorems yields irrationality or transcendence, and Erdős #269 remains open.

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

```sh
lake build ExternalVerification269ThreePrimeStructure Solutions.ExternalVerification269ThreePrimeStructure
```

## Erdős #1041

**The question.** If a monic polynomial f(z)=product_i(z-z_i) has all roots in the open unit disk, prove that two roots can be joined by a curve of length less than 2 contained in the open lemniscate |f|<1.

**What the release proves.** ExternalVerification1041FirstMergeCriticalValueSeparation proves the exact all-degree critical-value separation thresholds C(n, 4) < 1 for every n at least 3, C(n, 3) < 1 for every n at least 4, and C(n, 2) < 1 for every n at least 6, where C(n, S) = (1 + S)^(2/n) log(S/(S - 1)), together with the sign-free consumer that a squared length at most 4 C(n, S) with C(n, S) < 1 forces length strictly below 2.

**Where it is stuck.** The sharp constant is settled in every degree only under the critical-spectrum separation hypothesis, and the two surviving unconditional routes are the componentwise combined-charge lemma, that every nontrivial connected component C of the admissible critical forest satisfies the sum over edges e in C of D_e + K_e being at least 0, and the covering statement COVER, that for monic g with roots in the closed unit disk there is a level lambda in [mu, 1] and a compact connected subset Gamma of the first-merge component of {|g| <= lambda} carrying two roots with every point of Gamma within intrinsic distance 1 of a root.

**Smallest useful contribution** (computation). Re-run the degree-five moment computation with directed rounding rather than IEEE double arithmetic, which converts the fifth arithmetic-mean strengthening into a certificate-backed statement and opens the sixth.

**Strongest genuine longitudinal theorem.** Sharp constant 2 in every degree under critical-value separation.

Let f be monic of degree n ≥ 3 with a nonzero simple critical hub c, and suppose every other critical point d satisfies |1 − f(d)/f(c)| ≥ S > 1. Then two distinct roots of f are joined inside {|f| ≤ |f(c)|} by a path of length at most 2(1+S)^{1/n} √log(S/(S−1)), which is below 2 whenever C(n,S) = (1+S)^{2/n} log(S/(S−1)) < 1; exact thresholds are S = 4 for n ≥ 3, S = 3 for n ≥ 4 and S = 2 for n ≥ 6, each sharp in the degree since C(2,4), C(3,3) and C(5,2) exceed 1. With open-unit-disk roots the Fekete chain gives |f(c)| < 1, so Erdős #1041 holds for every such polynomial. The numerical kernel and the sign-free consumer are Lean-checked; analytic continuation, univalence, the area formula and Pólya's area-capacity inequality are ordinary mathematics.

Evidence: ordinary_proof. conditional on the separation hypothesis (a hypothesis on the critical spectrum, not an open statement); the Lean entry proves the three thresholds and the consumer only. The area bound behind the capacity-closure step is Dubinin's Theorem 1 (a Pólya-type inequality), an input the paper does not yet cite. Prior art: new, audited 2026-09-02; antecedent V. N. Dubinin, Some inequalities for polynomials and rational functions associated with lemniscates, Zap. Nauchn. Sem. POMI 404 (2012), 83-99 (Analytical theory of numbers and theory of functions, Part 27, ed. G. V. Kuz'mina and O. M. Fomenko, POMI, St. Petersburg, 2012, 262 pp.); English translation J. Math. Sci. 193:1 (2013), 45-54, DOI 10.1007/s10958-013-1432-4 (Theorem 1. Its text was NOT obtained (see searches_not_completed). Best available paraphrase is Terence Tao on the erdosproblems.com/1041 thread, 02:45 on 25 Mar 2026: "By Theorem 1 of this paper of Dubinin (a Polya type inequality), this area is at most s^{2/m} times the area of U; and by the classical Polya inequality, U has area at most pi.").

Routes: no Lean package in this release; paper labels `res:critical-value-separation`, `res:critical-value-thresholds`, `bdry:critical-value-separation`; public entry not_packaged.

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
- Degree four with a near-tie in the critical spectrum is Pendyala's and outside this theorem; degree 40 with S = 4 separation is inside it and outside Pendyala's.
- The anonymous general-degree manuscript of March 2026 was withdrawn by its author (Proposition 12 incorrect, thread 26 Mar 2026) and a second general-degree attempt of April 2026 was broken; nothing subsumes this theorem and the parent stays open with zero accepted proof claims (disposition E0_1041_shtuka_withdrawn).

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 1041` against the frontier.

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

**Smallest useful contribution** (proof). Supply the h = 1 cofinal adjacent-small-mismatch producer from actual consecutive-prime arithmetic. Coarse gap properties cannot supply it (the polynomial countermodel), the measured event density of 0.0042 to 0.0082 over 6.8 million primes is finite evidence only, and a Lean-checked consumer converts the producer into irrationality.

**Strongest genuine longitudinal theorem.** None. No genuine climb: the rational-tail normal form is pinned to one located obstruction (cofinal adjacent small mismatch), the coarse-gap route is closed by an explicit countermodel, and q > 10^12041 is a finite exclusion (longitudinal_truth_2026_09_01 §1).

**Best standalone structural theorem.** exact polynomial shift countermodel eliminating coarse-gap strategies.

The explicit digit word g(n) = 2(n^2 + 4n + 2) and the explicit rational orbit T(n) = 2(n + 4)^2 satisfy the dyadic tail recurrence T(N + 1) = 2 T(N) - g(N + 1) at every index. The word is positive, even and strictly increasing, hence unbounded and nonperiodic; every fixed tail shift T(N + h) - T(N) is an integer for every h and every N; and every difference of consecutive digits past the first term is at least fourteen, so it is never 2 or -2. The construction is an exact countermodel, and it eliminates every argument that would force the adjacent small-mismatch producer out of positivity, parity, polynomial growth, unboundedness, nonperiodicity, the dyadic recurrence and integrality at every fixed shift taken together. The mechanism is that an integer-valued quadratic orbit turns all-shift integrality into a polynomial identity over the integers while the word has constant second difference, so its adjacent differences grow linearly and clear the small window from the outset. The readers are number theorists working on the irrationality of the dyadic prime-gap series; priority for the construction has not been assessed. The orbit is not the actual consecutive-prime-gap orbit, so the theorem does not decide Erdős Problem 251.

Evidence: lean_kernel_checked. Prior art: unassessed, no audit date.

Routes: source [`ExternalVerification251PolynomialShiftCountermodel/`](ExternalVerification251PolynomialShiftCountermodel/), proof `Solutions.ExternalVerification251PolynomialShiftCountermodel`, package `ExternalVerification251PolynomialShiftCountermodel/comparator.json`; no paper label; public entry launch_core.

**Strongest unresolved producer** (`cofinal_adjacent_small_mismatch`). For each fixed h >= 1 and every N0, produce N >= N0 such that both actual tail shifts T_(N+h)-T_N and T_(N+h+1)-T_(N+1) lie strictly between -1 and 1 while g_(N+h+1) != g_(N+1). The checked finite consumer then excludes eventual integrality of the h-shift.

**Failed approaches and falsifiers.**

- Coarse gap properties (positive, even, increasing, unbounded, nonperiodic): the word g_n = 2(n²+4n+2) satisfies all of them, has rational value 32, and never produces an adjacent small mismatch.
- State compression by word repetition alone: the margin is recorded so the lane is not re-walked.
- Liouville-flavoured attacks: the certified expansion has irrationality-exponent witness 2.0007.
- The countermodel is not the actual prime-gap word; it rules out coarse-gap strategies only.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 251` against the frontier.

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

**Strongest genuine longitudinal theorem.** None. No genuine climb: the corpus holds finite exclusions (q > 10^12039, q ∤ 299999!), exact equivalences, and route ceilings; the target never entered through the cofinal statement (longitudinal_truth_2026_09_01 §1).

**Best standalone structural theorem.** quantitative square-subsequence channel-radius lower bound, exclusion of eventual three-halves upper bounds, and exact failure of little-o decay.

A channel is an index d at least 2 carrying the modulus d! - 1, obtained by reweighting each factorial term of the series so that the powers of d! divide out; the channel test at d compares that reweighted integer with the factorial moment modulo d! - 1. The main theorem is explicit: for every t at least 2^32 and all natural numbers M and R with M positive, M divisible by the least common multiple of d! - 1 over 2 ≤ d ≤ 2t^2, and M < (R+1)! - 1, the support radius satisfies 3t^3 < 2(R+1). Imposing those hypotheses at every large t gives two sequence forms: no radius function can eventually satisfy 2(R(t)+1) ≤ 3t^3, and R(t)+1 is not o(t^3), the second under hypotheses required only from t = 4096 onwards. The entire subcubic range is therefore closed on the square subsequence D = 2t^2, since every finite channel system meeting the hypotheses carries support radius above (3/2)t^3, which prices the method for anyone pursuing irrationality of series with factorial denominators. The nontrivial input is a finite lower estimate for the channel least common multiple, in which consecutive numbers d! - 1 are combined while their pairwise gcd losses are counted explicitly, and a Stirling bound converts that estimate into the cubic radius. This theorem family is the first presentation recorded in the development and its novelty is unassessed. The divisibility and factorial bounds remain hypotheses, so the irrationality question in Erdős Problem 68 is untouched, and the remaining problem is to derive those hypotheses from the factorial-gap series and to prove that the required channels vanish.

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

```sh
lake build ExternalVerification68CompanionOrbitBoundary Solutions.ExternalVerification68CompanionOrbitBoundary
lake build ExternalVerification68ChannelRadius Solutions.ExternalVerification68ChannelRadius
```

## Erdős #243

**The question.** Under a_{n+1}/a_n^2 -> 1 and rational reciprocal sum, force eventual Sylvester recurrence.

**What the release proves.** ExternalVerification243PeriodicNegativeOrbit proves that for every offset N, every period h > 0 and every positive drift M, positivity of the negative-magnitude sequence together with e_n < a_n on the tail, the exact recurrence and the shape equation D_n + e_n = (a_n - 1) C_n are contradictory, so no eventually periodic negative-magnitude orbit with positive drift carries a rational value.

**Where it is stuck.** The surviving signed-state obstruction is cofinally unbounded negative excursions in the exact dynamic cocycle, and the decisive producer is a global negative-mass, cumulative-LCM or repair-payment theorem.

**Smallest useful contribution** (proof). Formalise the bridge from Koizumi, Irrationality of the reciprocal sum of doubly exponential sequences, arXiv:2504.05933, INTEGERS 26 (2026), A28, so that bounded-negative rigidity becomes a statement about Erdős #243 itself under one added hypothesis.

**Strongest genuine longitudinal theorem.** bounded-negative complete rigidity and eventual Sylvester recurrence.

Exact reciprocal-tail dynamics with eventual strict centering, an eventual one-sided lower bound on the centered error, and division-free normalized vanishing have zero centered defect eventually and obey the exact Sylvester recurrence eventually. No periodicity assumption is used. The theorem is conditional and does not settle unrestricted Erdős #243.

Evidence: lean_kernel_checked. Prior art: extends, audited 2026-09-02; antecedent J. Koizumi, arXiv:2504.05933, Proposition 19(2) and Corollary 20(2) (Badea) (as above).

Routes: packaged privately, not in this release; no paper label; public entry reserve.

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

```sh
lake build ExternalVerification243PeriodicNegativeOrbit Solutions.ExternalVerification243PeriodicNegativeOrbit
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
- Equality closes the hope that hidden cancellation supplies extra cubic decay; any height improvement must come from arithmetic denominator extraction or a different integral model.

**Does a contribution advance the frontier?** It does when it proves the producer above, refutes the route that producer names, or states a theorem no claim in the frontier already carries; a restatement of a listed claim or a return to a superseded constant does not. Check the proof with the build command below; the maintainers classify the statement with `build_claim_frontier.py --decide --problem 1049` against the frontier.

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
