# Plectis Erdős Lean

**Will Cook · human-directed, AI-assisted mathematical research and formalisation · Lean 4 / Mathlib**

This repository contains Lean proofs and explicit theorem interfaces associated
with eight Erdős problems. A reader can inspect each selected statement in its
`Challenge.lean`, follow the corresponding proof through `Solution.lean`, and
compare it with the paper cited in `formalization.yaml`.

## Selected Palomar release

The first release selects the following configurations from the full checking
corpus. Each configuration names a finite list of statements; it does not
certify every claim in the linked paper. The first official full preflight, for **E257_01**, was
[rejected before proof execution](docs/palomar-release-v1/preflight-35917059793.json):
that candidate used Lean 4.30.0 and the pinned current verifier requires at least
4.35.0-rc2. The [upgraded candidate](https://github.com/wcook04/plectis-erdos-lean/commit/216567506f823f1e47b209f9443ae8e5f0fdec8b)
uses the matching Lean and Mathlib 4.35.0-rc2 release; its
[mechanical preflight](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35918585547) reached Solution compilation and found two compatibility errors in the #257 dependency chain. Their repair is in progress; verification has not passed. The remaining entries are disabled in the
[release selection](.github/palomar-release-selection-v1.json) while their
scope and exact-input checks are prepared.

| Entry | Selected mathematical unit | Boundary |
|---|---|---|
| [E257_01](PalomarCorpus/E257_01/formalization.yaml) | Weighted support criteria for reciprocal Mersenne subseries, including the all-base hereditary criterion | Five selected declarations; other claims of the papers are outside this entry. |
| [E249_29](PalomarCorpus/E249_29/formalization.yaml) | All-base bases and integral relations for the totient kernel | Exact kernel structure; does not decide irrationality of the dyadic totient series. |
| [E243_01](PalomarCorpus/E243_01/formalization.yaml) | Cubic-rate irrationality for reciprocal-tail series | The bounded-increment theorem in the paper is a separate result. |
| [E251_01](PalomarCorpus/E251_01/formalization.yaml) | Sparse perturbations preserving congruences | The conditional prime-gap application is outside this entry. |
| [E269_02](PalomarCorpus/E269_02/formalization.yaml) | Uniform kernel rank and nonseparation | Modular-minor strengthenings are outside this entry; the parent irrationality question remains open. |
| [E1049_01](PalomarCorpus/E1049_01/formalization.yaml) | An explicit rational-base irrationality region, including 31/4 and its positive powers | The region excludes 3/2; later sharp fixed-base and Hankel results are outside this entry. |
| [E68_05](PalomarCorpus/E68_05/formalization.yaml) | Carry, divisor-channel and finite-moment criteria | Structural scope awaiting selection approval; the two large numerical denominator exclusions are not certified here. |
| [E1041_01](PalomarCorpus/E1041_01/formalization.yaml) | Ani's degree-seven construction and the all-degree trinomial case | Seventeen statements now selected, including three exact Hausdorff endpoints; supported-toolchain elaboration and mechanical verification remain pending. Named-input low-critical-value wrappers retain their hypotheses. |

The [paper-scope appendix](docs/palomar-release-v1/eight_paper_coverage_appendix.md) accounts for every labelled paper row and links to the machine-readable dispositions.

The metadata records source credit and limitations. In particular, ani owns
the #1041 counterexample construction; Erdős's original series results,
Martin's affine-independence theorem, Coons's non-regularity result and
Zudilin's architecture retain their attribution in the relevant entries.
Will directs the AI-assisted research and formalisation. This does not imply
an independent human proof audit of every statement.

## Verification and registry status

The [official full-preflight workflow](.github/workflows/palomar-official-full-preflight.yml)
calls Palomar's complete mechanical verifier at a pinned revision, in `full`
mode, for one selected configuration and the exact candidate commit. Rendering
and editorial review are later, separate registry stages; this report does not
establish their outcomes. A caller-run preflight does not create a Palomar
submission or registration, and registration is not a peer-review or novelty
verdict.

The [mechanical replay workflow](.github/workflows/palomar-replay.yml) is a
separate regression check. Its successful runs do not establish that the
current candidate has passed Palomar's full pipeline. Axiom audits distinguish
intentional placeholders in Challenge specifications from the proof-bearing
Solution dependency closure.

## Full checking inventory

The complete corpus remains available for regression checks and precise
statement lookup. It is not a queue of registry submissions.

<!-- palomar-entry-table:begin (generated; do not edit by hand) -->
The Palomar entries are packed in the order the papers state their theorems; [`PalomarCorpus/README.md`](PalomarCorpus/README.md) lists every entry with its theorem count and title.

| Problem | Entries | Theorems |
|---|---|---:|
| #68 | `E68_01` to `E68_10` | 73 |
| #243 | `E243_01` to `E243_11` | 140 |
| #249 | `E249_01` to `E249_33` | 621 |
| #251 | `E251_01` to `E251_08` | 87 |
| #257 | `E257_01` to `E257_43` | 537 |
| #269 | `E269_01` to `E269_11` | 92 |
| #1041 | `E1041_01` to `E1041_08` | 108 |
| #1049 | `E1049_01` to `E1049_08` | 110 |
| Total | 132 entries | 1768 |

The problem-level entry `E257` of the previous layout was submitted to Palomar on 13 September 2026 at commit `52f29ad1` (submission `impkvgnxmpb7`). Its mechanical verification passed ([run 34784800531](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34784800531)); Palomar's render stage then failed on a known renderer defect ([PalomarSubmission #134](https://github.com/PalomarRegistry/PalomarSubmission/issues/134)), and the submission settled as `verification-error` on 14 September 2026. No entry of the present layout has been submitted.
<!-- palomar-entry-table:end -->

The generated inventory above records the earlier E257 submission separately.
The renderer fix merged upstream after that attempt; the selected release
still requires its own exact-input full reports. The 1,768 configured names (1,765 in the baseline plus three Hausdorff endpoints)
are a different count from labelled rows in the papers.

## Source-family catalogue

The following descriptions cover the `ExternalVerification*` source families.
They give additional context and their own exact configurations. For the
selected release, use the entries and scope boundaries above; do not treat
this larger catalogue as its submission list.

### Erdős #257: irrationality for every reciprocal-summable support and every integer base

For every integer base b at least two and every infinite set A of exponents whose reciprocal sum converges, the series with terms 1/(b^a - 1) supported on A is irrational. One declaration is compared and it carries exactly that statement. The support is an arbitrary infinite set of natural numbers, the exponent zero is normalised to zero by real division, and no pairwise-coprimality, periodicity, density, or powerful-support hypothesis appears. The whole reciprocal-summable support regime is settled uniformly in the base, so every support carrying a counterexample to universal Erdős Problem 257 has divergent reciprocal sum. The proof produces close returns of shifted binary support atoms from an LCM-prefix orbit-mean argument, transfers those returns to every radix through a pointwise inequality bounding the base-b atom displacement by twice the binary one, and closes with an exact radix integer orbit. Erdős (1968) proved the pairwise-coprime reciprocal-summable case for every integer base t at least two and stated that pairwise coprimality is superfluous by a more complicated argument he did not print. This development proves that stated extension, in every integer base, by an independent argument. No theorem-priority claim is made and no identification with Erdős's omitted argument is asserted. Reciprocal-divergent supports are untouched, so universal Erdős Problem 257 remains open.

Boundary. The compared result states that every infinite reciprocal-summable support A gives an irrational reciprocal-power subseries at every integer base at least two. The zero exponent is normalized to zero by real division. No pairwise-coprimality, periodicity, density, or powerful-support hypothesis is assumed. Challenge.lean contains the deliberate Comparator specification sorry; the proof-bearing Solution.lean and its imported source theorem are sorry-free. The atom comparison and close-return producer are subordinate proof mechanisms rather than extra results.

Source: [`ExternalVerification257ReciprocalSupport/`](ExternalVerification257ReciprocalSupport/), configuration `ExternalVerification257ReciprocalSupport/comparator.json`. One declaration is compared in that family entry; the Palomar entry [`PalomarCorpus/E257`](PalomarCorpus/E257/) compares the same theorem together with 49 others.

### Erdős #251: kernel-decided denominator floor for the prime-gap dyadic series

Every rational a/b equal to the prime-gap series of Erdős Problem 251, the dyadic series whose term at index n is (p_(n+1) - p_n)/2^(n+1), has denominator b at least 2^589, a number exceeding 10^177. The same floor holds for the zero-based prime series with term p_n/2^(n+1), whose value is 2 more than the gap series. Both floors are decided inside the Lean kernel. certCheck c u v u' v' X packages six integer conditions on a trial-division sieve run over every m < X: the count of primes below X equals c, v and v' are positive, the Farey determinant u'v = uv' + 1 holds, and two inequalities place the prime series strictly inside the interval from u/v to u'/v'. den_bound_of_certCheck converts a passing certificate at any truncation index c at least 9 into the bound v + v' <= b for every rational a/b equal to the prime series, with the omitted tail controlled by 5000(c+1)^4/2^(c+1). cert_10000 discharges that certificate at c = 1229 and X = 10000 on four explicit constants of 177 and 178 digits by kernel evaluation, and the sum v + v' of the two recorded denominators is at least 2^589. A lower bound on the denominator of a rational representation is compatible with rationality of either series. The package supplies no irrationality theorem and Erdős Problem 251 is not decided here.

Boundary. Four source-backed declarations expose a kernel-decided denominator floor of 2^589 for the Erdős #251 prime-gap series and for the zero-based prime series, together with the trial-division certificate that produces it. No irrationality theorem is claimed.

Source: [`ExternalVerification251KernelDenominatorFloor/`](ExternalVerification251KernelDenominatorFloor/), configuration `ExternalVerification251KernelDenominatorFloor/comparator.json`.

### Erdős #249: irrationality of fixed-resolution observables of the totient word

Fix a natural number m at least 2, an integer-valued letter map f on residues with f 0 = 0, and a residue r below m with gcd(r+1, m) = 1 and f r nonzero. The sum over all natural numbers n of f(φ(n) mod m) / 2^n is irrational. Six declarations are compared. At the dyadic resolutions m = 2^k with k at least 1 the coprimality condition is automatic at every even residue, so every integer-valued letter map vanishing at the zero residue and nonzero at some even residue below 2^k has irrational binary value. Specialising the letter map to the least nonnegative residue gives the headline consequence: for every m at least 3 the series A_m, the sum over all natural numbers n of (φ(n) mod m) / 2^n, is irrational. Three further declarations expose the machinery. The isolated pulse separation is the Diophantine core. For an integer sequence a whose terms are bounded in absolute value by C, a letter t at position N+1+L with t nonzero and a(N+1+i) = 0 for every i at most 2L other than i = L, and a positive integer q with 2qC < 2^L, every integer k satisfies q(|t| - C/2^L)/2^(N+1+L) ≤ |qV - k|, where V is the sum over all natural numbers n of a(n)/2^n. The packaged consumer of that separation proves that a bounded integer sequence carrying, for every L, a nonzero letter flanked by L zeros on each side has irrational binary value. The two-sided prime isolation supplies those pulses. For m at least 2 and r with gcd(r+1, m) = 1 and any bounds L and N there is a prime p exceeding both N and L+1 with φ(p) congruent to r modulo m and with m dividing φ(p-j) and φ(p+j) for every j with 0 < j ≤ L. Auxiliary primes congruent to 1 modulo m come from Dirichlet's theorem on primes in arithmetic progressions, and the Chinese remainder theorem glues them into a single congruence class for p. The separation mechanism is the Lambert-series argument of P. Erdős, On arithmetical properties of Lambert series, Journal of the Indian Mathematical Society 12 (1948); the declarations compared here apply it to the reduced sequences φ(n) mod m and no exact prior statement of them has been located. Every compared declaration is a statement about a reduced sequence φ(n) mod m or about an abstract bounded integer sequence. The value of the series in Erdős Problem 249, the sum over n at least 1 of φ(n)/2^n, is the subject of no declaration here, and that problem remains open. The converse half of the rational-relation classification for rational-valued letter maps and the bit-plane independence corollary are absent from this package. The rationality of A_1 and A_2 has no Lean witness in this development, so the hypothesis m at least 3 is stated without a sharpness claim.

Boundary. Six exact source-backed declarations. Challenge.lean contains six intentional Comparator specification sorries.

Source: [`ExternalVerification249ResidueClassTotientSeries/`](ExternalVerification249ResidueClassTotientSeries/), configuration `ExternalVerification249ResidueClassTotientSeries/comparator.json`.

### Erdős #269: the cofinal local-window escape is equivalent to irrationality of the three-prime running-LCM value

The actual cofinal local-window escape for the {2,3,5} dyadic shell orbit is equivalent to irrationality of the running-LCM value, with no hypotheses. Write H(x) = 2^(log 2 x) 3^(log 3 x) 5^(log 5 x) for the three-prime running-LCM height, let the dyadic shell at index a be the set of exponent triples (i,j,k) with 2^a <= 2^i 3^j 5^k < 2^(a+1), let the shell mass be the sum of 1/H(2^i 3^j 5^k) over that shell, and let S(a) be the sum of the shell masses from index a onward. The actual radix word b(a) is 2 times 3 or 1 according to whether a pure 3-power lies strictly inside the dyadic block, times 5 or 1 according to whether a pure 5-power does; the actual ordered digit m(a) is the shell cardinality corrected by the two threshold counts with the suffix coefficients 10 and 4 when the 3-jump precedes the 5-jump and 2 and 12 in the reverse order. The escape proposition at a short bound sb asserts that for every positive B coprime to 30 and every starting index there are lo at least that index and a positive window length len for which the window base is nonzero and the least positive residue of -B times the window forcing modulo the absolute window base exceeds sb B (lo+len); the actual escape is this proposition at the radix word b, the digit m, and the short bound B times 90 (n+1)^2. Eight declarations are compared. The actual escape holds if and only if S(0) is irrational, and if and only if S(1) is irrational. Irrationality of S(1) implies the escape at every short bound sb admitting a function c with sb B n at most c B (n+1)^2, which covers the actual short bound and every rescaling and sharpening of it inside the quadratic family. A rational value S(1) = p/q with q positive yields a positive B coprime to 30, a finite onset a0, and an integer sequence d satisfying d(n+1) = b(n) d(n) - B m(n), 0 < d(n), and |d(n)| at most B times 90 (n+1)^2 for every n at least a0. The normalized state X(a) = (H(2^a)/2) S(a) satisfies the exact window identity X(lo+len) = W X(lo) - F for the integer window base W and window forcing F of b and m. If that residue at (lo, len) is at most K and K is at least B times 90 (lo+len+1)^2, then B X(lo) lies within K / 2^len of an integer, for every K meeting the width condition and with no growth condition on K. For all c and lo there is a positive len with c (lo+len+1)^2 < 2^len. The equivalence establishes that the escape proposition is exactly as strong as the target, so proving it is proving Erdős #269. It proves neither side. Erdős #269 remains open, and nothing here bounds, computes, or decides the irrationality of S(0).

Boundary. Eight compared theorems expose the headline equivalence against S(0), the equivalence against S(1), the forward implication from irrationality to the actual escape, the quadratic-family form of that implication, the rationality-to-carry bridge, the real window identity for the genuine normalized state, the residue pinning inequality at an arbitrary admissible short bound, and the elementary exponential-over-quadratic window length. Challenge.lean contains eight deliberate specification sorries; the proof-bearing Solution imports the checked source.

Source: [`ExternalVerification269WindowEscapeEquivalence/`](ExternalVerification269WindowEscapeEquivalence/), configuration `ExternalVerification269WindowEscapeEquivalence/comparator.json`.

### Erdős #68: explicit cubic radius floor for simultaneous factorial channel cancellation

A channel is an index d at least 2 carrying the modulus d! - 1, obtained by reweighting each factorial term of the series so that the powers of d! divide out; the channel test at d compares that reweighted integer with the factorial moment modulo d! - 1. Six declarations are compared. The sharpest is explicit: for every t at least 2^32 and all natural numbers M and R with M positive, M divisible by the least common multiple of d! - 1 over 2 ≤ d ≤ 2t^2, and M < (R+1)! - 1, the support radius satisfies 3t^3 < 2(R+1). The same hypotheses imposed from t = 4096 onwards give t^3 < 8(R+1), which is the explicit bound available on 4096 ≤ t < 2^32. Imposing each hypothesis set at every large t gives the sequence forms: no radius function can eventually satisfy 2(R(t)+1) ≤ 3t^3, no radius function can eventually satisfy 8(R(t)+1) ≤ t^3, and R(t)+1 is not o(t^3). The sixth declaration evaluates the finite logarithmic constraint that produces these bounds at the value R+1 = (16/9)t^3 and proves that for every t at least 4 the constraint is satisfied there. That declaration bounds no support radius. It establishes that the logarithmic constraint alone does not force a lower bound at the constant 16/9, while the constant proved on this subsequence is 3/2. The subcubic range is closed on the square subsequence D = 2t^2, since every finite channel system meeting the hypotheses carries support radius above (3/2)t^3. The nontrivial input is a finite lower estimate for the channel least common multiple, in which consecutive numbers d! - 1 are combined while their pairwise gcd losses are counted explicitly, and a Stirling bound converts that estimate into the cubic radius. This theorem family is the first presentation recorded in the development and its novelty is unassessed. The divisibility and factorial bounds remain hypotheses, so the irrationality question in Erdős Problem 68 is untouched, and the remaining problem is to derive those hypotheses from the factorial-gap series and to prove that the required channels vanish.

Boundary. Six exact source-backed declarations; one trusted sorry per Challenge theorem.

Source: [`ExternalVerification68ChannelRadius/`](ExternalVerification68ChannelRadius/), configuration `ExternalVerification68ChannelRadius/comparator.json`.

### Erdős #1049: the rational-base contour of Zudilin's (14,12,14;27) forms

A Mathlib-only interface redeclares the trigamma series, the thirteen interval contributions summing to J, the constants C_1 = 1091/2 and C_0 = 266 - (3/pi^2)(225 - J) of Zudilin's (14,12,14;27) forms, the rational-base threshold theta* = C_0/C_1, and the parameter region of reduced bases a/b with log b / log a < theta*. Six statements are checked: the two-sided bound 81/200 < theta* < 1/2, the exclusion of 3/2 from the region, the membership of every positive power of 31/4, and the intermediate constants J >= 77.6 and C_0 > 88371/400. Membership in the region is a statement about parameters. It is the hypothesis consumed by the ordinary proof note attached to these forms, which derives irrationality of F(a/b) = sum_{m>=1} 1/((a/b)^m - 1) for every reduced base in the region from Zudilin's Lemma 7 and the accompanying lemmas. No theorem in this package formalises an analytic step of that note and none asserts anything about the arithmetic nature of F(a/b), so the package does not solve Erdős Problem 1049; irrationality at 3/2 remains open. The direction, the thirteen demi-intervals, the values C_1 = 545.5 and C_0 = 221.30008816..., and the ratio C_1/C_0 = 2.46497868... are printed in Zudilin 2004 (Acta Arith. 111, no. 2, p. 162), where that ratio is the integer-base irrationality-exponent bound of its Theorem 1. The constant theta* checked here is the reciprocal of that printed ratio. Zudilin 2016 separately announced a rational-base extension of the results of that later paper without computing a value. Novelty of the explicit rational-base threshold for F is unassessed.

Boundary. Six exact numeric and membership declarations; one trusted sorry per Challenge theorem.

Source: [`ExternalVerification1049RationalBaseContour/`](ExternalVerification1049RationalBaseContour/), configuration `ExternalVerification1049RationalBaseContour/comparator.json`.

### Erdős #243: bounded-negative-part rigidity for reciprocal-tail dynamics

Clearing denominators in the rational case of Erdős Problem 243 produces an exact integer orbit: multipliers a n greater than 1 drive C (n+1) + D n = a n * C n and D (n+1) = a n * D n, and the centred error is E n = D n - (a n - 1) * C n. The compared theorem proves complete rigidity of the bounded-negative branch of that orbit. An eventual one-sided lower bound -B ≤ E n on the centred error, together with division-free normalized vanishing K * Int.natAbs (E n) < C n at every scale K, forces two conclusions at once: the centred error is exactly zero from some index onward, and the multipliers satisfy the exact Sylvester recurrence a (n+1) = a n ^ 2 - a n + 1 from some index onward. The second conclusion is the Sylvester recurrence itself, which is the target shape for this dynamics, so the theorem reaches that endpoint inside the stated regime. The hypothesis list contains no periodicity assumption, no eventual periodicity assumption, and no sign condition on the centred error, so the statement covers aperiodic orbits and orbits whose centred error changes sign infinitely often. The normalized-vanishing hypothesis is stated division-free over the natural numbers, so the theorem consumes no real-analytic input. Eventual strict centring Int.natAbs (E n) < C n is the K = 1 instance of normalized vanishing and is absorbed into that hypothesis. The proof runs a natural-tail descent on the eventually nonnegative branch and a gcd-stabilisation and scale-reduction obstruction on the recurring bounded-negative branch, then composes the resulting zero-defect statement with the algebraic step that turns a vanishing centred state into the Sylvester successor. The exact recurrence, the one-sided lower bound, and normalized vanishing are hypotheses of the theorem. No declaration in this package produces them for an arbitrary orbit, orbits with cofinally unbounded negative centred error lie outside the statement, and Erdős Problem 243 remains open.

Boundary. In the `ExternalVerification243BoundedNegativePartRigidity` entry, one compared theorem packages eventual zero centred defect and the eventual exact Sylvester recurrence under the bounded-negative hypotheses, and its Challenge.lean has one intentional Comparator specification sorry. Its Solution.lean and the imported source are sorry-free.

Source: [`ExternalVerification243BoundedNegativePartRigidity/`](ExternalVerification243BoundedNegativePartRigidity/), configuration `ExternalVerification243BoundedNegativePartRigidity/comparator.json`. One theorem is compared in that family entry; the Palomar entry [`PalomarCorpus/E243`](PalomarCorpus/E243/) compares the same theorem together with 27 others.

### Erdős #1041: global two-root critical proximity and exact straight-line obstructions

For every degree n at least two and every list of n complex roots, at a critical point that is not a root the two distances to some pair of distinct root occurrences sum to at most twice the geometric mean of the n distances from that point. Behind the unit-disk regime stands a real-scalar inequality in N, t, d and e with no polynomial, root or critical point in its statement: for reals N at least two, t less than one, and 0 < d at most e with d at most 1, e at most 1 + t, e at most (N-1)d, and N at most (1 - t^2)(1/d^2 + (N-1)/e^2), the sum d + e is at most 2. Its intended reading takes N as the degree, t as the modulus of the critical point, and d at most e as the two smallest distances from that point to the roots. Strengthening e at most 1 + t to e less than 1 + t upgrades the conclusion to d + e strictly less than 2. The three displayed points 99/100, (99/100)w and (99/100)w^2, with w the primitive cube root of unity -1/2 + (sqrt 3 / 2)i, are roots of the monic cubic z^3 - (99/100)^3, every one of them has modulus strictly less than 1, and the midpoint of every pair of distinct roots has cubic value of modulus strictly larger than 1. That is an exact countermodel to universal straight-line containment for a polynomial whose roots satisfy the open-unit-disk hypothesis of Erdős #1041. For the explicit quintic root set a, ip, -ip, pu_plus, pu_minus with p = 999/1000, a = (901/902)p and u_plus, u_minus = (-451 +- 780i)/901, the sum of reciprocals of the five roots is zero, so the origin is a critical point, and the real root a has squared modulus strictly smaller than that of each of the other four roots, so it is the unique nearest root. At one tenth of that unique nearest spoke the factored quintic has modulus strictly larger than 1. The mechanism is the vanishing sum of reciprocals at a critical point converted into an inverse-square budget on the two smallest root distances, which is what makes the metric conclusion uniform in the degree, and priority for these statements is unassessed. The positive theorems supply distances between roots and critical points. Lemniscate containment lies outside their conclusions. The two obstructions rule out straight root-pair segments and the straight unique-nearest-root spoke, curved paths remain open, and Erdős #1041 remains open.

Boundary. Nine compared theorems expose the scale-sensitive critical metric selector, the global disk inverse-balance theorem and strict refinement, the complete quintic unique-nearest-spoke obstruction with its critical-point and uniqueness components, and the complete cubic all-straight-pair obstruction with its root identification and open-unit-disk certificate, without claiming unrestricted containment. The cubic safe-spoke theorem is compared only in ExternalVerification1041SolvedFamilies, so no declaration is owned by two entries.

Source: [`ExternalVerification1041CriticalGeometry/`](ExternalVerification1041CriticalGeometry/), configuration `ExternalVerification1041CriticalGeometry/comparator.json`.

## Every entry in this release

| Problem | Result | Entry |
| --- | --- | --- |
| #68 | Erdős #68: explicit cubic radius floor for simultaneous factorial channel cancellation | [`ExternalVerification68ChannelRadius`](ExternalVerification68ChannelRadius/) |
| #68 | Erdős #68 companion-orbit rationality boundary | [`ExternalVerification68CompanionOrbitBoundary`](ExternalVerification68CompanionOrbitBoundary/) |
| #68 | Erdős #68: remote factorial-grid kernels reduced by an exact prime unit translator | [`ExternalVerification68PrimeUnitTranslator`](ExternalVerification68PrimeUnitTranslator/) |
| #243 | Erdős #243: bounded-negative-part rigidity for reciprocal-tail dynamics | [`ExternalVerification243BoundedNegativePartRigidity`](ExternalVerification243BoundedNegativePartRigidity/) |
| #243 | Erdős #243: exclusion of bounded-rise reduced tails | [`ExternalVerification243BoundedRiseReducedTail`](ExternalVerification243BoundedRiseReducedTail/) |
| #243 | Erdős #243: exclusion of eventually periodic negative-magnitude orbits | [`ExternalVerification243PeriodicNegativeOrbit`](ExternalVerification243PeriodicNegativeOrbit/) |
| #249 | Erdős #249: unconditional clean prime anchors in the binary cyclotomic layers | [`ExternalVerification249BinaryCyclotomicAnchors`](ExternalVerification249BinaryCyclotomicAnchors/) |
| #249 | Erdős #249: complete dyadic totient-kernel structure | [`ExternalVerification249DyadicTotientKernel`](ExternalVerification249DyadicTotientKernel/) |
| #249 | Erdős #249: no finite linear recurrence for the Möbius-Mersenne power ladder, and its separation from the literal Möbius-Lambert ladder | [`ExternalVerification249MobiusMersenneLadderStructure`](ExternalVerification249MobiusMersenneLadderStructure/) |
| #249 | Erdős #249: a parity-perturbed rational control for the binary totient series | [`ExternalVerification249ParityPerturbedRationalControl`](ExternalVerification249ParityPerturbedRationalControl/) |
| #249 | Erdős #249: sharp minimiser and explicit 21/320 floor for the positive rank-one Möbius Mersenne cone | [`ExternalVerification249RankOneSharpFloor`](ExternalVerification249RankOneSharpFloor/) |
| #249 | Erdős #249: irrationality of fixed-resolution observables of the totient word | [`ExternalVerification249ResidueClassTotientSeries`](ExternalVerification249ResidueClassTotientSeries/) |
| #251 | Erdős #251: exact rational-tail collapse for the actual prime-gap dyadic series | [`ExternalVerification251ActualPrimeGapTail`](ExternalVerification251ActualPrimeGapTail/) |
| #251 | Erdős #251: bounded-perturbation countermodel anchored at the actual prime gaps | [`ExternalVerification251BoundedPerturbationCountermodel`](ExternalVerification251BoundedPerturbationCountermodel/) |
| #251 | Erdős #251: free-pair equivalence for the actual prime-gap dyadic series | [`ExternalVerification251FreePairEquivalence`](ExternalVerification251FreePairEquivalence/) |
| #251 | Erdős #251: kernel-decided denominator floor for the prime-gap dyadic series | [`ExternalVerification251KernelDenominatorFloor`](ExternalVerification251KernelDenominatorFloor/) |
| #251 | Erdős #251: exact countermodel to coarse gap-profile irrationality routes | [`ExternalVerification251PolynomialShiftCountermodel`](ExternalVerification251PolynomialShiftCountermodel/) |
| #251 | Erdős #251: unconditional prime-gap reformulation of the dyadic prime series | [`ExternalVerification251PrimeGapIdentity`](ExternalVerification251PrimeGapIdentity/) |
| #257 | Erdős #257: rational-fibre null theorem and supported Mersenne achievement-set geometry | [`ExternalVerification257AchievementSetGeometry`](ExternalVerification257AchievementSetGeometry/) |
| #257 | Erdős #257: exact multiplicative-order noncollapse at every integer base | [`ExternalVerification257FinitePeriodNoncollapse`](ExternalVerification257FinitePeriodNoncollapse/) |
| #257 | Erdős #257: rational values force unbounded integer tail orbits and mass lower bounds | [`ExternalVerification257RationalTailRigidity`](ExternalVerification257RationalTailRigidity/) |
| #257 | Erdős #257: irrationality for every reciprocal-summable support and every integer base | [`ExternalVerification257ReciprocalSupport`](ExternalVerification257ReciprocalSupport/) |
| #269 | Erdős #269: actual dyadic shell orbit, exact recurrence and integral-or-far escape | [`ExternalVerification269ActualShellOrbit`](ExternalVerification269ActualShellOrbit/) |
| #269 | Erdős #269: exact three-prime running-LCM identity and infinite kernel rank | [`ExternalVerification269ThreePrimeStructure`](ExternalVerification269ThreePrimeStructure/) |
| #269 | Erdős #269: the cofinal local-window escape is equivalent to irrationality of the three-prime running-LCM value | [`ExternalVerification269WindowEscapeEquivalence`](ExternalVerification269WindowEscapeEquivalence/) |
| #1041 | Erdős #1041: straight-chord selection from quantitative collinear critical-gap data | [`ExternalVerification1041CollinearChord`](ExternalVerification1041CollinearChord/) |
| #1041 | Erdős #1041: global two-root critical proximity and exact straight-line obstructions | [`ExternalVerification1041CriticalGeometry`](ExternalVerification1041CriticalGeometry/) |
| #1041 | Erdős #1041: sublevel containment of trinomial root spokes | [`ExternalVerification1041CyclicTrinomialFiber`](ExternalVerification1041CyclicTrinomialFiber/) |
| #1041 | Erdős #1041: uniform disk-family critical-value separation thresholds and a sign-free connector-length bound | [`ExternalVerification1041DiskFamilySeparation`](ExternalVerification1041DiskFamilySeparation/) |
| #1041 | Erdős #1041: exact all-degree critical-value separation thresholds and a sign-free first-merge length bound | [`ExternalVerification1041FirstMergeCriticalValueSeparation`](ExternalVerification1041FirstMergeCriticalValueSeparation/) |
| #1041 | Erdős #1041: strict length budget below two for quotient-fibre root lifts | [`ExternalVerification1041QuarticQuotientFiber`](ExternalVerification1041QuarticQuotientFiber/) |
| #1041 | Erdős #1041: checked kernels for three completely solved polynomial families | [`ExternalVerification1041SolvedFamilies`](ExternalVerification1041SolvedFamilies/) |
| #1041 | Erdős #1041: coefficient and energy criteria forcing two safe tetranomial spokes | [`ExternalVerification1041TetranomialSpokes`](ExternalVerification1041TetranomialSpokes/) |
| #1049 | Erdős #1049: exact first transformed Zudilin row and the 2^64 < 3^41 < 2^65 bracket | [`ExternalVerification1049AdelicHeightBridge`](ExternalVerification1049AdelicHeightBridge/) |
| #1049 | Erdős #1049: sharp rectangular Hermite–Padé threshold no-go with unique equality point | [`ExternalVerification1049HermitePadeNoGo`](ExternalVerification1049HermitePadeNoGo/) |
| #1049 | Erdős #1049: sharp rational gaps for integral linear forms and the exterior-determinant height tradeoff | [`ExternalVerification1049PrimeSupportSelectors`](ExternalVerification1049PrimeSupportSelectors/) |
| #1049 | Erdős #1049: no coordinatewise denominator clearing at the rational base 3/2 | [`ExternalVerification1049RationalBaseBarrier`](ExternalVerification1049RationalBaseBarrier/) |
| #1049 | Erdős #1049: the rational-base contour of Zudilin's (14,12,14;27) forms | [`ExternalVerification1049RationalBaseContour`](ExternalVerification1049RationalBaseContour/) |

## Reading an entry

A Palomar entry `PalomarCorpus/E{n}` is four files: `Challenge.lean`, `comparator.json`
and `formalization.yaml` in its directory, and its Solution `Solutions/PalomarCorpus/E{n}.lean`
with the adapters under `Solutions/PalomarCorpus/E{n}/`. Among the adapters,
`Statement.lean` is the Challenge minus its theorems, generated from it and compiled
against Mathlib alone; the other adapters import it instead of re-declaring any
definition, so the constants Comparator walks from each compared statement are the
same on both sides. Its axiom audit is supplied by
`scripts/check_axiom_budget.py --run-palomar`, which the release gate runs. The per-problem
sections above and the table below describe the `ExternalVerification*` family entries, the
internal regression inventory; their theorem counts are not the counts of the
`PalomarCorpus/E{n}` configurations.

Each `ExternalVerification*` entry is five files: four in its directory and its Solution under `Solutions/`.

- `<Entry>/Challenge.lean` states the theorem for a reviewer and does not prove it.
- `Solutions/<Entry>.lean` proves it. A `sorry` here would be fatal and there is none.
- `<Entry>/AxiomAudit.lean` prints the axioms each selected declaration depends on.
- `<Entry>/comparator.json` is the configuration a registry submission names.
- `<Entry>/formalization.yaml` records scope, sources, attribution and known divergences.

The Solution lives under its own module prefix because the registry compiles each
Challenge into a protected directory that shadows every module sharing its prefix.

## Method

[`METHOD.md`](METHOD.md) describes how the work reaches the models that do a large part
of it, and what makes the result safe to accept. In short: reasoning depth and harness
fitness are separable capabilities, the strongest available reasoner is often the one
with no tool access and one response per question, and the entry format below is what
converts an argument from such a source into a checked theorem. The test never asks who
produced the proof, which is what lets an argument be accepted from a source that cannot
be supervised.

[`skills/lean-checkpoint-entry/SKILL.md`](skills/lean-checkpoint-entry/SKILL.md) is the
authoring and review procedure for an entry, written to be usable against any problem
set and any proof assistant convention, not only this one.

## What this repository does not establish

A Lean proof establishes that the Solution proves the theorem the Challenge states,
on the axioms the audit prints. It does not establish that a result is new, that it
is important, or that anyone has reviewed it. Where the literature does not settle
novelty, the metadata records novelty as unassessed and makes no priority claim.
No human mathematical peer review is claimed for any entry in this release.

## Authorship

Will Cook is the human author and responsible maintainer.
AI systems assisted with mathematical exploration, proof search, formalisation and
Lean engineering, including systems reached only through a chat interface with no
access to this repository; [`METHOD.md`](METHOD.md) describes that arrangement and its
verification boundary. The author selected the public claims, reviewed their stated
boundaries and accepts responsibility for every statement in this repository.

## Citation

Cite this repository through `CITATION.cff`, at the commit you read.

## Build

```sh
lake exe cache get
lake build
```
