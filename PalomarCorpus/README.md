# Formal reductions, obstruction theorems, and verified subfamilies for eight Erdős problems

The Palomar publication entries of this repository. Each entry is one Comparator configuration, `PalomarCorpus/<entry>/comparator.json`, with its Challenge, its `formalization.yaml` and an `AxiomAudit.lean`; its Solution is `Solutions/PalomarCorpus/<entry>.lean`.

The entries restate the theorems of the Lean development for each problem in the order the papers state them: the long record first, then results stated only in the short note, then theorems no paper statement is bound to, grouped by the family they come from. Each theorem appears in exactly one entry, and every Challenge is at most 300 lines and 32 KiB. Family `ExternalVerification*` modules remain internal regression inventory.

## Entries

| Entry | Theorems | Title |
|---|---:|---|
| [`E68_01`](E68_01/) | 9 | Erdős #68, record sections 1 to 3: which prime powers survive reduction; the growth of the common denominator; rationality and the next integer above a scaled partial sum |
| [`E68_02`](E68_02/) | 9 | Erdős #68, record sections 3 to 5: rationality and the next integer above a scaled partial sum; a sufficient comparison between the tail and an integer gap; what can be achieved by cancelling finitely many weighted sums |
| [`E68_03`](E68_03/) | 7 | Erdős #68, record section 5.1: all solutions and their remainders modulo integers (part 1 of 2) |
| [`E68_04`](E68_04/) | 1 | Erdős #68, record section 5.1: all solutions and their remainders modulo integers (part 2 of 2) |
| [`E68_05`](E68_05/) | 6 | Erdős #68, note sections 1 to A: the denominator exclusions; integer vectors for cancelling weighted sums; comparing the tail with the distance to an integer |
| [`E68_06`](E68_06/) | 16 | Erdős #68, the adjacent unit carry window, channel radius and common denominator growth families |
| [`E68_07`](E68_07/) | 5 | Erdős #68, the finite denominator, Kempner index and moment ideal families |
| [`E68_08`](E68_08/) | 6 | Erdős #68, the moving factor scale split and multiplicative successor rigidity families |
| [`E68_09`](E68_09/) | 12 | Erdős #68, the multiplicative successor rigidity, prime pole and prime unit translator families |
| [`E68_10`](E68_10/) | 2 | Erdős #68, the strict successor carry family |
| [`E243_01`](E243_01/) | 13 | Erdős #243, record section 2: irrationality at the cubic rate; reduction under the zero lower-density assumption; a square condition from three consecutive numerators |
| [`E243_02`](E243_02/) | 15 | Erdős #243, record sections 4 to 7: integer numerators, denominators and errors; when a zero error forces the Sylvester recurrence; a criterion using new maxima of an LCM numerator |
| [`E243_03`](E243_03/) | 15 | Erdős #243, record sections 7.1 to 7.2: how fast the running maximum must increase; bounds that allow for cancellation and earlier decreases |
| [`E243_04`](E243_04/) | 8 | Erdős #243, record section 7.2: bounds that allow for cancellation and earlier decreases |
| [`E243_05`](E243_05/) | 8 | Erdős #243, record section 7.3: counting jumps before a prime power can be lost |
| [`E243_06`](E243_06/) | 14 | Erdős #243, record section 7.4: bounds on the error and on the original sequence |
| [`E243_07`](E243_07/) | 17 | Erdős #243, record sections 7 to 9: new maxima of reduced numerators; descent when the error is nonnegative; when the negative error is constant |
| [`E243_08`](E243_08/) | 14 | Erdős #243, record sections 10 to B: when the negative error is periodic; bounded increases and coprimality to earlier moduli; a lower bound on the error forces eventual zero |
| [`E243_09`](E243_09/) | 7 | Erdős #243, note sections 2 to 8: proof under a lower bound on the error; the arithmetic ingredients; a criterion using new maxima of an LCM numerator |
| [`E243_10`](E243_10/) | 16 | Erdős #243, the bounded negative part rigidity, bounded rise reduced tail and periodic negative orbit families |
| [`E243_11`](E243_11/) | 13 | Erdős #243, the record amplified cancellation visibility, record increment barrier and repair entropy families |
| [`E249_01`](E249_01/) | 23 | Erdős #249, record section 1.1: unconditional results |
| [`E249_02`](E249_02/) | 15 | Erdős #249, record sections 1 to 2: totient sections and tail differences; rational comparison sequences |
| [`E249_03`](E249_03/) | 16 | Erdős #249, record section 2.3: limits of specific reductions and estimates |
| [`E249_04`](E249_04/) | 20 | Erdős #249, record sections 2 to 5: rational comparison sequences; series identities and finite exclusions |
| [`E249_05`](E249_05/) | 20 | Erdős #249, record sections 5 to 6: series identities and finite exclusions; detailed statements |
| [`E249_06`](E249_06/) | 33 | Erdős #249, record sections 6.1 to 6.2: unconditional structure and finite examples; definitions and elementary identities |
| [`E249_07`](E249_07/) | 28 | Erdős #249, record section 6.2.1: initial implications (part 1 of 2) |
| [`E249_08`](E249_08/) | 22 | Erdős #249, record section 6.2.1: initial implications (part 2 of 2) |
| [`E249_09`](E249_09/) | 32 | Erdős #249, record sections 6.2.1 to 6.2.2: initial implications; equivalent quantified certificate conditions |
| [`E249_10`](E249_10/) | 15 | Erdős #249, record section 6.2.2: equivalent quantified certificate conditions |
| [`E249_11`](E249_11/) | 13 | Erdős #249, record section 6.3: consequences (part 1 of 3) |
| [`E249_12`](E249_12/) | 19 | Erdős #249, record section 6.3: consequences (part 2 of 3) |
| [`E249_13`](E249_13/) | 2 | Erdős #249, record section 6.3: consequences (part 3 of 3) |
| [`E249_14`](E249_14/) | 21 | Erdős #249, record section 6.4: further exact identities (part 1 of 3) |
| [`E249_15`](E249_15/) | 22 | Erdős #249, record section 6.4: further exact identities (part 2 of 3) |
| [`E249_16`](E249_16/) | 29 | Erdős #249, record section 6.4: further exact identities (part 3 of 3) |
| [`E249_17`](E249_17/) | 33 | Erdős #249, record sections 6.6.1 to 6.6.5: log-concavity of the Möbius-weighted series; integer recurrences and rational binary series; rational approximation with a squared-Mersenne remainder |
| [`E249_18`](E249_18/) | 28 | Erdős #249, record sections 6.6.5 to 6.6.9: a numerator polynomial with explicit positive coefficients; exact dyadic comparisons and tail bounds; squared distances between complex phases |
| [`E249_19`](E249_19/) | 24 | Erdős #249, record sections 6.6.9 to 6.6.13: coprime-pair sums; the single-parameter diagonal condition; prime divisors of Mersenne factors and finite exclusions |
| [`E249_20`](E249_20/) | 1 | Erdős #249, record section 6.6.13: the lower bound for rank-one quotients |
| [`E249_21`](E249_21/) | 19 | Erdős #249, record sections 6 to 9: detailed statements; index of unproved conditions |
| [`E249_22`](E249_22/) | 15 | Erdős #249, record sections 9.3.1 to 9.3.2: positivity and the remaining residue inequality; an exact endpoint identity |
| [`E249_23`](E249_23/) | 15 | Erdős #249, record sections 9.3.2 to 9.3.4: an exact endpoint identity; a bound on the last totient difference; separation of a rational approximation |
| [`E249_24`](E249_24/) | 31 | Erdős #249, record sections 9.3.4 to 9.3.10: separation of a rational approximation; the short-window examples through exponent 6; the diagonal certificate table |
| [`E249_25`](E249_25/) | 23 | Erdős #249, record sections 9.3.10 to 9.3.13: the residue margin at an LCM jump; a certificate for a four-tail combination; denominators of Möbius sums |
| [`E249_26`](E249_26/) | 10 | Erdős #249, record sections 9 to 10: index of unproved conditions; counterexamples to proposed deductions |
| [`E249_27`](E249_27/) | 20 | Erdős #249, record sections 12.1 to 12.2: the doubling identity; the full-block exponential-sum estimate |
| [`E249_28`](E249_28/) | 3 | Erdős #249, record sections 12.3 to 12.5: the four-term decomposition; depth equal to a period multiple |
| [`E249_29`](E249_29/) | 5 | Erdős #249, note section 1; the totient kernel basis family: a basis and all its relations; proof of the basis theorem |
| [`E249_30`](E249_30/) | 9 | Erdős #249, note sections 1 to 4: a basis and all its relations; bounded residues and rationality; tail differences and finite residue tests |
| [`E249_31`](E249_31/) | 9 | Erdős #249, the actual lcm orbit, binary cyclotomic anchors and canonical Mersenne frontier families |
| [`E249_32`](E249_32/) | 19 | Erdős #249, the carry rank frontier, dyadic totient kernel and Farey window exclusion families |
| [`E249_33`](E249_33/) | 27 | Erdős #249, the prefix two adic exclusion, rank one sharp floor and rational observable classification families |
| [`E251_01`](E251_01/) | 11 | Erdős #251, record sections 2 to 5: sparse congruence-preserving perturbations; summation by parts, with the endpoint retained; the tail recurrence and the exact criteria |
| [`E251_02`](E251_02/) | 12 | Erdős #251, record sections 5 to 8: the tail recurrence and the exact criteria; a local certificate, and one actual pair; two lower bounds on a possible rational denominator |
| [`E251_03`](E251_03/) | 10 | Erdős #251, record sections 8.2 to 8.6: algebraic nonconcentration survives the rationalising perturbation; the two-window event has density zero; recurring gap values differing by two do not suffice |
| [`E251_04`](E251_04/) | 6 | Erdős #251, record sections D to E: further criteria, examples and computational details; arithmetic-progression reformulations of integrality |
| [`E251_05`](E251_05/) | 10 | Erdős #251, note sections 1 to 4: introduction; the prime series and its actual tails; integral shifts: an exact algebraic classification |
| [`E251_06`](E251_06/) | 20 | Erdős #251, the actual prime gap tail, affine circularity and all residue logarithmic countermodel families |
| [`E251_07`](E251_07/) | 13 | Erdős #251, the lcm diagonal criterion, polynomial shift countermodel and prime gap identity families |
| [`E251_08`](E251_08/) | 5 | Erdős #251, the shifted four prime counting and sparse rationalisation families |
| [`E257_01`](E257_01/) | 5 | Erdős #257, record sections 1.2 to 1.5: a weighted condition on the support; positive divisor majorants; combining the two support criteria |
| [`E257_02`](E257_02/) | 8 | Erdős #257, record sections 1 to 2: support criteria and their proofs; limitations of the recorded methods |
| [`E257_03`](E257_03/) | 7 | Erdős #257, record section 2.3: equivalent formulations of half-membership |
| [`E257_04`](E257_04/) | 16 | Erdős #257, record sections 2.4 to 2.5: the size of the required error bounds; what finite certificates decide |
| [`E257_05`](E257_05/) | 14 | Erdős #257, record sections 5.2 to 5.5: what is proved; integer quotients and their remainder identity; a real-valued form of the quotient identity |
| [`E257_06`](E257_06/) | 14 | Erdős #257, record section 5.6: dynamics |
| [`E257_07`](E257_07/) | 2 | Erdős #257, record section 6.1: conditional membership tests (part 1 of 5) |
| [`E257_08`](E257_08/) | 18 | Erdős #257, record sections 6 to 9: detailed results and their hypotheses; which hypotheses remain unproved (part 1 of 3) |
| [`E257_09`](E257_09/) | 1 | Erdős #257, record section 6.1: conditional membership tests (part 2 of 5) |
| [`E257_10`](E257_10/) | 17 | Erdős #257, record sections 6 to 9: detailed results and their hypotheses; which hypotheses remain unproved (part 2 of 3) |
| [`E257_11`](E257_11/) | 8 | Erdős #257, record section 6.1: conditional membership tests (part 3 of 5) |
| [`E257_12`](E257_12/) | 19 | Erdős #257, record sections 6 to 10: detailed results and their hypotheses; hypothesis-specific obstructions (part 1 of 2) |
| [`E257_13`](E257_13/) | 11 | Erdős #257, record section 6.1: conditional membership tests (part 4 of 5) |
| [`E257_14`](E257_14/) | 18 | Erdős #257, record section 6.1: conditional membership tests (part 5 of 5) |
| [`E257_15`](E257_15/) | 11 | Erdős #257, record section 6.2: exact identities and reductions (part 1 of 5) |
| [`E257_16`](E257_16/) | 15 | Erdős #257, record sections 6.2 to 6.3: exact identities and reductions; consequence theorems (part 1 of 2) |
| [`E257_17`](E257_17/) | 15 | Erdős #257, record section 6.2: exact identities and reductions (part 2 of 5) |
| [`E257_18`](E257_18/) | 2 | Erdős #257, record section 6.2: exact identities and reductions (part 3 of 5) |
| [`E257_19`](E257_19/) | 14 | Erdős #257, record sections 6.2 to 6.3: exact identities and reductions; consequence theorems (part 2 of 2) |
| [`E257_20`](E257_20/) | 15 | Erdős #257, record section 6.2: exact identities and reductions (part 4 of 5) |
| [`E257_21`](E257_21/) | 14 | Erdős #257, record section 6.2: exact identities and reductions (part 5 of 5) |
| [`E257_22`](E257_22/) | 14 | Erdős #257: two implications yielding half-membership; compatible finite approximations; a quotient bound at a crossing |
| [`E257_23`](E257_23/) | 15 | Erdős #257: a quotient bound at a crossing; filling the remaining binary positions; reducing the dyadic-boundary checks |
| [`E257_24`](E257_24/) | 1 | Erdős #257: nonnegativity of the omitted-tail margin |
| [`E257_25`](E257_25/) | 15 | Erdős #257, record sections 6 to 9: detailed results and their hypotheses; which hypotheses remain unproved (part 3 of 3) |
| [`E257_26`](E257_26/) | 8 | Erdős #257: nonnegativity of the omitted-tail margin; square-root bounds for half-carries |
| [`E257_27`](E257_27/) | 13 | Erdős #257: square-root bounds for half-carries; a margin at an unspecified later horizon; equivalent conditions for infinitely many greedy skips |
| [`E257_28`](E257_28/) | 24 | Erdős #257: one-step quotient identities; bounds for the remaining binary positions; doubling the endpoint |
| [`E257_29`](E257_29/) | 18 | Erdős #257: uniqueness for gap-dominated finite weights; a geometric form of the quotient condition; bounds for a general coefficient sequence |
| [`E257_30`](E257_30/) | 23 | Erdős #257: restrictions on a support with rational value; the first crossing of the half-value; gap lengths and the measure of their union |
| [`E257_31`](E257_31/) | 27 | Erdős #257, record sections 6 to 10: detailed results and their hypotheses; hypothesis-specific obstructions (part 2 of 2) |
| [`E257_32`](E257_32/) | 6 | Erdős #257: general identities for perturbed greedy recurrences |
| [`E257_33`](E257_33/) | 15 | Erdős #257, record section 6.5: obstructions and countermodels |
| [`E257_34`](E257_34/) | 5 | Erdős #257, record sections 6.5 to 6.6: obstructions and countermodels; further finite and conditional results |
| [`E257_35`](E257_35/) | 16 | Erdős #257, record sections 8 to 9: approximations to the greedy orbit; which hypotheses remain unproved |
| [`E257_36`](E257_36/) | 14 | Erdős #257, record sections 10.3 to 10.4: related counterexamples and restrictions; the scalar-localisation height obstruction |
| [`E257_37`](E257_37/) | 19 | Erdős #257, record sections 11.1 to 11.5: reset bounds and finite weighted divisor sums; equivalent carry conditions at perfect-square depths; sparse and dense supports under the certificate criterion |
| [`E257_38`](E257_38/) | 9 | Erdős #257, record sections 12 to 13: what is open, stated exactly; logarithmic cost under arithmetic sampling |
| [`E257_39`](E257_39/) | 8 | Erdős #257, note sections 1 to 9: introduction and main results; finite-support denominator periods; greedy membership and an integer recurrence |
| [`E257_40`](E257_40/) | 11 | Erdős #257, the achievement set geometry, actual upper successor and Boolean Mobius carry families |
| [`E257_41`](E257_41/) | 13 | Erdős #257, the fair coding, finite period noncollapse and four ninths repair windows families |
| [`E257_42`](E257_42/) | 14 | Erdős #257, the rational membership, rational tail rigidity and reciprocal support families |
| [`E257_43`](E257_43/) | 5 | Erdős #257, the twenty one fatal branch family |
| [`E269_01`](E269_01/) | 13 | Erdős #269, record sections 1 to 2: the problem, and what is settled; the finite geometry of the running value |
| [`E269_02`](E269_02/) | 13 | Erdős #269, record sections 4 to 5: why the third prime prevents finite separation; the recurrence for tails between powers of two |
| [`E269_03`](E269_03/) | 6 | Erdős #269, record sections 5 to 6: the recurrence for tails between powers of two; bounding the tails and clearing a rational denominator |
| [`E269_04`](E269_04/) | 6 | Erdős #269, record section 6: bounding the tails and clearing a rational denominator |
| [`E269_05`](E269_05/) | 7 | Erdős #269, record sections 6 to 7: bounding the tails and clearing a rational denominator; a residue criterion and the bounds it allows |
| [`E269_06`](E269_06/) | 3 | Erdős #269, record sections 7 to 9: a residue criterion and the bounds it allows; the remaining arithmetic questions |
| [`E269_07`](E269_07/) | 6 | Erdős #269, record sections 9 to 10: the remaining arithmetic questions; further examples, conditional lemmas and source references |
| [`E269_08`](E269_08/) | 6 | Erdős #269, note sections 2 to 5: nonsingular minors of every order; the recurrence for the repeated sum; a window test and the remaining arithmetic |
| [`E269_09`](E269_09/) | 12 | Erdős #269, the actual shell orbit, all scale lattice and carry mechanism families |
| [`E269_10`](E269_10/) | 11 | Erdős #269, the integral branch pinning and three prime structure families |
| [`E269_11`](E269_11/) | 9 | Erdős #269, the window escape equivalence family |
| [`E1041_01`](E1041_01/) | 17 | Erdős #1041, record sections 1 to 3: the historical question; trinomials; a small least critical value |
| [`E1041_02`](E1041_02/) | 7 | Erdős #1041, record sections 4 to 7; the cubic path family: a path estimate from area and boundary length; degree three; collinear roots and two sparse polynomial families |
| [`E1041_03`](E1041_03/) | 12 | Erdős #1041, record section 7.1: collinear roots and Chebyshev comparison |
| [`E1041_04`](E1041_04/) | 13 | Erdős #1041, record sections 7 to 10: collinear roots and two sparse polynomial families; further families and counterexamples to proposed proof steps; the Newton value equation |
| [`E1041_05`](E1041_05/) | 11 | Erdős #1041, note sections 1 to 7: monic trinomials, in every degree; critical proximity and straight-path obstructions; solved polynomial families |
| [`E1041_06`](E1041_06/) | 18 | Erdős #1041, note sections 13 to 16: two chord constructions for binomials; a Poisson identity for critical-value means; a nonlinear integral for component mergers |
| [`E1041_07`](E1041_07/) | 21 | Erdős #1041, the critical geometry, cyclic trinomial fiber and degree seven counterexample families |
| [`E1041_08`](E1041_08/) | 9 | Erdős #1041, the solved families and tetranomial spokes families |
| [`E1049_01`](E1049_01/) | 25 | Erdős #1049, record section 2: the region b^ mu < a and the base 31/4; positive linear forms with integer coefficients |
| [`E1049_02`](E1049_02/) | 4 | Erdős #1049, record section 2.6: proofs, earlier work and limitations |
| [`E1049_03`](E1049_03/) | 18 | Erdős #1049, record sections 3 to 5; the adelic height bridge family: power comparisons and Hankel determinants; congruences after evaluation at 3/2 |
| [`E1049_04`](E1049_04/) | 10 | Erdős #1049, record sections 3 to 4: power comparisons and Hankel determinants; rescaling integer rows |
| [`E1049_05`](E1049_05/) | 16 | Erdős #1049, record sections 5 to 10: congruences after evaluation at 3/2; failure of the stated clearing conditions at 3/2; successive scaled remainders |
| [`E1049_06`](E1049_06/) | 9 | Erdős #1049, note sections 2 to 4: a region of rational bases at which F is irrational; supplementary arithmetic at 3/2 |
| [`E1049_07`](E1049_07/) | 23 | Erdős #1049, the Archimedean cap, Bezout Plucker jets and Hermite Pade no go families |
| [`E1049_08`](E1049_08/) | 5 | Erdős #1049, the rational base barrier and rational base region families |

## Theorems per problem

| Problem | Entries | Theorems |
|---|---:|---:|
| #68 | 10 | 73 |
| #243 | 11 | 140 |
| #249 | 33 | 621 |
| #251 | 8 | 87 |
| #257 | 43 | 537 |
| #269 | 11 | 92 |
| #1041 | 8 | 108 |
| #1049 | 8 | 110 |
| Total | 132 | 1768 |

## Paper-linked required Lean claims

- `erdos1041.ani_degree_seven_total_variation_counterexample` (#1041, lean_kernel_checked): ani’s degree-seven total-variation counterexample
  - compared as `PalomarCorpus.E1041.DegreeSevenCounterexample.degreeSevenCounterexample`
- `erdos1041.critical_geometry` (#1041, lean_kernel_checked): global critical-disk inverse-balance and geometric-mean two-root proximity with exact straight-path obstructions
  - compared as `PalomarCorpus.E1041.CriticalGeometry.criticalGeometricMean_twoRootProximity`
  - compared as `PalomarCorpus.E1041.CriticalGeometry.criticalDiskInverseBalance_twoRootProximity`
  - compared as `PalomarCorpus.E1041.CriticalGeometry.criticalDiskInverseBalance_twoRootProximity_strict`
  - compared as `PalomarCorpus.E1041.CriticalGeometry.nearestSpoke_reciprocal_balance`
  - compared as `PalomarCorpus.E1041.CriticalGeometry.nearestSpoke_unique_nearest_normSq`
  - compared as `PalomarCorpus.E1041.CriticalGeometry.nearestSpoke_unique_nearest_spoke_escapes`
  - compared as `PalomarCorpus.E1041.CriticalGeometry.allStraightCubic_roots`
  - compared as `PalomarCorpus.E1041.CriticalGeometry.allStraightCubic_roots_in_unitDisk`
  - compared as `PalomarCorpus.E1041.CriticalGeometry.allStraightCubic_every_pair_midpoint_escapes`
- `erdos1041.cubic_case_complete` (#1041, lean_kernel_checked): Erdős #1041 in degree three
  - compared as `PalomarCorpus.E1041.CubicPath.cubic_paper_complete`
  - compared as `PalomarCorpus.E1041.CubicPath.monic_cubic_connector`
  - compared as `PalomarCorpus.E1041.CubicPath.complete_translated_cubic_quotient_fibres`
- `erdos1041.cyclic_tetranomial_coefficient` (#1041, lean_kernel_checked): coefficient-controlled cyclic tetranomial root-spoke bounds
  - compared as `PalomarCorpus.E1041.TetranomialSpokes.tetranomialRoot_spoke_factorization`
  - compared as `PalomarCorpus.E1041.TetranomialSpokes.tetranomialRoot_spoke_norm_lt_one_of_lowCoeffBudget`
  - compared as `PalomarCorpus.E1041.TetranomialSpokes.tetranomialRoot_spoke_norm_lt_one_of_rootBudget`
- `erdos1041.cyclic_trinomial_fiber` (#1041, lean_kernel_checked): centered and translated cyclic trinomial spoke-factorization and two-short-fibre endpoint
  - compared as `PalomarCorpus.E1041.CyclicTrinomialFiber.trinomialRoot_spoke_factorization`
  - compared as `PalomarCorpus.E1041.CyclicTrinomialFiber.trinomialRoot_spoke_norm_le_constant`
  - compared as `PalomarCorpus.E1041.CyclicTrinomialFiber.trinomialRoot_spoke_norm_lt_one`
  - compared as `PalomarCorpus.E1041.CyclicTrinomialFiber.trinomialRoot_spoke_norm_lt_one_of_norm_lt_one`
  - compared as `PalomarCorpus.E1041.CyclicTrinomialFiber.cyclicTrinomial_two_short_fiber_displacements`
- `erdos1041.first_merge_critical_value_separation` (#1041, lean_kernel_checked): exact first-merge numerical threshold kernel: degree monotonicity, the S=4/n>=3, S=3/n>=4, and S=2/n>=6 regimes, and the sign-free squared-length-below-four consumer
  - compared as `PalomarCorpus.E1041.FirstMergeCriticalValueSeparation.firstMerge_exact_convenient_thresholds`
  - compared as `PalomarCorpus.E1041.FirstMergeCriticalValueSeparation.firstMerge_length_lt_two_of_squared_bound`
- `erdos1041.quartic_quotient_fiber` (#1041, lean_kernel_checked): translated quartic quotient-fibre root lift and strict endpoint budget
  - compared as `PalomarCorpus.E1041.QuarticQuotientFiber.rootLift_kernel_le_axis`
  - compared as `PalomarCorpus.E1041.QuarticQuotientFiber.rootLift_axis_integral`
  - compared as `PalomarCorpus.E1041.QuarticQuotientFiber.rootLift_endpoint_budget_lt_two`
  - compared as `PalomarCorpus.E1041.QuarticQuotientFiber.rootLift_length_lt_two_of_le_endpoint_budget`
- `erdos1041.r11_analytic_all_degree_critical_value_budget` (#1041, lean_kernel_checked): All-degree critical-value mean and quadratic power budget
  - compared as `PalomarCorpus.E1041.CriticalValueMean.paper_critical_value_mean`
- `erdos1041.signed_moment_tetranomial` (#1041, lean_kernel_checked): exact signed mixed-moment energy and two-index safe-spoke selection for centered tetranomial root families
  - compared as `PalomarCorpus.E1041.TetranomialSpokes.exists_two_tetranomialRoot_safeSpokes_of_moment_coeff_budget`
  - compared as `PalomarCorpus.E1041.TetranomialSpokes.sum_normSq_const_add_mul`
  - compared as `PalomarCorpus.E1041.TetranomialSpokes.exists_two_tails_norm_lt_one_of_exact_L2_budget`
- `erdos1041.solved_families` (#1041, lean_kernel_checked): sharp all-degree collinear root-diameter theorem with equality configurations, complete primitive sparse quintic, and translated cubic quotient fibres
  - compared as `PalomarCorpus.E1041.SolvedFamilies.SharpCollinear.existsPeakLeComparisonBound`
  - compared as `PalomarCorpus.E1041.SolvedFamilies.primitiveQuintic_twoStrictTailEnergies`
  - compared as `PalomarCorpus.E1041.SolvedFamilies.cubic_safeRootSpoke`
- `erdos1041.tetranomial_spokes` (#1041, lean_kernel_checked): Coefficient and energy criteria forcing two safe tetranomial spokes
  - compared as `PalomarCorpus.E1041.TetranomialSpokes.tetranomialRoot_spoke_factorization`
  - compared as `PalomarCorpus.E1041.TetranomialSpokes.tetranomialRoot_spoke_norm_lt_one_of_rootBudget`
  - compared as `PalomarCorpus.E1041.TetranomialSpokes.tetranomialRoot_spoke_norm_lt_one_of_lowCoeffBudget`
  - compared as `PalomarCorpus.E1041.TetranomialSpokes.sum_normSq_const_add_mul`
  - compared as `PalomarCorpus.E1041.TetranomialSpokes.exists_two_tails_norm_lt_one_of_exact_L2_budget`
  - compared as `PalomarCorpus.E1041.TetranomialSpokes.exists_two_tetranomialRoot_safeSpokes_of_moment_coeff_budget`
- `erdos1049.adelic_height_bridge` (#1049, lean_kernel_checked): sharp 41/65 adelic-height threshold, scalar-plus-border no-go, and four-jet bounded-fibre escape
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.zudilin_firstTransformedRow_initialMonomial`
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.zudilinSharpHankelOrderAndCoeff_algebraicAssembly`
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.threePow_fortyOne_lt_twoPow_sixtyFive`
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.twoPow_sixtyFour_lt_threePow_fortyOne`
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.threeHalves_rectangular_hp_gap_gt_threeThirteenths`
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.threeHalves_hankelChargeThreshold_lt_eightFortyOne`
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.zudilinScalarContent_cannot_meet_required_charge`
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.zudilinScalarPlusBorder_cannot_meet_required_charge`
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.three_two_scalar_margin_lt_explicit`
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.exists_distinct_binary_selectors_same_fourJet_of_power_certificate`
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.exists_distinct_binary_selectors_same_fourJet_of_rank_41`
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.fourJet_card_gt_two_pow_of_rank_41`
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.exists_ne_map_eq_map_ne_of_card_mul_lt`
- `erdos1049.archimedean_homogenisation_cap` (#1049, lean_kernel_checked): Archimedean cap and below-square nondecay without a degree limit
  - compared as `PalomarCorpus.E1049.ArchimedeanCap.archimedean_cap`
  - compared as `PalomarCorpus.E1049.ArchimedeanCap.cleared_below_square_not_tendsto_zero`
- `erdos1049.bezout_plucker_jets` (#1049, lean_kernel_checked): conditional Bezout-Plucker minor collapse and halved binary-selector exponent threshold
  - compared as `PalomarCorpus.E1049.BezoutPluckerJets.anchor_det_zero_forces_all_det_zero`
  - compared as `PalomarCorpus.E1049.BezoutPluckerJets.binary_row_collision_of_anchor_det_zero`
  - compared as `PalomarCorpus.E1049.BezoutPluckerJets.adjacent_det_zero_forces_all_det_zero`
  - compared as `PalomarCorpus.E1049.BezoutPluckerJets.zmod_binary_tail_collision_of_two_three_depth`
- `erdos1049.hankel_qorder_exact_all_rank` (#1049, lean_kernel_checked): Exact q-order N(N-1)(2N-1)/6 and leading coefficient (N!)^2(N+1)!/2^N of Zudilin's normalized Hankel determinant
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.zudilinSharpHankelOrderAndCoeff_algebraicAssembly`
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.coeff_zudilinNormalizedHankelDet_all_rat`
  - compared as `PalomarCorpus.E1049.AdelicHeightBridge.zudilinSharpHankelOrderAndCoeff_all`
- `erdos1049.hermite_pade_no_go` (#1049, lean_kernel_checked): rectangular Hermite-Pade threshold no-go with exact equality boundary
  - compared as `PalomarCorpus.E1049.HermitePadeNoGo.hpClearedGap_expansion`
  - compared as `PalomarCorpus.E1049.HermitePadeNoGo.hpClearedGap_nonpos`
  - compared as `PalomarCorpus.E1049.HermitePadeNoGo.hpClearedGap_eq_zero_iff`
  - compared as `PalomarCorpus.E1049.HermitePadeNoGo.rectangular_hp_threshold_le_classical`
  - compared as `PalomarCorpus.E1049.HermitePadeNoGo.rectangular_hp_threshold_eq_classical_iff`
- `erdos1049.prime_support_selectors` (#1049, lean_kernel_checked): sharp prime-supported two-selector rational gap, rational no-double-decay, one-row prime gaps, determinant-height tradeoff, and reduced selector collision
  - compared as `PalomarCorpus.E1049.PrimeSupportSelectors.twoSelector_rationalGap`
  - compared as `PalomarCorpus.E1049.PrimeSupportSelectors.integerLinearForm_rationalGap`
  - compared as `PalomarCorpus.E1049.PrimeSupportSelectors.rationalTwoSelector_notBothTendstoZero`
  - compared as `PalomarCorpus.E1049.PrimeSupportSelectors.twoSelector_detHeightDecay_tradeoff`
  - compared as `PalomarCorpus.E1049.PrimeSupportSelectors.twoSelector_unimodularHeightDecay_tradeoff`
  - compared as `PalomarCorpus.E1049.PrimeSupportSelectors.primeSupportedTwoSelector_rationalGap`
  - compared as `PalomarCorpus.E1049.PrimeSupportSelectors.primeSupportedOneRow_rationalGap`
  - compared as `PalomarCorpus.E1049.PrimeSupportSelectors.primePowerSupportedOneRow_rationalGap`
  - compared as `PalomarCorpus.E1049.PrimeSupportSelectors.zeroDenominatorCoordinates_binaryCollision`
- `erdos1049.rational_base_barrier` (#1049, lean_kernel_checked): exact rational-base cleared-tail recurrence, exponential forcing lower bound, and coordinatewise-corridor impossibility at three-halves
  - compared as `PalomarCorpus.E1049.RationalBaseBarrier.rationalBaseClearedTailQ_succ`
  - compared as `PalomarCorpus.E1049.RationalBaseBarrier.twoPow_le_rationalBaseForcingNat`
  - compared as `PalomarCorpus.E1049.RationalBaseBarrier.threeHalves_no_coordinatewiseCorridor`
- `erdos1049.three_halves_outside_published_height_regions` (#1049, lean_kernel_checked): 3/2 lies outside every published height region
  - compared as `PalomarCorpus.E1049.PublishedHeightRegions.threeHalves_zudilin_power_obstruction`
  - compared as `PalomarCorpus.E1049.PublishedHeightRegions.threeHalves_outside_zudilinHeightRegion`
  - compared as `PalomarCorpus.E1049.PublishedHeightRegions.threeHalves_outside_bundschuhVaananenHeightRegion`
  - compared as `PalomarCorpus.E1049.PublishedHeightRegions.eightyOneTwoHundredths_lt_threeHalves_log_ratio`
- `erdos243.bounded_negative_part_rigidity` (#243, lean_kernel_checked): bounded-negative complete rigidity and eventual Sylvester recurrence
  - compared as `PalomarCorpus.E243.BoundedNegativePartRigidity.boundedNegativePart_completeRigidity`
- `erdos243.crt_bounded_rise_barrier` (#243, lean_kernel_checked): CRT bounded-rise barrier: a slowly rising natural state cannot avoid an infinite pairwise-coprime modulus family at every strict rise
  - compared as `PalomarCorpus.E243.BoundedRiseReducedTail.no_eventuallyBoundedRise_reducedTail`
  - compared as `PalomarCorpus.E243.BoundedRiseReducedTail.no_boundedRise_reducedTail`
  - compared as `PalomarCorpus.E243.BoundedRiseReducedTail.no_boundedRise_of_tailAvoidance`
- `erdos243.original_coordinate_bounded_defect` (#243, lean_kernel_checked): The original rational-sum and quadratic-growth hypotheses force the Sylvester recurrence under one bounded product-defect hypothesis
  - compared as `PalomarCorpus.E243.OriginalCoordinateBoundedDefect.original_coordinate_bounded_defect`
- `erdos243.periodic_negative_orbit` (#243, lean_kernel_checked): phase-primitive, arbitrary-common-scale, and eventually periodic negative-magnitude orbit exclusion by prime lock, pigeonhole, and strong-induction descent
  - compared as `PalomarCorpus.E243.PeriodicNegativeOrbit.no_eventuallyPeriodicNegative_orbit`
  - compared as `PalomarCorpus.E243.PeriodicNegativeOrbit.no_periodicNegative_orbit`
  - compared as `PalomarCorpus.E243.PeriodicNegativeOrbit.no_phasePrimitivePeriodicNegative_orbit`
- `erdos243.primitive_record_two_unit_rigidity` (#243, lean_kernel_checked): Record-setting primitive jumps of size at most two force the Sylvester recurrence under arbitrary cancellation
  - compared as `PalomarCorpus.E243.PrimitiveRecordRigidity.protectedPrimePower_persists`
  - compared as `PalomarCorpus.E243.PrimitiveRecordRigidity.sylvesterStep_of_centeredZero_pair`
  - compared as `PalomarCorpus.E243.PrimitiveRecordRigidity.odd_record_cut`
  - compared as `PalomarCorpus.E243.PrimitiveRecordRigidity.recordRiseTwo_sylvesterNext_eventually`
  - compared as `PalomarCorpus.E243.PrimitiveRecordRigidity.exists_oddMultiple_trapHeight`
  - compared as `PalomarCorpus.E243.PrimitiveRecordRigidity.primitive_valuation_no_drop`
  - compared as `PalomarCorpus.E243.PrimitiveRecordRigidity.centeredZero_forces_unit`
  - compared as `PalomarCorpus.E243.PrimitiveRecordRigidity.numerator_bounded_of_oddPrimePower`
- `erdos243.protected_epoch_energy_criterion` (#243, lean_kernel_checked): Every protected odd prime-power epoch carries at least 1/16 of record energy, and finite energy is equivalent to the Sylvester recurrence
  - compared as `PalomarCorpus.E243.ProtectedEpochEnergy.protected_epoch_energy_integer`
- `erdos243.record_amplified_rigidity` (#243, lean_kernel_checked): A cancellation payment remains visible at the first later negative error
  - compared as `PalomarCorpus.E243.RecordAmplifiedCancellationVisibility.recordAmplified_error_after_cancellation`
- `erdos243.record_increment_unit_rigidity` (#243, lean_kernel_checked): True record increments of at most one force the Sylvester recurrence under arbitrary cancellation
  - compared as `PalomarCorpus.E243.RecordIncrementBarrier.recordIncrementOne_sylvesterNext_eventually`
- `erdos243.repair_entropy` (#243, lean_kernel_checked): repair-energy inequality, independent-family entropy bound, and eventual disappearance of fixed-length reset payments
  - compared as `PalomarCorpus.E243.RepairEntropy.repairedFamily_recovery_energy_divisionFree`
  - compared as `PalomarCorpus.E243.RepairEntropy.repaired_card_bound_of_independent`
  - compared as `PalomarCorpus.E243.RepairEntropy.eventually_recoveryPayment_eq_one_of_fixedLength`
- `erdos243.saturated_square_transport` (#243, lean_kernel_checked): Square transport of consecutive centred errors modulo the whole next numerator, and the record-amplified error after a cancellation
  - compared as `PalomarCorpus.E243.RecordAmplifiedCancellationVisibility.recordAmplified_error_after_cancellation`
  - compared as `PalomarCorpus.E243.SaturatedSquareTransport.legendre_defect_forces_nonsquare_content`
  - compared as `PalomarCorpus.E243.SaturatedSquareTransport.saturated_square_transport_raw`
- `erdos243.slow_rise_landing_barrier` (#243, lean_kernel_checked): Slow-rise landing barrier: the rise bound is needed only below twice the block product
  - compared as `PalomarCorpus.E243.SlowRiseBarrier.no_slowRise_reducedTail`
- `erdos243.summable_negative_mass_rigidity` (#243, lean_kernel_checked): summable normalized-negative-mass complete rigidity and eventual Sylvester recurrence
  - compared as `PalomarCorpus.E243.SummableNegativeMassRigidity.summableNegativeMass_completeRigidity`
  - compared as `PalomarCorpus.E243.SummableNegativeMassRigidity.finite_negative_mass_scalar`
  - compared as `PalomarCorpus.E243.SummableNegativeMassRigidity.canonical_finite_negative_mass`
- `erdos243.weighted_lcm_record_excess` (#243, lean_kernel_checked): Weighted LCM record first crossings and exact discounted summability criteria
  - compared as `PalomarCorpus.E243.WeightedRecordExcess.weighted_record_excess`
  - compared as `PalomarCorpus.E243.WeightedRecordExcess.weighted_growth_record_excess`
- `erdos249.actual_lcm_orbit` (#249, lean_kernel_checked): actual power-of-two LCM tail-orbit identity and exact cofinal nonintegrality equivalence to irrationality
  - compared as `PalomarCorpus.E249.ActualLcmOrbit.actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix`
  - compared as `PalomarCorpus.E249.ActualLcmOrbit.irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply`
- `erdos249.all_base_totient_kernel_rank` (#249, lean_kernel_checked): unconditional all-base totient kernel dimension k^e+1, canonical basis, and relation-module dimension
  - compared as `PalomarCorpus.E249.TotientKernelBasis.allSlopeAffineTotientFormsLinearIndependent`
  - compared as `PalomarCorpus.E249.TotientKernelBasis.allBaseTotientKernelBasisRankAndRelationDimension`
  - compared as `PalomarCorpus.E249.TotientKernelBasis.displayed_integral_normal_form`
- `erdos249.binary_cyclotomic_anchors` (#249, lean_kernel_checked): clean binary-cyclotomic anchors, unconditional unbounded prime-divisor supply, exact anchored-kill equivalence to irrationality, and the support-only period-lock boundary
  - compared as `PalomarCorpus.E249.BinaryCyclotomicAnchors.exists_clean_binaryCyclotomicAnchor`
  - compared as `PalomarCorpus.E249.BinaryCyclotomicAnchors.binaryCyclotomicLayer_unboundedPrimeDivisorSupply`
  - compared as `PalomarCorpus.E249.BinaryCyclotomicAnchors.binaryCyclotomicAnchoredKillSupply_iff_irrational`
  - compared as `PalomarCorpus.E249.BinaryCyclotomicAnchors.exists_unbounded_binaryCyclotomicSupport_with_periodLock_of_not_irrational`
- `erdos249.canonical_mersenne_frontier` (#249, lean_kernel_checked): canonical full-Mersenne-block residue recurrence and exact basepoint gap-supply equivalence to irrationality
  - compared as `PalomarCorpus.E249.CanonicalMersenneFrontier.fullMersenneBlockResidue_succ`
  - compared as `PalomarCorpus.E249.CanonicalMersenneFrontier.fullMersenneCenteredResidueGapSupply_of_canonicalBasepoint`
  - compared as `PalomarCorpus.E249.CanonicalMersenneFrontier.fullMersenneCanonicalBasepointResidueGapSupply_iff_irrational`
- `erdos249.carry_rank_frontier` (#249, lean_kernel_checked): rationality-to-tempered-carry equivalence, exact channel recovery, certificate-driven all-level carry-rank growth, tail-integrality bridge, and the modular-period/unbounded-rank frontier
  - compared as `PalomarCorpus.E249.CarryRankFrontier.not_irrational_totientSeries_implies_mod_period_and_unbounded_rank`
  - compared as `PalomarCorpus.E249.CarryRankFrontier.not_irrational_totientSeries_implies_unbounded_carryRank_unconditional`
  - compared as `PalomarCorpus.E249.CarryRankFrontier.finrank_canonicalCarryKernel_ge_of_certificate`
  - compared as `PalomarCorpus.E249.CarryRankFrontier.totient_carryKernel_diff`
  - compared as `PalomarCorpus.E249.CarryRankFrontier.carryShift_dvd_iff_tailDiff_mem_int`
  - compared as `PalomarCorpus.E249.CarryRankFrontier.not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit`
- `erdos249.dyadic_totient_kernel` (#249, lean_kernel_checked): explicit odd-core basis, full-span equality, canonical finite normal form, and exact ranks
  - compared as `PalomarCorpus.E249.DyadicTotientKernel.dyadicTotientKernelOddCoreBasisAndFiniteRanks`
- `erdos249.eventual_affine_endpoint_exclusion` (#249, lean_kernel_checked): The actual totient word excludes every eventually affine fixed-quotient endpoint-error mode
  - compared as `PalomarCorpus.E249.TotientAffineModeEscape.not_eventuallyAffine_pureDyadicEndpointError`
- `erdos249.farey_window_denominator_exclusion` (#249, lean_kernel_checked): Lean-checked Farey-window denominator exclusion (35 digits), superseded as the floor
  - compared as `PalomarCorpus.E249.FareyWindowExclusion.farey_rat_exclusion`
  - compared as `PalomarCorpus.E249.FareyWindowExclusion.farey_int_exclusion`
- `erdos249.full_depth_ray_amplifier` (#249, lean_kernel_checked): full-depth ray amplification, eventual two-syndetic kill multipliers, and exact equivalence of cofinal full-depth supply with irrationality
  - compared as `PalomarCorpus.E249.FullDepthRayAmplifier.eventually_twoSyndetic_fullDepthKillMultipliers_of_seed`
  - compared as `PalomarCorpus.E249.FullDepthRayAmplifier.exists_fullDepthKill_on_ray_iff_shift_notMem_int`
  - compared as `PalomarCorpus.E249.FullDepthRayAmplifier.apFullDepthEscape_iff_irrational`
  - compared as `PalomarCorpus.E249.FullDepthRayAmplifier.cofinalFullDepthKillSupply_iff_periodMultipleKillSupply`
  - compared as `PalomarCorpus.E249.FullDepthRayAmplifier.cofinalFullDepthKillSupply_iff_irrational`
- `erdos249.mobius_mersenne_all_rungs_strict_log_concavity` (#249, lean_kernel_checked): Strict log-concavity of the whole Möbius-Mersenne ladder
  - compared as `PalomarCorpus.E249.MobiusMersenneLadderStructure.mobiusMersenneTheta_no_linearRecurrence`
  - compared as `PalomarCorpus.E249.MobiusMersenneLadderStructure.mobiusMersenneTheta_no_linearRecurrence_of_eventually`
  - compared as `PalomarCorpus.E249.MobiusMersenneLadderStructure.mobiusMersenneTheta_strict_logConcave`
  - compared as `PalomarCorpus.E249.MobiusMersenneLadderStructure.mobiusMersenneTheta_hankel_two_neg`
  - compared as `PalomarCorpus.E249.MobiusMersenneLadderStructure.mobiusMersenneLambertRung_eq`
  - compared as `PalomarCorpus.E249.MobiusMersenneLadderStructure.lambertRung_shifted_hankelDet_eq_zero`
  - compared as `PalomarCorpus.E249.MobiusMersenneLadderStructure.mobiusMersenneTheta_ne_mobiusMersenneLambertRung`
- `erdos249.prefix_two_adic_valuation_exclusion` (#249, lean_kernel_checked): 2-adic valuation of the totient prefix integer: exclusion rectangle consumer (Lean) with an exact witness
  - compared as `PalomarCorpus.E249.PrefixTwoAdicExclusion.totientPrefix_eq_corpusForm`
  - compared as `PalomarCorpus.E249.PrefixTwoAdicExclusion.totientPrefix_succ`
  - compared as `PalomarCorpus.E249.PrefixTwoAdicExclusion.prefix_twoAdic_denominator_exclusion`
  - compared as `PalomarCorpus.E249.PrefixTwoAdicExclusion.prefix_twoAdic_denominator_lower_bound`
  - compared as `PalomarCorpus.E249.PrefixTwoAdicExclusion.prefix_twoAdic_odd_denominator_floor`
  - compared as `PalomarCorpus.E249.PrefixTwoAdicExclusion.oddPart_mul_prefixTail_eq_intCast`
- `erdos249.rank_one_sharp_floor` (#249, lean_kernel_checked): sharp positive rank-one Schur-cone floor, unique minimizer, positive-mixture closure, and rational-linear-form obstruction
  - compared as `PalomarCorpus.E249.RankOneSharpFloor.rankOneSubrankQuotient_ge_one_five`
  - compared as `PalomarCorpus.E249.RankOneSharpFloor.rankOneSubrankQuotient_eq_one_five_iff`
  - compared as `PalomarCorpus.E249.RankOneSharpFloor.rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty`
  - compared as `PalomarCorpus.E249.RankOneSharpFloor.rankOneSubrankQuotient_sub_theta_two_gt_one_div_sixteen`
  - compared as `PalomarCorpus.E249.RankOneSharpFloor.not_forall_rankOneSubrankQuotient_sub_theta_two_gt_one_div_fifteen`
  - compared as `PalomarCorpus.E249.RankOneSharpFloor.positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty`
  - compared as `PalomarCorpus.E249.RankOneSharpFloor.primitive_form_abs_gt_twentyOne_div_threeTwenty`
- `erdos249.residue_class_totient_series_irrational` (#249, lean_kernel_checked): irrationality of the residue-class totient series at modulus at least three (A_m = sum (phi(n) mod m)/2^n for m >= 3, and any nonzero integer observable of phi mod m at a residue r with r + 1 coprime to m)
  - compared as `PalomarCorpus.E249.ResidueClassTotientSeries.residue_series_irrational`
  - compared as `PalomarCorpus.E249.ResidueClassTotientSeries.irrational_totientObservable`
  - compared as `PalomarCorpus.E249.ResidueClassTotientSeries.fixed_resolution_observable_irrational`
  - compared as `PalomarCorpus.E249.ResidueClassTotientSeries.isolated_pulse_separation`
  - compared as `PalomarCorpus.E249.ResidueClassTotientSeries.two_sided_prime_isolation`
  - compared as `PalomarCorpus.E249.ResidueClassTotientSeries.irrational_dyadicValue_of_pulses`
- `erdos249.termwise_dyadic_window_vacuous` (#249, lean_kernel_checked): termwise dyadic windows exclude no denominator (Erdős-1948 transfer is vacuous for the totient)
  - compared as `PalomarCorpus.E249.TermwiseDyadicVacuous.termwise_dyadic_window_vacuous`
- `erdos249.totient_rigidity_theorems` (#249, lean_kernel_checked): two kernel-checked rigidity theorems for the totient: one exact prime law plus o(n) error forces phi; the exact even law plus eventual congruence modulo every integer forces phi
  - compared as `PalomarCorpus.E249.TotientRigidity.totient_prime_mul_of_dvd`
  - compared as `PalomarCorpus.E249.TotientRigidity.totient_two_mul_of_even`
  - compared as `PalomarCorpus.E249.TotientRigidity.even_law_and_eventual_congruence_forces_totient`
  - compared as `PalomarCorpus.E249.TotientRigidity.totient_two_mul_of_odd`
  - compared as `PalomarCorpus.E249.TotientRigidity.totient_prime_mul_of_not_dvd`
  - compared as `PalomarCorpus.E249.TotientRigidity.one_prime_law_and_little_o_forces_totient`
- `erdos251.actual_prime_gap_tail` (#251, lean_kernel_checked): actual prime-gap rational-candidate representation, unconditional actual-gap recurrence, denominator-driven eventual integral shift, and the fixed-shift smallness obstruction
  - compared as `PalomarCorpus.E251.ActualPrimeGapTail.exists_rationalPrimeGapTailState_representation_of_not_irrational`
  - compared as `PalomarCorpus.E251.ActualPrimeGapTail.rationalPrimeGapTailState_recurrence`
  - compared as `PalomarCorpus.E251.ActualPrimeGapTail.rationalPrimeGapTailShift_eventuallyIntegral`
  - compared as `PalomarCorpus.E251.ActualPrimeGapTail.rationalPrimeGapTail_has_positive_shift_not_eventually_small`
- `erdos251.affine_circularity` (#251, lean_kernel_checked): signed two-window normal form and exact affine and fixed-lattice circularity equivalences
  - compared as `PalomarCorpus.E251.AffineCircularity.adjacent_small_mismatch_iff_signed_two_window`
  - compared as `PalomarCorpus.E251.AffineCircularity.cofinal_affinePowTwo_escape_iff_not_eventuallyIntegral`
  - compared as `PalomarCorpus.E251.AffineCircularity.cofinal_blockResidue_escape_iff_not_eventuallyIntegral`
- `erdos251.all_residue_logarithmic_countermodel` (#251, lean_kernel_checked): A rational logarithmic dyadic word with small digits recurring in every residue class and PNT-scale cumulative growth
  - compared as `PalomarCorpus.E251.AllResidueLogarithmicCountermodel.exists_every_residue_logarithmic_countermodel`
- `erdos251.free_pair_equivalence` (#251, lean_kernel_checked): Free-pair lattice and the equivalence of irrationality with cofinal free-pair nonintegrality
  - compared as `PalomarCorpus.E251.FreePairEquivalence.irrational_primeGap_tsum_iff_cofinalFreePairNonintegral`
  - compared as `PalomarCorpus.E251.FreePairEquivalence.irrational_initial_iff_cofinalFreePairNonintegral`
  - compared as `PalomarCorpus.E251.FreePairEquivalence.cofinalFreePairNonintegral_iff_cofinalNonintegralTailShifts`
  - compared as `PalomarCorpus.E251.FreePairEquivalence.exists_free_pair_lattice`
  - compared as `PalomarCorpus.E251.FreePairEquivalence.free_pair_integral_iff_modEq`
  - compared as `PalomarCorpus.E251.FreePairEquivalence.primeGapRealTail_recurrence`
  - compared as `PalomarCorpus.E251.FreePairEquivalence.primeGapRealTail_zero`
- `erdos251.kernel_denominator_floor_2e589` (#251, lean_kernel_checked): Kernel-decided denominator floor b ≥ 2^589 for the prime series and the prime-gap series
  - compared as `PalomarCorpus.E251.KernelDenominatorFloor.cert_10000`
  - compared as `PalomarCorpus.E251.KernelDenominatorFloor.den_bound_of_certCheck`
  - compared as `PalomarCorpus.E251.KernelDenominatorFloor.kernel_denominator_floor`
  - compared as `PalomarCorpus.E251.KernelDenominatorFloor.kernel_denominator_floor_primeGap`
- `erdos251.lcm_diagonal_criterion` (#251, lean_kernel_checked): exact one-shift and cofinal dyadic-tail rationality classifier, multiplicative-order lattice, and generic deciding-schedule criterion with LCM specialization
  - compared as `PalomarCorpus.E251.LcmDiagonalCriterion.notIrrationalInitial_iff_exists_integral_positive_tailShift`
  - compared as `PalomarCorpus.E251.LcmDiagonalCriterion.irrationalInitial_iff_cofinalNonintegralTailShifts`
  - compared as `PalomarCorpus.E251.LcmDiagonalCriterion.tailShiftIntegral_iff_orderOf_dvd`
  - compared as `PalomarCorpus.E251.LcmDiagonalCriterion.irrationalInitial_iff_nonintegral_on_schedule`
  - compared as `PalomarCorpus.E251.LcmDiagonalCriterion.irrationalInitial_iff_allLcmDiagonal_nonintegral`
- `erdos251.polynomial_shift_countermodel` (#251, lean_kernel_checked): exact polynomial shift countermodel eliminating coarse-gap strategies
  - compared as `PalomarCorpus.E251.PolynomialShiftCountermodel.polynomialGapTailCountermodel`
- `erdos251.prime_gap_identity` (#251, lean_kernel_checked): unconditional convergence, exact prime/prime-gap summation-by-parts identity, and equivalent irrationality status
  - compared as `PalomarCorpus.E251.PrimeGapIdentity.prime0_le_polynomial`
  - compared as `PalomarCorpus.E251.PrimeGapIdentity.primeSeries_summable`
  - compared as `PalomarCorpus.E251.PrimeGapIdentity.primeGapSeries_summable`
  - compared as `PalomarCorpus.E251.PrimeGapIdentity.primeSeries_eq_two_add_primeGapSeries`
  - compared as `PalomarCorpus.E251.PrimeGapIdentity.primeSeries_irrational_iff_primeGapSeries`
  - compared as `PalomarCorpus.E251.PrimeGapIdentity.primeDisplayedSeries_eq_four_add_two_primeGapSeries`
  - compared as `PalomarCorpus.E251.PrimeGapIdentity.primeDisplayedSeries_irrational_iff_primeGapSeries`
- `erdos251.shifted_four_prime_counting_reduction` (#251, lean_kernel_checked): Shifted prime-gap coincidences reduce to an explicit four-prime counting problem
  - compared as `PalomarCorpus.E251.ShiftedFourPrimeCounting.shifted_count_bound`
  - compared as `PalomarCorpus.E251.ShiftedFourPrimeCounting.separated_zeroDensity_of_quad_sieve`
- `erdos257.achievement_set_geometry` (#257, lean_kernel_checked): achievement-set topology and exact volume dichotomy
  - compared as `PalomarCorpus.E257.AchievementSetGeometry.volume_supportedMersenneAchievementSet_eq_zero_of_rat_value`
  - compared as `PalomarCorpus.E257.AchievementSetGeometry.supportedMersenneAchievementSet_geometry_and_volume`
- `erdos257.actual_upper_successor` (#257, lean_kernel_checked): exact realized upper/right packet lower envelope equivalence with a pulse-free successor boundary, yielding a conditional infinite-support half-value counterexample and universal refutation
  - compared as `PalomarCorpus.E257.ActualUpperSuccessor.actualUpperRightPacketLinearEscape_iff_successorLinearEscape`
  - compared as `PalomarCorpus.E257.ActualUpperSuccessor.actualUpperSuccessorLinearEscape_completeCounterexample`
- `erdos257.boolean_mobius_carry` (#257, lean_kernel_checked): exact Boolean-Mobius carry certificate equivalence and support reconstruction
  - compared as `PalomarCorpus.E257.BooleanMobiusCarry.exists_booleanMobiusCarry_of_support_fraction`
  - compared as `PalomarCorpus.E257.BooleanMobiusCarry.support_fraction_of_booleanMobiusCarry`
  - compared as `PalomarCorpus.E257.BooleanMobiusCarry.BooleanMobiusCarryCertificate.reconstructsSupport`
  - compared as `PalomarCorpus.E257.BooleanMobiusCarry.exists_normalized_support_fraction_iff_exists_booleanMobiusCarry`
- `erdos257.divisibility_weighted_support_irrationality` (#257, lean_kernel_checked): Finite divisibility-weighted mass implies hereditary all-base irrationality, including explicit reciprocal-divergent short-gap supports.
  - compared as `PalomarCorpus.E257.DivisibilityWeightedSupport.divisibilityWeightedClaim`
- `erdos257.fair_coding_lebesgue_pushforward` (#257, lean_kernel_checked): Fair Mersenne digit coding gives restricted Lebesgue measure and almost-everywhere irrationality
  - compared as `PalomarCorpus.E257.FairCoding.measurePreserving_fairCoding`
  - compared as `PalomarCorpus.E257.FairCoding.fairCoding_rational_values_null`
  - compared as `PalomarCorpus.E257.FairCoding.fairCoding_pushforward_eq_volume_restrict`
- `erdos257.finite_period_noncollapse` (#257, lean_kernel_checked): complete finite-period noncollapse with denominator growth
  - compared as `PalomarCorpus.E257.FinitePeriodNoncollapse.finite_period_noncollapse_rat_den`
  - compared as `PalomarCorpus.E257.FinitePeriodNoncollapse.lcm_lt_den_finiteErdosSum`
- `erdos257.four_ninths_square_root_repair_windows` (#257, lean_kernel_checked): 4/9 membership is equivalent to a repair at some N in every interval [K,K+2 floor(sqrt K)+12). A single strict-increase window excludes membership.
  - compared as `PalomarCorpus.E257.FourNinthsRepairWindows.four_ninths_mem_iff_repairCofinal`
  - compared as `PalomarCorpus.E257.FourNinthsRepairWindows.four_ninths_not_mem_of_strict_sqrt_window`
  - compared as `PalomarCorpus.E257.FourNinthsRepairWindows.four_ninths_mem_iff_repair_sqrt_windows`
  - compared as `PalomarCorpus.E257.FourNinthsRepairWindows.exists_repair_in_sqrt_window`
- `erdos257.generic_real_target_square_root_repair_criterion` (#257, lean_kernel_checked): For every real x >= 0, define Q_N as floor_nat(2^N x) minus the actual greedy support Lambert prefix numerator. Membership of x in the Mersenne achievement set is equivalent to cofinal nonincreases of Q_N, to a nonincrease in every [K,K+2 floor(sqrt K)+12), to cofinal Q_N <= the actual next divisor load, and to cofinal Q_N <= N+1. One strict-increase window excludes membership.
  - compared as `PalomarCorpus.E257.GeneralRepairCriterion.mem_iff_greedyBinaryDefect_cofinal_repairs`
  - compared as `PalomarCorpus.E257.GeneralRepairCriterion.mem_iff_greedyBinaryDefect_sqrt_windows`
- `erdos257.literal_weighted_cover_separation` (#257, lean_kernel_checked): A literal weighted host outside every strengthened cover, with mixed hereditary irrationality
  - compared as `PalomarCorpus.E257.LiteralWeightedCover.exists_weighted_obstruction_with_mixed_heredity`
  - compared as `PalomarCorpus.E257.LiteralWeightedCover.exists_weighted_not_strengthened_host`
- `erdos257.mixed_weighted_cover_synchronisation` (#257, lean_kernel_checked): Mixed weighted and strengthened-cover supports have hereditary all-base irrationality
  - compared as `PalomarCorpus.E257.MixedWeightedCover.mixedSupportClaim`
- `erdos257.positive_skip_equivalence` (#257, lean_kernel_checked): strict positivity of finite half-greedy residuals and exact cofinal positive-skip equivalence
  - compared as `PalomarCorpus.E257.PositiveSkipEquivalence.greedyMersenneRemainderRat_half_pos`
  - compared as `PalomarCorpus.E257.PositiveSkipEquivalence.cofinalPositiveHalfGreedySkips_iff_half_mem`
- `erdos257.rational_membership_criterion` (#257, lean_kernel_checked): Rational membership in the Mersenne achievement set is equivalent to cofinal greedy skips
  - compared as `PalomarCorpus.E257.RationalMembership.rat_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite`
  - compared as `PalomarCorpus.E257.RationalMembership.infinite_greedyMersenneSkippedSupport_of_rat_mem`
  - compared as `PalomarCorpus.E257.RationalMembership.rat_mem_mersenneAchievementSet_iff_cofinal_greedy_skips`
  - compared as `PalomarCorpus.E257.RationalMembership.greedyMersenneSkippedSupport_infinite_iff_cofinal_skips`
- `erdos257.rational_tail_rigidity` (#257, lean_kernel_checked): support-uniform rational-tail rigidity: unbounded integral states, sublogarithmic divisor-coverage gaps, and sharp odd/dyadic reciprocal-mass constraints
  - compared as `PalomarCorpus.E257.RationalTailRigidity.exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction`
  - compared as `PalomarCorpus.E257.RationalTailRigidity.supportCoeffZeroWindow_length_le_eps_logb_add`
  - compared as `PalomarCorpus.E257.RationalTailRigidity.one_div_oddOrder_le_reciprocalMass_of_support_fraction`
  - compared as `PalomarCorpus.E257.RationalTailRigidity.dyadic_support_fraction_reciprocalMass_diverges_or_gt_one`
- `erdos257.reciprocal_support` (#257, lean_kernel_checked): irrationality for every infinite reciprocal-summable support at every integer base
  - compared as `PalomarCorpus.E257.ReciprocalSupport.irrational_supportPowerSeries_of_summable_reciprocal`
- `erdos257.scaled_greedy_trap` (#257, lean_kernel_checked): exact scaled greedy-trap equality, exponential escape off the achievement set, cofinal bounded-return characterization, and rational lower-separatrix criteria including one over twenty-one
  - compared as `PalomarCorpus.E257.ScaledGreedyTrap.mersenneAchievementSet_eq_scaledGreedyTrap`
  - compared as `PalomarCorpus.E257.ScaledGreedyTrap.scaledGreedyRemainder_tendsto_atTop_of_not_mem`
  - compared as `PalomarCorpus.E257.ScaledGreedyTrap.mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded`
  - compared as `PalomarCorpus.E257.ScaledGreedyTrap.rat_mem_mersenneAchievementSet_iff_scaledLowerBranchCofinally`
  - compared as `PalomarCorpus.E257.ScaledGreedyTrap.one_div_twentyOne_mem_iff_scaledLowerBranchCofinally`
  - compared as `PalomarCorpus.E257.ScaledGreedyTrap.one_div_twentyOne_mem_iff_scaledRemainder_cofinallyBounded`
- `erdos257.terminal_scaled_vanishing` (#257, lean_kernel_checked): terminal scaled vanishing produces an infinite-support value one half and refutes the universal irrationality assertion
  - compared as `PalomarCorpus.E257.TerminalScaledVanishing.terminalScaledVanishing_completeCounterexample`
- `erdos257.twenty_one_fatal_branch` (#257, lean_kernel_checked): exact denominator-twenty-one fatal-branch dichotomy, closed-state compactness, permanent escape, and affine supercapacity normal form
  - compared as `PalomarCorpus.E257.TwentyOneFatalBranch.twentyOneClosedRow_forces_quotientGreedy`
  - compared as `PalomarCorpus.E257.TwentyOneFatalBranch.one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates`
  - compared as `PalomarCorpus.E257.TwentyOneFatalBranch.one_div_twenty_one_mem_iff_not_fatalAlignedBranch`
  - compared as `PalomarCorpus.E257.TwentyOneFatalBranch.twentyOneFatalAlignedBranch_eventually_strict_supercapacity`
  - compared as `PalomarCorpus.E257.TwentyOneFatalBranch.twentyOneFatalAlignedBranch_eventually_affine_supercapacity`
- `erdos257.variable_exponent_fractional_cover_irrationality` (#257, lean_kernel_checked): Strengthened one-inverse-power positive covers give hereditary all-base irrationality
  - compared as `PalomarCorpus.E257.VariableExponentCover.strengthenedPositiveCoverClaim`
- `erdos257.weighted_support_dyadic_observation_summability` (#257, lean_kernel_checked): For arbitrary support A and nonnegative alpha on A, summability of indicator_(0<a and a in A) alpha(a)/a implies summability of j -> 2^(-j) sum_(0<a<=Q 2^j,a in A) alpha(a). Every finite sum over dyadic scales is at most 2Q times the weighted reciprocal total; the means over j=M,...,2M-1 tend to zero. Summability of alpha itself is not assumed.
  - compared as `PalomarCorpus.E257.DyadicObservationSummability.summable_dyadic_supportObservationMass`
  - compared as `PalomarCorpus.E257.DyadicObservationSummability.tendsto_dyadic_supportObservationMass_mean`
  - compared as `PalomarCorpus.E257.DyadicObservationSummability.dyadic_supportObservationMass_sum_le`
- `erdos269.actual_shell_orbit` (#269, lean_kernel_checked): actual infinite shell-tail recurrence and integer-or-cofinally-one-over-thirty-one dichotomy
  - compared as `PalomarCorpus.E269.ActualShellOrbit.actual_dyadicShellOrbit_recurrence_and_escape`
- `erdos269.all_scale_lattice` (#269, lean_kernel_checked): symmetric prime-power boundary clearing, rationality-to-all-scale lattice, and normalized-tail collision reduction
  - compared as `PalomarCorpus.E269.AllScaleLattice.qsmul_normalizedTailState_eq_int_of_value_eq_rat`
  - compared as `PalomarCorpus.E269.AllScaleLattice.exists_normalizedTailState_collision_of_value_eq_rat`
  - compared as `PalomarCorpus.E269.AllScaleLattice.smoothHeight_mul_prime_dvd_boundaryHeight`
  - compared as `PalomarCorpus.E269.AllScaleLattice.dyadicShellTsumTailR235_eq_range_add`
  - compared as `PalomarCorpus.E269.AllScaleLattice.heightNormalizer235_mul_windowMass_eq_int`
  - compared as `PalomarCorpus.E269.AllScaleLattice.two_mul_heightNormalizer235`
- `erdos269.carry_mechanism` (#269, lean_kernel_checked): conditional carry-lift extinction from two channel anchors, sharp four-state first-block obstruction, exact weighted block defect, residue-coboundary decomposition, and cofinal local-window consumer
  - compared as `PalomarCorpus.E269.CarryMechanism.no_carryLift_of_errorBound_below_twoPow`
  - compared as `PalomarCorpus.E269.CarryMechanism.no_unitAccurateLift_with_twoAnchors_and_firstTwoBlockNull`
  - compared as `PalomarCorpus.E269.CarryMechanism.perturbation_eq_zero_of_blockNull_twoAnchors`
  - compared as `PalomarCorpus.E269.CarryMechanism.carryLift_blockDefect`
  - compared as `PalomarCorpus.E269.CarryMechanism.no_positive_reducedCarry_of_cofinalLocalWindowEscape`
  - compared as `PalomarCorpus.E269.CarryMechanism.carry_eq_residueDigit_add_coboundary`
- `erdos269.integral_branch_pinning` (#269, lean_kernel_checked): surviving-window identification with the true normalized state, exact finite-depth mixed-radix telescope, integral upward closure, and actual pinning
  - compared as `PalomarCorpus.E269.IntegralBranchPinning.surviving_window_orbit_eq_true_state`
  - compared as `PalomarCorpus.E269.IntegralBranchPinning.trueNormalizedState_eq_telescope`
  - compared as `PalomarCorpus.E269.IntegralBranchPinning.integral_state_upward_closed`
  - compared as `PalomarCorpus.E269.IntegralBranchPinning.trueNormalizedState_pinning`
- `erdos269.rationality_carry_bridge` (#269, lean_kernel_checked): Rationality-to-reduced-carry bridge for the actual series, with an explicit quadratic state width
  - compared as `PalomarCorpus.E269.WindowEscapeEquivalence.exists_reducedCarry_of_value_eq_rat`
- `erdos269.three_prime_structure` (#269, lean_kernel_checked): exact running-LCM identity, logarithmic-cell constancy, exact jump count, height-fibre normal form, quadratic shell bound, arbitrary-order nonsingular minors, and no finite exact separation
  - compared as `PalomarCorpus.E269.ThreePrimeStructure.smoothPrefixLcm_eq_threePrimeHeight`
  - compared as `PalomarCorpus.E269.ThreePrimeStructure.threePrimeKernelQ_eq_of_sameLogCell`
  - compared as `PalomarCorpus.E269.ThreePrimeStructure.threePrimePositiveJumpSet_card`
  - compared as `PalomarCorpus.E269.ThreePrimeStructure.finiteSmoothKernelSum_groupedByHeight`
  - compared as `PalomarCorpus.E269.ThreePrimeStructure.smoothExponentShell_card_quadratic`
  - compared as `PalomarCorpus.E269.ThreePrimeStructure.kernel_235_minor_eq_neg_one_fifteen`
  - compared as `PalomarCorpus.E269.ThreePrimeStructure.exists_uniform_nonsingular_threePrimeKernel_minor`
  - compared as `PalomarCorpus.E269.ThreePrimeStructure.threePrimeKernel_infiniteRank_and_noFiniteSeparation`
- `erdos269.window_escape_equivalence` (#269, lean_kernel_checked): The cofinal local-window escape producer is exactly equivalent to irrationality of the {2,3,5} running-LCM series
  - compared as `PalomarCorpus.E269.WindowEscapeEquivalence.actualCofinalLocalWindowEscape_iff_irrational_value`
  - compared as `PalomarCorpus.E269.WindowEscapeEquivalence.actualCofinalLocalWindowEscape_iff`
  - compared as `PalomarCorpus.E269.WindowEscapeEquivalence.cofinalLocalWindowEscape_of_irrational`
  - compared as `PalomarCorpus.E269.WindowEscapeEquivalence.cofinalLocalWindowEscape_of_irrational_of_quadratic`
  - compared as `PalomarCorpus.E269.WindowEscapeEquivalence.exists_reducedCarry_of_value_eq_rat`
  - compared as `PalomarCorpus.E269.WindowEscapeEquivalence.trueNormalizedState_window`
  - compared as `PalomarCorpus.E269.WindowEscapeEquivalence.near_integer_of_residue_le_general`
  - compared as `PalomarCorpus.E269.WindowEscapeEquivalence.exists_pow_gt_quadratic`
- `erdos68.adjacent_unit_carry_window` (#68, lean_kernel_checked): adjacent unit-carry window characterization and exact two-step factorization
  - compared as `PalomarCorpus.E68.AdjacentUnitCarryWindow.consecutive_unit_carries_iff_positive_offset_le_den`
  - compared as `PalomarCorpus.E68.AdjacentUnitCarryWindow.twoStep_den_mul_transitionNormalizers`
  - compared as `PalomarCorpus.E68.AdjacentUnitCarryWindow.adjacentUnitCarryWindowDen_eq_twoStep_den`
  - compared as `PalomarCorpus.E68.AdjacentUnitCarryWindow.adjacentUnitCarryWindowOffset_eq_twoStep_factorization`
- `erdos68.channel_radius` (#68, lean_kernel_checked): quantitative square-subsequence channel-radius lower bound, exclusion of eventual three-halves upper bounds, and exact failure of little-o decay
  - compared as `PalomarCorpus.E68.ChannelRadius.square_subsequence_radius_three_halves_lower`
  - compared as `PalomarCorpus.E68.ChannelRadius.no_eventual_square_subsequence_three_halves_upper`
  - compared as `PalomarCorpus.E68.ChannelRadius.not_isLittleO_square_subsequence_radius`
  - compared as `PalomarCorpus.E68.ChannelRadius.square_subsequence_radius_cubic_lower`
  - compared as `PalomarCorpus.E68.ChannelRadius.no_eventual_square_subsequence_cubic_upper`
  - compared as `PalomarCorpus.E68.ChannelRadius.sharp_radius_satisfies_square_log_constraint`
- `erdos68.companion_orbit_boundary` (#68, lean_kernel_checked): Companion-orbit rationality boundary for the #68 series
  - compared as `PalomarCorpus.E68.CompanionOrbitBoundary.companionOrbitBoundary_strictSuccessorCarry`
  - compared as `PalomarCorpus.E68.CompanionOrbitBoundary.companionOrbitBoundary_genericShift`
  - compared as `PalomarCorpus.E68.CompanionOrbitBoundary.companionOrbitBoundary_factorialGapSeries`
  - compared as `PalomarCorpus.E68.CompanionOrbitBoundary.tsum_unitFactTerm_eq_exp_one_sub_two`
- `erdos68.exact_low_channel_moment_ideal` (#68, lean_kernel_checked): Exact attainable low-channel moment ideal with a content-one primitive generator
  - compared as `PalomarCorpus.E68.MomentIdeal.attainable_moment_ideal`
  - compared as `PalomarCorpus.E68.MomentIdeal.exact_moment_ideal_with_primitive_attainment`
  - compared as `PalomarCorpus.E68.MomentIdeal.minimum_moment_content_one`
  - compared as `PalomarCorpus.E68.MomentIdeal.minimumMoment_independent_prime`
- `erdos68.factorial_gap_lcm_lower_bound` (#68, lean_kernel_checked): Lean-checked 3/2 lower growth for lcm_{2<=n<=N}(n!-1)
  - compared as `PalomarCorpus.E68.CommonDenominatorGrowth.common_denominator_growth_liminf`
  - compared as `PalomarCorpus.E68.CommonDenominatorGrowth.common_denominator_growth`
- `erdos68.finite_size_denominator_exclusion_10e12040` (#68, lean_kernel_checked): Kernel-checked finite denominator floor q > 10^12040
  - compared as `PalomarCorpus.E68.FiniteDenominator.finite_denominator_exclusion`
- `erdos68.full_residual_integer_class` (#68, lean_kernel_checked): Full residual transparency and invariance modulo the integers
  - compared as `PalomarCorpus.E68.ResidualIntegerClass.equal_moment_residual_integer_difference`
  - compared as `PalomarCorpus.E68.ResidualIntegerClass.zero_moment_residual_integral`
  - compared as `PalomarCorpus.E68.ResidualIntegerClass.summable_fullResidual`
  - compared as `PalomarCorpus.E68.ResidualIntegerClass.residual_transparency`
- `erdos68.kempner_index_denominator_exclusion` (#68, lean_kernel_checked): Kempner-index exclusion: a non-unit carry at an index m at least 3 forces q ∤ (m−1)!
  - compared as `PalomarCorpus.E68.KempnerIndex.rational_denominator_not_dvd_fiftynine_factorial`
  - compared as `PalomarCorpus.E68.KempnerIndex.rational_denominator_not_dvd_pred_factorial_of_nonunit_carry`
- `erdos68.moving_factor_scale_split` (#68, lean_kernel_checked): one-moving-private-factor scale split, arbitrary split-factor normalized-collision criterion, and fixed-owner absorption no-go
  - compared as `PalomarCorpus.E68.MovingFactorScaleSplit.movingPrivateFactorScaleSplit_implies_irrational`
  - compared as `PalomarCorpus.E68.MovingFactorScaleSplit.splitFactorNormalizedCollision_implies_irrational`
  - compared as `PalomarCorpus.E68.MovingFactorScaleSplit.fixedOwnerPair_eventually_absorbed`
- `erdos68.multiplicative_successor_rigidity` (#68, lean_kernel_checked): Multiplicative rigidity of the strict successors, and irrationality from one fixed modulus
  - compared as `PalomarCorpus.E68.MultiplicativeSuccessorRigidity.eventually_dvd_gapSuccessor_of_not_irrational`
  - compared as `PalomarCorpus.E68.MultiplicativeSuccessorRigidity.gapSuccessor_dvd_of_eventually_dvd`
  - compared as `PalomarCorpus.E68.MultiplicativeSuccessorRigidity.irrational_factorialGapSeries_of_cofinal_not_dvd_gapSuccessor`
  - compared as `PalomarCorpus.E68.MultiplicativeSuccessorRigidity.not_eventually_odd_gapSuccessor_of_not_irrational`
  - compared as `PalomarCorpus.E68.MultiplicativeSuccessorRigidity.gapSuccessor_eq_mul_pred_of_dvd`
  - compared as `PalomarCorpus.E68.MultiplicativeSuccessorRigidity.factorial_mul_gapSuccessor_eq_of_eventually_dvd`
  - compared as `PalomarCorpus.E68.MultiplicativeSuccessorRigidity.irrational_factorialGapSeries_of_cofinal_odd_gapSuccessor`
- `erdos68.prime_pole` (#68, lean_kernel_checked): finite prime-pole residue formula
  - compared as `PalomarCorpus.E68.PrimePole.factorialGapPrefixLCMNumerator_mod_prime`
- `erdos68.prime_unit_translator` (#68, lean_kernel_checked): exact prime-unit translator profile, integer residual-translation law, and unconditional remote factorial-grid Cramer reduction
  - compared as `PalomarCorpus.E68.PrimeUnitTranslator.primeTranslator_moment_zero`
  - compared as `PalomarCorpus.E68.PrimeUnitTranslator.primeTranslator_channel_zero_of_lt_p`
  - compared as `PalomarCorpus.E68.PrimeUnitTranslator.primeTranslator_channel_at_prime`
  - compared as `PalomarCorpus.E68.PrimeUnitTranslator.primeTranslator_channel_zero_of_p_lt`
  - compared as `PalomarCorpus.E68.PrimeUnitTranslator.primeTranslator_channelResidual_eq_one`
  - compared as `PalomarCorpus.E68.PrimeUnitTranslator.channelResidual_appendPrimeTranslator`
  - compared as `PalomarCorpus.E68.PrimeUnitTranslator.exists_remote_factorialGrid_primeTranslator_reduction`
- `erdos68.strict_successor_carry` (#68, lean_kernel_checked): fixed companion-orbit rationality boundary and complete strict-successor carry characterization
  - compared as `PalomarCorpus.E68.StrictSuccessorCarry.companionOrbit_completeCharacterization`
  - compared as `PalomarCorpus.E68.StrictSuccessorCarry.strictSuccessorCarry_completeCharacterization`

## Paper-only claims (not manufactured as Comparator coverage)

85 frontier claims remain paper-only, including ordinary-paper
theorems that have formalized kernels or helpers.

- `erdos1041.all_degree_invariants_and_pinned_witness_connectors` (#1041): Completed trace-curvature measure, sharp nodal Crofton budget 2nR, polygonal contour 1-sin(pi/d), and exact noncritical-hub connectors on the pinned witnesses
- `erdos1041.centred_circle_quadrinomial` (#1041): Every monic with at most four nonzero coefficients and all roots on one centred circle, and the exact sextic refuting the two-tail selector
- `erdos1041.centroid_variance_chord_chart` (#1041): The centroid-variance chord chart: Var < (n-1)/(2n-1) forces a contained root chord, and second-moment data cannot reach the critical spectrum for n >= 6
- `erdos1041.chord_conditioned_bergman` (#1041): Chord-conditioned Bergman geodesic bound with optimal spectral coefficient and a separating rational cubic
- `erdos1041.circle_slice_angular_closure_thirteen_twentyfifths` (#1041): Unconditional all-degree regime: least critical value at most 13/25, via the circle-slice angular packing floor
- `erdos1041.cluster_separation_low_critical_closure` (#1041): Unconditional all-degree regime: least critical value at most 9/25, via pairwise hyperbolic separation of the ancestor component's roots
- `erdos1041.concyclic_alternation` (#1041): An adjacent-root chord in the open lemniscate for every concyclic root set of radius at most 2^(-1/n)
- `erdos1041.critical_value_separation_sharp_constant` (#1041): Sharp constant 2 in every degree under critical-value separation
- `erdos1041.disk_family_critical_value_separation` (#1041): all-degree Erdos 1041 conclusion in the disk-separated simple-hub regime: separation 4/3 from any real centre of the value segment suffices in every degree n >= 3
- `erdos1041.exterior_energy_has_no_failure_derived_floor` (#1041): The exterior coefficient energy S of the ancestor component has no floor derivable from the failure inequalities
- `erdos1041.first_merge_radius_two_threshold_n_ge_7` (#1041): Radius-2 threshold n ≥ 7 (superseded by the sharp n ≥ 6)
- `erdos1041.fixed_degree_angular_cluster_closure` (#1041): Fixed-degree regimes from the angular second-moment bound: mu_4 = 61/100 down to mu_9 = 19/50
- `erdos1041.free_hub_existence` (#1041): Free-hub existence: tail structure of the hub-Taylor criterion, the tied Newton face closed, the near-Fekete centroid closure, exact free hubs for the three hardest witnesses, and the sharp statement (FH)
- `erdos1041.free_point_fp4_and_central_radius` (#1041): Free-point theorem FP_4 and the all-degree central radius 0.8457729381…
- `erdos1041.hub_taylor_spoke_certificate_and_degree_five_hub_set_refutation` (#1041): Hub-Taylor truncation certificate (containment and length below 2 with no metric clause), certified at the centroid on both pinned witnesses, and an exact quintic refuting the fixed hub set in the surviving regime
- `erdos1041.hyperbolic_packing_arity_floor_two_fifths` (#1041): Unconditional all-degree regime: least critical value at most 2/5, via the hyperbolic packing floor on the COVER sum
- `erdos1041.low_critical_high_arity_closure` (#1041): Unconditional regimes: μ ≤ 1/2 with k ≥ 17, μ ≤ 1/4 with k ≥ 12, μ ≤ 1/8 with k ≥ 10
- `erdos1041.low_critical_potential_closure` (#1041): Unconditional all-degree regime: least critical value at most 199/1000, no arity or capacity hypothesis
- `erdos1041.middle_regime_canonical_hub` (#1041): Middle regime by a canonical hub: the adjacent chord law kappa_n, the central-root family that breaks uniform Fekete rigidity, the exact eta-cap, and the chord-minimum conjecture
- `erdos1041.near_fekete_inner_model_widening` (#1041): The widened near-Fekete inner model: exact reduction, the hub endpoint cancellation A_j = -K_j, the proper-slice correction, and a withdrawn degree-five refutation
- `erdos1041.r11_reciprocal_log_series` (#1041): Reciprocal logarithmic series with finite Taylor remainder control
- `erdos1041.r11_three_point_defect_scalar_kernel` (#1041): Three-point defect scalar identity and equality classification
- `erdos1041.r11_weighted_variance_and_free_point_endpoints` (#1041): Weighted variance identities and free-point endpoint consequences
- `erdos1041.separated_neck_arity_forcing` (#1041): Under failure the critical spectrum inside a k-root component is compressed to [N_k t, t): a third arity floor, and the independent 1/5 confirmation
- `erdos1041.sharp_collinear_root_diameter_theorem` (#1041): Sharp collinear root-diameter theorem with Chebyshev equality
- `erdos1041.sharp_symmetric_merge_envelope` (#1041): Exact capacity-speed identity and the sharp symmetric next-merge envelope with its non-negative fibre defect
- `erdos1041.three_exterior_checked_evidence_blocks` (#1041): Two checked three-exterior evidence blocks: the middle-r eighth-s endpoint strong-gain slab and the low-capacity angular selector switch
- `erdos1041.tie_race_landscape` (#1041): The tie race: an exact octic where spokes from c* exceed the largest critical value, and the measured laws that show every fixed path family fails by a hair at near-ties
- `erdos1041.translated_nonadjacent_trinomial` (#1041): Every translated trinomial (z-h)^n + A(z-h)^m + C with 1 <= m <= n-2, coprime exponents included
- `erdos1041.unconditional_constant_factor_71_over_10` (#1041): Unconditional constant-factor bound (71/10) μ^{1/n} inside K_{2μ}
- `erdos1049.f_31_over_4_irrational_conditional` (#1049): F(31/4) and every F((31/4)^r) are irrational, conditional on Zudilin 2004 Lemma 7 and Lemma 2
- `erdos1049.homogenisation_ceiling_fixed_diagonal` (#1049): Every outward scalar evaluation at 3/2 retains a positive forced-clearing main term
- `erdos1049.homogenisation_contour_hypothesis` (#1049): The 0.40568… contour as an underived hypothesis (superseded by the conditional theorem)
- `erdos243.counterexample_frontier_profile` (#243): Frontier profile of any counterexample to #243
- `erdos243.critical_boundary_integer_rounding_rigidity` (#243): Integer rounding under a divergent-reciprocal envelope forces a linear numerator and the Sylvester recurrence at and past the critical constant
- `erdos243.good_prime_wall_landing_barrier` (#243): Distinct primes of the denominator that never reach the numerator below a ceiling force a rise larger than the wall width at the crossing
- `erdos243.historical_square_payment` (#243): Erasing a prime power from the reduced denominator costs its square in the accumulated cancellation, however many steps it takes
- `erdos243.lcm_debt_tail_gcd_sandwich_and_retention` (#243): The tail gcd is sandwiched between the LCM overlap debt and its square, almost every fresh source keeps a prime in the reduced denominator, and simultaneous erasure carries no surcharge
- `erdos243.lcm_defect_criterion_is_primitive_reduction` (#243): The lcm-weighted defect criterion is the product criterion after primitive reduction
- `erdos243.polynomial_profile_rigidity` (#243): No eventual or density-one polynomial numerator profile: nine finite-field feedback certificates and the rational-root exclusion
- `erdos243.primitive_height_prime_height_dichotomy` (#243): A counterexample has unbounded primitive height over n or unbounded largest denominator prime over the running record
- `erdos243.record_excess_dichotomy_inclusive_loglog` (#243): The record-increment coefficient is zero or strictly greater than one, closing the inclusive log-log boundary
- `erdos243.record_increment_cancellation_tradeoff` (#243): Small true record increments force large accumulated cancellation: K + Gamma >= 1 and the finite record-retirement dichotomy
- `erdos243.rising_factorial_cubic_exclusion_cubic_rate_irrationality` (#243): No rising-factorial cubic numerator profile even up to density-zero repairs, and the reciprocal sum is irrational at the exact cubic rate 1 + 3/n + o(n^-3)
- `erdos243.shifted_excess_mass_obstruction` (#243): Every fixed integer baseline has divergent normalised excess negative mass on a counterexample
- `erdos243.slow_negative_part_rigidity` (#243): Log-log slow negative part forces eventual vanishing and the Sylvester recurrence
- `erdos243.two_modulus_cut_four_thirds_alternative` (#243): Record jumps of at most four are blocked by two persistent moduli, so a counterexample has jumps of five or cancellation at least u^(4/3) at records
- `erdos243.unconditional_square_transport_legendre_defect_charge` (#243): Unconditional square transport of consecutive errors and the payment forced by a Legendre defect
- `erdos243.uniform_quadratic_antishadowing` (#243): No exact integer orbit agrees with a rational multiple of a monic quadratic on more than three quarters of any long interval
- `erdos249.certified_cf_denominator_exclusion_10e12039` (#249): Certified continued-fraction denominator floor q > 10^12039 for ∑ φ(n)/2^n
- `erdos249.control_rigidity_and_prime_uniformity` (#249): rational controls: precision–error frontier, controls obeying any finite set of exact prime laws, and r03's exact-even control; the diagnosis is loss of prime uniformity at an o(n) error scale
- `erdos249.mechanism_gap_sigma_solved_and_no_eta_quotient` (#249): the mechanism gap: Erdős #250 (sigma) is solved by Duverney/Nesterenko, #249 is the unbounded-level Möbius superposition phi = (mu*mu)*sigma of it, the eta-quotient and finite-quasimodular routes do not exist, and every remaining implication is irrationality in another coordinate
- `erdos249.prefix_two_adic_unbounded_excess_condition` (#249): one-way sufficient condition: unbounded excess of v_2(P_n) over log2 n forces irrationality (the compression producer for the reduced dyadic prefixes)
- `erdos249.prefix_window_residue_diversity` (#249): Cofinal linear diversity of growing dyadic prefix residues is sufficient for irrationality
- `erdos249.rank_uniform_hankel_and_cyclotomic_denominators` (#249): rank-uniform signed Hankel domination of the Möbius–Mersenne ladder, the parity-corrected exact 2-adic valuation, and the closure of denominator compression inside the cyclotomic lattice (kappa = 0.4282 N^2 prefix denominators, derivative rungs, coupled Schur family)
- `erdos249.tail_only_denominator_exclusion_10e30` (#249): tail-only denominator exclusion: no S = a/(2^c v) with c <= 10^30 for every odd v <= 999999 and every divisor of 2^h - 1, h in {6,12,24,36,60}
- `erdos251.certified_cf_denominator_exclusion_10e12041` (#251): Certified continued-fraction denominator floor q > 10^12041 for the prime-gap dyadic series
- `erdos251.finite_sparse_window_localization` (#251): Exact finite localization of sparse support in a block window
- `erdos251.first_finite_denominator_exclusion_10e602` (#251): First finite denominator exclusion (superseded)
- `erdos251.polynomial_gap_countermodel_ratio_bound_receipt` (#251): Python ratio-bound receipt 25/32 for the countermodel value (superseded by the Lean tsum)
- `erdos251.polynomial_gap_countermodel_series_value_32` (#251): The polynomial countermodel series sums to exactly 32 (Lean tsum)
- `erdos251.scalar_truncation_consumers` (#251): Kernel-checked scalar consumers for bad-count and truncation-error bounds
- `erdos257.arbitrary_prime_power_support_irrationality` (#257): Every infinite subset of the prime powers, with fixed dilations and finite modifications, has irrational sum at every integer base, using the reviewed analytic correlation input.
- `erdos257.delayed_gluing_host_outside_finite_mixed` (#257): Delayed gluing gives hereditary all-base irrational supports beyond every finite weighted-cover mixture
- `erdos257.finite_logarithmic_fractional_cost_separation` (#257): No universal comparison of optimised cover cost with logarithmic divisor cost
- `erdos257.logarithmic_endpoint_arithmetic_counterexample` (#257): Arithmetic-period counterexample to the proposed logarithmic-endpoint estimate (E)
- `erdos257.logarithmic_initial_interval_bound` (#257): Surviving initial-interval bound for the logarithmic cover cost
- `erdos257.periodic_core_sparse_perturbation_probe` (#257): Falsification probes for the periodic-core sparse-perturbation programme pass with zero violations
- `erdos257.powerful_support_kernel` (#257): Powerful-support irrationality (superseded by the reciprocal-summable theorem)
- `erdos257.prime_cofactor_repair_obstruction` (#257): Actual modulus-420 tetraprime repair fails infinitely often; an exact 80-anchor prefix gives prime-cofactor jumps at least 7 for multiplier 120 and at least 2 for multiplier 420. General infinite admissible supports defeat every finite fixed multiplier menu.
- `erdos257.prime_repair_finite_support_rigidity` (#257): Bounded prime jumps characterize finite greedy support; eventual repair at every prime characterizes zero or a single Mersenne atom for targets below one.
- `erdos257.r11_geometry_measure_ahlfors_api` (#257): Ahlfors ball-growth API with explicit carrier, scale, exponent, constants, restriction, and mass transport
- `erdos257.r11_geometry_measure_exact_dimension_api` (#257): Exact local dimension, normalization, comparability, and Ahlfors transport API
- `erdos257.r11_geometry_measure_fourier_api` (#257): Paper Fourier transform with coding-map transports, convolution, and finite-measure injectivity
- `erdos257.r11_geometry_measure_hausdorff_api` (#257): Hausdorff-measure and dimension bridges from explicit upper and lower ball growth
- `erdos257.sub_logstar_reciprocal_mass_irrationality` (#257): Rational p/q forces liminf H_A(x)/ell(x) at least lambda_b(p/q)/2; sub-log-star mass implies hereditary all-base irrationality.
- `erdos257.twenty_one_two_anchor_divergence_density` (#257): Conditional 1/21 divergence density from finite selected anchors, including the 2/5 twelve-anchor bound
- `erdos269.certified_cf_denominator_exclusion_10e6768` (#269): Certified denominator floor 10^6768 for the {2,3,5} running-LCM series
- `erdos269.coordinate_fibre_decoding` (#269): Irrationality of every coordinate fibre for {2,3,5}, and of largest-prime fibres for all finite prime sets
- `erdos269.finite_farey_certificate_1_64e90` (#269): M = 200 Farey box exclusion (superseded)
- `erdos269.lattice_first_hit_denominator_exclusion_10e187` (#269): Lattice first-hit denominator screen at depth 420 (superseded)
- `erdos269.running_height_prime_power_telescope` (#269): ∑_{p∈{2,3,5}} (p−1) ∑_{n≥1} 1/H(p^n) = 1
- `erdos68.certified_cf_denominator_exclusion_10e12039` (#68): Certified continued-fraction denominator floor q > 10^12039
- `erdos68.polynomial_perturbation_lcm_growth` (#68): Uniform 3/2 LCM growth for every fixed nonzero polynomial perturbation n!+P(n)
- `erdos68.strict_successor_carry_search_q_ge_300000` (#68): Size exclusion q ≥ 300000 from the strict-successor carry search (superseded as the floor)

## Uncovered required Lean (not dropped by a Signal floor)

These `lean_kernel_checked` claims have no public Comparator identity yet.
They stay listed; they are not silently omitted and they are not submitted.


## Documented holds (required Lean not yet on the public v4.30 cut)

These remain required Lean. They are accounted, not Comparator coverage, and not submitted.

- `erdos1049.rational_base_region_theorem` (#1049): kind=hold family=None
- `erdos251.adjacent_gap_difference_three_prime_reduction` (#251): kind=hold family=None
- `erdos251.bounded_perturbation_countermodel` (#251): kind=None family=ExternalVerification251BoundedPerturbationCountermodel
- `erdos68.strict_successor_carry` (#68): kind=promote family=ExternalVerification68StrictSuccessorCarry

## Public Comparator families held out of this roster

- `ExternalVerification1041CollinearChord`: Public Comparator family with no lean_kernel_checked paper claim identity (exact FQN, package pointer, or verified-declaration basename). Not auto-selected. Ordinary-paper theorems stay paper-only even when kernels live in this directory.
- `ExternalVerification1041DiskFamilySeparation`: Public Comparator family with no lean_kernel_checked paper claim identity (exact FQN, package pointer, or verified-declaration basename). Not auto-selected. Ordinary-paper theorems stay paper-only even when kernels live in this directory.
- `ExternalVerification1049RationalBaseContour`: Public Comparator family with no lean_kernel_checked paper claim identity (exact FQN, package pointer, or verified-declaration basename). Not auto-selected. Ordinary-paper theorems stay paper-only even when kernels live in this directory.
- `ExternalVerification243TwoModulusRecordCut`: Public Comparator family with no lean_kernel_checked paper claim identity (exact FQN, package pointer, or verified-declaration basename). Not auto-selected. Ordinary-paper theorems stay paper-only even when kernels live in this directory.
- `ExternalVerification249ParityPerturbedRationalControl`: Public Comparator family with no lean_kernel_checked paper claim identity (exact FQN, package pointer, or verified-declaration basename). Not auto-selected. Ordinary-paper theorems stay paper-only even when kernels live in this directory.
- `ExternalVerification251BoundedPerturbationCountermodel`: Public Comparator family with no lean_kernel_checked paper claim identity (exact FQN, package pointer, or verified-declaration basename). Not auto-selected. Ordinary-paper theorems stay paper-only even when kernels live in this directory.
- `ExternalVerification68StrictSuccessorCarry`: Public Comparator family with no lean_kernel_checked paper claim identity (exact FQN, package pointer, or verified-declaration basename). Not auto-selected. Ordinary-paper theorems stay paper-only even when kernels live in this directory.
