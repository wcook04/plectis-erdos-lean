/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #269

Erdős asks whether the reciprocal sum of running least common multiples of the
`P`-smooth integers is irrational, for a finite set `P` of at least two primes.
This challenge restates results about that series at three prime
generators. The parent problem remains open, and nothing here proves
irrationality or transcendence of a three-prime value.

`ThreePrimeStructure` carries the principal result. With `H x` the product of
the largest powers of `p`, `q` and `r` not exceeding `x`, and
`K i j k = 1 / H (p ^ i * q ^ j * r ^ k)`, for primes `p`, `q`, `r` with
`p ≠ r` and `q ≠ r` the kernel has nonsingular minors of every order, with one
index choice valid in every third-coordinate layer, and admits no
representation `K i j k = ∑ l < d, f l i * G l j k` by finitely many
rational-valued separated factors. The identity `L x = H x` formalised here is
due to Steve Fan, who recorded it for an arbitrary finite prime set on the
erdosproblems.com page for this problem on 26 June 2026. The rank statements
are the addition.

`ActualShellOrbit` treats the literal `{2,3,5}` series. The dyadic shell masses
are summable, the normalized state obeys the exact affine recurrence
`X (a + 1) = b a * X a - m a` with radix in `{2, 6, 10, 30}`, and the orbit
either meets an integer or returns cofinally at distance at least `1/31` from
every integer. The integral branch is not excluded.

`WindowEscapeEquivalence` proves that the actual cofinal local-window escape
holds if and only if the series value is irrational. That is an exact
reformulation of the problem and decides nothing about the value.

`AllScaleLattice`, `IntegralBranchPinning` and `CarryMechanism` record the
clearing, pinning, rigidity and carry algebra that a remaining argument must
use. Their lift, anchor and escape inputs are hypotheses rather than proved
producers.

`ExactDenominator` supplies the reduced denominators and the exact three
power thresholds under a rational-value hypothesis. `FixedStartResidue`
supplies the eventual ceiling formula and its limit, retaining the integral
case in which the residue is the scaled final tail.
-/

open scoped BigOperators
open Filter
open scoped Topology BigOperators

namespace PalomarCorpus.E269.Shared
/-- The predicate that the power `p ^ e` lies strictly inside the dyadic block from `2 ^ a` to `2 ^ (a + 1)`, that is `2 ^ a < p ^ e` and `p ^ e < 2 ^ (a + 1)`; for an odd prime `p` it records that a new pure `p`-power is crossed strictly between two consecutive powers of two, so that the running least common multiple gains one further factor `p` inside that block. -/
noncomputable def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)
/-- The radix of the `a`th dyadic block for the primes 2, 3 and 5: the product of 2 with 3 when some power of 3 lies strictly inside the block from `2 ^ a` to `2 ^ (a + 1)` and with 5 when some power of 5 does, so its value is 2, 6, 10 or 30. It equals the ratio `H (2 ^ (a + 1)) / H (2 ^ a)` of consecutive three-prime running heights. -/
noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 *
        (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
        (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)
/-- The representative of the integer `x` modulo `C` in the range 1 to `C`, equal to `C` when `C` divides `x` and to the ordinary nonnegative remainder otherwise, so a zero residue class is recorded as `C` rather than as 0; for `C = 0` the value is `Int.natAbs x`. -/
noncomputable def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ :=
  if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))
/-- The smooth lattice value `p ^ i * q ^ j * r ^ k` attached to the exponent triple `(i, j, k)`. -/
noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k
/-- The finite set of exponent triples `(i, j, k)`, each entry smaller than `x`, whose smooth value `p ^ i * q ^ j * r ^ k` is strictly less than `x`; for generators at least 2 the entrywise cap is never binding, so the set is exactly the triples whose smooth value is below `x`, and for pairwise distinct primes those values are exactly the `{p, q, r}`-smooth numbers below `x`. -/
noncomputable def strictSmoothExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range x).product ((Finset.range x).product (Finset.range x))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 < x
/-- The exponent triples counted by `strictSmoothExponents` at `y` and not at `x`; for generators at least 2 and `x ≤ y` these are exactly the triples whose smooth value lies in the half open interval from `x` to `y`. -/
noncomputable def strictSmoothShell (p q r x y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothExponents p q r y \ strictSmoothExponents p q r x
/-- The `a`th dyadic shell for the primes 2, 3 and 5: the exponent triples `(i, j, k)` with `2 ^ a ≤ 2 ^ i * 3 ^ j * 5 ^ k < 2 ^ (a + 1)`. -/
noncomputable def dyadicSmoothShell235 (a : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothShell 2 3 5 (2 ^ a) (2 ^ (a + 1))
/-- The number of points of the `a`th dyadic shell whose smooth value is strictly below `p ^ Nat.log p (2 ^ (a + 1))`, the largest power of `p` not exceeding `2 ^ (a + 1)`; for odd `p`, when no power of `p` lies strictly inside the shell that threshold is at most `2 ^ a` and the count is 0, while at `p = 2` the threshold is `2 ^ (a + 1)` and the count is the whole shell. -/
noncomputable def dyadicBeforeThresholdCount235 (p a : ℕ) : ℕ :=
  ((dyadicSmoothShell235 a).filter fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      p ^ Nat.log p (2 ^ (a + 1))).card
/-- The forcing digit of the `a`th dyadic block for the primes 2, 3 and 5: the shell cardinality corrected by the two threshold counts, with coefficients 10 and 4 when the largest power of 3 below `2 ^ (a + 1)` does not exceed the largest power of 5 below it and with coefficients 2 and 12 otherwise. Its ordinary meaning is the sum over the shell of `H (2 ^ (a + 1)) / (2 * H x)`, a positive integer, and the two coefficient patterns record which of the two odd prime thresholds is the smaller. -/
noncomputable def dyadicOrderedBlockDigit235 (a : ℕ) : ℕ :=
  if 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤ 5 ^ Nat.log 5 (2 ^ (a + 1)) then
    (dyadicSmoothShell235 a).card +
      10 * dyadicBeforeThresholdCount235 3 a +
      4 * dyadicBeforeThresholdCount235 5 a
  else
    (dyadicSmoothShell235 a).card +
      2 * dyadicBeforeThresholdCount235 3 a +
      12 * dyadicBeforeThresholdCount235 5 a
/-- The three-prime height `H x = p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x`, the product of the largest powers of `p`, `q` and `r` not exceeding `x`; the `Nat.log` convention makes `H 0 = H 1 = 1`, and for pairwise distinct primes and `x` at least 1 this is the least common multiple of the smooth numbers at most `x`. -/
noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x
/-- The normalized state at scale `a` of an arbitrary real tail function `tail`, namely `(H (2 ^ a) / 2) * tail a` with the three-prime height for 2, 3 and 5 cast to the reals and the division taken in the reals. -/
noncomputable def dyadicNormalizedTailStateR235
    (tail : ℕ → ℝ) (a : ℕ) : ℝ :=
  ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a
/-- The rational mass of the `a`th dyadic shell, the sum over that shell of the reciprocal of the three-prime height of the corresponding smooth value. -/
noncomputable def dyadicShellMassQ235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    ((threePrimeHeight 2 3 5
      (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹)
/-- The real cast of the rational shell mass `dyadicShellMassQ235`. -/
noncomputable def dyadicShellMassR235 (a : ℕ) : ℝ :=
  dyadicShellMassQ235 a
/-- The tail of the shell masses from scale `a` onward, taken as the Mathlib unconditional sum of `dyadicShellMassR235 (a + n)` over `n`; summability is proved in `actual_dyadicShellOrbit_recurrence_and_escape`, so this is the genuine infinite sum, and the value at `a = 0` is the reciprocal running least common multiple sum of Erdős problem 269 for the prime set `{2, 3, 5}`. -/
noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ :=
  ∑' n : ℕ, dyadicShellMassR235 (a + n)
/-- The rational mass of the count consecutive dyadic smooth shells starting at start, with an empty window having mass zero. -/
noncomputable def dyadicSmoothWindowMassQ235 (start count : ℕ) : ℚ :=
  ∑ i ∈ Finset.range count, dyadicShellMassQ235 (start + i)
/-- The natural number H(2^a)/2, where H is the three-prime running height for 2, 3 and 5; the denominator theorem uses positive scales. -/
noncomputable def heightNormalizer235 (a : ℕ) : ℕ :=
  threePrimeHeight 2 3 5 (2 ^ a) / 2
/-- The genuine normalized state `(H (2 ^ a) / 2) * T a` of the literal `{2,3,5}` shell tail, that is `dyadicNormalizedTailStateR235` applied to the actual tail `dyadicShellTsumTailR235`. -/
noncomputable def trueNormalizedState (a : ℕ) : ℝ :=
  dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a
/-- The window base of the sequence `b` from index `lo` over `len` steps, the product `b lo * b (lo + 1) * ... * b (lo + len - 1)` defined by recursion on `len` with the empty product equal to 1. -/
noncomputable def windowBase (b : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 1
  | len + 1 => b (lo + len) * windowBase b lo len
/-- The accumulated forcing of the digit sequence `e` along the radix sequence `b` from index `lo`, defined by value 0 at length 0 and by `b (lo + len) * F + e (lo + len)` at length `len + 1`, where `F` is the value at length `len`. -/
noncomputable def windowForcing (b e : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 0
  | len + 1 => b (lo + len) * windowForcing b e lo len + e (lo + len)
/-- The escape proposition at a radix sequence `b`, a digit sequence `m` and a short bound: for every positive `B` coprime to 30 and every starting index there are a later index `lo` and a positive length `len` with nonzero window base such that the least positive residue of `-B` times the window forcing, modulo the absolute window base, exceeds the short bound evaluated at `B` and `lo + len`. It is named as a proposition and is not asserted. -/
noncomputable def CofinalLocalWindowEscape
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ) : Prop :=
  ∀ B : ℕ, 0 < B → Nat.Coprime B 30 →
    ∀ lo₀ : ℕ, ∃ lo len : ℕ,
      lo₀ ≤ lo ∧ 0 < len ∧
      0 < Int.natAbs (windowBase (fun n => b n) lo len) ∧
      shortBound B (lo + len) <
        leastPositiveResidue
          (Int.natAbs (windowBase (fun n => b n) lo len))
          (-((B : ℤ) *
            windowForcing (fun n => b n) (fun n => m n) lo len))
end PalomarCorpus.E269.Shared

namespace PalomarCorpus.E269.ActualShellOrbit
open scoped BigOperators
export PalomarCorpus.E269.Shared (DyadicInternalPower dyadicBeforeThresholdCount235 dyadicBlockBase235 dyadicNormalizedTailStateR235 dyadicOrderedBlockDigit235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight)
/-- The predicate that the real number `x` lies at distance at least `δ` from every integer, that is `δ ≤ |x - z|` for every integer `z`. -/
noncomputable def FarFromIntegers (x δ : ℝ) : Prop :=
  ∀ z : ℤ, δ ≤ |x - (z : ℝ)|
/-- Three unconditional assertions about the literal `{2,3,5}` shell orbit: the shell masses are summable; at every scale the normalized state satisfies the exact affine recurrence `X (a + 1) = b a * X a - m a` with the actual radix `dyadicBlockBase235 a` and the actual ordered digit `dyadicOrderedBlockDigit235 a` cast to the reals; and either some normalized state equals an integer, or for every index there is a later scale whose state lies at distance at least `1/31` from every integer. The integral branch is not excluded, and no irrationality, transcendence, equidistribution or density conclusion follows. -/
theorem actual_dyadicShellOrbit_recurrence_and_escape :
    Summable dyadicShellMassR235 ∧
      (∀ a : ℕ,
        dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (a + 1) =
          dyadicBlockBase235 a *
              dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a -
            dyadicOrderedBlockDigit235 a) ∧
      ((∃ a : ℕ, ∃ z : ℤ,
          dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a = (z : ℝ)) ∨
        ∀ a₀, ∃ a, a₀ ≤ a ∧
          FarFromIntegers
            (dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a)
            ((1 : ℝ) / 31)) := by
  sorry
end PalomarCorpus.E269.ActualShellOrbit

namespace PalomarCorpus.E269.AllScaleLattice
open scoped BigOperators
export PalomarCorpus.E269.Shared (dyadicNormalizedTailStateR235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 dyadicSmoothWindowMassQ235 heightNormalizer235 smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight)
/-- For `p` equal to 2, 3 or 5, for `x` positive and `x < p ^ m`, the product `p * H x` divides `H (p ^ m)`, where `H` is the three-prime height for 2, 3 and 5. This is the prime-power boundary clearing law used by the lattice reduction, and it is a supporting lemma rather than an advertised result. -/
theorem smoothHeight_mul_prime_dvd_boundaryHeight
    {p m x : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 5) (hx : 0 < x) (hlt : x < p ^ m) :
    p * threePrimeHeight 2 3 5 x ∣ threePrimeHeight 2 3 5 (p ^ m) := by
  sorry
/-- For `a` at least 1, twice the natural-number normalizer `H (2 ^ a) / 2` equals `H (2 ^ a)`, so the three-prime height at a dyadic boundary is even and the truncating division is exact. The hypothesis `1 ≤ a` is needed because `H (2 ^ 0) = 1`. Supporting lemma for the clearing arguments. -/
theorem two_mul_heightNormalizer235 (a : ℕ) (ha : 1 ≤ a) :
    2 * heightNormalizer235 a = threePrimeHeight 2 3 5 (2 ^ a) := by
  sorry
/-- For every start index and window length, the normalizer at the top of the window, `H (2 ^ (start + count)) / 2`, multiplied by the rational mass of that window of shells is a natural number, so a finite window of shell masses is cleared exactly by the height at its upper endpoint. -/
theorem heightNormalizer235_mul_windowMass_eq_int (start count : ℕ) :
    ∃ z : ℕ,
      (heightNormalizer235 (start + count) : ℚ) *
        dyadicSmoothWindowMassQ235 start count = (z : ℚ) := by
  sorry
/-- For all `a` and `k`, the tail at `a` equals the finite sum of the shell masses at `a, ..., a + k - 1` plus the tail at `a + k`, the exact finite-depth splitting identity for the actual infinite tail. -/
theorem dyadicShellTsumTailR235_eq_range_add (a k : ℕ) :
    dyadicShellTsumTailR235 a =
      ∑ i ∈ Finset.range k, dyadicShellMassR235 (a + i) +
        dyadicShellTsumTailR235 (a + k) := by
  sorry
/-- If `q` is positive and the tail from the first dyadic shell onward equals `p / q` as a real number, then for every `a` at least 1 the product of `q` with the normalized state at scale `a` is an integer. Rationality of the value therefore places the normalized state on the single lattice of multiples of `1/q`, simultaneously at all dyadic scales from 1 onward. The hypothesis is rationality; nothing here shows the value is irrational. -/
theorem qsmul_normalizedTailState_eq_int_of_value_eq_rat
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ))
    {a : ℕ} (ha : 1 ≤ a) :
    ∃ k : ℤ,
      (q : ℝ) * dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a =
        (k : ℝ) := by
  sorry
/-- If `q` is positive and the tail from the first dyadic shell onward equals `p / q`, then there are indices `i < j` and an integer `z` with the difference of the normalized states at scales `1 + j` and `1 + i` equal to `z`, so rationality forces two distinct scales whose normalized states are congruent modulo 1. Excluding such a collision is not proved here. -/
theorem exists_normalizedTailState_collision_of_value_eq_rat
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) :
    ∃ i j : ℕ, i < j ∧ ∃ z : ℤ,
      dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + j) -
        dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + i) =
          (z : ℝ) := by
  sorry
end PalomarCorpus.E269.AllScaleLattice

namespace PalomarCorpus.E269.CarryMechanism
open scoped BigOperators
export PalomarCorpus.E269.Shared (CofinalLocalWindowEscape leastPositiveResidue windowBase windowForcing)
/-- The defect `base n * z n - z (n + 1) - digit n`, measuring how far the integer sequence `z` is from satisfying the affine recurrence with radix `base` and digit sequence `digit` at index `n`; it vanishes at every index exactly when `z` is an exact integral orbit of that recurrence. -/
noncomputable def carryLiftPerturbation
    (base digit z : ℕ → ℤ) (n : ℕ) : ℤ :=
  base n * z n - z (n + 1) - digit n
/-- The discrepancy `D * z n - carry n` between `D` times the candidate lift `z` and the actual carry sequence at index `n`. -/
noncomputable def carryLiftError
    (D : ℤ) (z carry : ℕ → ℤ) (n : ℕ) : ℤ :=
  D * z n - carry n
/-- The partial sum of the first `N` terms of a sequence taking values in an additive commutative group. -/
noncomputable def channelPrefix {G : Type*} [AddCommGroup G]
    (ε : ℕ → G) (N : ℕ) : G :=
  ∑ n ∈ Finset.range N, ε n
/-- The condition that the prefix sums of `ε` depend only on the channel label: whenever `jumpBase a` and `jumpBase b` are equal, the prefixes of `ε` at `a` and at `b` are equal. Equivalently, the sum of `ε` over every block of indices between two positions carrying the same label vanishes. The labels range over an arbitrary index type and the values over an arbitrary additive commutative group. -/
noncomputable def ChannelBlockNull {ι G : Type*} [AddCommGroup G]
    (jumpBase : ℕ → ι) (ε : ℕ → G) : Prop :=
  ∀ a b, jumpBase a = jumpBase b →
    channelPrefix ε a = channelPrefix ε b
/-- The three-element type of channel labels `two`, `three` and `five`, with decidable equality, recording which prime channel supplies the jump at a given index. -/
inductive Prime235
  | two
  | three
  | five
  deriving DecidableEq
/-- A contradiction from the following hypotheses taken together: an integer carry with `carry (n + 1) = base n * carry n - D * digit n` at every index; a surjective channel labelling into `Prime235`; block-nullity of the perturbation of a candidate integer lift `z`; genuine `two` to `three` and `two` to `five` transitions at which that perturbation vanishes; a nonzero lift error at index 0; a bound sequence dominating the absolute lift error everywhere; every radix at least 2; and one index `N` at which the bound is smaller than `2 ^ N`. Each of these is assumed, and none is produced for the actual `{2,3,5}` orbit. -/
theorem no_carryLift_of_errorBound_below_twoPow
    (D : ℤ)
    (base digit z carry : ℕ → ℤ)
    (jumpBase : ℕ → Prime235)
    (hcarry :
      ∀ n, carry (n + 1) =
        base n * carry n - D * digit n)
    (hchannel : Function.Surjective jumpBase)
    (hnull :
      ChannelBlockNull jumpBase
        (carryLiftPerturbation base digit z))
    {n23 n25 : ℕ}
    (h23start : jumpBase n23 = .two)
    (h23end : jumpBase (n23 + 1) = .three)
    (h25start : jumpBase n25 = .two)
    (h25end : jumpBase (n25 + 1) = .five)
    (hanchor23 :
      carryLiftPerturbation base digit z n23 = 0)
    (hanchor25 :
      carryLiftPerturbation base digit z n25 = 0)
    (herror0 : carryLiftError D z carry 0 ≠ 0)
    (bound : ℕ → ℕ)
    (hbounded :
      ∀ n, Int.natAbs (carryLiftError D z carry n) ≤ bound n)
    (hbaseTwo : ∀ n, (2 : ℤ) ≤ base n)
    (N : ℕ) (hbelow : bound N < 2 ^ N) :
    False := by
  sorry
/-- A finite four-state incompatibility: four reals in the open unit interval, four integers each within distance strictly less than 1 of the corresponding real, the two anchor equations `2 * z0 - z1 - 1 = 0` and `2 * z2 - z3 - 1 = 0`, and the vanishing first block sum `(2 * z0 - z1 - 1) + (3 * z1 - z2 - 1) = 0` cannot hold together. The statement concerns four abstract states and asserts nothing about the actual shell orbit. -/
theorem no_unitAccurateLift_with_twoAnchors_and_firstTwoBlockNull
    (T0 T1 T2 T3 : ℝ)
    (z0 z1 z2 z3 : ℤ)
    (hT0 : 0 < T0 ∧ T0 < 1)
    (hT1 : 0 < T1 ∧ T1 < 1)
    (hT2 : 0 < T2 ∧ T2 < 1)
    (hT3 : 0 < T3 ∧ T3 < 1)
    (hacc0 : |(z0 : ℝ) - T0| < 1)
    (hacc1 : |(z1 : ℝ) - T1| < 1)
    (hacc2 : |(z2 : ℝ) - T2| < 1)
    (hacc3 : |(z3 : ℝ) - T3| < 1)
    (hanchor23 : 2 * z0 - z1 - 1 = 0)
    (hanchor25 : 2 * z2 - z3 - 1 = 0)
    (hfirstBlock :
      (2 * z0 - z1 - 1) +
        (3 * z1 - z2 - 1) = 0) :
    False := by
  sorry
/-- If the channel labelling into `Prime235` is surjective, the integer sequence `ε` is block-null for it, and `ε` vanishes at an index carrying a genuine `two` to `three` transition and at an index carrying a genuine `two` to `five` transition, then `ε` vanishes at every index. Supporting rigidity lemma for the carry-lift no-go theorems. -/
theorem perturbation_eq_zero_of_blockNull_twoAnchors
    {jumpBase : ℕ → Prime235}
    {ε : ℕ → ℤ}
    (hbase : Function.Surjective jumpBase)
    (hnull : ChannelBlockNull jumpBase ε)
    {n23 n25 : ℕ}
    (h23start : jumpBase n23 = .two)
    (h23end : jumpBase (n23 + 1) = .three)
    (h25start : jumpBase n25 = .two)
    (h25end : jumpBase (n25 + 1) = .five)
    (hanchor23 : ε n23 = 0)
    (hanchor25 : ε n25 = 0) :
    ∀ n, ε n = 0 := by
  sorry
/-- An exact identity for any integer carry obeying `carry (n + 1) = base n * carry n - D * digit n` and any `a ≤ b`: `D` times the sum of the lift perturbation over the interval from `a` to `b` equals the lift error at `a` minus the lift error at `b`, plus the sum over that interval of `(base n - 1)` times the lift error at `n`. The identity displays the endpoint and weighted interior error terms and cancels neither. -/
theorem carryLift_blockDefect
    (D : ℤ)
    (base digit z carry : ℕ → ℤ)
    (hcarry :
      ∀ n, carry (n + 1) =
        base n * carry n - D * digit n)
    (a b : ℕ) (hab : a ≤ b) :
    D * (∑ n ∈ Finset.Ico a b,
      carryLiftPerturbation base digit z n) =
      carryLiftError D z carry a -
        carryLiftError D z carry b +
      ∑ n ∈ Finset.Ico a b,
        (base n - 1) * carryLiftError D z carry n := by
  sorry
/-- The residue of the carry value `c` modulo `B`, using integer remainder. -/
noncomputable def carryResidue (B c : ℤ) : ℤ := c % B
/-- The quotient of the carry value `c` by `B`, using integer division. -/
noncomputable def carryQuotient (B c : ℤ) : ℤ := c / B
/-- The digit read off from one step of the residue coordinate, `(base * residue - nextResidue) / B`, using integer division. -/
noncomputable def residueDigit (B base residue nextResidue : ℤ) : ℤ :=
  (base * residue - nextResidue) / B
/-- For `B` positive and any integer carry with `carry (n + 1) = base n * carry n - B * digit n`, writing the residue as `carry n` modulo `B` and the quotient as `carry n` divided by `B`, every digit decomposes as the residue digit at that step plus `base n` times the quotient at `n` minus the quotient at `n + 1`. The decomposition separates a finite residue part from an integral coboundary; the quotient coordinate remains uncontrolled. -/
theorem carry_eq_residueDigit_add_coboundary
    (B : ℤ) (hB : 0 < B)
    (base carry digit : ℕ → ℤ)
    (hrec : ∀ n,
      carry (n + 1) = base n * carry n - B * digit n) :
    let residue := fun n => carryResidue B (carry n)
    let quotient := fun n => carryQuotient B (carry n)
    ∀ n,
      digit n =
        residueDigit B (base n)
          (residue n) (residue (n + 1)) +
        base n * quotient n - quotient (n + 1) := by
  sorry
/-- If the cofinal local-window escape holds for a radix sequence `b`, a digit sequence `m` and a short bound, then for every positive `B` coprime to 30 there is no integer sequence `d` that satisfies `d (n + 1) = b n * d n - B * m n` at every index, is positive at every index, and has absolute value at most the short bound at `B` and `n` at every index. The escape proposition is a hypothesis here rather than a theorem. -/
theorem no_positive_reducedCarry_of_cofinalLocalWindowEscape
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ)
    (hescape : CofinalLocalWindowEscape b m shortBound)
    (B : ℕ) (hBpos : 0 < B) (hBcoprime : Nat.Coprime B 30)
    (d : ℕ → ℤ)
    (hrec : ∀ n,
      d (n + 1) = (b n : ℤ) * d n - (B : ℤ) * (m n : ℤ))
    (hpos : ∀ n, 0 < d n)
    (hbound : ∀ n, Int.natAbs (d n) ≤ shortBound B n) :
    False := by
  sorry
end PalomarCorpus.E269.CarryMechanism

namespace PalomarCorpus.E269.ExactDenominator
open scoped BigOperators
export PalomarCorpus.E269.Shared (dyadicNormalizedTailStateR235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 dyadicSmoothWindowMassQ235 heightNormalizer235 smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight trueNormalizedState)
/-- The sum of the real dyadic shell masses from scale zero, equal to the literal reciprocal running-LCM series at the primes 2, 3 and 5. -/
noncomputable def paperSeries235 : ℝ := dyadicShellTsumTailR235 0
/-- The rational normalized tail obtained from a proposed value N/D by subtracting the initial term 1 and the shells at scales 1 through a-1, then multiplying by H(2^a)/2. -/
noncomputable def rationalTailState (N : ℤ) (D a : ℕ) : ℚ :=
  (heightNormalizer235 a : ℚ) *
    ((N : ℚ) / (D : ℚ) - 1 - dyadicSmoothWindowMassQ235 1 (a - 1))
/-- Under a reduced rational-value hypothesis with denominator 2^u 3^v 5^w B and B positive and coprime to 30, identifies the actual tail state, both exact reduced denominators, and the equivalence between clearing at scale a and the three power thresholds. This is conditional arithmetic, not a proof that the series is rational or irrational. -/
theorem exact_denominators_and_threshold_clearing
    {N : ℤ} {u v w B a : ℕ}
    (hB : 0 < B) (hB30 : Nat.Coprime B 30)
    (hcop : Nat.Coprime N.natAbs (2 ^ u * 3 ^ v * 5 ^ w * B))
    (ha : 1 ≤ a)
    (hval : paperSeries235 =
      (N : ℝ) / ((2 ^ u * 3 ^ v * 5 ^ w * B : ℕ) : ℝ)) :
    ((rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a : ℚ) : ℝ) =
        trueNormalizedState a ∧
      (rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w * B) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      ((B : ℚ) * rationalTailState N
          (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      (((B : ℚ) * rationalTailState N
          (2 ^ u * 3 ^ v * 5 ^ w * B) a).den = 1 ↔
        2 ^ (u + 1) ≤ 2 ^ a ∧ 3 ^ v ≤ 2 ^ a ∧ 5 ^ w ≤ 2 ^ a) := by
  sorry
end PalomarCorpus.E269.ExactDenominator

namespace PalomarCorpus.E269.FixedStartResidue
open Filter
open scoped Topology BigOperators
export PalomarCorpus.E269.Shared (DyadicInternalPower dyadicBeforeThresholdCount235 dyadicBlockBase235 dyadicNormalizedTailStateR235 dyadicOrderedBlockDigit235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 leastPositiveResidue smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight trueNormalizedState windowForcing)
/-- The product of the actual dyadic radices over the window from lo through lo+len-1; it is 1 for the empty window. -/
noncomputable def actualWindowProduct (lo len : ℕ) : ℕ :=
  ∏ j ∈ Finset.range len, dyadicBlockBase235 (lo + j)
/-- The accumulated integer forcing of the actual dyadic shell digits over a window, using the same affine recurrence as the normalized tail. -/
noncomputable abbrev actualWindowForcing (lo len : ℕ) : ℤ :=
  windowForcing (fun a => (dyadicBlockBase235 a : ℤ))
    (fun a => (dyadicOrderedBlockDigit235 a : ℤ)) lo len
/-- For every fixed positive multiplier B and starting scale lo, the least positive residue of minus B times the window forcing eventually equals (ceil(B X_lo)-B X_lo) times the window product plus B X_(lo+h), including the integral case. -/
theorem eventually_fixedStartResidue_formula (B lo : ℕ) (hB : 0 < B) :
    ∀ᶠ h in atTop,
      (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) =
        ((⌈(B : ℝ) * trueNormalizedState lo⌉ : ℤ) : ℝ) *
            (actualWindowProduct lo h : ℝ) -
          (B : ℝ) * trueNormalizedState lo *
            (actualWindowProduct lo h : ℝ) +
          (B : ℝ) * trueNormalizedState (lo + h) := by
  sorry
/-- At each fixed starting scale and positive multiplier, the least positive residue divided by the window product converges to ceil(B X_lo)-B X_lo. The limit is zero exactly when B X_lo is integral. -/
theorem fixedStartResidue_ratio_tendsto (B lo : ℕ) (hB : 0 < B) :
    Tendsto
      (fun h : ℕ =>
        (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) /
            (actualWindowProduct lo h : ℝ))
      atTop
      (nhds (((⌈(B : ℝ) * trueNormalizedState lo⌉ : ℤ) : ℝ) -
        (B : ℝ) * trueNormalizedState lo)) := by
  sorry
/-- If B X_lo is an integer with B positive, the least positive window residue eventually equals the positive final tail B X_(lo+h), so the integral case is explicitly retained. -/
theorem eventually_fixedStartResidue_eq_tail_of_integral
    (B lo : ℕ) (hB : 0 < B) (hInt : ∃ z : ℤ, (B : ℝ) * trueNormalizedState lo = z) :
    ∀ᶠ h in atTop,
      (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) =
        (B : ℝ) * trueNormalizedState (lo + h) := by
  sorry
end PalomarCorpus.E269.FixedStartResidue

namespace PalomarCorpus.E269.IntegralBranchPinning
open scoped BigOperators
export PalomarCorpus.E269.Shared (DyadicInternalPower dyadicBeforeThresholdCount235 dyadicBlockBase235 dyadicNormalizedTailStateR235 dyadicOrderedBlockDigit235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight trueNormalizedState)
/-- For every scale `a` the genuine state satisfies `X a = m a / b a + X (a + 1) / b a`, with the actual ordered digit and the actual radix cast to the reals, so each state equals its digit anchor `m a / b a` plus the next state divided by the same radix. -/
theorem trueNormalizedState_pinning (a : ℕ) :
    trueNormalizedState a =
      (dyadicOrderedBlockDigit235 a : ℝ) / (dyadicBlockBase235 a : ℝ) +
        trueNormalizedState (a + 1) / (dyadicBlockBase235 a : ℝ) := by
  sorry
/-- For every base index `m` and depth `K`, the genuine state at `m` equals the finite mixed-radix sum of the ordered digits at `m, ..., m + K - 1` divided by the running products of the radices, plus the exact remainder `(H (2 ^ m) / 2)` times the tail at `m + K`. The remaining source tail is displayed rather than discarded. -/
theorem trueNormalizedState_eq_telescope (m K : ℕ) :
    trueNormalizedState m =
      (∑ i ∈ Finset.range K,
          (dyadicOrderedBlockDigit235 (m + i) : ℝ) /
            ∏ j ∈ Finset.range (i + 1), (dyadicBlockBase235 (m + j) : ℝ)) +
        (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 *
          dyadicShellTsumTailR235 (m + K) := by
  sorry
/-- If the genuine state equals an integer at one scale `a`, then it equals an integer at every scale `n` at least `a`. The theorem propagates the integral branch upward and does not exclude it. -/
theorem integral_state_upward_closed {a : ℕ} {z : ℤ}
    (hint : trueNormalizedState a = (z : ℝ)) :
    ∀ n, a ≤ n → ∃ z' : ℤ, trueNormalizedState n = (z' : ℝ) := by
  sorry
/-- A rigidity statement from a base index `A`: if a real sequence `y` satisfies the actual recurrence `y (n + 1) = b n * y n - m n` at every `n` at least `A`, if both `y n` and the genuine state lie in the window that is open at `m n / b n` and closed at `m n / b n + width n` for every such `n`, and if `width (A + k) / 2 ^ k` falls below every positive bound for all large `k`, then `y A` equals the genuine state at `A`. The window hypotheses for the genuine state and the vanishing hypothesis on the width are assumptions. -/
theorem surviving_window_orbit_eq_true_state
    (width : ℕ → ℝ) (A : ℕ) (y : ℕ → ℝ)
    (hrec : ∀ n, A ≤ n →
      y (n + 1) =
        (dyadicBlockBase235 n : ℝ) * y n -
          (dyadicOrderedBlockDigit235 n : ℝ))
    (hwin : ∀ n, A ≤ n →
      (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < y n ∧
        y n ≤ (dyadicOrderedBlockDigit235 n : ℝ) /
          (dyadicBlockBase235 n : ℝ) + width n)
    (hwidth : ∀ n, A ≤ n →
      (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) <
          trueNormalizedState n ∧
        trueNormalizedState n ≤
          (dyadicOrderedBlockDigit235 n : ℝ) /
            (dyadicBlockBase235 n : ℝ) + width n)
    (hvanish : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      width (A + k) / 2 ^ k < ε) :
    y A = trueNormalizedState A := by
  sorry
end PalomarCorpus.E269.IntegralBranchPinning

namespace PalomarCorpus.E269.ThreePrimeStructure
export PalomarCorpus.E269.Shared (smooth3Val threePrimeHeight)
/-- The rational running-LCM kernel at the exponent triple `(i, j, k)`, the inverse in the rationals of the natural-number three-prime height of `p ^ i * q ^ j * r ^ k`. -/
noncomputable def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹
/-- The finite index set of exponent triples `(i, j, k)` with `i ≤ Nat.log p x`, `j ≤ Nat.log q x`, `k ≤ Nat.log r x` and smooth value at most `x`; for pairwise distinct primes these are the exponent coordinates of the `{p, q, r}`-smooth numbers not exceeding `x`. -/
noncomputable def smoothPrefixExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (Nat.log p x + 1)).product
      ((Finset.range (Nat.log q x + 1)).product
        (Finset.range (Nat.log r x + 1)))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 ≤ x
/-- The least common multiple of the smooth values `p ^ i * q ^ j * r ^ k` over the index set `smoothPrefixExponents p q r x`, that is the running least common multiple of all `{p, q, r}`-smooth numbers at most `x`. -/
noncomputable def smoothPrefixLcm (p q r x : ℕ) : ℕ :=
  (smoothPrefixExponents p q r x).lcm
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2
/-- The condition that `x` and `y` have the same integer logarithm in each of the three bases `p`, `q` and `r`, so that they lie in one cell of the common refinement of the three logarithmic partitions. -/
noncomputable def SameThreePrimeLogCell (p q r x y : ℕ) : Prop :=
  Nat.log p x = Nat.log p y ∧
    Nat.log q x = Nat.log q y ∧
      Nat.log r x = Nat.log r y
/-- The finite set of the first `count` positive powers of `p`, namely `p ^ 1` through `p ^ count`. -/
noncomputable def positivePrimePowers (p count : ℕ) : Finset ℕ :=
  (Finset.range count).image fun e => p ^ (e + 1)
/-- The union of the first `count` positive powers of each of `p`, `q` and `r`, that is the first `count` values in each of the three channels at which the running least common multiple jumps. -/
noncomputable def threePrimePositiveJumpSet (p q r count : ℕ) : Finset ℕ :=
  (positivePrimePowers p count ∪ positivePrimePowers q count) ∪
    positivePrimePowers r count
/-- The rectangular index set of exponent triples `(i, j, k)` with `i ≤ hp`, `j ≤ hq` and `k ≤ hr`. -/
noncomputable def smoothExponentBox (hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (hp + 1)).product
    ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))
/-- The three-prime height of the smooth value of the exponent triple `e`, that is `H (p ^ e.1 * q ^ e.2.1 * r ^ e.2.2)`. -/
noncomputable def smoothPointHeight (p q r : ℕ) (e : ℕ × ℕ × ℕ) : ℕ :=
  threePrimeHeight p q r (smooth3Val p q r e.1 e.2.1 e.2.2)
/-- The subset of the exponent box with bounds `hp`, `hq`, `hr` on which the point height equals `H`, that is one fibre of the height map over that box. -/
noncomputable def smoothHeightFiber
    (p q r hp hq hr H : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (smoothExponentBox hp hq hr).filter fun e => smoothPointHeight p q r e = H
/-- The subset of the exponent box with bounds `hp`, `hq`, `hr` whose smooth value lies in the half open interval from `lo` to `hi`. -/
noncomputable def smoothExponentShell
    (p q r lo hi hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (hp + 1)).product
      ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))).filter
    fun e => lo ≤ smooth3Val p q r e.1 e.2.1 e.2.2 ∧
      smooth3Val p q r e.1 e.2.1 e.2.2 < hi
/-- For pairwise distinct primes `p`, `q`, `r` and every nonzero `x`, the least common multiple of the `{p, q, r}`-smooth numbers at most `x` equals `p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x`, the product of the three maximal pure prime powers not exceeding `x`. This is the three-prime case of the running least common multiple factorisation identity recorded by Steve Fan for an arbitrary finite prime set, and it is not claimed as new here. -/
theorem smoothPrefixLcm_eq_threePrimeHeight
    {p q r x : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hx : x ≠ 0) :
    smoothPrefixLcm p q r x = threePrimeHeight p q r x := by
  sorry
/-- With no hypothesis on the generators, the kernel takes equal values at two exponent triples whose smooth values lie in the same logarithmic cell, that is whose three integer logarithms in the bases `p`, `q` and `r` agree. -/
theorem threePrimeKernelQ_eq_of_sameLogCell
    {p q r i j k i' j' k' : ℕ}
    (hcell : SameThreePrimeLogCell p q r
      (smooth3Val p q r i j k) (smooth3Val p q r i' j' k')) :
    threePrimeKernelQ p q r i j k =
      threePrimeKernelQ p q r i' j' k' := by
  sorry
/-- For pairwise distinct primes `p`, `q`, `r`, the first `count` positive powers in the three channels are all distinct, so the jump set has exactly `3 * count` elements. -/
theorem threePrimePositiveJumpSet_card
    {p q r count : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (threePrimePositiveJumpSet p q r count).card = 3 * count := by
  sorry
/-- With no hypothesis on the generators, the sum of the kernel over a finite exponent box equals the sum, over the heights attained on that box, of the cardinality of the corresponding height fibre scaled by the reciprocal of that height. The multiplicities of the running least common multiple values are exposed rather than cancelled. -/
theorem finiteSmoothKernelSum_groupedByHeight
    (p q r hp hq hr : ℕ) :
    (∑ e ∈ smoothExponentBox hp hq hr,
      threePrimeKernelQ p q r e.1 e.2.1 e.2.2) =
      ∑ H ∈ (smoothExponentBox hp hq hr).image (smoothPointHeight p q r),
        (smoothHeightFiber p q r hp hq hr H).card • ((H : ℚ)⁻¹) := by
  sorry
/-- Under the hypotheses that `r` is positive, the shell width satisfies `hi ≤ r * lo`, the exponent bounds are sorted as `hp ≤ hq ≤ hr`, and `hp + hq + hr = j`, nine times the cardinality of the exponent shell is at most `(j + 3) ^ 2`. Supporting multiplicity bound behind the quadratic majorant for the shell masses. -/
theorem smoothExponentShell_card_quadratic
    {p q r lo hi hp hq hr j : ℕ}
    (hrPos : 0 < r) (hwidth : hi ≤ r * lo)
    (hpq : hp ≤ hq) (hqr : hq ≤ hr)
    (hsum : hp + hq + hr = j) :
    9 * (smoothExponentShell p q r lo hi hp hq hr).card ≤
      (j + 3) ^ 2 := by
  sorry
/-- The two by two minor of the `{2,3,5}` kernel on the exponent pairs `(0,0)`, `(1,1)`, `(1,0)` and `(0,1)` in the layer `k = 0` equals `-1/15`; those four entries are `1`, `1/60`, `1/2` and `1/6` in that order, so the determinant is `1/60 - 1/12`. This single nonzero determinant excludes a rank-one separated representation and nothing beyond that. -/
theorem kernel_235_minor_eq_neg_one_fifteen :
    threePrimeKernelQ 2 3 5 0 0 0 *
          threePrimeKernelQ 2 3 5 1 1 0 -
        threePrimeKernelQ 2 3 5 1 0 0 *
          threePrimeKernelQ 2 3 5 0 1 0 =
      -(1 / 15 : ℚ) := by
  sorry
/-- The predicate that no positive integer multiple of the real number `α` is an integer, that is the fractional part of `n * α` is nonzero for every positive `n`; for a real number this holds exactly when `α` is irrational. -/
noncomputable def NoIntegerOrbit (α : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → Int.fract ((n : ℝ) * α) ≠ 0
/-- For natural numbers `p`, `q`, `r` each greater than 1 such that neither `Real.logb r p` nor `Real.logb r q` has a positive integer multiple that is an integer, and for every order `n`, there are injective index maps `I` and `J` from `Fin n` to the naturals such that the `n` by `n` determinant of the kernel entries `K (I a) (J b) k` is nonzero for every value `k` of the third exponent, with one choice of `I` and `J` valid in all layers at once. The theorem asserts existence of suitable index families and constrains the leading minors in no way. -/
theorem exists_uniform_nonsingular_threePrimeKernel_minor
    {p q r : ℕ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hα : NoIntegerOrbit (Real.logb r p)) (hβ : NoIntegerOrbit (Real.logb r q))
    (n : ℕ) :
    ∃ I J : Fin n → ℕ,
      Function.Injective I ∧ Function.Injective J ∧
        ∀ k : ℕ,
          (Matrix.det fun a b : Fin n =>
            threePrimeKernelQ p q r (I a) (J b) k) ≠ 0 := by
  sorry
/-- For primes `p`, `q`, `r` with `p ≠ r` and `q ≠ r`, and with no hypothesis relating `p` and `q`, two conclusions hold: for every order `n` there are injective index maps giving a nonzero `n` by `n` kernel minor simultaneously in every layer `k`; and for no natural number `d` are there rational-valued functions `f` and `G` with `K i j k` equal to the sum over `l < d` of `f l i * G l j k` for all `i`, `j`, `k`. The second clause excludes exact finite separated representations of that shape. Neither clause yields irrationality or transcendence. -/
theorem threePrimeKernel_infiniteRank_and_noFiniteSeparation
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    (∀ n : ℕ,
      ∃ I J : Fin n → ℕ,
        Function.Injective I ∧ Function.Injective J ∧
          ∀ k : ℕ,
            (Matrix.det fun a b : Fin n =>
              threePrimeKernelQ p q r (I a) (J b) k) ≠ 0) ∧
      (∀ d : ℕ,
        ¬ ∃ (f : Fin d → ℕ → ℚ) (G : Fin d → ℕ → ℕ → ℚ),
            ∀ i j k,
              threePrimeKernelQ p q r i j k =
                ∑ l : Fin d, f l i * G l j k) := by
  sorry
end PalomarCorpus.E269.ThreePrimeStructure

namespace PalomarCorpus.E269.WindowEscapeEquivalence
open scoped BigOperators
export PalomarCorpus.E269.Shared (CofinalLocalWindowEscape DyadicInternalPower dyadicBeforeThresholdCount235 dyadicBlockBase235 dyadicNormalizedTailStateR235 dyadicOrderedBlockDigit235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 leastPositiveResidue smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight trueNormalizedState windowBase windowForcing)
/-- The quadratic width `90 * (n + 1) ^ 2`, the short bound used by the rationality-to-carry bridge and by the actual escape proposition. The accompanying paper proves that it also bounds the genuine normalized state at index `n`; no compared declaration here proves that bound. -/
noncomputable def bridgeWidth (n : ℕ) : ℕ := 90 * (n + 1) ^ 2
/-- The proposition `CofinalLocalWindowEscape` instantiated at the actual radix word `dyadicBlockBase235`, the actual ordered digit `dyadicOrderedBlockDigit235` and the short bound `B * 90 * (n + 1) ^ 2`. It is named as a proposition and is not asserted. -/
noncomputable def ActualCofinalLocalWindowEscape : Prop :=
  CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235
    (fun B n => B * bridgeWidth n)
/-- An unconditional equivalence: the actual cofinal local-window escape holds if and only if `dyadicShellTsumTailR235 0` is irrational, that is if and only if the reciprocal running least common multiple sum of Erdős problem 269 at the prime set `{2, 3, 5}` is irrational. The theorem proves an equivalence of two propositions and proves neither of them. -/
theorem actualCofinalLocalWindowEscape_iff_irrational_value :
    ActualCofinalLocalWindowEscape ↔ Irrational (dyadicShellTsumTailR235 0) := by
  sorry
/-- An unconditional equivalence: the actual cofinal local-window escape holds if and only if the tail `dyadicShellTsumTailR235 1` from the first dyadic shell onward is irrational. That tail is the series value minus 1, so this is the same equivalence in the shifted coordinate, and it proves neither side. -/
theorem actualCofinalLocalWindowEscape_iff :
    ActualCofinalLocalWindowEscape ↔ Irrational (dyadicShellTsumTailR235 1) := by
  sorry
/-- The forward direction of the equivalence: irrationality of `dyadicShellTsumTailR235 1` implies the actual cofinal local-window escape. Supporting implication of `actualCofinalLocalWindowEscape_iff`. -/
theorem cofinalLocalWindowEscape_of_irrational
    (h : Irrational (dyadicShellTsumTailR235 1)) :
    ActualCofinalLocalWindowEscape := by
  sorry
/-- If `dyadicShellTsumTailR235 1` is irrational, then for every short bound `sb` admitting a function `c` with `sb B n ≤ c B * (n + 1) ^ 2` for all `B` and `n`, the cofinal local-window escape holds at the actual radix word and the actual ordered digit for that short bound. Escape at every sharpening of the width inside the quadratic family is therefore implied by irrationality, so no such sharpening gives a producer weaker than the target. -/
theorem cofinalLocalWindowEscape_of_irrational_of_quadratic
    (h : Irrational (dyadicShellTsumTailR235 1)) (sb : ℕ → ℕ → ℕ) (c : ℕ → ℕ)
    (hsb : ∀ B n, sb B n ≤ c B * (n + 1) ^ 2) :
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 sb := by
  sorry
/-- If `q` is positive and `dyadicShellTsumTailR235 1` equals `p / q`, then there are a positive `B` coprime to 30, a finite onset index, and an integer sequence `d` satisfying `d (n + 1) = b n * d n - B * m n`, positivity of `d n`, and `|d n| ≤ B * 90 * (n + 1) ^ 2` at every index from that onset onward, where `b` and `m` are the actual radix word and the actual ordered digit. The hypothesis is rationality of the value; the theorem produces the carry and excludes nothing on its own. -/
theorem exists_reducedCarry_of_value_eq_rat
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) :
    ∃ (B a₀ : ℕ) (d : ℕ → ℤ), 0 < B ∧ Nat.Coprime B 30 ∧
      (∀ n, a₀ ≤ n →
        d (n + 1) = (dyadicBlockBase235 n : ℤ) * d n
          - (B : ℤ) * (dyadicOrderedBlockDigit235 n : ℤ)) ∧
      (∀ n, a₀ ≤ n → 0 < d n) ∧
      (∀ n, a₀ ≤ n → Int.natAbs (d n) ≤ B * bridgeWidth n) := by
  sorry
/-- The exact window identity for the genuine normalized state: for all `lo` and `len`, the state at `lo + len` equals the integer window base of the actual radix word times the state at `lo`, minus the accumulated integer forcing of the actual ordered digits over that window, both integers cast to the reals. -/
theorem trueNormalizedState_window (lo len : ℕ) :
    trueNormalizedState (lo + len)
      = ((windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len : ℤ) : ℝ)
          * trueNormalizedState lo
        - ((windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
              (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len : ℤ) : ℝ) := by
  sorry
/-- If `B` is positive, `K` is at least `B * 90 * (lo + len + 1) ^ 2`, and the least positive residue of `-B` times the window forcing, modulo the absolute window base, is at most `K`, then some integer `k` satisfies `|B * X lo - k| ≤ K / 2 ^ len` for the genuine normalized state `X`. The width condition on `K` is required, no growth condition is imposed on `K`, and no irrationality conclusion follows. -/
theorem near_integer_of_residue_le_general
    (B lo len K : ℕ) (hB : 0 < B)
    (hKle : B * bridgeWidth (lo + len) ≤ K)
    (hres : leastPositiveResidue
        (Int.natAbs (windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len))
        (-((B : ℤ) * windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
             (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len))
      ≤ K) :
    ∃ k : ℤ, |(B : ℝ) * trueNormalizedState lo - (k : ℝ)|
      ≤ ((K : ℕ) : ℝ) / 2 ^ len := by
  sorry
/-- For every `c` and `lo` there is a positive window length `len` with `c * (lo + len + 1) ^ 2 < 2 ^ len`, the elementary fact that a power of two eventually overtakes a quadratic. Supporting lemma for the escape equivalence. -/
theorem exists_pow_gt_quadratic (c lo : ℕ) :
    ∃ len : ℕ, 0 < len ∧ c * (lo + len + 1) ^ 2 < 2 ^ len := by
  sorry
/-- The exact jump index a + floor(log_3(2^a)) + floor(log_5(2^a)) at the dyadic endpoint 2^a, using integer-floor logarithms to bases 3 and 5. -/
noncomputable def paperJumpIndex (a : ℕ) : ℕ := a + Nat.log 3 (2 ^ a) + Nat.log 5 (2 ^ a)
/-- The rational quadratic majorant (n^2 + 8*n + 18)/9 at a jump index n. -/
noncomputable def carryMajorantQ (n : ℕ) : ℚ := ((n : ℚ) ^ 2 + 8 * n + 18) / 9
/-- The natural floor of B times the rational quadratic carry majorant at the jump index of the dyadic endpoint 2^a. -/
noncomputable def longPaperCap (B a : ℕ) : ℕ :=
  ⌊(B : ℚ) * carryMajorantQ (paperJumpIndex a)⌋₊
/-- The explicit natural quadratic cap 90*B*(a+1)^2 for the actual dyadic orbit. -/
noncomputable def shortPaperCap (B a : ℕ) : ℕ := 90 * B * (a + 1) ^ 2
/-- The full long-paper escape proposition: every natural cap dominating the long-paper cap and tending to zero after division by 8^a gives an escape condition equivalent to irrationality of the literal {2,3,5} reciprocal running-LCM series. Both named caps satisfy the decay condition, the long cap is bounded by the short cap, and escape at each named cap is equivalent to irrationality. The zero cap always gives escape. The equivalences do not assert irrationality, and the zero cap is not asserted to dominate the long cap. -/
theorem octic_escape_whole :
    (∀ G : ℕ → ℕ → ℕ,
      (∀ B a, 0 < B → longPaperCap B a ≤ G B a) →
      (∀ B, 0 < B → Filter.Tendsto
        (fun a : ℕ => (G B a : ℝ) / (8 : ℝ) ^ a) Filter.atTop (nhds 0)) →
      (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 G ↔
        Irrational (dyadicShellTsumTailR235 0))) ∧
    (∀ B : ℕ, Filter.Tendsto
      (fun a : ℕ => (longPaperCap B a : ℝ) / (8 : ℝ) ^ a) Filter.atTop (nhds 0)) ∧
    (∀ B a : ℕ, longPaperCap B a ≤ shortPaperCap B a) ∧
    (∀ B : ℕ, Filter.Tendsto
      (fun a : ℕ => (shortPaperCap B a : ℝ) / (8 : ℝ) ^ a) Filter.atTop (nhds 0)) ∧
    (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 longPaperCap ↔
      Irrational (dyadicShellTsumTailR235 0)) ∧
    (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 shortPaperCap ↔
      Irrational (dyadicShellTsumTailR235 0)) ∧
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 (fun _ _ => 0) := by
  sorry
end PalomarCorpus.E269.WindowEscapeEquivalence
