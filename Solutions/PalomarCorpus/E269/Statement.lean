/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E269

Every non-theorem declaration of `PalomarCorpus/E269/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

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
end PalomarCorpus.E269.ActualShellOrbit

namespace PalomarCorpus.E269.AllScaleLattice
open scoped BigOperators
export PalomarCorpus.E269.Shared (dyadicNormalizedTailStateR235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight)
/-- The integer normalizer `H (2 ^ a) / 2` for the primes 2, 3 and 5, with the division taken in the natural numbers; for `a` at least 1 the height is even and the division is exact, while the value at `a = 0` is 0 because `H 1 = 1`. -/
noncomputable def heightNormalizer235 (a : ℕ) : ℕ :=
  threePrimeHeight 2 3 5 (2 ^ a) / 2
/-- The rational mass of the finite window of `count` consecutive dyadic shells beginning at index `start`, the sum of `dyadicShellMassQ235 (start + i)` over `i < count`. -/
noncomputable def dyadicSmoothWindowMassQ235 (start count : ℕ) : ℚ :=
  ∑ i ∈ Finset.range count, dyadicShellMassQ235 (start + i)
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
/-- The residue of the carry value `c` modulo `B`, using integer remainder. -/
noncomputable def carryResidue (B c : ℤ) : ℤ := c % B
/-- The quotient of the carry value `c` by `B`, using integer division. -/
noncomputable def carryQuotient (B c : ℤ) : ℤ := c / B
/-- The digit read off from one step of the residue coordinate, `(base * residue - nextResidue) / B`, using integer division. -/
noncomputable def residueDigit (B base residue nextResidue : ℤ) : ℤ :=
  (base * residue - nextResidue) / B
end PalomarCorpus.E269.CarryMechanism

namespace PalomarCorpus.E269.IntegralBranchPinning
open scoped BigOperators
export PalomarCorpus.E269.Shared (DyadicInternalPower dyadicBeforeThresholdCount235 dyadicBlockBase235 dyadicNormalizedTailStateR235 dyadicOrderedBlockDigit235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight trueNormalizedState)
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
/-- The predicate that no positive integer multiple of the real number `α` is an integer, that is the fractional part of `n * α` is nonzero for every positive `n`; for a real number this holds exactly when `α` is irrational. -/
noncomputable def NoIntegerOrbit (α : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → Int.fract ((n : ℝ) * α) ≠ 0
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
end PalomarCorpus.E269.WindowEscapeEquivalence
