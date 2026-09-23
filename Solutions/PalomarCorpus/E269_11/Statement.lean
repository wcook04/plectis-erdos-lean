/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E269_11

Every non-theorem declaration of `PalomarCorpus/E269_11/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E269.WindowEscapeEquivalence
open scoped BigOperators
/-- The smooth lattice value `p ^ i * q ^ j * r ^ k` attached to the exponent triple `(i, j, k)`. -/
noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ := p ^ i * q ^ j * r ^ k
/-- The three-prime height `H x = p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x`, the product of the largest powers of `p`, `q` and `r` not exceeding `x`; the `Nat.log` convention makes `H 0 = H 1 = 1`, and for pairwise distinct primes and `x` at least 1 this is the least common multiple of the smooth numbers at most `x`. -/
noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x
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
/-- The rational mass of the `a`th dyadic shell, the sum over that shell of the reciprocal of the three-prime height of the corresponding smooth value. -/
noncomputable def dyadicShellMassQ235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    ((threePrimeHeight 2 3 5
      (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹)
/-- The real cast of the rational shell mass `dyadicShellMassQ235`. -/
noncomputable def dyadicShellMassR235 (a : ℕ) : ℝ := dyadicShellMassQ235 a
/-- The predicate that the power `p ^ e` lies strictly inside the dyadic block from `2 ^ a` to `2 ^ (a + 1)`, that is `2 ^ a < p ^ e` and `p ^ e < 2 ^ (a + 1)`; for an odd prime `p` it records that a new pure `p`-power is crossed strictly between two consecutive powers of two, so that the running least common multiple gains one further factor `p` inside that block. -/
noncomputable def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)
/-- The radix of the `a`th dyadic block for the primes 2, 3 and 5: the product of 2 with 3 when some power of 3 lies strictly inside the block from `2 ^ a` to `2 ^ (a + 1)` and with 5 when some power of 5 does, so its value is 2, 6, 10 or 30. It equals the ratio `H (2 ^ (a + 1)) / H (2 ^ a)` of consecutive three-prime running heights. -/
noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 * (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
        (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)
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
/-- The tail of the shell masses from scale `a` onward, taken as the Mathlib unconditional sum of `dyadicShellMassR235 (a + n)` over `n`; summability is proved in `actual_dyadicShellOrbit_recurrence_and_escape`, so this is the genuine infinite sum, and the value at `a = 0` is the reciprocal running least common multiple sum of Erdős problem 269 for the prime set `{2, 3, 5}`. -/
noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ :=
  ∑' n : ℕ, dyadicShellMassR235 (a + n)
/-- The normalized state at scale `a` of an arbitrary real tail function `tail`, namely `(H (2 ^ a) / 2) * tail a` with the three-prime height for 2, 3 and 5 cast to the reals and the division taken in the reals. -/
noncomputable def dyadicNormalizedTailStateR235
    (tail : ℕ → ℝ) (a : ℕ) : ℝ :=
  ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a
/-- The genuine normalized state `(H (2 ^ a) / 2) * T a` of the literal `{2,3,5}` shell tail, that is `dyadicNormalizedTailStateR235` applied to the actual tail `dyadicShellTsumTailR235`. -/
noncomputable def trueNormalizedState (a : ℕ) : ℝ :=
  dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a
/-- The representative of the integer `x` modulo `C` in the range 1 to `C`, equal to `C` when `C` divides `x` and to the ordinary nonnegative remainder otherwise, so a zero residue class is recorded as `C` rather than as 0; for `C = 0` the value is `Int.natAbs x`. -/
noncomputable def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ :=
  if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))
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
/-- The quadratic width `90 * (n + 1) ^ 2`, the short bound used by the rationality-to-carry bridge and by the actual escape proposition. The accompanying paper proves that it also bounds the genuine normalized state at index `n`; no compared declaration here proves that bound. -/
noncomputable def bridgeWidth (n : ℕ) : ℕ := 90 * (n + 1) ^ 2
/-- The proposition `CofinalLocalWindowEscape` instantiated at the actual radix word `dyadicBlockBase235`, the actual ordered digit `dyadicOrderedBlockDigit235` and the short bound `B * 90 * (n + 1) ^ 2`. It is named as a proposition and is not asserted. -/
noncomputable def ActualCofinalLocalWindowEscape : Prop :=
  CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235
    (fun B n => B * bridgeWidth n)
/-- The exact jump index a + floor(log_3(2^a)) + floor(log_5(2^a)) at the dyadic endpoint 2^a, using integer-floor logarithms to bases 3 and 5. -/
noncomputable def paperJumpIndex (a : ℕ) : ℕ := a + Nat.log 3 (2 ^ a) + Nat.log 5 (2 ^ a)
/-- The rational quadratic majorant (n^2 + 8*n + 18)/9 at a jump index n. -/
noncomputable def carryMajorantQ (n : ℕ) : ℚ := ((n : ℚ) ^ 2 + 8 * n + 18) / 9
/-- The natural floor of B times the rational quadratic carry majorant at the jump index of the dyadic endpoint 2^a. -/
noncomputable def longPaperCap (B a : ℕ) : ℕ :=
  ⌊(B : ℚ) * carryMajorantQ (paperJumpIndex a)⌋₊
/-- The explicit natural quadratic cap 90*B*(a+1)^2 for the actual dyadic orbit. -/
noncomputable def shortPaperCap (B a : ℕ) : ℕ := 90 * B * (a + 1) ^ 2
end PalomarCorpus.E269.WindowEscapeEquivalence
