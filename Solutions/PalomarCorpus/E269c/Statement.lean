/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E269c

Every non-theorem declaration of `PalomarCorpus/E269c/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E269.PaperStatementsC
open scoped BigOperators
/-- A positive `p`-power lies strictly inside the dyadic block `(2^a, 2^(a+1))`. Endpoints are excluded because the dyadic jump itself is the distinguished terminal factor of the compressed block. Local copy of ErdosProblems.Erdos269.DyadicInternalPower, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)
/-- A real number is at least `δ` from every integer. Local copy of ErdosProblems.Erdos269.FarFromIntegers, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FarFromIntegers (x δ : ℝ) : Prop :=
  ∀ z : ℤ, δ ≤ |x - (z : ℝ)|
/-- The product of the largest pure `p`-, `q`-, and `r`-powers not exceeding `x`. For a `{p,q,r}`-smooth `x`, this is the running LCM of the smooth prefix. Local copy of ErdosProblems.Erdos269.threePrimeHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x
/-- Normalize a real source tail by half of the current endpoint height. Local copy of ErdosProblems.Erdos269.dyadicNormalizedTailStateR235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicNormalizedTailStateR235 (tail : ℕ → ℝ) (a : ℕ) : ℝ :=
  ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a
/-- The `{p,q,r}`-smooth lattice point with exponent vector `(i,j,k)`. Local copy of ErdosProblems.Erdos269.smooth3Val, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k
/-- Strict `{p,q,r}`-smooth exponent prefix. The ambient exponent box of side `x` is deliberately redundant; it gives a finite, integer-only carrier for the strict inequality used by the returned floor-sum formula. Local copy of ErdosProblems.Erdos269.strictSmoothExponents, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictSmoothExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range x).product ((Finset.range x).product (Finset.range x))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 < x
/-- Exact shell between two strict cutoffs. Local copy of ErdosProblems.Erdos269.strictSmoothShell, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictSmoothShell (p q r x y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothExponents p q r y \ strictSmoothExponents p q r x
/-- The actual `{2,3,5}`-smooth exponent points in the half-open dyadic shell `[2^a,2^(a+1))`. Local copy of ErdosProblems.Erdos269.dyadicSmoothShell235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicSmoothShell235 (a : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothShell 2 3 5 (2 ^ a) (2 ^ (a + 1))
/-- Literal reciprocal running-height mass of one half-open dyadic shell. Local copy of ErdosProblems.Erdos269.dyadicShellMassQ235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicShellMassQ235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    ((threePrimeHeight 2 3 5
      (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹)
/-- Real-valued shell mass used by the actual infinite analytic tail. Local copy of ErdosProblems.Erdos269.dyadicShellMassR235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicShellMassR235 (a : ℕ) : ℝ :=
  dyadicShellMassQ235 a
/-- The literal infinite tail beginning at dyadic shell `a`. Local copy of ErdosProblems.Erdos269.dyadicShellTsumTailR235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ :=
  ∑' n : ℕ, dyadicShellMassR235 (a + n)
/-- The genuine infinite normalized tail state. Local copy of ErdosProblems.Erdos269.trueNormalizedState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def trueNormalizedState (a : ℕ) : ℝ :=
  dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a
/-- The exact all-denominator, all-start nonintegrality statement of the long record. Local copy of ErdosProblems.Erdos269.PaperR7.AllReducedTailsNonintegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def AllReducedTailsNonintegral : Prop :=
  ∀ B : ℕ, 0 < B → Nat.Coprime B 30 → ∀ a : ℕ, 1 ≤ a →
    ∀ z : ℤ, (B : ℝ) * trueNormalizedState a ≠ (z : ℝ)
/-- Local copy of ErdosProblems.Erdos269.PaperR7.Exponent235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev Exponent235 := ℕ × ℕ × ℕ
/-- Local copy of ErdosProblems.Erdos269.PaperR7.exponentValue235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exponentValue235 (e : Exponent235) : ℕ :=
  smooth3Val 2 3 5 e.1 e.2.1 e.2.2
/-- Positive smooth integers, counted once as numbers rather than as exponents. Local copy of ErdosProblems.Erdos269.PaperR7.Smooth235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Smooth235 := {x : ℕ // x ∈ Set.range exponentValue235}
/-- The forcing digit as printed in the short note, before any regrouping. Local copy of ErdosProblems.Erdos269.PaperR7.literalForcing235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def literalForcing235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) /
      (2 * (threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ))
/-- Geometric (unconstrained) quadratic majorant. Local copy of ErdosProblems.Erdos269.carryMajorantQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryMajorantQ (n : ℕ) : ℚ :=
  ((n : ℚ) ^ 2 + 8 * n + 18) / 9
/-- The long record's actual jump index. Local copy of ErdosProblems.Erdos269.PaperR7.paperJumpIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperJumpIndex (a : ℕ) : ℕ := a + Nat.log 3 (2 ^ a) + Nat.log 5 (2 ^ a)
/-- The long record's exact cap. It is NOT the short note's `90` cap. Local copy of ErdosProblems.Erdos269.PaperR7.longPaperCap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def longPaperCap (B a : ℕ) : ℕ :=
  ⌊(B : ℚ) * carryMajorantQ (paperJumpIndex a)⌋₊
/-- A canonical integer-valued representative; equality to the scaled state is proved below. Local copy of ErdosProblems.Erdos269.PaperR7.paperReducedCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperReducedCarry (B a : ℕ) : ℤ :=
  ⌊(B : ℝ) * trueNormalizedState a⌋
/-- Exponent vectors of the actual `{p,q,r}`-smooth prefix up to `x`. The logarithmic box makes the prefix finite; the final filter keeps only products which really lie below `x`. Local copy of ErdosProblems.Erdos269.smoothPrefixExponents, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def smoothPrefixExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (Nat.log p x + 1)).product
      ((Finset.range (Nat.log q x + 1)).product
        (Finset.range (Nat.log r x + 1)))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 ≤ x
/-- The literal running LCM of the finite smooth prefix. Local copy of ErdosProblems.Erdos269.smoothPrefixLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def smoothPrefixLcm (p q r x : ℕ) : ℕ :=
  (smoothPrefixExponents p q r x).lcm
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2
/-- The original running-LCM summand at a smooth integer. Local copy of ErdosProblems.Erdos269.PaperR7.smoothReciprocal235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def smoothReciprocal235 (x : Smooth235) : ℝ :=
  (smoothPrefixLcm 2 3 5 x.val : ℝ)⁻¹
/-- The scalar `S` as a sum over actual distinct smooth integers and actual LCMs. Local copy of ErdosProblems.Erdos269.PaperR7.paperSeries235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperSeries235 : ℝ := ∑' x : Smooth235, smoothReciprocal235 x
/-- Jump-constrained quadratic majorant. Local copy of ErdosProblems.Erdos269.carryMajorantQtilde, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryMajorantQtilde (n : ℕ) : ℚ :=
  (1210 * (n : ℚ) ^ 2 + 9130 * n + 18847) / 11979
/-- Number of shell points before the new `p`-power threshold. Local copy of ErdosProblems.Erdos269.dyadicBeforeThresholdCount235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicBeforeThresholdCount235 (p a : ℕ) : ℕ :=
  ((dyadicSmoothShell235 a).filter fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      p ^ Nat.log p (2 ^ (a + 1))).card
/-- The exact radix of the dyadic block after compressing all internal `3`- and `5`-power jumps. Each internal channel contributes its prime once, and the terminal dyadic jump contributes the factor `2`. Local copy of ErdosProblems.Erdos269.dyadicBlockBase235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 *
        (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
        (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)
/-- The source-faithful ordered block digit. Its coefficients are the suffix products from processing the later odd jump first: `10,4` when the `3`-jump precedes the `5`-jump, and `2,12` in the reverse order. Local copy of ErdosProblems.Erdos269.dyadicOrderedBlockDigit235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicOrderedBlockDigit235 (a : ℕ) : ℕ :=
  if 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤ 5 ^ Nat.log 5 (2 ^ (a + 1)) then
    (dyadicSmoothShell235 a).card +
      10 * dyadicBeforeThresholdCount235 3 a +
      4 * dyadicBeforeThresholdCount235 5 a
  else
    (dyadicSmoothShell235 a).card +
      2 * dyadicBeforeThresholdCount235 3 a +
      12 * dyadicBeforeThresholdCount235 5 a
/-- Canonical positive representative of an integer modulo `C`: a zero residue is represented by `C`, and every nonzero residue by its nonnegative Euclidean remainder. The definition is total at `C = 0`, but all theorems using its positive-representative meaning assume `0 < C`. Local copy of ErdosProblems.Erdos269.leastPositiveResidue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ :=
  if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))
end PalomarCorpus.E269.PaperStatementsC
