/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E269a

Every non-theorem declaration of `PalomarCorpus/E269a/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E269.PaperStatementsA
open scoped BigOperators
/-- A positive `p`-power lies strictly inside the dyadic block `(2^a, 2^(a+1))`. Endpoints are excluded because the dyadic jump itself is the distinguished terminal factor of the compressed block. Local copy of ErdosProblems.Erdos269.DyadicInternalPower, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.cubicShiftCoefficient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cubicShiftCoefficient : ℕ → ℤ
  | 0 => 1
  | 1 => -3
  | 2 => 3
  | _ => -1
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.entryStrip, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def entryStrip {α : Type*} [DecidableEq α] (T : ℕ → Finset α) : ℕ → Finset α
  | 0 => T 0
  | n + 1 => T (n + 1) \ T n
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.triangleLogPoint, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def triangleLogPoint (v : ℕ × ℕ) : ℝ :=
  (v.1 : ℝ) * Real.logb 2 3 + (v.2 : ℝ) * Real.logb 2 5
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.triangleTheta, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def triangleTheta (p : ℕ) : ℝ := 1 / Real.logb 2 p
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.literalLogWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def literalLogWeight (a : ℕ) (v : ℕ × ℕ) : ℕ :=
  3 ^ (⌊((a : ℝ) + 1) * triangleTheta 3⌋₊ -
    ⌊((a : ℝ) + Int.fract (triangleLogPoint v)) * triangleTheta 3⌋₊) *
  5 ^ (⌊((a : ℝ) + 1) * triangleTheta 5⌋₊ -
    ⌊((a : ℝ) + Int.fract (triangleLogPoint v)) * triangleTheta 5⌋₊)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.triangleOddPart, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def triangleOddPart (v : ℕ × ℕ) : ℕ := 3 ^ v.1 * 5 ^ v.2
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.literalTriangle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def literalTriangle (a : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (a + 1)).product (Finset.range (a + 1))).filter
    (fun v => triangleOddPart v < 2 ^ (a + 1))
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.phaseFloor, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def phaseFloor (p a : ℕ) (t : ℝ) : ℤ :=
  ⌊((a : ℝ) + t) * triangleTheta p⌋
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.phaseCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def phaseCarry (p a : ℕ) (t : ℝ) (u : ℕ) : ℤ :=
  phaseFloor p (a + u) t - phaseFloor p a t - phaseFloor p u 0
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.phaseChi, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def phaseChi (a : ℕ) (t : ℝ) (u : ℕ) : ℝ :=
  (3 : ℝ) ^ (-phaseCarry 3 a t u) * (5 : ℝ) ^ (-phaseCarry 5 a t u)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.phaseOmega, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def phaseOmega (a : ℕ) (t : ℝ) : ℝ :=
  (3 : ℝ) ^ (phaseFloor 3 a 1 - phaseFloor 3 a t) *
    (5 : ℝ) ^ (phaseFloor 5 a 1 - phaseFloor 5 a t)
/-- The product of the largest pure `p`-, `q`-, and `r`-powers not exceeding `x`. For a `{p,q,r}`-smooth `x`, this is the running LCM of the smooth prefix. Local copy of ErdosProblems.Erdos269.threePrimeHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x
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
/-- Number of shell points before the new `p`-power threshold. Local copy of ErdosProblems.Erdos269.dyadicBeforeThresholdCount235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicBeforeThresholdCount235 (p a : ℕ) : ℕ :=
  ((dyadicSmoothShell235 a).filter fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      p ^ Nat.log p (2 ^ (a + 1))).card
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
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.recodedCoefficient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def recodedCoefficient (q a : ℕ) : ℝ :=
  (dyadicOrderedBlockDigit235 a : ℝ) * (q : ℝ) ^ (a + 1) /
    (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.shiftHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev shiftHeight (n : ℕ) : ℕ := threePrimeHeight 2 3 5 (2 ^ n)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.shiftGamma, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftGamma (a t : ℕ) : ℝ :=
  (shiftHeight t : ℝ) * (shiftHeight (a + 1) : ℝ) / (shiftHeight (a + t + 1) : ℝ)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.shiftedPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftedPrefix (t : ℕ) : ℝ :=
  (shiftHeight t : ℝ) * ∑ k ∈ Finset.range t,
    (dyadicOrderedBlockDigit235 k : ℝ) / (shiftHeight (k + 1) : ℝ)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.shiftedCorrection, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftedCorrection (c : ℕ → ℤ) (σ r : ℕ) : ℝ :=
  15 * ∑ j ∈ Finset.range (σ + 1), (c j : ℝ) * shiftedPrefix (j * r)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.shiftedLeading, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftedLeading (c : ℕ → ℤ) (σ r : ℕ) : ℤ :=
  15 * ∑ j ∈ Finset.range (σ + 1), c j * (shiftHeight (j * r) : ℤ)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.shiftedNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftedNumerator (c : ℕ → ℤ) (σ r a : ℕ) : ℝ :=
  15 * ∑ j ∈ Finset.range (σ + 1), (c j : ℝ) * shiftGamma a (j * r) *
    (dyadicOrderedBlockDigit235 (a + j * r) : ℝ)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.shiftedQuadraticConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftedQuadraticConstant (c : ℕ → ℤ) (σ : ℕ) : ℝ :=
  225 * ∑ j ∈ Finset.range (σ + 1), |(c j : ℝ)| * (max 1 j : ℝ) ^ 2
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.triangleQuadraticDenominator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def triangleQuadraticDenominator : ℝ :=
  (2 * Real.logb 2 3 + 1) * (2 * Real.logb 2 5 + 1)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.triangleRectangleSide, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def triangleRectangleSide (a p : ℕ) : ℕ :=
  ⌊(a : ℝ) / (2 * Real.logb 2 p)⌋₊ + 1
/-- The integer-power condition defining the paper's first clearing index. Local copy of ErdosProblems.Erdos269.PaperR13.ClearingCondition, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ClearingCondition (u v w a : ℕ) : Prop :=
  1 ≤ a ∧ 2 ^ (u + 1) ≤ 2 ^ a ∧ 3 ^ v ≤ 2 ^ a ∧ 5 ^ w ≤ 2 ^ a
/-- Local copy of ErdosProblems.Erdos269.PaperR7.Exponent235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev Exponent235 := ℕ × ℕ × ℕ
/-- Local copy of ErdosProblems.Erdos269.PaperR7.exponentValue235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exponentValue235 (e : Exponent235) : ℕ :=
  smooth3Val 2 3 5 e.1 e.2.1 e.2.2
/-- Positive smooth integers, counted once as numbers rather than as exponents. Local copy of ErdosProblems.Erdos269.PaperR7.Smooth235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Smooth235 := {x : ℕ // x ∈ Set.range exponentValue235}
/-- The literal reduction: invert the natural running-LCM height modulo B. Local copy of ErdosProblems.Erdos269.PaperR7.kernelMod235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def kernelMod235 (B i j k : ℕ) : ZMod B :=
  (threePrimeHeight 2 3 5 (smooth3Val 2 3 5 i j k) : ZMod B)⁻¹
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
/-- The exact radix of the dyadic block after compressing all internal `3`- and `5`-power jumps. Each internal channel contributes its prime once, and the terminal dyadic jump contributes the factor `2`. Local copy of ErdosProblems.Erdos269.dyadicBlockBase235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 *
        (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
        (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)
/-- The first `count` positive powers of one prime base. Exponent zero is omitted because it is the common initial value `1` in every channel. Local copy of ErdosProblems.Erdos269.positivePrimePowers, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positivePrimePowers (p count : ℕ) : Finset ℕ :=
  (Finset.range count).image fun e => p ^ (e + 1)
/-- The finite union of the first `count` positive powers in each of the three prime channels. Local copy of ErdosProblems.Erdos269.threePrimePositiveJumpSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def threePrimePositiveJumpSet (p q r count : ℕ) : Finset ℕ :=
  (positivePrimePowers p count ∪ positivePrimePowers q count) ∪
    positivePrimePowers r count
/-- The finite jump set including the unique common origin `1`. Local copy of ErdosProblems.Erdos269.threePrimeJumpSetWithOrigin, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def threePrimeJumpSetWithOrigin (p q r count : ℕ) : Finset ℕ :=
  insert 1 (threePrimePositiveJumpSet p q r count)
/-- The exact rational lattice kernel attached to the running-LCM height. Local copy of ErdosProblems.Erdos269.threePrimeKernelQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹
end PalomarCorpus.E269.PaperStatementsA
