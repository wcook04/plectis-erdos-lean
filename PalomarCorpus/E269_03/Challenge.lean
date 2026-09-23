/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #269, record sections 5 to 6: the recurrence for tails between powers of two; bounding the tails and clearing a rational denominator

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #269, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #269 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators

namespace PalomarCorpus.E269_03.Shared
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
end PalomarCorpus.E269_03.Shared

namespace PalomarCorpus.E269.PaperStatementsA
open scoped BigOperators
export PalomarCorpus.E269_03.Shared (dyadicBeforeThresholdCount235 dyadicOrderedBlockDigit235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell)
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
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.triangleQuadraticDenominator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def triangleQuadraticDenominator : ℝ :=
  (2 * Real.logb 2 3 + 1) * (2 * Real.logb 2 5 + 1)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.triangleRectangleSide, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def triangleRectangleSide (a p : ℕ) : ℕ :=
  ⌊(a : ℝ) / (2 * Real.logb 2 p)⌋₊ + 1
/-- States long269:res:literal-triangle from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.literal_triangle_whole in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem literal_triangle_whole :
    (∀ a, dyadicOrderedBlockDigit235 a = ∑ v ∈ literalTriangle a, literalLogWeight a v) ∧
    (∀ a v, v ∈ literalTriangle a →
      literalLogWeight a v = 1 ∨ literalLogWeight a v = 3 ∨
      literalLogWeight a v = 5 ∨ literalLogWeight a v = 15) ∧
    (∀ a, triangleRectangleSide a 3 * triangleRectangleSide a 5 ≤ dyadicOrderedBlockDigit235 a) ∧
    (∀ a : ℕ, (a + 1 : ℝ) ^ 2 / triangleQuadraticDenominator ≤ dyadicOrderedBlockDigit235 a ∧
      (dyadicOrderedBlockDigit235 a : ℝ) ≤ 15 * (a + 1 : ℝ) ^ 2) ∧
    (∀ M : ℝ, ∃ a : ℕ, M < dyadicOrderedBlockDigit235 a) := by
  sorry
end PalomarCorpus.E269.PaperStatementsA

namespace PalomarCorpus.E269.PaperStatementsC
open scoped BigOperators
export PalomarCorpus.E269_03.Shared (dyadicBeforeThresholdCount235 dyadicOrderedBlockDigit235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell)
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
/-- Local copy of ErdosProblems.Erdos269.PaperR7.Exponent235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev Exponent235 := ℕ × ℕ × ℕ
/-- Local copy of ErdosProblems.Erdos269.PaperR7.exponentValue235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exponentValue235 (e : Exponent235) : ℕ :=
  smooth3Val 2 3 5 e.1 e.2.1 e.2.2
/-- Positive smooth integers, counted once as numbers rather than as exponents. Local copy of ErdosProblems.Erdos269.PaperR7.Smooth235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Smooth235 := {x : ℕ // x ∈ Set.range exponentValue235}
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
/-- The exact radix of the dyadic block after compressing all internal `3`- and `5`-power jumps. Each internal channel contributes its prime once, and the terminal dyadic jump contributes the factor `2`. Local copy of ErdosProblems.Erdos269.dyadicBlockBase235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 *
        (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
        (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)
/-- States long269:res:all-scale-lattice from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.long_all_scale_lattice_exact in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem long_all_scale_lattice_exact :
    (∀ u b : ℕ, u ≤ b → ∃ z : ℕ,
      (threePrimeHeight 2 3 5 (2 ^ b) : ℝ) / 2 *
        (∑ i ∈ Finset.range (b - u), dyadicShellMassR235 (u + i)) = (z : ℝ)) ∧
    (∀ (N : ℤ) (D : ℕ), 0 < D → paperSeries235 = (N : ℝ) / (D : ℝ) →
      (∀ a : ℕ, 1 ≤ a → ∃ z : ℤ,
        (D : ℝ) * trueNormalizedState a = (z : ℝ)) ∧
      ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ D + 1 ∧ ∃ z : ℤ,
        trueNormalizedState i - trueNormalizedState j = (z : ℝ)) := by
  sorry
/-- States long269:res:actual-cancellation, long269:res:actual-carry-bound, long269:res:denominator-reduction from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR11.longPaperCap_le_three_squareR11 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem longPaperCap_le_three_squareR11 (B a : ℕ) :
    longPaperCap B a ≤ 3 * B * (a + 1) ^ 2 := by
  sorry
/-- States long269:res:actual-cancellation, long269:res:actual-carry-bound, long269:res:denominator-reduction from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR11.long_fixed_split_bridgeR11 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem long_fixed_split_bridgeR11 {N : ℤ} {D u v w B : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    ∀ a, u + 1 + 2 * v + 3 * w ≤ a →
      (paperReducedCarry B a : ℝ) = (B : ℝ) * trueNormalizedState a ∧
      1 ≤ paperReducedCarry B a ∧
      paperReducedCarry B (a + 1) =
        (dyadicBlockBase235 a : ℤ) * paperReducedCarry B a -
          (B : ℤ) * (dyadicOrderedBlockDigit235 a : ℤ) ∧
      paperReducedCarry B a ≤ (longPaperCap B a : ℤ) := by
  sorry
/-- States long269:res:actual-dichotomy from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.scaled_integer_or_cofinal_separation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem scaled_integer_or_cofinal_separation (B : ℤ) :
    (∃ a : ℕ, ∀ n, a ≤ n →
      ∃ z : ℤ, (B : ℝ) * trueNormalizedState n = (z : ℝ)) ∨
    (∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
      FarFromIntegers ((B : ℝ) * trueNormalizedState a) ((1 : ℝ) / 31)) := by
  sorry
/-- States long269:res:actual-tail-bound from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR8.actual_tail_rank_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem actual_tail_rank_bound (a : ℕ) :
    0 < trueNormalizedState a ∧
      trueNormalizedState a ≤ (carryMajorantQ (paperJumpIndex a) : ℝ) := by
  sorry
end PalomarCorpus.E269.PaperStatementsC
