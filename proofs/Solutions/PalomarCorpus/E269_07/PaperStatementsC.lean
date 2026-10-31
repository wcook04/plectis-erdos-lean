/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.ActualSharpTailMajorantR10
import ErdosProblems.Erdos269.BoundedRadixTailEscape
import ErdosProblems.Erdos269.DyadicBlockMassIdentity
import ErdosProblems.Erdos269.DyadicBlockThresholdPartition
import ErdosProblems.Erdos269.DyadicOrderedTailRecurrence
import ErdosProblems.Erdos269.DyadicShellSummability
import ErdosProblems.Erdos269.IntegralBranchExtinction
import ErdosProblems.Erdos269.JumpConstraintMajorant
import ErdosProblems.Erdos269.LongWindowCapR11
import ErdosProblems.Erdos269.PaperCompleteR20.BoundedLatticeCollision
import ErdosProblems.Erdos269.PaperCompleteR20.DyadicAlphabetWhole
import ErdosProblems.Erdos269.PaperCompleteR20.EightScaleRigidity
import ErdosProblems.Erdos269.PaperR7ActualOrbit
import ErdosProblems.Erdos269.PaperR7BasicAssembly
import ErdosProblems.Erdos269.PaperR7RationalBridge
import ErdosProblems.Erdos269.PaperR7SeriesIdentification
import ErdosProblems.Erdos269.PaperR7WindowResults
import ErdosProblems.Erdos269.PaperR8RankMajorant
import ErdosProblems.Erdos269.ResidueEscape
import ErdosProblems.Erdos269.RestrictedFloorSum
import ErdosProblems.Erdos269.ThreePrimeRunningLcm
import Solutions.PalomarCorpus.E269_07.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E269.PaperStatementsC
export PalomarCorpus.E269_07.Shared (Exponent235 Smooth235 dyadicSmoothShell235 exponentValue235 paperSeries235 smooth3Val smoothPrefixExponents smoothPrefixLcm smoothReciprocal235 strictSmoothExponents strictSmoothShell threePrimeHeight)

noncomputable def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)

noncomputable def FarFromIntegers (x δ : ℝ) : Prop :=
  ∀ z : ℤ, δ ≤ |x - (z : ℝ)|

noncomputable def literalForcing235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) /
      (2 * (threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ))

noncomputable def carryMajorantQ (n : ℕ) : ℚ :=
  ((n : ℚ) ^ 2 + 8 * n + 18) / 9

noncomputable def paperJumpIndex (a : ℕ) : ℕ := a + Nat.log 3 (2 ^ a) + Nat.log 5 (2 ^ a)

noncomputable def longPaperCap (B a : ℕ) : ℕ :=
  ⌊(B : ℚ) * carryMajorantQ (paperJumpIndex a)⌋₊

noncomputable def paperReducedCarry (B a : ℕ) : ℤ :=
  ⌊(B : ℝ) * trueNormalizedState a⌋

noncomputable def carryMajorantQtilde (n : ℕ) : ℚ :=
  (1210 * (n : ℚ) ^ 2 + 9130 * n + 18847) / 11979

noncomputable def dyadicBeforeThresholdCount235 (p a : ℕ) : ℕ :=
  ((dyadicSmoothShell235 a).filter fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      p ^ Nat.log p (2 ^ (a + 1))).card

noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 *
        (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
        (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)

noncomputable def dyadicOrderedBlockDigit235 (a : ℕ) : ℕ :=
  if 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤ 5 ^ Nat.log 5 (2 ^ (a + 1)) then
    (dyadicSmoothShell235 a).card +
      10 * dyadicBeforeThresholdCount235 3 a +
      4 * dyadicBeforeThresholdCount235 5 a
  else
    (dyadicSmoothShell235 a).card +
      2 * dyadicBeforeThresholdCount235 3 a +
      12 * dyadicBeforeThresholdCount235 5 a

noncomputable def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ :=
  if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))

theorem dyadic_alphabet_whole :
    (∀ a : ℕ,
      (∃ m : ℕ, 0 < m ∧ literalForcing235 a = (m : ℚ)) ∧
      (dyadicBlockBase235 a = 2 ∨ dyadicBlockBase235 a = 6 ∨
        dyadicBlockBase235 a = 10 ∨ dyadicBlockBase235 a = 30)) ∧
    literalForcing235 4 = 65 ∧ dyadicBlockBase235 4 = 30 ∧
    (∃ a : ℕ, dyadicBlockBase235 a < dyadicOrderedBlockDigit235 a) := @ErdosProblems.Erdos269.PaperCompleteR20.dyadic_alphabet_whole

theorem long_all_scale_lattice_exact :
    (∀ u b : ℕ, u ≤ b → ∃ z : ℕ,
      (threePrimeHeight 2 3 5 (2 ^ b) : ℝ) / 2 *
        (∑ i ∈ Finset.range (b - u), dyadicShellMassR235 (u + i)) = (z : ℝ)) ∧
    (∀ (N : ℤ) (D : ℕ), 0 < D → paperSeries235 = (N : ℝ) / (D : ℝ) →
      (∀ a : ℕ, 1 ≤ a → ∃ z : ℤ,
        (D : ℝ) * trueNormalizedState a = (z : ℝ)) ∧
      ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ D + 1 ∧ ∃ z : ℤ,
        trueNormalizedState i - trueNormalizedState j = (z : ℝ)) := @ErdosProblems.Erdos269.PaperCompleteR20.long_all_scale_lattice_exact

theorem paper_pinning_and_eight_scale_rigidity :
    (∀ a : ℕ, trueNormalizedState a =
      ((dyadicOrderedBlockDigit235 a : ℝ) + trueNormalizedState (a + 1)) /
        (dyadicBlockBase235 a : ℝ) ∧ 0 < trueNormalizedState a) ∧
    (∀ a : ℕ, ∀ z : ℤ, trueNormalizedState a = (z : ℝ) →
      ∀ n, a ≤ n → ∃ w : ℤ, trueNormalizedState n = (w : ℝ)) ∧
    (∀ (width : ℕ → ℝ) (A : ℕ) (y : ℕ → ℝ),
      (∀ n, 0 < width n) →
      (∀ n, A ≤ n → y (n + 1) =
        (dyadicBlockBase235 n : ℝ) * y n - (dyadicOrderedBlockDigit235 n : ℝ)) →
      (∀ n, A ≤ n →
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < y n ∧
        y n ≤ (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) →
      (∀ n, A ≤ n →
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < trueNormalizedState n ∧
        trueNormalizedState n ≤
          (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) →
      (∀ ε > 0, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → width (A + k) / 8 ^ k < ε) →
      y A = trueNormalizedState A) := @ErdosProblems.Erdos269.PaperCompleteR20.paper_pinning_and_eight_scale_rigidity

theorem actual_sharp_tail_bound (a : ℕ) :
    0 < trueNormalizedState a ∧
    trueNormalizedState a ≤ (carryMajorantQtilde (paperJumpIndex a) : ℝ) ∧
    (carryMajorantQtilde (paperJumpIndex a) : ℝ) <
      (carryMajorantQ (paperJumpIndex a) : ℝ) := @ErdosProblems.Erdos269.PaperR10.actual_sharp_tail_bound a

theorem longPaperCap_le_three_squareR11 (B a : ℕ) :
    longPaperCap B a ≤ 3 * B * (a + 1) ^ 2 := @ErdosProblems.Erdos269.PaperR11.longPaperCap_le_three_squareR11 B a

theorem long_fixed_split_bridgeR11 {N : ℤ} {D u v w B : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    ∀ a, u + 1 + 2 * v + 3 * w ≤ a →
      (paperReducedCarry B a : ℝ) = (B : ℝ) * trueNormalizedState a ∧
      1 ≤ paperReducedCarry B a ∧
      paperReducedCarry B (a + 1) =
        (dyadicBlockBase235 a : ℤ) * paperReducedCarry B a -
          (B : ℤ) * (dyadicOrderedBlockDigit235 a : ℤ) ∧
      paperReducedCarry B a ≤ (longPaperCap B a : ℤ) := @ErdosProblems.Erdos269.PaperR11.long_fixed_split_bridgeR11 N D u v w B hB hD hval

theorem allReducedTailsNonintegral_iff :
    AllReducedTailsNonintegral ↔ Irrational paperSeries235 := @ErdosProblems.Erdos269.PaperR7.allReducedTailsNonintegral_iff

theorem long_actual_orbit :
    Summable dyadicShellMassR235 ∧
    paperSeries235 = (∑' a : ℕ, dyadicShellMassR235 a) ∧
    (∀ a : ℕ,
      0 < dyadicOrderedBlockDigit235 a ∧
      (dyadicOrderedBlockDigit235 a : ℝ) =
        (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) / 2 * dyadicShellMassR235 a ∧
      trueNormalizedState (a + 1) =
        (dyadicBlockBase235 a : ℝ) * trueNormalizedState a -
          (dyadicOrderedBlockDigit235 a : ℝ) ∧
      trueNormalizedState a =
        ∑' n : ℕ, (dyadicOrderedBlockDigit235 (a + n) : ℝ) /
          ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (a + j) : ℝ)) := @ErdosProblems.Erdos269.PaperR7.long_actual_orbit

theorem paper_finite_endpoint_obstruction {W K : ℕ} {d B F : ℤ}
    (hW : 0 < W) (hd : 0 < d) (hbound : d ≤ (K : ℤ))
    (hmod : Int.ModEq (W : ℤ) d (-B * F)) :
    leastPositiveResidue W (-B * F) ≤ K := @ErdosProblems.Erdos269.PaperR7.paper_finite_endpoint_obstruction W K d B F hW hd hbound hmod

theorem scaled_integer_or_cofinal_separation (B : ℤ) :
    (∃ a : ℕ, ∀ n, a ≤ n →
      ∃ z : ℤ, (B : ℝ) * trueNormalizedState n = (z : ℝ)) ∨
    (∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
      FarFromIntegers ((B : ℝ) * trueNormalizedState a) ((1 : ℝ) / 31)) := @ErdosProblems.Erdos269.PaperR7.scaled_integer_or_cofinal_separation B

theorem short_actual_orbit :
    Summable smoothReciprocal235 ∧
    (∀ a : ℕ, Summable (fun n : ℕ => dyadicShellMassR235 (a + n))) ∧
    (∀ a : ℕ,
      trueNormalizedState (a + 1) =
        (dyadicBlockBase235 a : ℝ) * trueNormalizedState a -
          (dyadicOrderedBlockDigit235 a : ℝ)) ∧
    (∀ a : ℕ, 0 < trueNormalizedState a ∧
      trueNormalizedState a ≤ (8640 / 343 : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 ∧
      (8640 / 343 : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 <
        90 * ((a + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ B : ℤ,
      (∃ a : ℕ, ∀ n, a ≤ n → ∃ z : ℤ,
        (B : ℝ) * trueNormalizedState n = (z : ℝ)) ∨
      (∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
        FarFromIntegers ((B : ℝ) * trueNormalizedState a) ((1 : ℝ) / 31))) := @ErdosProblems.Erdos269.PaperR7.short_actual_orbit

theorem short_fixed_split_bridge {N : ℤ} {D u v w B : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    ∀ a : ℕ, u + 1 + 2 * v + 3 * w ≤ a →
      (paperReducedCarry B a : ℝ) = (B : ℝ) * trueNormalizedState a ∧
      0 < paperReducedCarry B a ∧
      paperReducedCarry B (a + 1) =
        (dyadicBlockBase235 a : ℤ) * paperReducedCarry B a -
          (B : ℤ) * (dyadicOrderedBlockDigit235 a : ℤ) ∧
      paperReducedCarry B a ≤ ((90 * B * (a + 1) ^ 2 : ℕ) : ℤ) := @ErdosProblems.Erdos269.PaperR7.short_fixed_split_bridge N D u v w B hB hD hval

theorem actual_tail_rank_bound (a : ℕ) :
    0 < trueNormalizedState a ∧
      trueNormalizedState a ≤ (carryMajorantQ (paperJumpIndex a) : ℝ) := @ErdosProblems.Erdos269.PaperR8.actual_tail_rank_bound a

end PalomarCorpus.E269.PaperStatementsC
