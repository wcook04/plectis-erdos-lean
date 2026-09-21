/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #269

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos269.ActualSharpTailMajorantR10`,
`ErdosProblems.Erdos269.BoundedRadixTailEscape`,
`ErdosProblems.Erdos269.DyadicBlockMassIdentity`,
`ErdosProblems.Erdos269.DyadicBlockThresholdPartition`,
`ErdosProblems.Erdos269.DyadicOrderedTailRecurrence`,
`ErdosProblems.Erdos269.DyadicShellSummability`,
`ErdosProblems.Erdos269.IntegralBranchExtinction`,
`ErdosProblems.Erdos269.JumpConstraintMajorant`, `ErdosProblems.Erdos269.LongWindowCapR11`,
`ErdosProblems.Erdos269.PaperCompleteR20.BoundedLatticeCollision`,
`ErdosProblems.Erdos269.PaperCompleteR20.DyadicAlphabetWhole`,
`ErdosProblems.Erdos269.PaperCompleteR20.EightScaleRigidity`,
`ErdosProblems.Erdos269.PaperR7ActualOrbit`, `ErdosProblems.Erdos269.PaperR7BasicAssembly`,
`ErdosProblems.Erdos269.PaperR7RationalBridge`,
`ErdosProblems.Erdos269.PaperR7SeriesIdentification`,
`ErdosProblems.Erdos269.PaperR7WindowResults`, `ErdosProblems.Erdos269.PaperR8RankMajorant`,
`ErdosProblems.Erdos269.ResidueEscape`, `ErdosProblems.Erdos269.RestrictedFloorSum`,
`ErdosProblems.Erdos269.ThreePrimeRunningLcm`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification269PaperStatementsC

noncomputable def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)

noncomputable def FarFromIntegers (x δ : ℝ) : Prop :=
  ∀ z : ℤ, δ ≤ |x - (z : ℝ)|

noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

noncomputable def dyadicNormalizedTailStateR235 (tail : ℕ → ℝ) (a : ℕ) : ℝ :=
  ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a

noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k

noncomputable def strictSmoothExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range x).product ((Finset.range x).product (Finset.range x))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 < x

noncomputable def strictSmoothShell (p q r x y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothExponents p q r y \ strictSmoothExponents p q r x

noncomputable def dyadicSmoothShell235 (a : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothShell 2 3 5 (2 ^ a) (2 ^ (a + 1))

noncomputable def dyadicShellMassQ235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    ((threePrimeHeight 2 3 5
      (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹)

noncomputable def dyadicShellMassR235 (a : ℕ) : ℝ :=
  dyadicShellMassQ235 a

noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ :=
  ∑' n : ℕ, dyadicShellMassR235 (a + n)

noncomputable def trueNormalizedState (a : ℕ) : ℝ :=
  dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a

noncomputable def AllReducedTailsNonintegral : Prop :=
  ∀ B : ℕ, 0 < B → Nat.Coprime B 30 → ∀ a : ℕ, 1 ≤ a →
    ∀ z : ℤ, (B : ℝ) * trueNormalizedState a ≠ (z : ℝ)

noncomputable abbrev Exponent235 := ℕ × ℕ × ℕ

noncomputable def exponentValue235 (e : Exponent235) : ℕ :=
  smooth3Val 2 3 5 e.1 e.2.1 e.2.2

noncomputable def Smooth235 := {x : ℕ // x ∈ Set.range exponentValue235}

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

noncomputable def smoothPrefixExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (Nat.log p x + 1)).product
      ((Finset.range (Nat.log q x + 1)).product
        (Finset.range (Nat.log r x + 1)))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 ≤ x

noncomputable def smoothPrefixLcm (p q r x : ℕ) : ℕ :=
  (smoothPrefixExponents p q r x).lcm
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2

noncomputable def smoothReciprocal235 (x : Smooth235) : ℝ :=
  (smoothPrefixLcm 2 3 5 x.val : ℝ)⁻¹

noncomputable def paperSeries235 : ℝ := ∑' x : Smooth235, smoothReciprocal235 x

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

/-- States res:dyadic-alphabet from the short record for Erdős problem #269. Transported from
ErdosProblems.Erdos269.PaperCompleteR20.dyadic_alphabet_whole in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadic_alphabet_whole :
    (∀ a : ℕ,
      (∃ m : ℕ, 0 < m ∧ literalForcing235 a = (m : ℚ)) ∧
      (dyadicBlockBase235 a = 2 ∨ dyadicBlockBase235 a = 6 ∨
        dyadicBlockBase235 a = 10 ∨ dyadicBlockBase235 a = 30)) ∧
    literalForcing235 4 = 65 ∧ dyadicBlockBase235 4 = 30 ∧
    (∃ a : ℕ, dyadicBlockBase235 a < dyadicOrderedBlockDigit235 a) := by
  sorry

/-- States long269:res:all-scale-lattice from the long record for Erdős problem #269.
Transported from ErdosProblems.Erdos269.PaperCompleteR20.long_all_scale_lattice_exact in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
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

/-- States long269:res:pinning from the long record for Erdős problem #269. Transported from
ErdosProblems.Erdos269.PaperCompleteR20.paper_pinning_and_eight_scale_rigidity in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
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
      y A = trueNormalizedState A) := by
  sorry

/-- States long269:res:jump-constrained-bound from the long record for Erdős problem #269.
Transported from ErdosProblems.Erdos269.PaperR10.actual_sharp_tail_bound in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem actual_sharp_tail_bound (a : ℕ) :
    0 < trueNormalizedState a ∧
    trueNormalizedState a ≤ (carryMajorantQtilde (paperJumpIndex a) : ℝ) ∧
    (carryMajorantQtilde (paperJumpIndex a) : ℝ) <
      (carryMajorantQ (paperJumpIndex a) : ℝ) := by
  sorry

/-- States long269:res:actual-cancellation, long269:res:actual-carry-bound,
long269:res:denominator-reduction from the long record for Erdős problem #269. Transported
from ErdosProblems.Erdos269.PaperR11.longPaperCap_le_three_squareR11 in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem longPaperCap_le_three_squareR11 (B a : ℕ) :
    longPaperCap B a ≤ 3 * B * (a + 1) ^ 2 := by
  sorry

/-- States long269:res:actual-cancellation, long269:res:actual-carry-bound,
long269:res:denominator-reduction from the long record for Erdős problem #269. Transported
from ErdosProblems.Erdos269.PaperR11.long_fixed_split_bridgeR11 in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
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

/-- States long269:res:tails-equivalence from the long record for Erdős problem #269.
Transported from ErdosProblems.Erdos269.PaperR7.allReducedTailsNonintegral_iff in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem allReducedTailsNonintegral_iff :
    AllReducedTailsNonintegral ↔ Irrational paperSeries235 := by
  sorry

/-- States long269:eq:shell-digit-identity, long269:res:actual-orbit from the long record for
Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.long_actual_orbit in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
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
          ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (a + j) : ℝ)) := by
  sorry

/-- States res:consumer from the short record for Erdős problem #269. Transported from
ErdosProblems.Erdos269.PaperR7.paper_finite_endpoint_obstruction in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_finite_endpoint_obstruction {W K : ℕ} {d B F : ℤ}
    (hW : 0 < W) (hd : 0 < d) (hbound : d ≤ (K : ℤ))
    (hmod : Int.ModEq (W : ℤ) d (-B * F)) :
    leastPositiveResidue W (-B * F) ≤ K := by
  sorry

/-- States long269:res:actual-dichotomy from the long record for Erdős problem #269. Transported
from ErdosProblems.Erdos269.PaperR7.scaled_integer_or_cofinal_separation in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem scaled_integer_or_cofinal_separation (B : ℤ) :
    (∃ a : ℕ, ∀ n, a ≤ n →
      ∃ z : ℤ, (B : ℝ) * trueNormalizedState n = (z : ℝ)) ∨
    (∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
      FarFromIntegers ((B : ℝ) * trueNormalizedState a) ((1 : ℝ) / 31)) := by
  sorry

/-- States res:actual-orbit from the short record for Erdős problem #269. Transported from
ErdosProblems.Erdos269.PaperR7.short_actual_orbit in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
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
        FarFromIntegers ((B : ℝ) * trueNormalizedState a) ((1 : ℝ) / 31))) := by
  sorry

/-- States res:denominator-reduction from the short record for Erdős problem #269. Transported
from ErdosProblems.Erdos269.PaperR7.short_fixed_split_bridge in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem short_fixed_split_bridge {N : ℤ} {D u v w B : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    ∀ a : ℕ, u + 1 + 2 * v + 3 * w ≤ a →
      (paperReducedCarry B a : ℝ) = (B : ℝ) * trueNormalizedState a ∧
      0 < paperReducedCarry B a ∧
      paperReducedCarry B (a + 1) =
        (dyadicBlockBase235 a : ℤ) * paperReducedCarry B a -
          (B : ℤ) * (dyadicOrderedBlockDigit235 a : ℤ) ∧
      paperReducedCarry B a ≤ ((90 * B * (a + 1) ^ 2 : ℕ) : ℤ) := by
  sorry

/-- States long269:res:actual-tail-bound from the long record for Erdős problem #269.
Transported from ErdosProblems.Erdos269.PaperR8.actual_tail_rank_bound in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem actual_tail_rank_bound (a : ℕ) :
    0 < trueNormalizedState a ∧
      trueNormalizedState a ≤ (carryMajorantQ (paperJumpIndex a) : ℝ) := by
  sorry

end Erdos249257.ExternalVerification269PaperStatementsC
