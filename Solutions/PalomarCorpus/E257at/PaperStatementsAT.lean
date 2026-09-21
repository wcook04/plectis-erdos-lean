/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.CertificateKernel
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.HalfCarryReachability
import Erdos249257.HalfCylinderFinalMiddleCellEscape
import Erdos249257.HalfCylinderMiddleCarryLowerBound
import ErdosProblems.Erdos257.PaperCompleteR21.LinearChannelAndMiddleCellExclusion
import ErdosProblems.Erdos257.PaperCompleteR21.TerminalStripExactRowGap
import Solutions.PalomarCorpus.E257at.Statement

open Set
open Filter
open scoped BigOperators
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAT

noncomputable def halfStripBound (n : ℕ) : ℕ :=
  2 * Nat.sqrt n + 4

theorem binaryCoeffTail_supportCoeff_coe_finset_le_card
    (F : Finset ℕ) (N : ℕ) :
    binaryCoeffTail (supportCoeff (↑F : Set ℕ)) N ≤ (F.card : ℝ) := @Erdos249257.binaryCoeffTail_supportCoeff_coe_finset_le_card F N

theorem mobiusCenteredHalfCarry_add_two
    (A : Set ℕ) (N : ℕ) :
    mobiusCenteredHalfCarry A (N + 2) =
      4 * mobiusCenteredHalfCarry A N - pairedCenteredForcing A N := @Erdos249257.mobiusCenteredHalfCarry_add_two A N

theorem mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half
    (A : Set ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry A N := @Erdos249257.mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half A hone hseries N

theorem paper_exact_row_integerHalfCarry_eq_one
    {D : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d)
    (hexact : localPrefixQuotient D M = 2 ^ (M - 1) - 1) :
    integerHalfCarry (↑D : Set ℕ) (M - 1) = 1 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_integerHalfCarry_eq_one D M hM hD hexact

theorem paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient
    {D : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d) :
    integerHalfCarry (↑D : Set ℕ) (M - 1) =
      (2 : ℤ) ^ (M - 1) - (localPrefixQuotient D M : ℤ) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient D M hM hD

theorem paper_mobiusCenteredHalfCarry_add_two (A : Set ℕ) (N : ℕ) :
    mobiusCenteredHalfCarry A (N + 2) =
      4 * mobiusCenteredHalfCarry A N - pairedCenteredForcing A N := @ErdosProblems.Erdos257.PaperCompleteR21.paper_mobiusCenteredHalfCarry_add_two A N

theorem paper_terminal_strip_witness_six :
    (∀ d ∈ ({2, 3} : Finset ℕ), 2 ≤ d ∧ d ≤ 6) ∧
      localPrefixQuotient ({2, 3} : Finset ℕ) 6 = 30 ∧
      integerHalfCarry (↑({2, 3} : Finset ℕ) : Set ℕ) (6 - 1) = 2 ∧ := @ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_witness_six

end PalomarCorpus.E257.PaperStatementsAT
