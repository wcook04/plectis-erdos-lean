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
import ErdosProblems.Erdos257.PaperCompleteR21.LinearChannelAndMiddleCellExclusion
import ErdosProblems.Erdos257.PaperCompleteR21.TerminalStripExactRowGap
import Solutions.PalomarCorpus.E257_42.Statement

open Filter
open Set
open Topology
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsQ
export PalomarCorpus.E257_42.Shared (affineBinaryOrbit integerHalfCarry supportCoeff)

noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)

noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d

theorem paper_exact_row_integerHalfCarry_eq_one
    {D : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d)
    (hexact : localPrefixQuotient D M = 2 ^ (M - 1) - 1) :
    integerHalfCarry (↑D : Set ℕ) (M - 1) = 1 := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_integerHalfCarry_eq_one D M hM hD hexact

theorem paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient
    {D : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d) :
    integerHalfCarry (↑D : Set ℕ) (M - 1) =
      (2 : ℤ) ^ (M - 1) - (localPrefixQuotient D M : ℤ) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient D M hM hD

theorem paper_mobiusCenteredHalfCarry_add_two (A : Set ℕ) (N : ℕ) :
    mobiusCenteredHalfCarry A (N + 2) =
      4 * mobiusCenteredHalfCarry A N - pairedCenteredForcing A N := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_mobiusCenteredHalfCarry_add_two A N

end PalomarCorpus.E257.PaperStatementsQ
