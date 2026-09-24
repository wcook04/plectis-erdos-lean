/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CertificateKernel
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.HalfCarryReachability
import ErdosProblems.Erdos257.PaperCompleteR20.CarryCollapseCorrespondence
import ErdosProblems.Erdos257.PaperCompleteR21.LinearChannelAndMiddleCellExclusion
import ErdosProblems.Erdos257.PaperCompleteR21.SquareDepthAndHalfMembershipEquivalences
import ErdosProblems.Erdos257.PaperCompleteR21.TerminalStripExactRowGap
import Solutions.PalomarCorpus.E257_45.Statement

open Filter
open Set
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsL
export PalomarCorpus.E257_45.Shared (supportCoeff)

noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1

theorem square_depth_witness (A : Set ℕ) (hone : 1 ∉ A)
    (hhalf : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (k : ℕ) (hk : 1 ≤ k) :
    (integerHalfCarry A (k^2-1) : ℝ) = binaryCoeffTail (supportCoeff A) (k^2) ∧
    binaryCoeffTail (supportCoeff A) (k^2) ≤ 2*(k : ℝ)+4 ∧
    (halfStripBound (k^2) : ℝ) = 2*(k : ℝ)+4 := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR20.square_depth_witness A hone hhalf k hk

theorem paper_cofiniteRightTail_ne_zero_centeredEndpoint
    (A : Set ℕ) (D : ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (hcofinite : Set.Ioi D ⊆ A) :
    mobiusCenteredHalfCarry A (2 * D + 1) ≠ 0 := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_cofiniteRightTail_ne_zero_centeredEndpoint A D hone hseries hcofinite

theorem paper_relaxed_constant_six_every_depth
    (A : Set ℕ) (hone : 1 ∉ A) (hvalue : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (M : ℕ) (hM : 1 ≤ M) :
    |(integerHalfCarry A (M - 1) : ℝ)| ≤ 2 * (Nat.sqrt M : ℝ) + 6 := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_relaxed_constant_six_every_depth A hone hvalue M hM

theorem paper_square_depth_terminal_bound (A : Set ℕ) (hone : 1 ∉ A)
    (hhalf : erdosSupportSeries 2 A = (1 : ℝ) / 2) (k : ℕ) (hk : 1 ≤ k) :
    (integerHalfCarry A (k ^ 2 - 1) : ℝ) = binaryCoeffTail (supportCoeff A) (k ^ 2) ∧
      binaryCoeffTail (supportCoeff A) (k ^ 2) ≤ 2 * (k : ℝ) + 4 ∧
      (halfStripBound (k ^ 2) : ℝ) = 2 * (k : ℝ) + 4 := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_square_depth_terminal_bound A hone hhalf k hk

theorem paper_terminal_strip_forces_half_membership
    (hcofinal : ∀ N : ℕ, ∃ M : ℕ, max N 1 ≤ M ∧ ∃ D : Finset ℕ,
      (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧
      |(integerHalfCarry (↑D : Set ℕ) (M - 1) : ℝ)| ≤ (halfStripBound M : ℝ)) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_forces_half_membership hcofinal

end PalomarCorpus.E257.PaperStatementsL
