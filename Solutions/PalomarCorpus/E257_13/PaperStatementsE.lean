/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CertificateKernel
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.HalfCarryReachability
import ErdosProblems.Erdos257.PaperCompleteR20.CofinalCarryCollapse
import Solutions.PalomarCorpus.E257_13.Statement

open Filter
open Set
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsE
export PalomarCorpus.E257_13.Shared (affineBinaryOrbit erdosSupportSeries integerHalfCarry mobiusCenteredHalfCarry supportCoeff)

noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

theorem infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound
    (A : Set ℕ) (hzero : 0 ∉ A) (hone : 1 ∉ A)
    (hnonneg : ∀ N : ℕ, 0 ≤ mobiusCenteredHalfCarry A N)
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry A N : ℝ) ≤
        2 * Real.sqrt (N : ℝ) + 4) :
    A.Infinite ∧ erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  set_option smartUnfolding false in
  exact @Erdos249257.HalfCarryReachability.infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound A hzero hone hnonneg hbound

theorem integerHalfCarry_eq_scaled_residual_add_tail
    (A : Set ℕ) (hone : 1 ∉ A) (N : ℕ) :
    (integerHalfCarry A N : ℝ) =
      (2 : ℝ) ^ (N + 1) * ((1 : ℝ) / 2 - erdosSupportSeries 2 A) +
        binaryCoeffTail (supportCoeff A) (N + 1) := by
  set_option smartUnfolding false in
  exact @Erdos249257.HalfCarryReachability.integerHalfCarry_eq_scaled_residual_add_tail A hone N

theorem half_of_cofinal_absolute_carry (A : Set ℕ) (hone : 1 ∉ A)
    (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      |(integerHalfCarry A N : ℝ)| ≤ C*Real.sqrt ((N : ℝ)+1)+D) :
    erdosSupportSeries 2 A = (1 : ℝ)/2 := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR20.half_of_cofinal_absolute_carry A hone C D h

end PalomarCorpus.E257.PaperStatementsE
