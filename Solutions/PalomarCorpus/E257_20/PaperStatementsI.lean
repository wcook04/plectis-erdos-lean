/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CertificateKernel
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.HalfCarryReachability
import Erdos249257.HalfCylinderFinalMiddleCellEscape
import Solutions.PalomarCorpus.E257_20.Statement

open Set
open scoped BigOperators
open Filter
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsI
export PalomarCorpus.E257_20.Shared (supportCoeff)

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

theorem mobiusCenteredHalfCarry_add_two
    (A : Set ℕ) (N : ℕ) :
    mobiusCenteredHalfCarry A (N + 2) =
      4 * mobiusCenteredHalfCarry A N - pairedCenteredForcing A N := by
  set_option smartUnfolding false in
  exact @Erdos249257.mobiusCenteredHalfCarry_add_two A N

theorem mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half
    (A : Set ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry A N := by
  set_option smartUnfolding false in
  exact @Erdos249257.mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half A hone hseries N

end PalomarCorpus.E257.PaperStatementsI
