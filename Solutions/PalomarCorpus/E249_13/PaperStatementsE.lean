/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.TotientCarryKernelRigidity
import ErdosProblems.Erdos249.PaperCompleteR21.GenericCarryRankCeilingCounterexample
import ErdosProblems.Erdos249.ParityPerturbedRationalControl
import Solutions.PalomarCorpus.E249_13.Statement

open Module
open Filter
open Set
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsE
export PalomarCorpus.E249_13.Shared (IsTemperedBinaryOrbit S TotientCarryIndex binaryCoeffSeries canonicalCarryKernelFamily carryKernelSeq control delta dig digit rem step xi)

theorem fiveQuarter_comparison_rational_with_carryRank_floor :
    (∀ n : ℕ, control n ≤ n)
      ∧ (∀ n : ℕ, n % 2 = 1 →
          control n = Nat.totient n)
      ∧ (∀ n : ℕ,
          |(control n : ℤ) - Nat.totient n| ≤ 2)
      ∧ binaryCoeffSeries control = 5 / 4
      ∧ ¬ Irrational (binaryCoeffSeries control)
      ∧ ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
          IsTemperedBinaryOrbit control v u
            ∧ ∀ e : ℕ, 2 ^ e - 1 ≤
                finrank ℚ
                  (Submodule.span ℚ
                    (Set.range (canonicalCarryKernelFamily u e))) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.fiveQuarter_comparison_rational_with_carryRank_floor

end PalomarCorpus.E249.PaperStatementsE
