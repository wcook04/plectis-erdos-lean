/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.GreedyAchievementSet
import Erdos249257.MobiusSignSupportNoGo
import ErdosProblems.Erdos257.PaperCompleteR21.MobiusSignAndFiniteCertificates
import Solutions.PalomarCorpus.E257_36.Statement

open ArithmeticFunction
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAQ
export PalomarCorpus.E257_36.Shared (mersenneWeight)

theorem half_lt_tsum_negativeMobius :
    (1 : ℝ) / 2 < ∑' d : ℕ+, negativeMobiusTerm d := @Erdos249257.MobiusSignSupportNoGo.half_lt_tsum_negativeMobius

theorem tsum_negativeMobius_eq_half_add_positiveMobiusTail :
    (∑' d : ℕ+, negativeMobiusTerm d) =
      1 / 2 + ∑' d : ℕ+, positiveMobiusTailTerm d := @Erdos249257.MobiusSignSupportNoGo.tsum_negativeMobius_eq_half_add_positiveMobiusTail

theorem paper_first_positiveMobius_tail_term :
    (∀ d : ℕ+, (d : ℕ) < 6 → positiveMobiusTailTerm d = 0) ∧
      moebius 6 = 1 ∧
      positiveMobiusTailTerm (⟨6, by norm_num⟩ : ℕ+) = (1 : ℝ) / 63 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_first_positiveMobius_tail_term

theorem paper_mobius_support_overshoots_half :
    (∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1)) = 1 / 2 ∧
      (∑' d : ℕ+, negativeMobiusTerm d)
        = 1 / 2 + ∑' d : ℕ+, positiveMobiusTailTerm d ∧
      (1 : ℝ) / 2 + 1 / 63 ≤ ∑' d : ℕ+, negativeMobiusTerm d ∧
      (1 : ℝ) / 2 < ∑' d : ℕ+, negativeMobiusTerm d := @ErdosProblems.Erdos257.PaperCompleteR21.paper_mobius_support_overshoots_half

end PalomarCorpus.E257.PaperStatementsAQ
