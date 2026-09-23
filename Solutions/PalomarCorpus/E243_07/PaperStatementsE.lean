/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR21.ClassicalHalfspaceSigns
import Solutions.PalomarCorpus.E243_07.Statement

open Filter
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E243.PaperStatementsE
export PalomarCorpus.E243_07.Shared (shiftedCorrectionTerm)

theorem growthDefect_eq_neg_relativeError_add_shiftedCorrection
    {a aNext D DNext C CNext E ENext : ℝ}
    (hD : DNext = a * D)
    (hC : CNext = a * C - D)
    (hE : E = D - (a - 1) * C)
    (hENext : ENext = DNext - (aNext - 1) * CNext)
    (hne : aNext * C * CNext ≠ 0) :
    a ^ 2 / aNext - 1 =
      -(E / C) + shiftedCorrectionTerm a aNext C CNext E ENext := @ErdosProblems.Erdos243.PaperCompleteR21.growthDefect_eq_neg_relativeError_add_shiftedCorrection a aNext D DNext C CNext E ENext hD hC hE hENext hne

theorem shiftedCorrectionTerm_pos_and_lt_three_div
    {A ANext C CNext E ENext : ℝ}
    (hA : 2 ≤ A) (hANext : A ^ 2 / 2 ≤ ANext)
    (hθ : |E / C| ≤ 1 / 4) (hθNext : |ENext / CNext| ≤ 1 / 4) :
    0 < shiftedCorrectionTerm A ANext C CNext E ENext ∧
      shiftedCorrectionTerm A ANext C CNext E ENext < 3 / A := by
  apply ErdosProblems.Erdos243.PaperCompleteR21.shiftedCorrectionTerm_pos_and_lt_three_div <;> assumption

theorem sylvesterTail_shiftedCorrection
    {a aNext D DNext C CNext E ENext : ℝ}
    (hD : DNext = a * D)
    (hC : CNext = a * C - D)
    (hE : E = D - (a - 1) * C)
    (hENext : ENext = DNext - (aNext - 1) * CNext)
    (ha : 1 < a)
    (hsyl : aNext = a ^ 2 - a + 1)
    (hzero : E = 0) :
    ENext = 0 ∧
      shiftedCorrectionTerm a aNext C CNext E ENext = (a - 1) / aNext ∧
      0 < shiftedCorrectionTerm a aNext C CNext E ENext := @ErdosProblems.Erdos243.PaperCompleteR21.sylvesterTail_shiftedCorrection a aNext D DNext C CNext E ENext hD hC hE hENext ha hsyl hzero

end PalomarCorpus.E243.PaperStatementsE
