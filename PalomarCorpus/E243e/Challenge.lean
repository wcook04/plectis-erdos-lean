/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #243, band e

Erdős problem #243 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E243` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open scoped BigOperators

namespace PalomarCorpus.E243.PaperStatementsE
open Filter
open scoped BigOperators
/-- The correction term `Λ_n` of `long243:eq:shiftedsign`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.shiftedCorrectionTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftedCorrectionTerm (a aNext C CNext E ENext : ℝ) : ℝ :=
  (1 - E / C) * (a - 1 + ENext / CNext) / aNext
/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.growthDefect_eq_neg_relativeError_add_shiftedCorrection in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem growthDefect_eq_neg_relativeError_add_shiftedCorrection
    {a aNext D DNext C CNext E ENext : ℝ}
    (hD : DNext = a * D)
    (hC : CNext = a * C - D)
    (hE : E = D - (a - 1) * C)
    (hENext : ENext = DNext - (aNext - 1) * CNext)
    (hne : aNext * C * CNext ≠ 0) :
    a ^ 2 / aNext - 1 =
      -(E / C) + shiftedCorrectionTerm a aNext C CNext E ENext := by
  sorry
/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.shiftedCorrectionTerm_pos_and_lt_three_div in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem shiftedCorrectionTerm_pos_and_lt_three_div
    {A ANext C CNext E ENext : ℝ}
    (hA : 2 ≤ A) (hANext : A ^ 2 / 2 ≤ ANext)
    (hθ : |E / C| ≤ 1 / 4) (hθNext : |ENext / CNext| ≤ 1 / 4) :
    0 < shiftedCorrectionTerm A ANext C CNext E ENext ∧
      shiftedCorrectionTerm A ANext C CNext E ENext < 3 / A := by
  sorry
/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.sylvesterTail_shiftedCorrection in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
      0 < shiftedCorrectionTerm a aNext C CNext E ENext := by
  sorry
end PalomarCorpus.E243.PaperStatementsE
