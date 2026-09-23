/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.GreedyAchievementSet
import Erdos249257.MobiusSignSupportNoGo
import ErdosProblems.Erdos257.PaperCompleteR21.MobiusSignAndFiniteCertificates

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.GreedyAchievementSet`, `Erdos249257.MobiusSignSupportNoGo`,
`ErdosProblems.Erdos257.PaperCompleteR21.MobiusSignAndFiniteCertificates`.
-/

open ArithmeticFunction
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

namespace Erdos249257.ExternalVerification257PaperStatementsAQ

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def negativeMobiusTerm (d : ℕ+) : ℝ :=
  if moebius (d : ℕ) = -1 then mersenneWeight (d : ℕ) else 0

noncomputable def positiveMobiusTailTerm (d : ℕ+) : ℝ :=
  if moebius (d : ℕ) = 1 ∧ (d : ℕ) ≠ 1 then mersenneWeight (d : ℕ) else 0

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

end Erdos249257.ExternalVerification257PaperStatementsAQ
