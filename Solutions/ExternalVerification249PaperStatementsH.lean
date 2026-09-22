/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos249.PaperCompleteR7.ArithmeticAssemblies

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos249.PaperCompleteR7.ArithmeticAssemblies`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification249PaperStatementsH

theorem irrational_totient_iff_moebius_square :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) ↔
      Irrational (∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := @ErdosProblems.Erdos249.PaperCompleteR7.irrational_totient_iff_moebius_square

end Erdos249257.ExternalVerification249PaperStatementsH
