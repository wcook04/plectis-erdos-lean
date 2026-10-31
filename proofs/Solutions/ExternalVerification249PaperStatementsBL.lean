/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.PivotAntiReconstruction
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.Erdos249.PaperCompleteR21.BinaryDigitChangeDensity

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.PivotAntiReconstruction`, `Erdos249257.TotientTailPeriodKiller`,
`ErdosProblems.Erdos249.PaperCompleteR21.BinaryDigitChangeDensity`.
-/

open scoped Classical
open Finset

namespace Erdos249257.ExternalVerification249PaperStatementsBL

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

noncomputable def tailOrbitFirstExp (h N : ℕ) : ℂ :=
  Complex.exp
    (((2 * Real.pi * (totientTail (N + h) - totientTail N) : ℝ) : ℂ) *
      Complex.I)

noncomputable def totientAlphaShift (h : ℕ) : ℝ :=
  ((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)

theorem tailOrbitFirstExp_re_eq (h N : ℕ) :
    (tailOrbitFirstExp h N).re = Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * totientAlphaShift h)) := @ErdosProblems.Erdos249.PaperCompleteR21.tailOrbitFirstExp_re_eq h N

end Erdos249257.ExternalVerification249PaperStatementsBL
