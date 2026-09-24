/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.PaperFiniteAssembliesR7`.
-/

open scoped BigOperators

universe u

namespace Erdos249257.ExternalVerification1049PaperStatementsT

/-- States long1049:res:plucker-collapse, res:plucker-collapse from the long record and the
short record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.PaperR7.plucker_paper_statement in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem plucker_paper_statement :
    (∀ (R₀ : Type u) [CommRing R₀] (w : ℕ → R₀ × R₀),
      (∀ n, IsCoprime (w n).1 (w n).2) →
      (∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0) →
      ∀ i j, (w i).1 * (w j).2 - (w i).2 * (w j).1 = 0) ∧
    (∀ (R S k : ℕ)
      (w : ℕ → ZMod (2 ^ S * 3 ^ R) × ZMod (2 ^ S * 3 ^ R)),
      (∀ n, IsCoprime (w n).1 (w n).2) →
      (∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0) →
      0 < R → S + 2 * R ≤ k →
      ∃ s t : Fin k → Bool, s ≠ t ∧
        (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0) := by
  sorry

end Erdos249257.ExternalVerification1049PaperStatementsT
