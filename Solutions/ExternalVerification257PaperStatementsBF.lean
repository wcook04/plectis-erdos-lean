/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.CertificateKernel
import ErdosProblems.Erdos257.PaperCompleteR21.SquarefreeSupportEngineCeiling
import ErdosProblems.Erdos257.SquarefreeSupportIncidence

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CertificateKernel`,
`ErdosProblems.Erdos257.PaperCompleteR21.SquarefreeSupportEngineCeiling`,
`ErdosProblems.Erdos257.SquarefreeSupportIncidence`.
-/

open Filter
open Topology
open Finset

namespace Erdos249257.ExternalVerification257PaperStatementsBF

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

noncomputable def squarefreeSupport : Set ℕ := {d : ℕ | 2 ≤ d ∧ Squarefree d}

theorem paper_squarefree_support_engine_ceiling :
    (squarefreeSupport = {d : ℕ | 2 ≤ d ∧ Squarefree d}) ∧
      (∀ n : ℕ, n ≠ 0 →
        supportCoeff squarefreeSupport n
          = 2 ^ n.primeFactors.card - 1) ∧
      (∀ n : ℕ, 2 ≤ n → Odd (supportCoeff squarefreeSupport n)) ∧
      (∀ b : ℕ, 2 ≤ b → 2 ∣ b →
        ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
            (b ^ K ∣ ∑ r ∈ Finset.Icc 1 K,
              supportCoeff squarefreeSupport (N + r) * b ^ (K - r)) ∧
            (∑ r ∈ Finset.Icc (K + 1) L,
              supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
            (∃ t : ℕ, 0 < supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
            q * (C + (N + L + 2)) < b ^ L)) ∧
      (∀ b : ℕ, 2 ≤ b → 2 ∣ b →
        ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
            (∀ r ∈ Finset.Icc 1 K,
              b ^ r ∣ supportCoeff squarefreeSupport (N + r)) ∧
            (∑ r ∈ Finset.Icc (K + 1) L,
              supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
            (∃ t : ℕ, 0 < supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
            q * (C + (N + L + 2)) < b ^ L)) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_squarefree_support_engine_ceiling

end Erdos249257.ExternalVerification257PaperStatementsBF
