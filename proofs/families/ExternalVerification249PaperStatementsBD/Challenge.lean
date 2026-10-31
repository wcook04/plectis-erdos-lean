/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CertificateKernel`, `Erdos249257.CompositeDilationDefect`,
`ErdosProblems.Erdos249.PaperCompleteR21.CompositeDilationIdentity`.
-/

open Filter
open Topology

namespace Erdos249257.ExternalVerification249PaperStatementsBD

noncomputable def compositeDilationDefect (A : Set ℕ) (a x : ℕ) : ℕ :=
  by
    classical
    exact ((a * x).divisors.filter fun d =>
      d ∈ A ∧ ¬ d ∣ x ∧ d ≠ a).card

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_divisor_count in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem composite_dilation_divisor_count (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (ha1 : 1 ≤ a) (hx1 : 1 ≤ x) :
    supportCoeff A (a * x) =
      supportCoeff A x + (if a ∣ x then 0 else 1) +
        compositeDilationDefect A a x := by
  sorry

/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_divisor_count_prime_support in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem composite_dilation_divisor_count_prime_support (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (hx1 : 1 ≤ x) (hAprime : ∀ d ∈ A, d.Prime) :
    supportCoeff A (a * x) = supportCoeff A x + (if a ∣ x then 0 else 1) := by
  sorry

/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.lambert_support_series in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lambert_support_series (A : Set ℕ) :
    (∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a) =
      ∑' m : ℕ, (supportCoeff A (m + 1) : ℝ) / (2 : ℝ) ^ (m + 1) := by
  sorry

/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.lambert_support_series_restricted in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lambert_support_series_restricted (A : Set ℕ) :
    (∑' a : ℕ, Set.indicator {a ∈ A | 1 ≤ a} (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a) =
      ∑' m : ℕ, (supportCoeff A (m + 1) : ℝ) / (2 : ℝ) ^ (m + 1) := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsBD
