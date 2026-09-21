/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band d

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Topology

namespace PalomarCorpus.E249.PaperStatementsBD
open Filter
open Topology
/-- Support divisors created by multiplication by `a`, excluding the distinguished divisor `a` itself. Local copy of Erdos249257.CompositeDilationDefect.compositeDilationDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def compositeDilationDefect (A : Set ℕ) (a x : ℕ) : ℕ :=
  by
    classical
    exact ((a * x).divisors.filter fun d =>
      d ∈ A ∧ ¬ d ∣ x ∧ d ≠ a).card
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}` — the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_divisor_count in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem composite_dilation_divisor_count (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (ha1 : 1 ≤ a) (hx1 : 1 ≤ x) :
    supportCoeff A (a * x) =
      supportCoeff A x + (if a ∣ x then 0 else 1) +
        compositeDilationDefect A a x := by
  sorry
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_divisor_count_prime_support in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem composite_dilation_divisor_count_prime_support (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (hx1 : 1 ≤ x) (hAprime : ∀ d ∈ A, d.Prime) :
    supportCoeff A (a * x) = supportCoeff A x + (if a ∣ x then 0 else 1) := by
  sorry
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lambert_support_series in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lambert_support_series (A : Set ℕ) :
    (∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a) =
      ∑' m : ℕ, (supportCoeff A (m + 1) : ℝ) / (2 : ℝ) ^ (m + 1) := by
  sorry
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lambert_support_series_restricted in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lambert_support_series_restricted (A : Set ℕ) :
    (∑' a : ℕ, Set.indicator {a ∈ A | 1 ≤ a} (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a) =
      ∑' m : ℕ, (supportCoeff A (m + 1) : ℝ) / (2 : ℝ) ^ (m + 1) := by
  sorry
end PalomarCorpus.E249.PaperStatementsBD
