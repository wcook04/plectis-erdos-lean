/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band q

Erdős problem #251 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E251` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Topology
open scoped BigOperators

namespace PalomarCorpus.E251.PaperStatementsQ
open Filter
open Topology
open scoped BigOperators
/-- Euclidean distance to the complete integer lattice. Local copy of ErdosProblems.Erdos251.PaperR7.integerDistance, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerDistance (x : ℝ) : ℝ :=
  Metric.infDist x (Set.range (fun z : ℤ => (z : ℝ)))
/-- Local copy of ErdosProblems.Erdos251.PaperR7.majorantRemainderTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def majorantRemainderTerm (M : ℕ → ℝ) (h N L j : ℕ) : ℝ :=
  (M (N + h + L + j + 1) + M (N + L + j + 1)) / 2 ^ (L + j + 1)
/-- Local copy of ErdosProblems.Erdos251.PaperR7.majorantRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def majorantRemainder (M : ℕ → ℝ) (h N L : ℕ) : ℝ :=
  ∑' j : ℕ, majorantRemainderTerm M h N L j
/-- Zero-based prime enumeration. Local copy of ErdosProblems.Erdos251.prime0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n
/-- Zero-based consecutive prime gap. Local copy of ErdosProblems.Erdos251.primeGap0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n
/-- Local copy of ErdosProblems.Erdos251.PaperR7.signedWindow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def signedWindow (h N L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range L,
    ((primeGap0 (N + h + j + 1) : ℝ) - primeGap0 (N + j + 1)) / 2 ^ (j + 1)
/-- The real term in the normalized zero-based prime series. Local copy of ErdosProblems.Erdos251.primeDyadicTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)
/-- States eq:truncation, res:truncation from the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.irrational_prime_series_of_finite_truncation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_prime_series_of_finite_truncation (M : ℕ → ℝ)
    (hM : ∀ n, (primeGap0 n : ℝ) ≤ M n)
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N L : ℕ,
      N₀ ≤ N ∧ 1 ≤ L ∧ Summable (majorantRemainderTerm M h N L) ∧
      majorantRemainder M h N L < integerDistance (signedWindow h N L)) :
    Irrational (∑' n : ℕ, primeDyadicTerm n) := by
  sorry
end PalomarCorpus.E251.PaperStatementsQ
