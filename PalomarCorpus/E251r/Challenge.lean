/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band r

Erdős problem #251 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E251` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Topology
open Finset
open scoped BigOperators

namespace PalomarCorpus.E251.PaperStatementsR
open Filter
open Topology
open Finset
open scoped BigOperators
/-- Zero-based prime enumeration. Local copy of ErdosProblems.Erdos251.prime0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n
/-- Four distinct primes with two outer gaps differing by r. Local copy of ErdosProblems.Erdos251.PaperR9.ShiftCounting.quadCandidates, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def quadCandidates (N H : ℕ) (r : ℤ) : Finset ((ℕ × ℕ) × ℕ) := by
  classical
  exact (((range (prime0 N)).product (range (H + 1))).product (range (H + 1))).filter
    (fun z =>
      0 < z.1.2 ∧ z.1.2 < z.2 ∧ 0 < (z.1.2 : ℤ) + r ∧
      Nat.Prime z.1.1 ∧ Nat.Prime (z.1.1 + z.1.2) ∧ Nat.Prime (z.1.1 + z.2) ∧
      Nat.Prime (((z.1.1 : ℤ) + z.2 + z.1.2 + r).toNat))
/-- Zero-based consecutive prime gap. Local copy of ErdosProblems.Erdos251.primeGap0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n
/-- Local copy of ErdosProblems.Erdos251.PaperR9.ShiftCounting.shiftedMatches, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftedMatches (h N : ℕ) (r : ℤ) : Finset ℕ := by
  classical
  exact (range N).filter (fun n => (primeGap0 (n + h) : ℤ) - primeGap0 n = r)
/-- States long251:res:shiftedcount from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR9.ShiftCounting.shifted_count_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem shifted_count_bound (h N H : ℕ) (hh : 2 ≤ h) (r : ℤ) :
    (H + 1) * (shiftedMatches h N r).card ≤
      (h + 1) * prime0 (N + (h + 1)) + (H + 1) * (quadCandidates N H r).card := by
  sorry
end PalomarCorpus.E251.PaperStatementsR
