/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #243, band o

Erdős problem #243 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E243` under the Challenge size ceiling; it does not replace it.
-/

open Filter

namespace PalomarCorpus.E243.PaperStatementsO
open Filter
/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. Local copy of ErdosProblems.Erdos243.centeredState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- States long243:res:gcdsparse from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.sparse_gcd_changes in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sparse_gcd_changes
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hlim : Tendsto (fun n ↦ |(E n : ℝ)| / (C n : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N ↦
      (((Finset.range N).filter (fun j ↦
        Nat.gcd (C j) (D j) < Nat.gcd (C (j + 1)) (D (j + 1)))).card : ℝ) /
          (N : ℝ)) atTop (nhds 0) ∧
    (∀ B L : ℕ, ∃ n, B ≤ n ∧ ∀ j, j ≤ L →
      Nat.gcd (C (n + j)) (D (n + j)) = Nat.gcd (C n) (D n)) := by
  sorry
end PalomarCorpus.E243.PaperStatementsO
