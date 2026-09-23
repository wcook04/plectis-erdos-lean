/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243_06

Every non-theorem declaration of `PalomarCorpus/E243_06/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open scoped Topology
open scoped BigOperators
open Finset

namespace PalomarCorpus.E243_06.Shared
/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. Local copy of ErdosProblems.Erdos243.centeredState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- The original-coordinate product defect at index `n`, the real number `(P n / a n) * (a n ^ 2 / a (n+1) - 1)` where `P n = ∏_{j < n} a j`, which weighs the departure from the Sylvester growth relation by the prefix product; the naturals `P n`, `a n` and `a (n+1)` are cast to the reals. -/
noncomputable def productDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)
/-- The truncated base-two iterated logarithm log₂(log₂(max(4, x))). -/
noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2
/-- The running maximum `max_{k ≤ n} u k` of a natural-valued sequence, given by `runningMax u 0 = u 0` and `runningMax u (n+1) = max (runningMax u n) (u (n+1))`. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- The increment of the running maximum divided by the truncated iterated logarithm of its preceding value. -/
noncomputable def recordLogLogCharge (U : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((runningMax U (n + 1) - runningMax U n : ℕ) : ℝ) / recordLogLog (runningMax U n)
/-- The extended-real limit superior of the normalized running-record increments. -/
noncomputable def recordTheta (U : ℕ → ℕ) : EReal :=
  limsup (fun n ↦ (recordLogLogCharge U n : EReal)) atTop
end PalomarCorpus.E243_06.Shared

namespace PalomarCorpus.E243.PaperStructuresAA
open Filter
export PalomarCorpus.E243_06.Shared (centeredState)
end PalomarCorpus.E243.PaperStructuresAA

namespace PalomarCorpus.E243.PaperStructuresAB
open Filter
export PalomarCorpus.E243_06.Shared (centeredState recordLogLog)
/-- An integer height which the paper's normaliser sends to its index. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.binaryTower, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryTower (n : ℕ) : ℕ := 2 ^ (2 ^ n)
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
end PalomarCorpus.E243.PaperStructuresAB

namespace PalomarCorpus.E243.PaperStructuresAE
open Filter
open scoped Topology
export PalomarCorpus.E243_06.Shared (centeredState recordLogLog recordLogLogCharge recordTheta runningMax)
end PalomarCorpus.E243.PaperStructuresAE

namespace PalomarCorpus.E243.OriginalCoordinateBoundedDefect
open Filter
export PalomarCorpus.E243_06.Shared (prefixProduct productDefect)
end PalomarCorpus.E243.OriginalCoordinateBoundedDefect

namespace PalomarCorpus.E243.PaperStatementsL
open Filter
open scoped BigOperators
export PalomarCorpus.E243_06.Shared (prefixProduct productDefect recordLogLog)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
end PalomarCorpus.E243.PaperStatementsL

namespace PalomarCorpus.E243.PaperStatementsR
open Filter
open scoped Topology
export PalomarCorpus.E243_06.Shared (recordLogLog recordLogLogCharge recordTheta runningMax)
end PalomarCorpus.E243.PaperStatementsR

namespace PalomarCorpus.E243.PaperStatementsB
open Filter
open Finset
open scoped BigOperators
open scoped Topology
end PalomarCorpus.E243.PaperStatementsB

namespace PalomarCorpus.E243.PaperStatementsF
open Filter
end PalomarCorpus.E243.PaperStatementsF
