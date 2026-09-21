/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243i

Every non-theorem declaration of `PalomarCorpus/E243i/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open scoped Topology
open scoped BigOperators

namespace PalomarCorpus.E243.PaperStatementsI
open Filter
open scoped Topology
open scoped BigOperators
/-- The exact real-valued normaliser from the inclusive boundary. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.recordLogLog, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2
/-- The error observable in the inclusive corollary. The negative part is formed in integers first, and then cast into the ordinary real quotient. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.negativeErrorLogLogCharge, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def negativeErrorLogLogCharge (U : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  ((max (-E n) 0 : ℤ) : ℝ) / recordLogLog (U n)
/-- The positive integers divisible by none of the moduli: the set the paper enumerates as `(u n)`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.Avoids, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Avoids (m : ℕ → ℕ) (n : ℕ) : Prop := 0 < n ∧ ∀ j, ¬ (m j ∣ n)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalDenominator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. Local copy of ErdosProblems.Erdos243.centeredState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
end PalomarCorpus.E243.PaperStatementsI
