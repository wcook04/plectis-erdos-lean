/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperFiniteCertificatesR7
import Solutions.PalomarCorpus.E251_02.Statement

open Filter Topology
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace PalomarCorpus.E251.ExactDenominatorFloors
export PalomarCorpus.E251_02.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)

theorem denominator_floor_both (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ((∑' n, primeDyadicTerm n) = a / b → 2 ^ 589 ≤ b ∧ 10 ^ 177 < b) ∧
    ((∑' n, primeGapDyadicTerm n) = a / b → 2 ^ 589 ≤ b ∧ 10 ^ 177 < b) := by
  simpa only [prime0, primeGap0, primeDyadicTerm, primeGapDyadicTerm, ErdosProblems.Erdos251.prime0, ErdosProblems.Erdos251.primeGap0, ErdosProblems.Erdos251.primeDyadicTerm, ErdosProblems.Erdos251.primeGapDyadicTerm] using
    ErdosProblems.Erdos251.PaperR7.denominator_floor_both a b hb

end PalomarCorpus.E251.ExactDenominatorFloors
end
