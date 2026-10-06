/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperLargeCertificateR7
import Solutions.PalomarCorpus.E251_07.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStructuresI
export PalomarCorpus.E251_07.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)

theorem denominator_floor_both (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b ∨
      (∑' n, primeGapDyadicTerm n) = a / b) :
    2 ^ 39997 ≤ b ∧ 10 ^ 12040 < b := @ErdosProblems.Erdos251.PaperR7.LargeCertificate.denominator_floor_both

end PalomarCorpus.E251.PaperStructuresI
