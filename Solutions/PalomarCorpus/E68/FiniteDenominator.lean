/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.PaperCompleteFiniteSizeCertificate
import Solutions.PalomarCorpus.E68.Statement

namespace PalomarCorpus.E68.FiniteDenominator
export PalomarCorpus.E68.Shared (factorialGapSeries)

theorem finite_denominator_exclusion (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hS : factorialGapSeries = (a : ℝ) / q) :
    (2 : ℕ) ^ 39990 ≤ q ∧ (10 : ℕ) ^ 12040 < q := by
  have h := ErdosProblems.Erdos68.PaperComplete.FiniteLead.SizeOnly.denominator_exclusion a q hq hS
  exact ⟨h.1, h.2.2⟩

end PalomarCorpus.E68.FiniteDenominator
