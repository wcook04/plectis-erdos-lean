/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.FirstMergeCriticalValueSeparation
import Solutions.PalomarCorpus.E1041.Statement

namespace PalomarCorpus.E1041.FirstMergeCriticalValueSeparation

theorem firstMerge_exact_convenient_thresholds :
    (∀ n : ℕ, 3 ≤ n → firstMergeSquaredCoefficient n 4 < 1) ∧
    (∀ n : ℕ, 4 ≤ n → firstMergeSquaredCoefficient n 3 < 1) ∧
    (∀ n : ℕ, 6 ≤ n → firstMergeSquaredCoefficient n 2 < 1) := by
  simpa [firstMergeSquaredCoefficient,
    ErdosProblems.Erdos1041.firstMergeSquaredCoefficient] using
    ErdosProblems.Erdos1041.firstMerge_exact_convenient_thresholds

theorem firstMerge_length_lt_two_of_squared_bound
    {n : ℕ} {S length : ℝ}
    (hbound : length ^ 2 ≤ 4 * firstMergeSquaredCoefficient n S)
    (hthreshold : firstMergeSquaredCoefficient n S < 1) :
    length < 2 := by
  apply ErdosProblems.Erdos1041.firstMerge_length_lt_two_of_squared_bound
  · simpa [firstMergeSquaredCoefficient,
      ErdosProblems.Erdos1041.firstMergeSquaredCoefficient] using hbound
  · simpa [firstMergeSquaredCoefficient,
      ErdosProblems.Erdos1041.firstMergeSquaredCoefficient] using hthreshold

end PalomarCorpus.E1041.FirstMergeCriticalValueSeparation
