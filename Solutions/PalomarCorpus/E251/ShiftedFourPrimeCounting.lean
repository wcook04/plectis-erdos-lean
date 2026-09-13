/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.ShiftedCountingSourceR11
import Solutions.PalomarCorpus.E251.Statement

open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

noncomputable section

namespace PalomarCorpus.E251.ShiftedFourPrimeCounting
export PalomarCorpus.E251.Shared (prime0 primeGap0)

theorem shifted_count_bound (h N H : ℕ) (hh : 2 ≤ h) (r : ℤ) :
    (H + 1) * (shiftedMatches h N r).card ≤
      (h + 1) * prime0 (N + (h + 1)) + (H + 1) * (quadCandidates N H r).card := by
  exact ErdosProblems.Erdos251.PaperR11.PrimeSource.shifted_count_bound h N H hh r

theorem separated_zeroDensity_of_quad_sieve (h : ℕ) (hh : 2 ≤ h) (r : ℤ)
    (hsieve : SeparatedQuadSieve_target h r) :
    ZeroDensity {n | (primeGap0 (n + h) : ℤ) - primeGap0 n = r} := by
  exact ErdosProblems.Erdos251.PaperR11.PrimeSource.separated_zeroDensity_of_quad_sieve h hh r hsieve

end PalomarCorpus.E251.ShiftedFourPrimeCounting
