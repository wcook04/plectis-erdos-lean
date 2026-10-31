/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import Solutions.PalomarCorpus.E251_07.Statement

open Filter Topology
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace PalomarCorpus.E251.PrimeGapNonperiodicity
export PalomarCorpus.E251_07.Shared (prime0 primeGap0)

noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

theorem primeGap0_not_eventually_periodic
    {h : ℕ} (hpos : 0 < h) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N →
      primeGap0 (N + h + 1) = primeGap0 (N + 1) := by
  simpa only [prime0, primeGap0, primeDyadicTerm, primeGapDyadicTerm, ErdosProblems.Erdos251.prime0, ErdosProblems.Erdos251.primeGap0, ErdosProblems.Erdos251.primeDyadicTerm, ErdosProblems.Erdos251.primeGapDyadicTerm] using
    ErdosProblems.Erdos251.primeGap0_not_eventually_periodic hpos

end PalomarCorpus.E251.PrimeGapNonperiodicity
end
