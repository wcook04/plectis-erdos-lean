/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.Erdos249.PaperCompleteR7.ShortNoteAssemblies
import Solutions.PalomarCorpus.E249_30.Statement

open scoped BigOperators
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsM

theorem fullDepth_amplification :
    (∀ d N : ℕ, 0 < d →
      (totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) →
      ∃ T : ℕ, 0 < T ∧ ∀ t : ℕ, T ≤ t →
        certifiedKill (t * d) N (t * d) ∨
          certifiedKill ((t + 1) * d) N ((t + 1) * d)) ∧
    (∀ d N : ℕ, 0 < d →
      ((∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔
        totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ))) ∧
    ((∀ d : ℕ, 0 < d → ∀ N : ℕ,
        ∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) := @ErdosProblems.Erdos249.PaperCompleteR7.fullDepth_amplification

end PalomarCorpus.E249.PaperStatementsM
