/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.PaperFiniteAssembliesR7
import Solutions.PalomarCorpus.E1049_05.Statement

open scoped BigOperators
universe u

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

universe u

namespace PalomarCorpus.E1049.PaperStatementsT

theorem plucker_paper_statement :
    (∀ (R₀ : Type u) [CommRing R₀] (w : ℕ → R₀ × R₀),
      (∀ n, IsCoprime (w n).1 (w n).2) →
      (∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0) →
      ∀ i j, (w i).1 * (w j).2 - (w i).2 * (w j).1 = 0) ∧
    (∀ (R S k : ℕ)
      (w : ℕ → ZMod (2 ^ S * 3 ^ R) × ZMod (2 ^ S * 3 ^ R)),
      (∀ n, IsCoprime (w n).1 (w n).2) →
      (∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0) →
      0 < R → S + 2 * R ≤ k →
      ∃ s t : Fin k → Bool, s ≠ t ∧
        (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0) := @ErdosProblems.Erdos1049.PaperR7.plucker_paper_statement

end PalomarCorpus.E1049.PaperStatementsT
