/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.PaperFiniteAssembliesR7
import ErdosProblems.Erdos1049.RationalBaseLambert
import Solutions.PalomarCorpus.E1049k.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStatementsK

theorem charge_ceilings :
    (∀ N : ℤ, 0 < N →
      41 * (N ^ 3 - N) < 39 * (4 * N ^ 3 - 3 * N ^ 2)) ∧
    (∀ N : ℤ, 2 ≤ N →
      41 * (2 * N ^ 3 - N) < 39 * (4 * N ^ 3 - 3 * N ^ 2)) ∧
    (∀ N E : ℤ, 0 < N → E ≤ N ^ 3 - N →
      41 * E < 39 * (4 * N ^ 3 - 3 * N ^ 2)) ∧
    (∀ N E : ℤ, 2 ≤ N → E ≤ 2 * N ^ 3 - N →
      41 * E < 39 * (4 * N ^ 3 - 3 * N ^ 2)) := @ErdosProblems.Erdos1049.PaperR7.charge_ceilings

theorem forcing_term (B : ℕ) (c : ℕ → ℕ) (N : ℕ) :
    (∀ s : ℕ, 2 ≤ s → 1 ≤ B → 1 ≤ c (N + 1) →
      2 ^ (N + 1) ≤ rationalBaseForcingNat s B c N) ∧
      rationalBaseForcingNat 1 B c N = B * c (N + 1) := @ErdosProblems.Erdos1049.PaperR7.forcing_term B c N

theorem power_bracket :
    (2 : ℕ) ^ 64 < 3 ^ 41 ∧ 3 ^ 41 < 2 ^ 65 ∧
      (41 : ℝ) / 65 < Real.log 2 / Real.log 3 ∧
      Real.log 3 / Real.log 2 < (65 : ℝ) / 41 := @ErdosProblems.Erdos1049.PaperR7.power_bracket

theorem scalar_margin {C0 C1 : ℝ} (hC1 : 0 < C1)
    (hs : C0 ≤ 0 ∨ 2 * C0 ≤ C1) :
    C0 * Real.log 3 - C1 * Real.log 2 < 0 ∧
      (0 < C0 → 2 * C0 ≤ C1 →
        C0 * Real.log 3 - C1 * Real.log 2 < -((17 : ℝ) / 41) * C0 * Real.log 2) := @ErdosProblems.Erdos1049.PaperR7.scalar_margin C0 C1 hC1 hs

end PalomarCorpus.E1049.PaperStatementsK
