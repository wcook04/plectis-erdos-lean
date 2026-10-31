/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.CyclotomicAnchoredKill
import Solutions.PalomarCorpus.E249_31.Statement

open scoped BigOperators

namespace PalomarCorpus.E249.BinaryCyclotomicAnchors
export PalomarCorpus.E249_31.Shared (totientTail)

theorem exists_clean_binaryCyclotomicAnchor
    (h N₀ : ℕ) (hh : 0 < h) :
    ∃ q p : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ binaryCyclotomicLayer (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 := by
  simpa [binaryCyclotomicLayer,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.exists_clean_binaryCyclotomicAnchor
      h N₀ hh

theorem binaryCyclotomicLayer_unboundedPrimeDivisorSupply
    (h : ℕ) (hh : 0 < h) :
    UnboundedPrimeDivisorSupply binaryCyclotomicLayer h := by
  simpa [UnboundedPrimeDivisorSupply, binaryCyclotomicLayer,
    ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.UnboundedPrimeDivisorSupply,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer_unboundedPrimeDivisorSupply
      h hh

theorem binaryCyclotomicAnchoredKillSupply_iff_irrational :
    CyclotomicAnchoredKillSupply binaryCyclotomicLayer ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  simpa [CyclotomicAnchoredKillSupply, certifiedKill, windowDiscrepancy,
    binaryCyclotomicLayer,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.CyclotomicAnchoredKillSupply,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.certifiedKill,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.windowDiscrepancy] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicAnchoredKillSupply_iff_irrational

theorem exists_unbounded_binaryCyclotomicSupport_with_periodLock_of_not_irrational
    (hrat : ¬ Irrational
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧
      UnboundedPrimeDivisorSupply binaryCyclotomicLayer h ∧
      ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
        totientTail (N + h) - totientTail N ∈
          Set.range ((↑) : ℤ → ℝ) := by
  simpa [UnboundedPrimeDivisorSupply, binaryCyclotomicLayer, totientTail,
    ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.UnboundedPrimeDivisorSupply,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientTail] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.exists_unbounded_binaryCyclotomicSupport_with_periodLock_of_not_irrational
      hrat

end PalomarCorpus.E249.BinaryCyclotomicAnchors
