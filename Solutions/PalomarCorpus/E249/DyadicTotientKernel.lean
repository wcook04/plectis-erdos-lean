/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.TotientMahlerDefect
import Solutions.PalomarCorpus.E249.Shared

open Module

namespace PalomarCorpus.E249.DyadicTotientKernel
export PalomarCorpus.E249.Shared (TotientCanonicalIndex canonicalTotientKernelFamily totientKernelSeq)

noncomputable abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)

noncomputable def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val

noncomputable abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)

noncomputable def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val

noncomputable abbrev TotientOddCoreIndex := Fin 2 ⊕ Σ j : ℕ, Fin (2 ^ j)

noncomputable def oddCoreTotientKernelFamily : TotientOddCoreIndex → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j + 1) (2 * r.val + 1)

theorem dyadicTotientKernelOddCoreBasisAndFiniteRanks :
    LinearIndependent ℚ oddCoreTotientKernelFamily ∧
      Submodule.span ℚ (Set.range fullTotientKernelFamily) =
        Submodule.span ℚ (Set.range oddCoreTotientKernelFamily) ∧
      ∀ e : ℕ, 1 ≤ e →
        Submodule.span ℚ
            (Set.range (totientKernelThroughLevelFamily e)) =
          Submodule.span ℚ
            (Set.range (canonicalTotientKernelFamily e)) ∧
        finrank ℚ
            (Submodule.span ℚ
              (Set.range (totientKernelThroughLevelFamily e))) = 2 ^ e + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [oddCoreTotientKernelFamily, totientKernelSeq,
      Erdos257PeriodNoncollapse.oddCoreTotientKernelFamily,
      Erdos257PeriodNoncollapse.totientKernelSeq] using
      Erdos257PeriodNoncollapse.linearIndependent_oddCoreTotientKernelFamily
  · simpa [fullTotientKernelFamily, oddCoreTotientKernelFamily,
      totientKernelSeq, Erdos257PeriodNoncollapse.fullTotientKernelFamily,
      Erdos257PeriodNoncollapse.oddCoreTotientKernelFamily,
      Erdos257PeriodNoncollapse.totientKernelSeq] using
      Erdos257PeriodNoncollapse.span_range_fullTotientKernel_eq_span_range_oddCore
  · intro e he
    constructor
    · simpa [totientKernelThroughLevelFamily,
        canonicalTotientKernelFamily, totientKernelSeq,
        Erdos257PeriodNoncollapse.totientKernelThroughLevelFamily,
        Erdos257PeriodNoncollapse.canonicalTotientKernelFamily,
        Erdos257PeriodNoncollapse.totientKernelSeq] using
        Erdos257PeriodNoncollapse.span_totientKernelThroughLevelFamily_eq_canonical
          e he
    · simpa [totientKernelThroughLevelFamily, totientKernelSeq,
        Erdos257PeriodNoncollapse.totientKernelThroughLevelFamily,
        Erdos257PeriodNoncollapse.totientKernelSeq] using
        Erdos257PeriodNoncollapse.finrank_totientKernelThroughLevelFamily_eq e he

end PalomarCorpus.E249.DyadicTotientKernel
