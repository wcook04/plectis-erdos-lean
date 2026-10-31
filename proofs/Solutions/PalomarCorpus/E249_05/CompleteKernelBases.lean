/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.PaperCompleteR8.FullKernelAssemblies
import Solutions.PalomarCorpus.E249_05.Statement

open Filter Topology
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace PalomarCorpus.E249.CompleteKernelBases

noncomputable abbrev AllBaseCanonicalIndex (k e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)

noncomputable def allBaseCanonicalResidue (k : ℕ) {e : ℕ}
    (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) : ℕ :=
  k * x.2.1.val + (x.2.2.val + 1)

noncomputable def allBaseCanonicalFamily (k e : ℕ) : AllBaseCanonicalIndex k e → ℕ → ℚ
  | Sum.inl i => allBaseTotientKernelSeq k i.val 0
  | Sum.inr x => allBaseTotientKernelSeq k (x.1.val + 1) (allBaseCanonicalResidue k x)

noncomputable def missingEulerProduct (k u : ℕ) : ℚ :=
  ∏ p ∈ k.primeFactors.filter (fun p => ¬ p ∣ u), (1 - (p : ℚ)⁻¹)

noncomputable def fullRetainedChannel : TotientOddCoreIndex → TotientDyadicKernelIndex
  | Sum.inl i => ⟨i.val, ⟨0, by positivity⟩⟩
  | Sum.inr ⟨j, r⟩ => ⟨j + 1, ⟨2 * r.val + 1, by
      have hr := r.isLt
      rw [pow_succ]
      omega⟩⟩

noncomputable abbrev FullRelations := LinearMap.ker (Finsupp.linearCombination ℚ fullTotientKernelFamily)
noncomputable abbrev FullOmitted := {i : TotientDyadicKernelIndex // i ∉ Set.range fullRetainedChannel}

theorem displayed_all_base_kernel (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily k e))) =
      k ^ e + 1 ∧
    (∃ b : Module.Basis (AllBaseCanonicalIndex k e) ℚ
        (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily k e))),
      ∀ i, (b i : ℕ → ℚ) = allBaseCanonicalFamily k e i) ∧
    (∀ j : ℕ, 1 ≤ j →
      allBaseTotientKernelSeq k j 0 =
        (k ^ (j - 1) : ℚ) • allBaseTotientKernelSeq k 1 0) ∧
    (∀ j t u : ℕ, 1 ≤ t → t < j →
      allBaseTotientKernelSeq k j (k ^ t * u) =
        ((k : ℚ) ^ t * missingEulerProduct k u) •
          allBaseTotientKernelSeq k (j - t) u) := by
  exact ErdosProblems.Erdos249.PaperCompleteR8.displayed_all_base_kernel k e hk he

theorem displayed_full_dyadic_basis :
    (∃ b : Module.Basis TotientOddCoreIndex ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily)),
      ∀ i, (b i : ℕ → ℚ) = oddCoreTotientKernelFamily i) ∧
    (∃ b : Module.Basis FullOmitted ℚ FullRelations,
      ∀ o, ∃ j : TotientOddCoreIndex, ∃ a : ℕ,
        fullTotientKernelFamily o.val = (a : ℚ) • oddCoreTotientKernelFamily j ∧
        (b o : TotientDyadicKernelIndex →₀ ℚ) =
          Finsupp.single o.val 1 - Finsupp.single (fullRetainedChannel j) (a : ℚ)) ∧
    (∀ e : ℕ, 1 ≤ e → Module.finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) = 2 ^ e + 1) ∧
    Module.finrank ℚ (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily 2 0))) = 1 := by
  exact ErdosProblems.Erdos249.PaperCompleteR8.displayed_full_dyadic_basis

theorem displayed_canonical_and_full_dyadic :
    (∀ e : ℕ, Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1 ∧
      LinearIndependent ℚ (canonicalTotientKernelFamily e)) ∧
    (∃ b : Module.Basis TotientOddCoreIndex ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily)),
      ∀ i, (b i : ℕ → ℚ) = oddCoreTotientKernelFamily i) ∧
    (∀ e : ℕ, 1 ≤ e → Module.finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) = 2 ^ e + 1) ∧
    Module.finrank ℚ (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily 2 0))) = 1 := by
  exact ErdosProblems.Erdos249.PaperCompleteR8.displayed_canonical_and_full_dyadic

end PalomarCorpus.E249.CompleteKernelBases
end
