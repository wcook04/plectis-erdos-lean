/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusCofinalExactRows
import Erdos249257.BooleanMobiusCriticalCapacityCofinal
import Erdos249257.BooleanMobiusCriticalCapacityGeometric
import Erdos249257.BooleanMobiusExactRowCrossing
import Erdos249257.BooleanMobiusExactRowDoubling
import Erdos249257.BooleanMobiusGlobalRepair
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.BooleanMobiusSkipRow
import Erdos249257.BooleanMobiusSkippedCoreCriticalCapacity
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCylinderIntegerGreedy
import ErdosProblems.Erdos257.PaperCompleteR20.QuotientRowIdentity
import ErdosProblems.Erdos257.PaperCompleteR20.QuotientRowReal
import ErdosProblems.Erdos257.PaperCompleteR21.ExactRowDichotomyCountermodels
import ErdosProblems.Erdos257.PaperCompleteR21.MersenneQuotientRowRecurrences
import Solutions.PalomarCorpus.E257_33.Statement

open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAR
export PalomarCorpus.E257_33.Shared (localMersennePrefixValue localMersenneQuotient localPrefixQuotient mersenneWeightRat)

noncomputable def ExactLocalMersenneHalfRow (n : ℕ) : Prop :=
  ∃ D : Finset ℕ,
    (∀ d ∈ D, 2 ≤ d ∧ d ≤ n) ∧
      localPrefixQuotient D n = 2 ^ (n - 1) - 1

noncomputable def CofinalExactLocalMersenneHalfRows : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ExactLocalMersenneHalfRow n

noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)

noncomputable def SkippedCoreCriticalQuotientSupply : Prop :=
  ∀ (D : Finset ℕ) (c : ℕ),
    4 ≤ c →
    (∀ d ∈ D, 2 ≤ d ∧ d < c) →
    localMersennePrefixValue D < (1 / 2 : ℚ) →
    (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c →
    2 ^ ((2 * c - 2) - 1) ≤
      localPrefixQuotient (insert c D) (2 * c - 2)

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0

noncomputable def exactLocalMersenneRowValue (D : Finset ℕ) : ℝ :=
  ((localMersennePrefixValue D : ℚ) : ℝ)

noncomputable def localMersenneGeometricQuotient (M d : ℕ) : ℕ :=
  2 ^ (M % d) * ∑ j ∈ Finset.range (M / d), (2 ^ d) ^ j

noncomputable def localGeometricPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneGeometricQuotient M d

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

noncomputable def rowDeviation (n : ℕ) (D : Finset ℕ) : ℤ :=
  (2 : ℤ)^(2*n-1) - (2 : ℤ)^(n+1) - ∑ d ∈ D, (truncatedMersenneWeight n d : ℤ)

theorem abs_exactLocalMersenneRowValue_sub_half_le
    {D : Finset ℕ} {n : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) :
    |exactLocalMersenneRowValue D - (1 : ℝ) / 2| ≤
      ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := @Erdos249257.abs_exactLocalMersenneRowValue_sub_half_le D n hn hD hquot

theorem abs_localMersennePrefixValue_sub_half_le
    {D : Finset ℕ} {n : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) :
    |((localMersennePrefixValue D : ℚ) : ℝ) - (1 : ℝ) / 2| ≤
      ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := @Erdos249257.abs_localMersennePrefixValue_sub_half_le D n hn hD hquot

theorem cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply
    (hcap : SkippedCoreCriticalQuotientSupply) :
    CofinalExactLocalMersenneHalfRows := @Erdos249257.cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply hcap

theorem exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCoreSharpCapacity
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hsharp : localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) :
    ExactLocalMersenneHalfRow (2 * c - 2) := @Erdos249257.exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCoreSharpCapacity D c hc hD hbelow hsharp

theorem exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below
    {D : Finset ℕ} {n : ℕ}
    (hn : 6 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (htwo : 2 ∈ D)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, d ∉ D → n < d) ∧
      2 ∈ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * n - 1) ∧
      localPrefixQuotient E (2 * n - 1) =
        2 ^ ((2 * n - 1) - 1) - 1 := @Erdos249257.exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below D n hn hD htwo hquot hbelow

theorem exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hsharp : localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, d ∉ D → c < d) ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * c - 2) ∧
      localPrefixQuotient E (2 * c - 2) =
        2 ^ ((2 * c - 2) - 1) - 1 := @Erdos249257.exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity D c hc hD hbelow hsharp

theorem exists_first_localMersenne_crossing
    {E : Finset ℕ}
    (hE : ∀ d ∈ E, 2 ≤ d)
    (habove : (1 / 2 : ℚ) < localMersennePrefixValue E) :
    ∃ c : ℕ,
      c ∈ E ∧
      4 ≤ c ∧
      localMersennePrefixValue (E.filter fun d ↦ d < c) < (1 / 2 : ℚ) ∧
      (1 / 2 : ℚ) <
        localMersennePrefixValue (insert c (E.filter fun d ↦ d < c)) := @Erdos249257.exists_first_localMersenne_crossing E hE habove

theorem half_mem_mersenneAchievementSet_of_cofinalExactLocalRows
    (hcofinal : CofinalExactLocalMersenneHalfRows) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := @Erdos249257.half_mem_mersenneAchievementSet_of_cofinalExactLocalRows hcofinal

theorem half_mem_mersenneAchievementSet_of_criticalQuotientSupply
    (hcap : SkippedCoreCriticalQuotientSupply) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := @Erdos249257.half_mem_mersenneAchievementSet_of_criticalQuotientSupply hcap

theorem localBinarySuffix_two_mul_sub_one_lt_upperWindow_of_exact_below
    {D : Finset ℕ} {n : ℕ}
    (hn : 6 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (htwo : 2 ∈ D)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * n - 1) < 2 ^ (n - 1) := @Erdos249257.localBinarySuffix_two_mul_sub_one_lt_upperWindow_of_exact_below D n hn hD htwo hquot hbelow

theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) ↔
      2 ^ ((2 * c - 2) - 1) ≤
        localPrefixQuotient (insert c D) (2 * c - 2) := @Erdos249257.localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff D c hc hD hbelow

theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometric
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) ↔
      2 ^ ((2 * c - 2) - 1) ≤
        localGeometricPrefixQuotient (insert c D) (2 * c - 2) := @Erdos249257.localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometric D c hc hD hbelow

theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometricCore
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) ↔
      2 ^ ((2 * c - 2) - 1) - 2 ^ (c - 2) ≤
        localGeometricPrefixQuotient D (2 * c - 2) := @Erdos249257.localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometricCore D c hc hD hbelow

theorem precriticalCrossingTax_of_futureThreshold
    {D : Finset ℕ} {c t : ℕ}
    (hc : 4 ≤ c)
    (ht : t ≤ c - 3)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hres :
      (1 / 2 : ℚ) - localMersennePrefixValue D <
        ∑ j ∈ Finset.range t, mersenneWeightRat (c + j + 1))
    (hroom : c - 2 ≤ 2 ^ (c - t - 3)) :
    localFractionMass (insert c D) (2 * c - 3) - 1 <
      (2 : ℚ) ^ (2 * c - 3) *
        (localMersennePrefixValue (insert c D) - (1 / 2 : ℚ)) := @Erdos249257.precriticalCrossingTax_of_futureThreshold D c t hc ht hD hres hroom

theorem paper_real_quotient_core {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) :
    ∃ eta : ℝ,
      (rowDeviation n D : ℝ) = (4 : ℝ)^n *
        ((∑ d ∈ (Finset.Ico 2 n) \ D, mersenneWeight d) -
          (erdosBorweinMersenneConstant-3/2)) + eta ∧
      0 < eta ∧ eta < (n : ℝ)+2/3 ∧ |eta| < 2*(n : ℝ)+2 := @ErdosProblems.Erdos257.PaperCompleteR20.paper_real_quotient_core n hn D hD

theorem paper_real_quotient_margins {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) (H : ℝ) :
    ((H+(2*(n : ℝ)+2))/(4 : ℝ)^n <
      |(∑ d ∈ (Finset.Ico 2 n) \ D, mersenneWeight d) - (erdosBorweinMersenneConstant-3/2)| →
      H < |(rowDeviation n D : ℝ)|) ∧
    (H < |(rowDeviation n D : ℝ)| →
      (H-(2*(n : ℝ)+2))/(4 : ℝ)^n <
      |(∑ d ∈ (Finset.Ico 2 n) \ D, mersenneWeight d) - (erdosBorweinMersenneConstant-3/2)|) := @ErdosProblems.Erdos257.PaperCompleteR20.paper_real_quotient_margins n hn D hD H

theorem paper_capacity_band_exclusion {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    D.card ≤ c - 2 ∧ c - 2 ≤ 2 ^ (c - 2) ∧
      (Finset.Icc (2 ^ (c - 2)) (2 ^ (c - 2) + (c - 3))).card = c - 2 ∧
      (localBinarySuffix D 1 (2 * c - 2) ∉
          Finset.Icc (2 ^ (c - 2)) (2 ^ (c - 2) + (c - 3)) →
        localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_capacity_band_exclusion D c hc hD hbelow hskip

theorem paper_exact_row_from_skipped_prefix {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * c - 2) ∧
      localPrefixQuotient E (2 * c - 2) = 2 ^ (2 * c - 3) - 1 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_from_skipped_prefix D c hc hD hbelow hskip

theorem paper_finite_row_value_ne_half {D : Finset ℕ} (h0 : 0 ∉ D) :
    localMersennePrefixValue D ≠ (1 / 2 : ℚ) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_row_value_ne_half D h0

theorem paper_fractional_mass_bound_not_necessary :
    localMersennePrefixValue ({2, 3} : Finset ℕ) = 10 / 21 ∧
      localMersennePrefixValue ({2, 3} : Finset ℕ) < (1 / 2 : ℚ) ∧
      localMersennePrefixValue (insert 5 ({2, 3} : Finset ℕ)) = 331 / 651 ∧
      (1 / 2 : ℚ) < localMersennePrefixValue (insert 5 ({2, 3} : Finset ℕ)) ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 = 6 ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 < 8 ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 < 2 ^ (5 - 2) ∧
      localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 = 757 / 651 ∧
      1 < localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 ∧
      localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 =
        localFractionMass ({2, 3} : Finset ℕ) 8 + localMersenneFraction 8 5 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_fractional_mass_bound_not_necessary

theorem paper_fractional_mass_bound_suffices_for_sharp_capacity
    {D : Finset ℕ} {c : ℕ} (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) < localMersennePrefixValue (insert c D))
    (hfrac : localFractionMass (insert c D) (2 * c - 2) ≤ 1) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_fractional_mass_bound_suffices_for_sharp_capacity D c hc hD hbelow hcross hfrac

end PalomarCorpus.E257.PaperStatementsAR
