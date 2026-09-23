/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR11.InclusiveLimsup
import ErdosProblems.Erdos243.PaperCompleteR11.LogLogNormaliser
import ErdosProblems.Erdos243.PaperCompleteR21.MaximalGapConstant
import ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState
import ErdosProblems.Erdos243.ReciprocalTailRigidity
import Solutions.PalomarCorpus.E243_03.Statement

open Filter
open scoped Topology
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E243.PaperStatementsI
export PalomarCorpus.E243_03.Shared (canonicalDenominator canonicalNaturalNumerator centeredState clearedIntegerNumerator negativeErrorLogLogCharge prefixProduct recordLogLog sylvesterNext)

noncomputable def Avoids (m : ℕ → ℕ) (n : ℕ) : Prop := 0 < n ∧ ∀ j, ¬ (m j ∣ n)

theorem canonical_negativeError_limsup_gt_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
    (1 : EReal) < limsup (fun n ↦ (negativeErrorLogLogCharge C E n : EReal)) atTop := @ErdosProblems.Erdos243.PaperCompleteR11.canonical_negativeError_limsup_gt_one a ha hapos p q hq hs hgrowth hnot

theorem maximal_gap_limsup_eq_inv_sigma
    (m : ℕ → ℕ) (hm2 : ∀ j, 2 ≤ m j) (hmono : StrictMono m)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (Cs : ℝ) (hscale : ∀ j, |recordLogLog (m j : ℝ) - (j : ℝ)| ≤ Cs)
    (σ : ℝ) (hσpos : 0 < σ)
    (hσ : Tendsto (fun T => ∏ j ∈ Finset.range T, (1 - 1 / (m j : ℝ))) atTop (nhds σ)) :
    limsup (fun n : ℕ =>
        ((Nat.nth (Avoids m) (n + 1) : ℝ) - (Nat.nth (Avoids m) n : ℝ)) /
          recordLogLog (Nat.nth (Avoids m) n : ℝ)) atTop = σ⁻¹ := by
  apply ErdosProblems.Erdos243.PaperCompleteR21.maximal_gap_limsup_eq_inv_sigma <;> assumption

end PalomarCorpus.E243.PaperStatementsI
