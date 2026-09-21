/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #243, band i

Erdős problem #243 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E243` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open scoped Topology
open scoped BigOperators

namespace PalomarCorpus.E243.PaperStatementsI
open Filter
open scoped Topology
open scoped BigOperators
/-- The exact real-valued normaliser from the inclusive boundary. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.recordLogLog, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2
/-- The error observable in the inclusive corollary. The negative part is formed in integers first, and then cast into the ordinary real quotient. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.negativeErrorLogLogCharge, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def negativeErrorLogLogCharge (U : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  ((max (-E n) 0 : ℤ) : ℝ) / recordLogLog (U n)
/-- The positive integers divisible by none of the moduli: the set the paper enumerates as `(u n)`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.Avoids, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Avoids (m : ℕ → ℕ) (n : ℕ) : Prop := 0 < n ∧ ∀ j, ¬ (m j ∣ n)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalDenominator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. Local copy of ErdosProblems.Erdos243.centeredState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
/-- States long243:res:loglogboundary from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR11.canonical_negativeError_limsup_gt_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canonical_negativeError_limsup_gt_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
    (1 : EReal) < limsup (fun n ↦ (negativeErrorLogLogCharge C E n : EReal)) atTop := by
  sorry
/-- States long243:res:gapconstant from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.maximal_gap_limsup_eq_inv_sigma in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem maximal_gap_limsup_eq_inv_sigma
    (m : ℕ → ℕ) (hm2 : ∀ j, 2 ≤ m j) (hmono : StrictMono m)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (Cs : ℝ) (hscale : ∀ j, |recordLogLog (m j : ℝ) - (j : ℝ)| ≤ Cs)
    (σ : ℝ) (hσpos : 0 < σ)
    (hσ : Tendsto (fun T => ∏ j ∈ Finset.range T, (1 - 1 / (m j : ℝ))) atTop (nhds σ)) :
    limsup (fun n : ℕ =>
        ((Nat.nth (Avoids m) (n + 1) : ℝ) - (Nat.nth (Avoids m) n : ℝ)) /
          recordLogLog (Nat.nth (Avoids m) n : ℝ)) atTop = σ⁻¹ := by
  sorry
end PalomarCorpus.E243.PaperStatementsI
