/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #243, record sections 10 to B: when the negative error is periodic; bounded increases and coprimality to earlier moduli; a lower bound on the error forces eventual zero

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #243, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #243 remains open, and no theorem in
this entry decides it.
-/

open Filter
open scoped BigOperators
open scoped Topology

namespace PalomarCorpus.E243_08.Shared
/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. Local copy of ErdosProblems.Erdos243.centeredState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
end PalomarCorpus.E243_08.Shared

namespace PalomarCorpus.E243.PaperStatementsA
export PalomarCorpus.E243_08.Shared (centeredState sylvesterNext)
/-- States long243:res:crt from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.exists_shiftedBlock_consecutiveMultiples in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_shiftedBlock_consecutiveMultiples
    (B : ℕ) (m : ℕ → ℕ)
    (hm : ∀ i, i < B → 2 ≤ m i)
    (hpair : ∀ i, i < B → ∀ j, j < B → i ≠ j → Nat.Coprime (m i) (m j))
    (L : ℕ) :
    ∃ t, L < t ∧ ∀ i, i < B → m i ∣ t + i := by
  sorry
/-- States long243:res:barrier from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.no_boundedRise_coprimeToEarlierModuli in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_boundedRise_coprimeToEarlierModuli
    (u : ℕ → ℕ) (B : ℕ) (hB : 1 ≤ B)
    (hrise : ∀ n, u (n + 1) ≤ u n + B)
    (hTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    ¬ ∃ m : ℕ → ℕ,
      (∀ i, 2 ≤ m i) ∧
      (∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) ∧
      (∀ i t, i < t → Nat.gcd (m i) (u t) = 1) := by
  sorry
/-- States long243:res:periodic from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.no_periodicNegative_shapeEquation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_periodicNegative_shapeEquation
    (h M : ℕ) (hh : 0 < h) (hM : 0 < M) :
    ¬ ∃ a D C e : ℕ → ℕ,
      (∀ n, 2 ≤ a n) ∧
      (∀ n, 0 < e n) ∧
      (∀ n, e n < a n) ∧
      (∀ n, D (n + 1) = a n * D n) ∧
      (∀ n, C (n + 1) = C n + e n) ∧
      (∀ n, D n + e n = (a n - 1) * C n) ∧
      (∀ n, e (n + h) = e n) ∧
      (∀ n, C (n + h) = C n + M) := by
  sorry
/-- States long243:res:gcdstab, res:gcdstab from the long record and the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.gcd_stabilises_and_reduces in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem gcd_stabilises_and_reduces
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hnegative : ∃ B : ℕ, ∀ N, ∃ t,
      N ≤ t ∧ E t < 0 ∧ -(B : ℤ) ≤ E t) :
    ∃ N g : ℕ, 0 < g ∧
      (∀ n, N ≤ n → Nat.gcd (C n) (D n) = g) ∧
      (∀ n, N ≤ n → 0 < C n / g) ∧
      (∀ n, N ≤ n → Nat.Coprime (C n / g) (D n / g)) ∧
      (∀ n, N ≤ n → C (n + 1) / g + D n / g = a n * (C n / g)) ∧
      (∀ n, N ≤ n → D (n + 1) / g = a n * (D n / g)) := by
  sorry
/-- States long243:res:reduced, res:reduced from the long record and the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.persistent_coprimality in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem persistent_coprimality
    (a u v : ℕ → ℕ)
    (hred : ∀ n, Nat.Coprime (u n) (v n))
    (hu : ∀ n, u (n + 1) + v n = a n * u n)
    (hv : ∀ n, v (n + 1) = a n * v n) :
    (∀ n, Nat.Coprime (a n) (v n)) ∧
    (∀ i j, i ≠ j → Nat.Coprime (a i) (a j)) ∧
    (∀ i t, i < t → Nat.Coprime (a i) (u t)) := by
  sorry
/-- States long243:res:cor from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.boundedNegativePart_sylvesterNext_eventually in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem boundedNegativePart_sylvesterNext_eventually
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry
/-- States long243:res:bounded, res:bounded from the long record and the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.eventuallyBoundedNegativePart_eventually_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem eventuallyBoundedNegativePart_eventually_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  sorry
end PalomarCorpus.E243.PaperStatementsA

namespace PalomarCorpus.E243.PaperStatementsO
open Filter
export PalomarCorpus.E243_08.Shared (centeredState)
/-- States long243:res:gcdsparse from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.sparse_gcd_changes in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sparse_gcd_changes
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hlim : Tendsto (fun n ↦ |(E n : ℝ)| / (C n : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N ↦
      (((Finset.range N).filter (fun j ↦
        Nat.gcd (C j) (D j) < Nat.gcd (C (j + 1)) (D (j + 1)))).card : ℝ) /
          (N : ℝ)) atTop (nhds 0) ∧
    (∀ B L : ℕ, ∃ n, B ≤ n ∧ ∀ j, j ≤ L →
      Nat.gcd (C (n + j)) (D (n + j)) = Nat.gcd (C n) (D n)) := by
  sorry
end PalomarCorpus.E243.PaperStatementsO

namespace PalomarCorpus.E243.PaperStatementsL
open Filter
open scoped BigOperators
export PalomarCorpus.E243_08.Shared (centeredState sylvesterNext)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalDenominator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n
/-- States long243:res:frontier, res:frontier from the long record and the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.canonical_frontier in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canonical_frontier
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
    (∃ N, ∀ n, N ≤ n → E n ≠ 0) ∧
    Tendsto (fun n ↦ |(E n : ℝ)| / (C n : ℝ)) atTop (nhds 0) ∧
    (∀ N B : ℕ, ∃ n, N ≤ n ∧ E n < -(B : ℤ)) ∧
    Tendsto (fun N ↦ ∑ n ∈ Finset.range N,
      max (-(E n : ℝ)) 0 / (C n : ℝ)) atTop atTop := by
  sorry
/-- States long243:res:mass, res:mass, res:massscalar from the long record and the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.finite_negative_mass_paper in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_negative_mass_paper :
    (∀ (C : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, 0 < C n) →
      (∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n) →
      Summable (fun n ↦ max (-(E n : ℝ)) 0 / (C n : ℝ)) →
      ∃ N, ∀ n, N ≤ n → E n = 0) ∧
    (∀ (a C D : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, 0 < C n) →
      (∀ n, C (n + 1) + D n = a n * C n) →
      (∀ n, D (n + 1) = a n * D n) →
      (∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)) →
      Summable (fun n ↦ max (-(E n : ℝ)) 0 / (C n : ℝ)) →
      ∃ N, ∀ n, N ≤ n →
        (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) := by
  sorry
end PalomarCorpus.E243.PaperStatementsL

namespace PalomarCorpus.E243.PaperStatementsD
open Filter
open scoped BigOperators
open scoped Topology
/-- States long243:res:variablerise from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.exists_sparse_prime_coprime_sequence in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_sparse_prime_coprime_sequence :
    ∃ (p : ℕ → ℕ) (u : ℕ → ℕ),
      StrictMono p ∧ (∀ i, Nat.Prime (p i)) ∧
      StrictMono u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop atTop ∧
      (∀ i n, Nat.Coprime (u n) (p i)) ∧
      (∃ Cst : ℝ, ∀ n, ((u (n + 1) : ℝ) - (u n : ℝ))
          ≤ Cst * Real.sqrt (Real.log (Real.log ((u n : ℝ) + Real.exp (Real.exp 1))))) ∧
      Tendsto (fun n => ((u (n + 1) : ℝ) - (u n : ℝ))
          / Real.log (Real.log ((u n : ℝ) + 3))) atTop (𝓝 0) := by
  sorry
end PalomarCorpus.E243.PaperStatementsD

namespace PalomarCorpus.E243.PaperStatementsI
open Filter
open scoped Topology
open scoped BigOperators
/-- The exact real-valued normaliser from the inclusive boundary. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.recordLogLog, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2
/-- The positive integers divisible by none of the moduli: the set the paper enumerates as `(u n)`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.Avoids, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Avoids (m : ℕ → ℕ) (n : ℕ) : Prop := 0 < n ∧ ∀ j, ¬ (m j ∣ n)
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

namespace PalomarCorpus.E243.PaperStatementsK
/-- Numerator of the forced normalized constant-negative update. Local copy of ErdosProblems.Erdos243.forcedNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def forcedNumerator (n : ℕ) (a : ℤ) : ℤ :=
  (n + 1 : ℤ) * a ^ 2 - (n + 2 : ℤ) * a + (n + 3 : ℤ)
/-- Exact survival predicate for the first `remaining` forced divisions. Local copy of ErdosProblems.Erdos243.ForcedSurvives, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ForcedSurvives : ℕ → ℕ → ℤ → Prop
  | 0, _, _ => True
  | remaining + 1, index, a =>
      let d : ℤ := index + 2
      d ∣ forcedNumerator index a ∧
        ForcedSurvives remaining (index + 1)
          (forcedNumerator index a / d)
/-- States long243:res:residue from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.forcedOrbit_survives_iff_of_factorial_modEq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem forcedOrbit_survives_iff_of_factorial_modEq
    (h : ℕ) (a b : ℤ)
    (hab : a ≡ b [ZMOD ((h + 1).factorial : ℤ)]) :
    ForcedSurvives h 0 a ↔ ForcedSurvives h 0 b := by
  sorry
/-- States long243:res:residue, res:residue from the long record and the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.forcedSurvives_iff_of_modEq_factorial in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem forcedSurvives_iff_of_modEq_factorial
    {h : ℕ} {a b : ℤ}
    (hab : a ≡ b [ZMOD ((h + 1).factorial : ℤ)]) :
    ForcedSurvives h 0 a ↔ ForcedSurvives h 0 b := by
  sorry
end PalomarCorpus.E243.PaperStatementsK
