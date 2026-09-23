/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #243, record section 7.4: bounds on the error and on the original sequence

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #243, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #243 remains open, and no theorem in
this entry decides it.
-/

open Filter
open scoped Topology
open scoped BigOperators
open Finset

namespace PalomarCorpus.E243_06.Shared
/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. Local copy of ErdosProblems.Erdos243.centeredState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- The original-coordinate product defect at index `n`, the real number `(P n / a n) * (a n ^ 2 / a (n+1) - 1)` where `P n = ∏_{j < n} a j`, which weighs the departure from the Sylvester growth relation by the prefix product; the naturals `P n`, `a n` and `a (n+1)` are cast to the reals. -/
noncomputable def productDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)
/-- The truncated base-two iterated logarithm log₂(log₂(max(4, x))). -/
noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2
/-- The running maximum `max_{k ≤ n} u k` of a natural-valued sequence, given by `runningMax u 0 = u 0` and `runningMax u (n+1) = max (runningMax u n) (u (n+1))`. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- The increment of the running maximum divided by the truncated iterated logarithm of its preceding value. -/
noncomputable def recordLogLogCharge (U : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((runningMax U (n + 1) - runningMax U n : ℕ) : ℝ) / recordLogLog (runningMax U n)
/-- The extended-real limit superior of the normalized running-record increments. -/
noncomputable def recordTheta (U : ℕ → ℕ) : EReal :=
  limsup (fun n ↦ (recordLogLogCharge U n : EReal)) atTop
end PalomarCorpus.E243_06.Shared

namespace PalomarCorpus.E243.PaperStructuresAA
open Filter
export PalomarCorpus.E243_06.Shared (centeredState)
/-- States long243:res:slownegative from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.tail_multiplier_quadratic_lower in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_multiplier_quadratic_lower (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (n : ℕ) (hsmall : 4 * Int.natAbs (E n) < C n) :
    4 * a n ^ 2 ≤ 5 * a (n + 1) + 5 * a n := by
  sorry
end PalomarCorpus.E243.PaperStructuresAA

namespace PalomarCorpus.E243.PaperStructuresAB
open Filter
export PalomarCorpus.E243_06.Shared (centeredState recordLogLog)
/-- An integer height which the paper's normaliser sends to its index. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.binaryTower, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryTower (n : ℕ) : ℕ := 2 ^ (2 ^ n)
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
/-- States long243:res:slownegative from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_unbounded_of_error_not_eventually_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exactOrbit_unbounded_of_error_not_eventually_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → E n = 0) :
    ∀ H : ℕ, ∃ n, H ≤ C n := by
  sorry
/-- States long243:res:slownegative from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.exists_multiplier_ge_four in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_multiplier_ge_four (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n) (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (N : ℕ) (hN : ∀ n, N ≤ n → 4 * Int.natAbs (E n) < C n) (M : ℕ) :
    ∃ t, M ≤ t ∧ N ≤ t ∧ 4 ≤ a t := by
  sorry
/-- States long243:res:slownegative from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.slowNegative_eventually_zero_and_sylvesterNext_unconditional in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem slowNegative_eventually_zero_and_sylvesterNext_unconditional
    (a C D : ℕ → ℕ) (E : ℕ → ℤ) (δ : ℝ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hDstep : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hslow : ∃ N, ∀ n, N ≤ n → E n < 0 →
      -((E n : ℤ) : ℝ) ≤ (1 - δ) * recordLogLog ((C n : ℕ) : ℝ)) :
    (∃ N, ∀ n, N ≤ n → E n = 0) ∧
      ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry
/-- States long243:res:slownegative from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.tail_binaryTower_lower in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_binaryTower_lower (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (N : ℕ) (hN : ∀ n, N ≤ n → 4 * Int.natAbs (E n) < C n) (h4 : 4 ≤ a N) :
    ∀ k, 2 * binaryTower k ≤ a (N + k) := by
  sorry
end PalomarCorpus.E243.PaperStructuresAB

namespace PalomarCorpus.E243.PaperStructuresAE
open Filter
open scoped Topology
export PalomarCorpus.E243_06.Shared (centeredState recordLogLog recordLogLogCharge recordTheta runningMax)
/-- States long243:res:slownegative from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_one_le_recordTheta in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exactOrbit_one_le_recordTheta
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n) (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → E n = 0) :
    (1 : EReal) ≤ recordTheta C := by
  sorry
/-- States long243:res:slownegative from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_recordTheta_gt_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exactOrbit_recordTheta_gt_one
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n) (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → E n = 0) :
    (1 : EReal) < recordTheta C := by
  sorry
end PalomarCorpus.E243.PaperStructuresAE

namespace PalomarCorpus.E243.OriginalCoordinateBoundedDefect
open Filter
export PalomarCorpus.E243_06.Shared (prefixProduct productDefect)
/-- Principal theorem in the problem's own coordinates: if `a` is a strictly increasing sequence of positive integers whose reciprocal series has sum the rational number `p / q` with `q > 0`, whose growth satisfies `a (n+1) / a n ^ 2 → 1` in the reals, and whose product defect `(P n / a n) * (a n ^ 2 / a (n+1) - 1)` is bounded above by one constant `M` from some index onward, then `a (n+1) = a n ^ 2 - a n + 1` in the integers for all large `n`. The upper bound on the product defect is a hypothesis of the statement. It is assumed and not derived from the rational-sum and growth hypotheses. -/
theorem original_coordinate_bounded_defect
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hupper : ∃ M : ℝ, ∃ N, ∀ n, N ≤ n → productDefect a n ≤ M) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  sorry
end PalomarCorpus.E243.OriginalCoordinateBoundedDefect

namespace PalomarCorpus.E243.PaperStatementsL
open Filter
open scoped BigOperators
export PalomarCorpus.E243_06.Shared (prefixProduct productDefect recordLogLog)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
/-- States long243:res:strausbounded from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.original_coordinate_slow_growth_defect in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem original_coordinate_slow_growth_defect
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (δ : ℝ) (hδ : 0 < δ)
    (hslow : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      productDefect a n ≤ (1 - δ) / (q : ℝ) *
        recordLogLog ((prefixProduct a n : ℝ) / (a n : ℝ))) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  sorry
/-- States long243:res:strausbounded from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.prefix_ratio_le_canonicalNumerator in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem prefix_ratio_le_canonicalNumerator
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) (n : ℕ) :
    (prefixProduct a n : ℝ) / (a n : ℝ) ≤
      ((canonicalNaturalNumerator a p q n : ℕ) : ℝ) := by
  sorry
end PalomarCorpus.E243.PaperStatementsL

namespace PalomarCorpus.E243.PaperStatementsR
open Filter
open scoped Topology
export PalomarCorpus.E243_06.Shared (recordLogLog recordLogLogCharge recordTheta runningMax)
/-- States long243:res:strausbounded from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.recordTheta_le_of_slow_negative in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem recordTheta_le_of_slow_negative
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (hE : ∀ n, E n = (D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ))
    (c : ℝ) (hc0 : 0 ≤ c) (N : ℕ)
    (hslow : ∀ n, N ≤ n → -((E n : ℤ) : ℝ) ≤ c * recordLogLog ((C n : ℕ) : ℝ)) :
    recordTheta C ≤ ((c : ℝ) : EReal) := by
  sorry
end PalomarCorpus.E243.PaperStatementsR

namespace PalomarCorpus.E243.PaperStatementsB
open Filter
open Finset
open scoped BigOperators
open scoped Topology
/-- States long243:res:onethreshold, res:inclusiveone from the long record and the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR20.original_coordinate_inclusive_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem original_coordinate_inclusive_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε)
    (hbound : ∃ N : ℕ, ∀ n, N ≤ n →
      (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1 ≤
        1 / (n : ℝ) + K / (n : ℝ) ^ (1 + ε)) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  sorry
/-- States long243:res:onethreshold, res:inclusiveone from the long record and the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR20.original_coordinate_inclusive_one_pointwise in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem original_coordinate_inclusive_one_pointwise
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hbound : ∃ N : ℕ, ∀ n, N ≤ n →
      (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1 ≤ 1 / (n : ℝ)) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  sorry
end PalomarCorpus.E243.PaperStatementsB

namespace PalomarCorpus.E243.PaperStatementsF
open Filter
/-- States long243:res:onethreshold from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.original_coordinate_strict_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem original_coordinate_strict_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (r : ℝ) (hr : r < 1)
    (hlimsup : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) * max ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) 0 ≤ r) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  sorry
end PalomarCorpus.E243.PaperStatementsF
