/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band g

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

namespace PalomarCorpus.E249.PaperStatementsG
/-- Local copy of Erdos249257.TotientTailPeriodKiller.diagonalPincerCertificateScales, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalPincerCertificateScales : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17]
/-- Local copy of Erdos249257.TotientTailPeriodKiller.diagonalPincerCertificateScalesThroughT64, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalPincerCertificateScalesThroughT64 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59, 61, 64]
/-- Local copy of Erdos249257.TotientTailPeriodKiller.diagonalPincerKillDepth, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalPincerKillDepth : ℕ → ℕ
  | 1 => 6
  | 2 => 5
  | 3 => 7
  | 4 => 7
  | 5 => 9
  | 7 => 14
  | 8 => 15
  | 9 => 14
  | 11 => 21
  | 13 => 22
  | 16 => 23
  | 17 => 26
  | _ => 0
/-- Local copy of Erdos249257.TotientTailPeriodKiller.diagonalPincerKillDepthThroughT64, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalPincerKillDepthThroughT64 : ℕ → ℕ
  | 1 => 6
  | 2 => 5
  | 3 => 7
  | 4 => 7
  | 5 => 9
  | 7 => 14
  | 8 => 15
  | 9 => 14
  | 11 => 21
  | 13 => 22
  | 16 => 23
  | 17 => 26
  | 19 => 32
  | 23 => 35
  | 25 => 38
  | 27 => 40
  | 29 => 45
  | 31 => 49
  | 32 => 50
  | 37 => 56
  | 41 => 61
  | 43 => 66
  | 47 => 73
  | 49 => 76
  | 53 => 81
  | 59 => 88
  | 61 => 94
  | 64 => 93
  | _ => 0
/-- The crude two-tail cost attached to an inverse/adjugate row. Recovering `φ(x)` as `2 R_(x-1) - R_x` and applying `R_M ≤ M+2` termwise gives the factor `2(x+1) + (x+2)`. Local copy of Erdos249257.totientAdjugateTailCost, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientAdjugateTailCost
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (x : ι → ℕ) : ℚ :=
  ∑ i, |w i| * (2 * ((x i : ℚ) + 1) + ((x i : ℚ) + 2))
/-- The first `H` totient-tail letters at `N`, cleared by `2^H`. Local copy of ErdosProblems.Erdos249.CyclotomicAnchoredKill.totientBlock, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientBlock (H N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range H,
    (Nat.totient (N + 1 + j) : ℤ) * 2 ^ (H - 1 - j)
/-- The arguments of the totient evaluations in a family of two windows. Local copy of ErdosProblems.Erdos249.PaperCompleteR20.certificateWindowIndices, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certificateWindowIndices (H N L : ℕ) : Finset ℕ :=
  (Finset.Icc 1 H).biUnion fun h =>
    (Finset.range L).image (fun j => N + 1 + j) ∪
      (Finset.range L).image (fun j => N + h + 1 + j)
/-- States catalogue:cert:b11, prop:B11-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.historical_table_size_and_initial_depths in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem historical_table_size_and_initial_depths :
    diagonalPincerCertificateScalesThroughT64.length = 28 ∧
    diagonalPincerCertificateScalesThroughT64.Nodup ∧
    diagonalPincerCertificateScalesThroughT64.getLast? = some 64 ∧
    ([1,2,3,4,5,7,8,9,11,13,16,17].map diagonalPincerKillDepthThroughT64) =
      [6,5,7,7,9,14,15,14,21,22,23,26] := by
  sorry
/-- States catalogue:cert:a12 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.sixteen_certificate_windows in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sixteen_certificate_windows :
    certificateWindowIndices 16 14 9 = Finset.Icc 15 39 ∧
      (certificateWindowIndices 16 14 9).card = 25 := by
  sorry
/-- States catalogue:cert:a11 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.small_certificate_windows in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem small_certificate_windows :
    certificateWindowIndices 8 12 16 = Finset.Icc 13 36 ∧
      (certificateWindowIndices 8 12 16).card = 24 := by
  sorry
/-- States prop:b6 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.b6_adjugate_tail_cost_floor in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem b6_adjugate_tail_cost_floor
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (x : ι → ℕ)
    (hisolate : ∑ i, w i * (Nat.totient (x i) : ℚ) = 1) :
    (1 : ℚ) ≤ ∑ i, |w i| * (Nat.totient (x i) : ℚ)
      ∧ (∑ i, |w i| * (Nat.totient (x i) : ℚ)) ≤ ∑ i, |w i| * (x i : ℚ)
      ∧ totientAdjugateTailCost w x = ∑ i, |w i| * (3 * (x i : ℚ) + 4)
      ∧ (3 : ℚ) ≤ totientAdjugateTailCost w x
      ∧ ¬ totientAdjugateTailCost w x < 1 := by
  sorry
/-- States prop:b6 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.b6_compressed_adjoint_identity_impossible in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem b6_compressed_adjoint_identity_impossible
    {Q v : ℕ} (hQ : 0 < Q) (hv : 0 < v) {A b : ℤ}
    (hA : A ≠ 0) (hid : (Q : ℤ) * (v : ℤ) * A = b) :
    ¬ |b| < (Q : ℤ) * (v : ℤ) := by
  sorry
/-- States prop:b6 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.b6_rankOneSubrankQuotient_sub_totientSeries_offset_gt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem b6_rankOneSubrankQuotient_sub_totientSeries_offset_gt
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 480 <
      (∑ d ∈ Finset.Icc 1 Y,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ (e + 2)) ^ 2 /
        (∑ d ∈ Finset.Icc 1 Y,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ (2 * e + 2)) -
        ((∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.diagonalPincerCertificateScales_list in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem diagonalPincerCertificateScales_list :
    diagonalPincerCertificateScales = [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17] := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.diagonalPincerKillDepth_list in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem diagonalPincerKillDepth_list :
    diagonalPincerCertificateScales.map diagonalPincerKillDepth =
      [6, 5, 7, 7, 9, 14, 15, 14, 21, 22, 23, 26] := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_eq_paper_indexed_sum in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totientBlock_eq_paper_indexed_sum (a N : ℕ) :
    totientBlock a N
      = ∑ j ∈ Finset.Icc 1 a, (Nat.totient (N + j) : ℤ) * 2 ^ (a - j) := by
  sorry
end PalomarCorpus.E249.PaperStatementsG
