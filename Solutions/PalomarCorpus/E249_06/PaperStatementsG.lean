/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerCertificatesT64
import Erdos249257.TotientTailCarryPeriod
import ErdosProblems.Erdos249.CyclotomicAnchoredKill
import ErdosProblems.Erdos249.PaperCompleteR20.FiniteCertificateBatch
import ErdosProblems.Erdos249.PaperCompleteR21.DiagonalCertificateTableScales
import ErdosProblems.Erdos249.PaperCompleteR21.FourLinearConstructionLimits
import ErdosProblems.Erdos249.PaperCompleteR21.TotientBlockConcatenation
import Solutions.PalomarCorpus.E249_06.Statement

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsG
export PalomarCorpus.E249_06.Shared (diagonalPincerCertificateScalesThroughT64 diagonalPincerKillDepthThroughT64)

noncomputable def diagonalPincerCertificateScales : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17]

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

noncomputable def totientAdjugateTailCost
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (x : ι → ℕ) : ℚ :=
  ∑ i, |w i| * (2 * ((x i : ℚ) + 1) + ((x i : ℚ) + 2))

noncomputable def totientBlock (H N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range H,
    (Nat.totient (N + 1 + j) : ℤ) * 2 ^ (H - 1 - j)

theorem historical_table_size_and_initial_depths :
    diagonalPincerCertificateScalesThroughT64.length = 28 ∧
    diagonalPincerCertificateScalesThroughT64.Nodup ∧
    diagonalPincerCertificateScalesThroughT64.getLast? = some 64 ∧
    ([1,2,3,4,5,7,8,9,11,13,16,17].map diagonalPincerKillDepthThroughT64) =
      [6,5,7,7,9,14,15,14,21,22,23,26] := @ErdosProblems.Erdos249.PaperCompleteR20.historical_table_size_and_initial_depths

theorem sixteen_certificate_windows :
    certificateWindowIndices 16 14 9 = Finset.Icc 15 39 ∧
      (certificateWindowIndices 16 14 9).card = 25 := @ErdosProblems.Erdos249.PaperCompleteR20.sixteen_certificate_windows

theorem small_certificate_windows :
    certificateWindowIndices 8 12 16 = Finset.Icc 13 36 ∧
      (certificateWindowIndices 8 12 16).card = 24 := @ErdosProblems.Erdos249.PaperCompleteR20.small_certificate_windows

theorem b6_adjugate_tail_cost_floor
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (x : ι → ℕ)
    (hisolate : ∑ i, w i * (Nat.totient (x i) : ℚ) = 1) :
    (1 : ℚ) ≤ ∑ i, |w i| * (Nat.totient (x i) : ℚ)
      ∧ (∑ i, |w i| * (Nat.totient (x i) : ℚ)) ≤ ∑ i, |w i| * (x i : ℚ)
      ∧ totientAdjugateTailCost w x = ∑ i, |w i| * (3 * (x i : ℚ) + 4)
      ∧ (3 : ℚ) ≤ totientAdjugateTailCost w x
      ∧ ¬ totientAdjugateTailCost w x < 1 := @ErdosProblems.Erdos249.PaperCompleteR21.b6_adjugate_tail_cost_floor ι inferInstance w x hisolate

theorem b6_compressed_adjoint_identity_impossible
    {Q v : ℕ} (hQ : 0 < Q) (hv : 0 < v) {A b : ℤ}
    (hA : A ≠ 0) (hid : (Q : ℤ) * (v : ℤ) * A = b) :
    ¬ |b| < (Q : ℤ) * (v : ℤ) := @ErdosProblems.Erdos249.PaperCompleteR21.b6_compressed_adjoint_identity_impossible Q v hQ hv A b hA hid

theorem b6_rankOneSubrankQuotient_sub_totientSeries_offset_gt
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 480 <
      (∑ d ∈ Finset.Icc 1 Y,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ (e + 2)) ^ 2 /
        (∑ d ∈ Finset.Icc 1 Y,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ (2 * e + 2)) -
        ((∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2) := @ErdosProblems.Erdos249.PaperCompleteR21.b6_rankOneSubrankQuotient_sub_totientSeries_offset_gt e Y he hY

theorem diagonalPincerCertificateScales_list :
    diagonalPincerCertificateScales = [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17] := @ErdosProblems.Erdos249.PaperCompleteR21.diagonalPincerCertificateScales_list

theorem diagonalPincerKillDepth_list :
    diagonalPincerCertificateScales.map diagonalPincerKillDepth =
      [6, 5, 7, 7, 9, 14, 15, 14, 21, 22, 23, 26] := @ErdosProblems.Erdos249.PaperCompleteR21.diagonalPincerKillDepth_list

theorem totientBlock_eq_paper_indexed_sum (a N : ℕ) :
    totientBlock a N
      = ∑ j ∈ Finset.Icc 1 a, (Nat.totient (N + j) : ℤ) * 2 ^ (a - j) := @ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_eq_paper_indexed_sum a N

end PalomarCorpus.E249.PaperStatementsG
