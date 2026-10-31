/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record sections 6 to 9: detailed statements; index of unproved conditions

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Matrix
open ArithmeticFunction
open Finset

namespace PalomarCorpus.E249_21.Shared
/-- The binary block of `H` consecutive totient values starting at `N + 1`, most significant weight first: `∑_{j < H} φ(N + 1 + j) 2 ^ (H - 1 - j)`, an integer. It equals `2 ^ H R_N - R_{N + H}` for the binary totient tail `R_N`, and is `0` when `H = 0`. -/
noncomputable def totientBlock (H N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range H,
    (Nat.totient (N + 1 + j) : ℤ) * 2 ^ (H - 1 - j)
/-- The signed binary discrepancy `D_{h,N,L} = ∑_{j < L} (φ(N + h + 1 + j) - φ(N + 1 + j)) 2 ^ (L - 1 - j)` between two length-`L` totient windows separated by the shift `h`, an integer satisfying `|2 ^ L (R_{N + h} - R_N) - D_{h,N,L}| ≤ N + h + L + 2`. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The residue angle used by the first additive character. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstAngle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))
/-- The complex first additive character of the endpoint discrepancy. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstExp, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)
end PalomarCorpus.E249_21.Shared

namespace PalomarCorpus.E249.PaperStatementsBG
open scoped BigOperators
open Matrix
open ArithmeticFunction
/-- The `n`th atom of the Möbius--Mersenne power ladder, with the positive integer index shifted to `n + 1`. Local copy of Erdos249257.SignedQMomentObstruction.mobiusMersenneTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)
/-- The Möbius--Mersenne power ladder `Θᵣ`. Local copy of Erdos249257.SignedQMomentObstruction.mobiusMersenneTheta, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n
/-- The first `Y` atoms of the Möbius--Mersenne rung `r`. Local copy of ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n
/-- The rank-one strict-subrank quotient from the first `Y` atoms. Local copy of ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ :=
  mobiusMersennePrefix Y (e + 2) ^ 2 /
    mobiusMersennePrefix Y (2 * e + 2)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.positive_direct_sum_sub_theta_two_gt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem positive_direct_sum_sub_theta_two_gt
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (e Y : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < w i)
    (he : ∀ i ∈ s, 1 ≤ e i)
    (hY : ∀ i ∈ s, 4 ≤ Y i) :
    (1 : ℝ) / 480 <
      (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) /
          (∑ i ∈ s, w i) -
        mobiusMersenneTheta 2 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.primitive_form_abs_gt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem primitive_form_abs_gt
    {e Y q : ℕ} {p : ℤ}
    (he : 1 ≤ e) (hY : 4 ≤ Y) (hq : 1 ≤ q)
    (hquot :
      rankOneSubrankQuotient e Y = (p : ℝ) / q) :
    (q : ℝ) / 480 <
      |(q : ℝ) * mobiusMersenneTheta 2 - p| := by
  sorry
end PalomarCorpus.E249.PaperStatementsBG

namespace PalomarCorpus.E249.PaperStatementsAJ
export PalomarCorpus.E249_21.Shared (totientBlock)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_four_eval in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cyclotomic_four_eval (x : ℤ) :
    (Polynomial.cyclotomic 4 ℤ).eval x = x ^ 2 + 1 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_four_two_pow_eq_cyclotomic_two in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cyclotomic_four_two_pow_eq_cyclotomic_two (h : ℕ) :
    (Polynomial.cyclotomic 4 ℤ).eval ((2 : ℤ) ^ h) = 2 ^ (2 * h) + 1 ∧
      (Polynomial.cyclotomic 2 ℤ).eval ((2 : ℤ) ^ (2 * h)) = 2 ^ (2 * h) + 1 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_three_eval_two_not_dvd_doubling_chain in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cyclotomic_three_eval_two_not_dvd_doubling_chain :
    (Polynomial.cyclotomic 3 ℤ).eval 2 = 7 ∧
      orderOf ((2 : ℕ) : ZMod 7) = 3 ∧
      (∀ j : ℕ, ¬ (3 ∣ 2 ^ j)) ∧
      (∀ j : ℕ, ¬ (7 ∣ 2 ^ 2 ^ j - 1)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_three_two_pow in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cyclotomic_three_two_pow (h : ℕ) :
    (Polynomial.cyclotomic 3 ℤ).eval ((2 : ℤ) ^ h) = 2 ^ (2 * h) + 2 ^ h + 1 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.orderOf_two_mod_seven in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orderOf_two_mod_seven : orderOf ((2 : ℕ) : ZMod 7) = 3 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.three_not_dvd_two_pow in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem three_not_dvd_two_pow (j : ℕ) : ¬ (3 ∣ 2 ^ j) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_concatenation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totientBlock_concatenation (a b N : ℕ) :
    totientBlock (a + b) N = 2 ^ b * totientBlock a N + totientBlock b (N + a) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_doubling in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totientBlock_doubling (h N : ℕ) :
    totientBlock (2 * h) N = 2 ^ h * totientBlock h N + totientBlock h (N + h) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsG
export PalomarCorpus.E249_21.Shared (totientBlock)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_eq_paper_indexed_sum in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totientBlock_eq_paper_indexed_sum (a N : ℕ) :
    totientBlock a N
      = ∑ j ∈ Finset.Icc 1 a, (Nat.totient (N + j) : ℤ) * 2 ^ (a - j) := by
  sorry
end PalomarCorpus.E249.PaperStatementsG

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_21.Shared (windowDiscrepancy windowFirstAngle windowFirstExp)
/-- Cofinal complex first-harmonic norm saving. This is a checked direct analytic interface, stronger than the already-landed real-part interface. Local copy of Erdos249257.TotientTailPeriodKiller.DTWFirstHarmonicNormGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DTWFirstHarmonicNormGap : Prop :=
  ∀ h : ℕ, 0 < h → ∀ X₀ : ℕ, ∃ X L : ℕ,
    max X₀ 1 ≤ X ∧
    16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
    ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖
      ≤ (21 / 25 : ℝ) * X
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
/-- States thm:hgap-norm from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.blockNormCondition_unfolded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem blockNormCondition_unfolded :
    DTWFirstHarmonicNormGap ↔
      ∀ h : ℕ, 0 < h → ∀ X₀ : ℕ, ∃ X L : ℕ,
        max X₀ 1 ≤ X ∧
        16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
        ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X := by
  sorry
/-- States thm:hgap-subset from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.block_real_part_bound_of_subset_form in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem block_real_part_bound_of_subset_form {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ Finset.Ico X (2 * X),
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := by
  sorry
/-- States thm:hgap-norm from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_block_norm_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_certifiedKill_of_block_norm_bound {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := by
  sorry
/-- States thm:hgap-real from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_block_real_part_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_certifiedKill_of_block_real_part_bound {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ Finset.Ico X (2 * X),
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := by
  sorry
/-- States thm:hgap-subset from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_subset_real_part_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_certifiedKill_of_subset_real_part_bound {h X L : ℕ}
    (T : Finset ℕ)
    (hTlt : ∀ N ∈ T, N < 2 * X)
    (hTne : T.Nonempty)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ T,
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * T.card) :
    ∃ N ∈ T, certifiedKill h N L := by
  sorry
/-- States thm:hgap-norm from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_blockNormCondition in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_blockNormCondition (hgap : DTWFirstHarmonicNormGap) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
export PalomarCorpus.E249_21.Shared (windowDiscrepancy windowFirstAngle windowFirstExp)
/-- Real part of the first additive character of the endpoint discrepancy modulo `2^L`. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstCos, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstCos (h N L : ℕ) : ℝ :=
  Real.cos
    (2 * Real.pi *
      (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
        ((2 ^ L : ℤ) : ℝ)))
/-- States thm:hgap-norm from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.real_part_bound_of_norm_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_part_bound_of_norm_bound {h X L : ℕ} (hX : (0 : ℝ) ≤ X)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    (21 / 25 : ℝ) < 9 / 10 ∧
      (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X := by
  sorry
/-- States thm:hgap-real from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.windowFirstCos_unfolded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem windowFirstCos_unfolded (h N L : ℕ) :
    windowFirstCos h N L
      = Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAU
