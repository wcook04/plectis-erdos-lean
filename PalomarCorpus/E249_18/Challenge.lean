/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record sections 6.6.5 to 6.6.9: a numerator polynomial with explicit positive coefficients; exact dyadic comparisons and tail bounds; squared distances between complex phases

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open scoped Polynomial
open Finset
open scoped ArithmeticFunction.Moebius

namespace PalomarCorpus.E249_18.Shared
/-- The coefficient of the #249 constant in `R_(2H) - R_H`. Local copy of Erdos249257.FullTargetPrimeAdjunctionNoGo.diagonalCoefficient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalCoefficient (H : ℕ) : ℕ := 2 ^ H * (2 ^ H - 1)
/-- Closed geometric budget for every omitted channel when `2H ≤ D`. Local copy of Erdos249257.ActualForeignResidueProjection.foreignComplementBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def foreignComplementBound (H D : ℕ) : ℝ :=
  (diagonalCoefficient H : ℝ) *
    (2 / (2 : ℝ) ^ D + 4 / (3 * (4 : ℝ) ^ D))
/-- The Mersenne denominator at exponent `n`. Local copy of Erdos249257.RadicalMobiusShadow.mersenne, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenne (n : ℕ) : ℕ := 2 ^ n - 1
/-- The integral numerator, written as its squarefree-divisor expansion. For `s ⊆ primeFactors(r)`, put `d = ∏ p ∈ s, p`. Then the summand is `(-1)^|s| (r/d) ((2^r-1)/(2^d-1))`. This is exactly the nonzero part of `Σ_{d ∣ r} μ(d) (r/d) ((2^r-1)/(2^d-1))`: nonsquarefree divisors have Möbius coefficient zero. The subset form makes that finite support explicit and keeps the definition executable without factoring irrelevant divisors. Local copy of Erdos249257.RadicalMobiusShadow.mobiusNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusNumerator (r : ℕ) : ℤ :=
  ∑ s ∈ r.primeFactors.powerset,
    (-1 : ℤ) ^ s.card *
      ((r / s.prod id : ℕ) : ℤ) *
        (((mersenne r) / (mersenne (s.prod id)) : ℕ) : ℤ)
/-- The unscaled radical shadow `B(r) = M_r / (2^r - 1)`. Local copy of Erdos249257.RadicalMobiusShadow.baseMobiusShadow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def baseMobiusShadow (r : ℕ) : ℚ :=
  Rat.divInt (mobiusNumerator r) (mersenne r : ℤ)
/-- The least positive shift sending `N` to a multiple of `d`. Local copy of Erdos249257.ActualForeignResidueProjection.residueOffset, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def residueOffset (d N : ℕ) : ℕ := d - N % d
/-- The exact Möbius residue channel whose sum is the local totient tail. Local copy of Erdos249257.ActualForeignResidueProjection.foreignResidueKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def foreignResidueKernel (d N : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    (2 : ℝ) ^ (d - residueOffset d N) *
      (((N + residueOffset d N : ℕ) : ℝ) /
          ((d : ℝ) * ((2 : ℝ) ^ d - 1)) +
        1 / (((2 : ℝ) ^ d - 1) ^ 2))
/-- Contribution of channel `d` to the diagonal `R_(2H) - R_H`. Local copy of Erdos249257.ActualForeignResidueProjection.residueIncrement, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def residueIncrement (d H : ℕ) : ℝ :=
  foreignResidueKernel d (2 * H) - foreignResidueKernel d H
/-- The actual foreign channels up to cutoff `D`; divisor channels are the explicit shadow and are deliberately excluded. Local copy of Erdos249257.ActualForeignResidueProjection.projectedForeignDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def projectedForeignDefect (H D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, if d ∣ H then 0 else residueIncrement d H
/-- The squarefree kernel used by the numeric shadow: the product of the distinct prime factors of `n`. For `n = 0` this convention gives `1`; all development-facing scaling theorems assume `0 < n`. Local copy of Erdos249257.RadicalMobiusShadow.squarefreeKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def squarefreeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p
/-- The numeric shadow at an arbitrary scale. By construction it only sees the distinct prime factors of `H`. Local copy of Erdos249257.RadicalMobiusShadow.numericMobiusShadow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def numericMobiusShadow (H : ℕ) : ℚ :=
  baseMobiusShadow (squarefreeKernel H) / (squarefreeKernel H : ℚ)
/-- The exact rational explicit shadow at an arbitrary scale. Local copy of Erdos249257.FullTargetPrimeAdjunctionNoGo.scaleExplicitShadowRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def scaleExplicitShadowRat (H : ℕ) : ℚ :=
  (H : ℚ) * numericMobiusShadow H
/-- Local copy of Erdos249257.FullTargetPrimeAdjunctionNoGo.scaleExplicitShadow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def scaleExplicitShadow (H : ℕ) : ℝ :=
  (scaleExplicitShadowRat H : ℝ)
end PalomarCorpus.E249_18.Shared

namespace PalomarCorpus.E249.PaperStatementsAO
open scoped BigOperators
open scoped Polynomial
/-- The paper's numerator polynomial `∑_{d ∣ r} μ(d)(r/d) ∑_{j<r/d} X^{dj}`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.paperNumeratorPolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperNumeratorPolynomial (r : ℕ) : Polynomial ℤ :=
  ∑ d ∈ r.divisors,
    Polynomial.C (ArithmeticFunction.moebius d * ((r / d : ℕ) : ℤ)) *
      ∑ j ∈ Finset.range (r / d), (Polynomial.X : Polynomial ℤ) ^ (d * j)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.four_thirds_tsum_eighth_pow_tail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem four_thirds_tsum_eighth_pow_tail (m : ℕ) :
    (4 / 3 : ℝ) * ∑' k : ℕ, ((1 : ℝ) / 8) ^ (m + k + 1) =
      (4 / 21 : ℝ) * ((1 : ℝ) / 8) ^ m := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.mersenneRemainderTail_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneRemainderTail_le {m : ℕ} (hm : 0 < m) :
    ∑' k : ℕ,
        (1 / ((2 : ℝ) ^ (m + k + 1) - 1) - ((1 : ℝ) / 2) ^ (m + k + 1) -
          ((1 : ℝ) / 4) ^ (m + k + 1)) ≤
      (4 / 21 : ℝ) * ((1 : ℝ) / 8) ^ m := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.mersenneRemainder_identity_and_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneRemainder_identity_and_bound {n : ℕ} (hn : 2 ≤ n) :
    1 / ((2 : ℝ) ^ n - 1) - ((1 : ℝ) / 2) ^ n - ((1 : ℝ) / 4) ^ n =
        ((1 : ℝ) / 8) ^ n / (1 - ((1 : ℝ) / 2) ^ n) ∧
      1 / ((2 : ℝ) ^ n - 1) - ((1 : ℝ) / 2) ^ n - ((1 : ℝ) / 4) ^ n ≤
        (4 / 3 : ℝ) * ((1 : ℝ) / 8) ^ n := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.one_sub_half_pow_ge in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_sub_half_pow_ge {n : ℕ} (hn : 2 ≤ n) :
    (3 : ℝ) / 4 ≤ 1 - ((1 : ℝ) / 2) ^ n := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eval_two in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperNumerator_eval_two {r : ℕ} (_hr : Squarefree r) :
    (((paperNumeratorPolynomial r).eval 2 : ℤ) : ℚ) =
      ∑ d ∈ r.divisors,
        (ArithmeticFunction.moebius d : ℚ) * ((r / d : ℕ) : ℚ) *
          (((2 : ℚ) ^ r - 1) / ((2 : ℚ) ^ d - 1)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eval_two_primeSubsetForm in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperNumerator_eval_two_primeSubsetForm {r : ℕ} (hr : Squarefree r) :
    (paperNumeratorPolynomial r).eval 2 =
      ∑ s ∈ r.primeFactors.powerset,
        (-1 : ℤ) ^ s.card * ((r / s.prod id : ℕ) : ℤ) *
          ((((2 ^ r - 1) / (2 ^ s.prod id - 1) : ℕ)) : ℤ) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tsum_eighth_pow_tail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_eighth_pow_tail (m : ℕ) :
    ∑' k : ℕ, ((1 : ℝ) / 8) ^ (m + k + 1) = (1 / 7 : ℝ) * ((1 : ℝ) / 8) ^ m := by
  sorry
end PalomarCorpus.E249.PaperStatementsAO

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
open Finset
/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`: the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
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
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.sum_sq_dist_from_phase_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sum_sq_dist_from_phase_one (h L : ℕ) (T : Finset ℕ) :
    ∑ N ∈ T, ‖windowFirstExp h N L - 1‖ ^ 2 =
      2 * (T.card : ℝ) - 2 * ∑ N ∈ T, (windowFirstExp h N L).re := by
  sorry
end PalomarCorpus.E249.PaperStatementsAX

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
export PalomarCorpus.E249_18.Shared (baseMobiusShadow mersenne mobiusNumerator numericMobiusShadow scaleExplicitShadow scaleExplicitShadowRat squarefreeKernel)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.boundary_pair_at_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem boundary_pair_at_one :
    (1, 0) ∈ (Finset.antidiagonal 1).filter
        (fun p : ℕ × ℕ => 0 < p.1 ∧ Nat.Coprime p.1 p.2) ∧
      ((Finset.antidiagonal 1).filter
        (fun p : ℕ × ℕ => 0 < p.1 ∧ Nat.Coprime p.1 p.2)).card = 1 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.card_coprime_antidiagonal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem card_coprime_antidiagonal (n : ℕ) :
    ((Finset.antidiagonal n).filter
        (fun p : ℕ × ℕ => 0 < p.1 ∧ Nat.Coprime p.1 p.2)).card = Nat.totient n := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.card_mul_sq_le_pairwise_energy in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem card_mul_sq_le_pairwise_energy {α : Type*} [DecidableEq α]
    (T : Finset α) (z : α → ℂ) (P : Finset (α × α)) (δ : ℝ)
    (hP : P ⊆ T.product T) (hδ : 0 ≤ δ)
    (hsep : ∀ p ∈ P, δ ≤ ‖z p.1 - z p.2‖) :
    (P.card : ℝ) * δ ^ 2 ≤ ∑ i ∈ T, ∑ j ∈ T, ‖z i - z j‖ ^ 2 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.scaleExplicitShadow_eq_divisorChannels in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem scaleExplicitShadow_eq_divisorChannels {H : ℕ} (hH : 0 < H) :
    scaleExplicitShadow H =
      (H : ℝ) *
        ∑ d ∈ H.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
            ((d : ℝ) * ((2 : ℝ) ^ d - 1)) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAE

namespace PalomarCorpus.E249.PaperStatementsBE
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
export PalomarCorpus.E249_18.Shared (diagonalCoefficient foreignComplementBound foreignResidueKernel projectedForeignDefect residueIncrement residueOffset)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.divisorChannels_sum_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem divisorChannels_sum_eq (H : ℕ) (_hH : 0 < H) :
    ∑ d ∈ H.divisors, residueIncrement d H =
      (H : ℝ) *
        ∑ d ∈ H.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
            ((d : ℝ) * ((2 : ℝ) ^ d - 1)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.foreignComplementBound_paper in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem foreignComplementBound_paper (H D : ℕ) :
    foreignComplementBound H D =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
        (2 / (2 : ℝ) ^ D + 4 / (3 * (4 : ℝ) ^ D)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.projectedForeignDefect_paper in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem projectedForeignDefect_paper (H D : ℕ) :
    projectedForeignDefect H D =
      ∑ d ∈ Finset.Icc 1 D,
        (if d ∣ H then 0
          else foreignResidueKernel d (2 * H) - foreignResidueKernel d H) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.residueKernel_increment_of_dvd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem residueKernel_increment_of_dvd {d H : ℕ} (hd : 0 < d) (hdvd : d ∣ H) :
    foreignResidueKernel d (2 * H) - foreignResidueKernel d H =
      (H : ℝ) * ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
        ((d : ℝ) * ((2 : ℝ) ^ d - 1)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.residueOffset_of_dvd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem residueOffset_of_dvd {d H : ℕ} (_hd : 0 < d) (hdvd : d ∣ H) :
    residueOffset d H = d ∧ residueOffset d (2 * H) = d := by
  sorry
end PalomarCorpus.E249.PaperStatementsBE

namespace PalomarCorpus.E249.PaperStatementsBK
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open Finset
export PalomarCorpus.E249_18.Shared (baseMobiusShadow diagonalCoefficient foreignComplementBound foreignResidueKernel mersenne mobiusNumerator numericMobiusShadow projectedForeignDefect residueIncrement residueOffset scaleExplicitShadow scaleExplicitShadowRat squarefreeKernel)
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_not_integral_of_separation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tailDifference_not_integral_of_separation {H D : ℕ}
    (hbound :
      |totientTail (2 * H) - totientTail H -
        (scaleExplicitShadow H + projectedForeignDefect H D)| ≤
        foreignComplementBound H D)
    (hsep : ∀ z : ℤ,
      foreignComplementBound H D <
        |scaleExplicitShadow H + projectedForeignDefect H D - (z : ℝ)|) :
    totientTail (2 * H) - totientTail H ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsBK

namespace PalomarCorpus.E249.PaperStatementsAJ
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_gcd_layer_total in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem coprimeLattice_gcd_layer_total {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then (r ^ (g + 1)) ^ (p.1 + p.2) else 0)
      = (r / (1 - r)) ^ 2 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_gcd_layer_total_eq_one_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem coprimeLattice_gcd_layer_total_eq_one_iff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then (r ^ (g + 1)) ^ (p.1 + p.2) else 0))
        = 1 ↔ r = 1 / 2 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_halfOpen_half_eq_series in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem coprimeLattice_halfOpen_half_eq_series :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then (1 / 2 : ℝ) ^ (p.1 + p.2) else 0)
      = ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_halfOpen_sum in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem coprimeLattice_halfOpen_sum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = ∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_lambert_half_eq_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem coprimeLattice_lambert_half_eq_one :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          (1 / 2 : ℝ) ^ (p.1 + p.2) / (1 - (1 / 2 : ℝ) ^ (p.1 + p.2)) else 0) = 1 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_lambert_identity in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem coprimeLattice_lambert_identity {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          r ^ (p.1 + p.2) / (1 - r ^ (p.1 + p.2)) else 0)
      = (r / (1 - r)) ^ 2 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_lambert_rational in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem coprimeLattice_lambert_rational (s : ℚ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∃ v : ℚ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          (s : ℝ) ^ (p.1 + p.2) / (1 - (s : ℝ) ^ (p.1 + p.2)) else 0)
      = (v : ℝ) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_positive_sum in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem coprimeLattice_positive_sum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = (∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1)) - r := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_removed_pair in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem coprimeLattice_removed_pair (a b : ℕ) :
    ((0 < a ∧ Nat.Coprime a b) ∧ ¬ (0 < a ∧ 0 < b ∧ Nat.Coprime a b))
      ↔ (a = 1 ∧ b = 0) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsAK
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tsum_totient_pow_shift in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_totient_pow_shift {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, (Nat.totient n : ℝ) * r ^ n)
      = ∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAK
