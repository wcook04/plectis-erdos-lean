/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record sections 6.6.1 to 6.6.5: log-concavity of the Möbius-weighted series; integer recurrences and rational binary series; rational approximation with a squared-Mersenne remainder

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
open scoped ArithmeticFunction.Moebius
open scoped Polynomial

namespace PalomarCorpus.E249_17.Shared
/-- The paper's numerator polynomial `∑_{d ∣ r} μ(d)(r/d) ∑_{j<r/d} X^{dj}`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.paperNumeratorPolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperNumeratorPolynomial (r : ℕ) : Polynomial ℤ :=
  ∑ d ∈ r.divisors,
    Polynomial.C (ArithmeticFunction.moebius d * ((r / d : ℕ) : ℤ)) *
      ∑ j ∈ Finset.range (r / d), (Polynomial.X : Polynomial ℤ) ^ (d * j)
/-- The squarefree kernel used by the numeric shadow: the product of the distinct prime factors of `n`. For `n = 0` this convention gives `1`; all development-facing scaling theorems assume `0 < n`. Local copy of Erdos249257.RadicalMobiusShadow.squarefreeKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def squarefreeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p
end PalomarCorpus.E249_17.Shared

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
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.mobiusMersenneTheta_one_and_two in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusMersenneTheta_one_and_two :
    mobiusMersenneTheta 1 = 1 / 2 ∧
      mobiusMersenneTheta 2
        = (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) - 1 / 2 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.theta_hankel_det_neg in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem theta_hankel_det_neg (r : ℕ) (hr : 1 ≤ r) :
    Matrix.det (Matrix.of
        ![![mobiusMersenneTheta r, mobiusMersenneTheta (r + 1)],
          ![mobiusMersenneTheta (r + 1), mobiusMersenneTheta (r + 2)]]) < 0 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.theta_hankel_two_neg in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem theta_hankel_two_neg (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2)
        - mobiusMersenneTheta (r + 1) ^ 2 < 0 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.theta_strict_logConcave in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem theta_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2)
      < mobiusMersenneTheta (r + 1) ^ 2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsBG

namespace PalomarCorpus.E249.PaperStatementsAK
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.twoAtom_hankel_gap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem twoAtom_hankel_gap (r : ℕ) :
    (1 - 1 / (3 : ℝ) ^ (r + 1)) ^ 2
        - (1 - 1 / (3 : ℝ) ^ r) * (1 - 1 / (3 : ℝ) ^ (r + 2))
      = 4 / (3 : ℝ) ^ (r + 2) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.twoAtom_strict_logConcave in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem twoAtom_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    (1 - 1 / (3 : ℝ) ^ r) * (1 - 1 / (3 : ℝ) ^ (r + 2))
      < (1 - 1 / (3 : ℝ) ^ (r + 1)) ^ 2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAK

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
export PalomarCorpus.E249_17.Shared (squarefreeKernel)
/-- Explicit three-way phase form of one foreign channel. Local copy of Erdos249257.DiagonalFreshLossBridge.foreignChannelPhaseTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def foreignChannelPhaseTerm (d H s : ℕ) : ℤ :=
  if d ∣ 2 * H + s then
    ArithmeticFunction.moebius d * ((((2 * H + s) / d : ℕ) : ℤ))
  else if d ∣ H + s then
    -(ArithmeticFunction.moebius d * ((((H + s) / d : ℕ) : ℤ)))
  else 0
/-- The paper's `d`-summand of the complementary sum at height `H`, offset `s`: `μ(d)((2H+s)/d · 1_{d ∣ 2H+s} - (H+s)/d · 1_{d ∣ H+s})`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.complementSummand, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def complementSummand (d H s : ℕ) : ℚ :=
  (ArithmeticFunction.moebius d : ℚ) *
    (((2 * H + s : ℕ) : ℚ) / (d : ℚ) * (if d ∣ 2 * H + s then 1 else 0) -
      ((H + s : ℕ) : ℚ) / (d : ℚ) * (if d ∣ H + s then 1 else 0))
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.abs_mobiusSquareTail_le_paper in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem abs_mobiusSquareTail_le_paper (D : ℕ) :
    |∑' k : ℕ,
        ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
          (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2)| ≤
      4 / (3 * (((2 : ℝ) ^ (D + 1) - 1) ^ 2)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.abs_moebius_cast_le_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem abs_moebius_cast_le_one (d : ℕ) :
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.complementSummand_eq_phaseTerm in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem complementSummand_eq_phaseTerm {d H s : ℕ} (hd : 0 < d) (hdH : ¬d ∣ H) :
    complementSummand d H s = ((foreignChannelPhaseTerm d H s : ℤ) : ℚ) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.complementSummand_low_double_echo in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem complementSummand_low_double_echo {d H s : ℕ} (_hH : 0 < H) (_hd : 0 < d)
    (hdH : ¬d ∣ H) (hLow : d ∣ H + s) :
    complementSummand d H s =
        -((ArithmeticFunction.moebius d : ℚ) * ((H + s : ℕ) : ℚ) / (d : ℚ)) ∧
      complementSummand d H (2 * s) =
        2 * ((ArithmeticFunction.moebius d : ℚ) * ((H + s : ℕ) : ℚ) / (d : ℚ)) ∧
      (d ∣ 2 * H + 2 * s ∧ ¬d ∣ H + 2 * s) ∧
      complementSummand d H (2 * s) = -2 * complementSummand d H s := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.divisorIndex_endpoint_behaviour in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem divisorIndex_endpoint_behaviour {d H s : ℕ} (hdH : d ∣ H) :
    (d ∣ 2 * H + s ↔ d ∣ s) ∧ (d ∣ H + s ↔ d ∣ s) ∧
      (ArithmeticFunction.moebius d : ℚ) * ((2 * H + s : ℕ) : ℚ) / (d : ℚ) -
          (ArithmeticFunction.moebius d : ℚ) * ((H + s : ℕ) : ℚ) / (d : ℚ) =
        (ArithmeticFunction.moebius d : ℚ) * (H : ℚ) / (d : ℚ) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.doubling_tempered_sequence_eq_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem doubling_tempered_sequence_eq_zero
    (d : ℕ → ℝ) (hrec : ∀ N : ℕ, d (N + 1) = 2 * d N)
    (hlittleO :
      Filter.Tendsto (fun N : ℕ ↦ d N / (2 : ℝ) ^ N) Filter.atTop (nhds 0)) :
    ∀ N : ℕ, d N = 0 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.mersenne_geometric_shift in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenne_geometric_shift (D j : ℕ) :
    (2 : ℝ) ^ j * ((2 : ℝ) ^ (D + 1) - 1) ≤ (2 : ℝ) ^ (D + 1 + j) - 1 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.squarefreeKernel_eq_prod_primeFactors in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem squarefreeKernel_eq_prod_primeFactors (H : ℕ) :
    squarefreeKernel H = ∏ p ∈ H.primeFactors, p := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.sum_divisorIndices_mobius in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sum_divisorIndices_mobius (H s : ℕ) (hH : 0 < H) :
    ∑ d ∈ {d ∈ H.divisors | d ∣ s},
        (ArithmeticFunction.moebius d : ℚ) * (H : ℚ) / (d : ℚ) =
      (H : ℚ) * (Nat.totient (Nat.gcd H s) : ℚ) / (Nat.gcd H s : ℚ) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.sum_divisors_moebius_div_eq_totient_div in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sum_divisors_moebius_div_eq_totient_div {g : ℕ} (hg : 0 < g) :
    ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℚ) / (d : ℚ) =
      (Nat.totient g : ℚ) / (g : ℚ) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientDifference_doubling_seam in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totientDifference_doubling_seam (H r : ℕ) (hH : Even H) :
    (Even r →
        (Nat.totient (4 * H + 2 * r) : ℤ) - (Nat.totient (2 * H + 2 * r) : ℤ) =
          2 * ((Nat.totient (2 * H + r) : ℤ) - (Nat.totient (H + r) : ℤ))) ∧
      (Odd r →
        (Nat.totient (4 * H + 2 * r) : ℤ) - (Nat.totient (2 * H + 2 * r) : ℤ) =
          (Nat.totient (2 * H + r) : ℤ) - (Nat.totient (H + r) : ℤ)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientDifference_eq_divisorPart_add_complement in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totientDifference_eq_divisorPart_add_complement (H s : ℕ) (hH : 0 < H) :
    (Nat.totient (2 * H + s) : ℚ) - (Nat.totient (H + s) : ℚ) =
      (H : ℚ) * (Nat.totient (Nat.gcd H s) : ℚ) / (Nat.gcd H s : ℚ) +
        ∑ d ∈ {d ∈ Finset.Icc 1 (2 * H + s) | ¬d ∣ H}, complementSummand d H s := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_eq_half_add_moebius_sq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totientSeries_eq_half_add_moebius_sq :
    (∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ)) =
      1 / 2 +
        ∑' d : ℕ+,
          ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) /
            (((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_pnat_form in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totientSeries_pnat_form :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) =
      ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totient_eq_mobius_divisor_sum in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_eq_mobius_divisor_sum (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℤ) =
      ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * ((n / d : ℕ) : ℤ) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totient_two_mul_even in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_two_mul_even {n : ℕ} (hn : Even n) :
    Nat.totient (2 * n) = 2 * Nat.totient n := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totient_two_mul_odd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_two_mul_odd {n : ℕ} (hn : Odd n) :
    Nat.totient (2 * n) = Nat.totient n := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tsum_quarter_geometric in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_quarter_geometric : ∑' j : ℕ, ((1 : ℝ) / 4) ^ j = 4 / 3 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAE

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
open Finset
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- The integer prefix `Φ_N = ∑_{n=0}^{N} φ(n)·2^{N-n}` of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_eq_coefficient_mul_series in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tailDifference_eq_coefficient_mul_series (H : ℕ) :
    totientTail (2 * H) - totientTail H =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) +
        (((totientPrefix H : ℕ) : ℝ) - ((totientPrefix (2 * H) : ℕ) : ℝ)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_sub_rationalApproximation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tailDifference_sub_rationalApproximation (H D : ℕ) :
    totientTail (2 * H) - totientTail H -
        (((totientPrefix H : ℕ) : ℝ) - ((totientPrefix (2 * H) : ℕ) : ℝ) +
          (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
            (1 / 2 +
              ∑ d ∈ Finset.Icc 1 D,
                ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
                  (((2 : ℝ) ^ d - 1) ^ 2))) =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
        ∑' k : ℕ,
          ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
            (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAX

namespace PalomarCorpus.E249.PaperStatementsAQ
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial
export PalomarCorpus.E249_17.Shared (paperNumeratorPolynomial squarefreeKernel)
/-- The natural coefficient in the gcd-word presentation. Local copy of Erdos249257.RepunitMobiusNumerator.gcdWordCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def gcdWordCoeff (r k : ℕ) : ℕ :=
  (r / r.gcd k) * (r.gcd k).totient
/-- `1 + X^d + ... + X^((q - 1)d)`. Local copy of Erdos249257.RepunitMobiusNumerator.spacedRepunit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def spacedRepunit (d q : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range q, Polynomial.monomial (d * j) 1
/-- The divisor-signed polynomial numerator. For positive `r`, evaluation at `X = 2` is the common-denominator Möbius numerator; the public bridge below is stated only on the formal development.s squarefree boundary. Local copy of Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusNumeratorPolynomial (r : ℕ) : ℤ[X] :=
  ∑ d ∈ r.divisors,
    Polynomial.C (ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))) *
      spacedRepunit d (r / d)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperNumeratorPolynomial_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperNumeratorPolynomial_eq (r : ℕ) :
    paperNumeratorPolynomial r = mobiusNumeratorPolynomial r := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.sum_divisorIndices_radical_form in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sum_divisorIndices_radical_form (H s : ℕ) (hH : 0 < H) :
    ∑ d ∈ {d ∈ H.divisors | d ∣ s},
        ArithmeticFunction.moebius d * ((H / d : ℕ) : ℤ) =
      ((H / squarefreeKernel H : ℕ) : ℤ) *
        (gcdWordCoeff
          (squarefreeKernel H) s : ℤ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAQ

namespace PalomarCorpus.E249.PaperStatementsAO
open scoped BigOperators
open scoped Polynomial
export PalomarCorpus.E249_17.Shared (paperNumeratorPolynomial)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.mersenne_dvd_of_dvd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenne_dvd_of_dvd {d r : ℕ} (hd : d ∣ r) :
    (2 ^ d - 1 : ℕ) ∣ (2 ^ r - 1 : ℕ) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_coeff_eq_gcd_divisor_sum in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperNumerator_coeff_eq_gcd_divisor_sum {r k : ℕ} (hr : Squarefree r)
    (hk : k < r) :
    (paperNumeratorPolynomial r).coeff k =
      ∑ d ∈ (Nat.gcd r k).divisors,
        ArithmeticFunction.moebius d * ((r / d : ℕ) : ℤ) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_coeff_eq_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperNumerator_coeff_eq_zero {r k : ℕ} (hr : Squarefree r) (hk : r ≤ k) :
    (paperNumeratorPolynomial r).coeff k = 0 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_coeff_pos in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperNumerator_coeff_pos {r k : ℕ} (hr : Squarefree r) (hk : k < r) :
    0 < (paperNumeratorPolynomial r).coeff k := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eq_gcdWordForm in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperNumerator_eq_gcdWordForm {r : ℕ} (hr : Squarefree r) :
    paperNumeratorPolynomial r =
      ∑ k ∈ Finset.range r,
        Polynomial.C (((r / Nat.gcd r k) * Nat.totient (Nat.gcd r k) : ℕ) : ℤ) *
          (Polynomial.X : Polynomial ℤ) ^ k := by
  sorry
end PalomarCorpus.E249.PaperStatementsAO
