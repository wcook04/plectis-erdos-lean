/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band d

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators

namespace PalomarCorpus.E257.PaperStatementsAD
open scoped BigOperators
/-- The exact quotient digit created when the row is multiplied by four. Local copy of Erdos249257.HalfCylinderIntegerGreedy.rowPulse, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rowPulse (s d : ℕ) : ℕ :=
  (if d ∣ 2 * s + 2 then 1 else 0) +
    2 * (if d ∣ 2 * s + 1 then 1 else 0)
/-- The binary-boundary target before any selected divisor weights are removed. Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamSubsetTarget, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s
/-- The exact integer weight contributed at seam rank `s` by selecting a proper divisor rank `d < s`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.truncatedMersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
/-- `Hₜ = lcm(1, ..., t)`. The interval avoids inserting zero into the finite LCM. Local copy of Erdos249257.MersenneShadowCyclotomicNoncollapse.lcmHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmHeight (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).lcm (fun n ↦ n)
/-- Prime indices in the development's upper half `(t/2, t]`. Local copy of Erdos249257.MersenneShadowCyclotomicNoncollapse.upperHalfPrimes, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def upperHalfPrimes (t : ℕ) : Finset ℕ :=
  (Finset.Ioc (t / 2) t).filter Nat.Prime
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
/-- The squarefree kernel used by the numeric shadow: the product of the distinct prime factors of `n`. For `n = 0` this convention gives `1`; all development-facing scaling theorems assume `0 < n`. Local copy of Erdos249257.RadicalMobiusShadow.squarefreeKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def squarefreeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p
/-- The numeric shadow at an arbitrary scale. By construction it only sees the distinct prime factors of `H`. Local copy of Erdos249257.RadicalMobiusShadow.numericMobiusShadow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def numericMobiusShadow (H : ℕ) : ℚ :=
  baseMobiusShadow (squarefreeKernel H) / (squarefreeKernel H : ℚ)
/-- Number of selected lower ranks which divide the next endpoint. Local copy of Erdos249257.endpointDivisorContribution, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card
/-- The quotient of one scaled Mersenne weight written without division: a shift by the Euclidean remainder times a finite geometric word. Local copy of Erdos249257.localMersenneGeometricQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneGeometricQuotient (M d : ℕ) : ℕ :=
  2 ^ (M % d) * ∑ j ∈ Finset.range (M / d), (2 ^ d) ^ j
/-- The integral part of `2^M / (2^d - 1)`. Local copy of Erdos249257.localMersenneQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- Sum of the integral quotient contributions of a finite Boolean support. Local copy of Erdos249257.localPrefixQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d
/-- `D` is the paper's `D_n`: among the quotient sums over subsets of `{2,…,n-1}` it gives the largest sum at most `T_n`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.IsRowLower, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsRowLower (n : ℕ) (D : Finset ℕ) : Prop :=
  D ⊆ Finset.Ico 2 n ∧
    localPrefixQuotient D (2 * n) ≤ seamSubsetTarget n ∧
      ∀ S, S ⊆ Finset.Ico 2 n →
        localPrefixQuotient S (2 * n) ≤ seamSubsetTarget n →
          localPrefixQuotient S (2 * n) ≤ localPrefixQuotient D (2 * n)
/-- `B` is the paper's `B_n`: among the quotient sums over subsets of `{2,…,n-1}` it gives the smallest sum strictly greater than `T_n`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.IsRowUpper, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsRowUpper (n : ℕ) (B : Finset ℕ) : Prop :=
  B ⊆ Finset.Ico 2 n ∧
    seamSubsetTarget n < localPrefixQuotient B (2 * n) ∧
      ∀ S, S ⊆ Finset.Ico 2 n →
        seamSubsetTarget n < localPrefixQuotient S (2 * n) →
          localPrefixQuotient B (2 * n) ≤ localPrefixQuotient S (2 * n)
/-- The paper's integral Möbius numerator `A_r = ∑_{d ∣ r} μ(d) (r/d) (M_r / M_d)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.paperA, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperA (r : ℕ) : ℤ :=
  ∑ d ∈ r.divisors,
    ArithmeticFunction.moebius d * (((r / d : ℕ)) : ℤ) *
      (((mersenne r /
        mersenne d : ℕ)) : ℤ)
/-- The paper's finite rational sum `B(r) = ∑_{d ∣ r} μ(d)(r/d) / (2^d - 1)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.paperB, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperB (r : ℕ) : ℚ :=
  ∑ d ∈ r.divisors,
    ((ArithmeticFunction.moebius d : ℤ) : ℚ) * ((r : ℚ) / (d : ℚ)) /
      ((2 : ℚ) ^ d - 1)
/-- States thm:mersenne-channel-growth from the long record for Erdős problem #257. Transported from Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_scaledMobiusShadow_den_lower_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lcmHeight_scaledMobiusShadow_den_lower_bound
    {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤
      ((lcmHeight t : ℚ) *
        numericMobiusShadow (lcmHeight t)).den := by
  sorry
/-- States thm:mersenne-channel-growth from the long record for Erdős problem #257. Transported from Erdos249257.MersenneShadowDenominatorGrowth.upperHalfMersenneProduct_lower_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem upperHalfMersenneProduct_lower_bound {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤
      ∏ p ∈ upperHalfPrimes t, mersenne p := by
  sorry
/-- States record:257bm-c9 from the long record for Erdős problem #257. Transported from Erdos249257.exists_boolean_word_of_lt_two_pow in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_boolean_word_of_lt_two_pow
    {V L : ℕ} (hV : V < 2 ^ L) :
    ∃ y : List ℕ,
      y.length = L ∧
      (∀ b ∈ y, b = 0 ∨ b = 1) ∧
      Nat.ofDigits 2 y = V := by
  sorry
/-- States record:257bm-i12 from the long record for Erdős problem #257. Transported from Erdos249257.localMersenneQuotient_eq_geometric in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem localMersenneQuotient_eq_geometric
    {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient M d = localMersenneGeometricQuotient M d := by
  sorry
/-- States record:257bm-c9 from the long record for Erdős problem #257. Transported from Erdos249257.localMersenneQuotient_eq_two_pow_sub_of_half_lt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem localMersenneQuotient_eq_two_pow_sub_of_half_lt
    {M d : ℕ} (hd2 : 2 ≤ d) (hhalf : M / 2 < d) (hdM : d ≤ M) :
    localMersenneQuotient M d = 2 ^ (M - d) := by
  sorry
/-- States record:257bm-i1b from the long record for Erdős problem #257. Transported from Erdos249257.localPrefixQuotient_succ in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem localPrefixQuotient_succ
    {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D (M + 1) =
      2 * localPrefixQuotient D M +
        endpointDivisorContribution D (M + 1) := by
  sorry
/-- States record:257bm-i-rank2 from the long record for Erdős problem #257. Transported from Erdos249257.two_mem_of_exact_localMersenneQuotient in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_mem_of_exact_localMersenneQuotient
    {D : Finset ℕ} {n : ℕ}
    (hn : 3 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) :
    2 ∈ D := by
  sorry
/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.channelProduct_coprime_mobiusNumerator_of_one_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem channelProduct_coprime_mobiusNumerator_of_one_le
    {P : Finset ℕ} {t r : ℕ} (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    Nat.Coprime (∏ p ∈ P, mersenne p)
      (mobiusNumerator r).natAbs := by
  sorry
/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paperA_eq_mobiusNumerator in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperA_eq_mobiusNumerator {r : ℕ} (hr : Squarefree r) :
    paperA r = mobiusNumerator r := by
  sorry
/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paperB_eq_baseMobiusShadow in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperB_eq_baseMobiusShadow {r : ℕ} (hr : Squarefree r) :
    paperB r = baseMobiusShadow r := by
  sorry
/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paperB_eq_divInt_paperA in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperB_eq_divInt_paperA {r : ℕ} (hr : Squarefree r) :
    paperB r = Rat.divInt (paperA r) (mersenne r : ℤ) := by
  sorry
/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_channel_factor_gcd_eq_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_channel_factor_gcd_eq_one
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 2 ^ Nat.gcd p q - 1 ∧
      Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 1 := by
  sorry
/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_channel_factors_pairwise_coprime in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_channel_factors_pairwise_coprime
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime) :
    (P : Set ℕ).Pairwise fun p q => Nat.Coprime (2 ^ p - 1) (2 ^ q - 1) := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_consecutive_not_both_divisible in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_consecutive_not_both_divisible {d m : ℕ} (hd : 2 ≤ d) :
    ¬ (d ∣ m + 1 ∧ d ∣ m + 2) := by
  sorry
/-- States record:257bm-i10 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_sum_inv_odd_den_odd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_finite_sum_inv_odd_den_odd {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hodd : ∀ i ∈ s, Odd (f i)) :
    Odd (∑ i ∈ s, (1 : ℚ) / ((f i : ℤ) : ℚ)).den := by
  sorry
/-- States record:257bm-i10 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_sum_inv_odd_ne_half in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_finite_sum_inv_odd_ne_half {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hodd : ∀ i ∈ s, Odd (f i)) :
    (∑ i ∈ s, (1 : ℚ) / ((f i : ℤ) : ℚ)) ≠ (1 : ℚ) / 2 := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_isRowLower_unique in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_isRowLower_unique {n : ℕ} (hn : 5 ≤ n) {D D₀ : Finset ℕ}
    (hD : IsRowLower n D) (hD₀ : IsRowLower n D₀) : D = D₀ := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_isRowUpper_unique in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_isRowUpper_unique {n : ℕ} (hn : 5 ≤ n) {B B₀ : Finset ℕ}
    (hB : IsRowUpper n B) (hB₀ : IsRowUpper n B₀) : B = B₀ := by
  sorry
/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_channel_survival in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_mersenne_channel_survival
    (P : Finset ℕ) {t h r : ℕ}
    (ht : 1 ≤ t) (hh : 1 ≤ h) (hr1 : 1 ≤ r) (hrsf : Squarefree r)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p) :
    (∏ p ∈ P, (2 ^ p - 1)) / Nat.gcd (∏ p ∈ P, (2 ^ p - 1)) h ∣
      ((h : ℚ) * paperB r).den := by
  sorry
/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_channel_survival_of_coprime_scale in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_mersenne_channel_survival_of_coprime_scale
    (P : Finset ℕ) {t h r : ℕ}
    (ht : 1 ≤ t) (hh : 1 ≤ h) (hr1 : 1 ≤ r) (hrsf : Squarefree r)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hscale : Nat.gcd (∏ p ∈ P, (2 ^ p - 1)) h = 1) :
    (∏ p ∈ P, (2 ^ p - 1)) ∣ ((h : ℚ) * paperB r).den := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_rowLower_existsUnique in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowLower_existsUnique {n : ℕ} (hn : 5 ≤ n) :
    ∃! D : Finset ℕ, IsRowLower n D := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_rowPulse_eq_indicators in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowPulse_eq_indicators (n d : ℕ) :
    rowPulse n d =
      2 * (if d ∣ 2 * n + 1 then 1 else 0) +
        (if d ∣ 2 * n + 2 then 1 else 0) := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_rowQuotient_eq_weightSum in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowQuotient_eq_weightSum (n : ℕ) (S : Finset ℕ) :
    localPrefixQuotient S (2 * n) = ∑ d ∈ S, truncatedMersenneWeight n d := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_rowTarget_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowTarget_eq (n : ℕ) :
    seamSubsetTarget n = 2 ^ (2 * n - 1) - 2 ^ n := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_rowUpper_existsUnique in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowUpper_existsUnique {n : ℕ} (hn : 5 ≤ n) :
    ∃! B : Finset ℕ, IsRowUpper n B := by
  sorry
/-- States thm:dynamics from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_rowWeight_eq_floor in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowWeight_eq_floor (n d : ℕ) :
    truncatedMersenneWeight n d = 4 ^ n / (2 ^ d - 1) := by
  sorry
/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.upperHalfChannel_survivorProduct_dvd_den_of_one_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem upperHalfChannel_survivorProduct_dvd_den_of_one_le
    (P : Finset ℕ) {t r h : ℕ} (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    (∏ p ∈ P, mersenne p) /
        Nat.gcd (∏ p ∈ P, mersenne p) h ∣
      (Rat.divInt ((h : ℤ) * mobiusNumerator r)
        (mersenne r : ℤ)).den := by
  sorry
end PalomarCorpus.E257.PaperStatementsAD
