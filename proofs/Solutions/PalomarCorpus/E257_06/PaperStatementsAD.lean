/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusCriticalCapacityGeometric
import Erdos249257.BooleanMobiusExactRowRankTwo
import Erdos249257.BooleanMobiusExactTransition
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.HalfCylinderIntegerGreedy
import Erdos249257.MersenneShadowCyclotomicNoncollapse
import Erdos249257.MersenneShadowDenominatorGrowth
import Erdos249257.RadicalMobiusShadow
import ErdosProblems.Erdos257.PaperCompleteR21.MersenneChannelSurvivalAllHeights
import ErdosProblems.Erdos257.PaperCompleteR21.OddReciprocalDenominators
import ErdosProblems.Erdos257.PaperCompleteR21.ThreeBranchRowDynamics
import Solutions.PalomarCorpus.E257_06.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAD
export PalomarCorpus.E257_06.Shared (IsRowLower IsRowUpper localMersenneQuotient localPrefixQuotient rowPulse seamSubsetTarget truncatedMersenneWeight)

noncomputable def lcmHeight (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).lcm (fun n ↦ n)

noncomputable def upperHalfPrimes (t : ℕ) : Finset ℕ :=
  (Finset.Ioc (t / 2) t).filter Nat.Prime

noncomputable def mersenne (n : ℕ) : ℕ := 2 ^ n - 1

noncomputable def mobiusNumerator (r : ℕ) : ℤ :=
  ∑ s ∈ r.primeFactors.powerset,
    (-1 : ℤ) ^ s.card *
      ((r / s.prod id : ℕ) : ℤ) *
        (((mersenne r) / (mersenne (s.prod id)) : ℕ) : ℤ)

noncomputable def baseMobiusShadow (r : ℕ) : ℚ :=
  Rat.divInt (mobiusNumerator r) (mersenne r : ℤ)

noncomputable def squarefreeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

noncomputable def numericMobiusShadow (H : ℕ) : ℚ :=
  baseMobiusShadow (squarefreeKernel H) / (squarefreeKernel H : ℚ)

noncomputable def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card

noncomputable def localMersenneGeometricQuotient (M d : ℕ) : ℕ :=
  2 ^ (M % d) * ∑ j ∈ Finset.range (M / d), (2 ^ d) ^ j

noncomputable def paperA (r : ℕ) : ℤ :=
  ∑ d ∈ r.divisors,
    ArithmeticFunction.moebius d * (((r / d : ℕ)) : ℤ) *
      (((mersenne r /
        mersenne d : ℕ)) : ℤ)

noncomputable def paperB (r : ℕ) : ℚ :=
  ∑ d ∈ r.divisors,
    ((ArithmeticFunction.moebius d : ℤ) : ℚ) * ((r : ℚ) / (d : ℚ)) /
      ((2 : ℚ) ^ d - 1)

theorem lcmHeight_scaledMobiusShadow_den_lower_bound
    {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤
      ((lcmHeight t : ℚ) *
        numericMobiusShadow (lcmHeight t)).den := @Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_scaledMobiusShadow_den_lower_bound t ht

theorem upperHalfMersenneProduct_lower_bound {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤
      ∏ p ∈ upperHalfPrimes t, mersenne p := @Erdos249257.MersenneShadowDenominatorGrowth.upperHalfMersenneProduct_lower_bound t ht

theorem exists_boolean_word_of_lt_two_pow
    {V L : ℕ} (hV : V < 2 ^ L) :
    ∃ y : List ℕ,
      y.length = L ∧
      (∀ b ∈ y, b = 0 ∨ b = 1) ∧
      Nat.ofDigits 2 y = V := @Erdos249257.exists_boolean_word_of_lt_two_pow V L hV

theorem localMersenneQuotient_eq_geometric
    {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient M d = localMersenneGeometricQuotient M d := @Erdos249257.localMersenneQuotient_eq_geometric M d hd

theorem localMersenneQuotient_eq_two_pow_sub_of_half_lt
    {M d : ℕ} (hd2 : 2 ≤ d) (hhalf : M / 2 < d) (hdM : d ≤ M) :
    localMersenneQuotient M d = 2 ^ (M - d) := @Erdos249257.localMersenneQuotient_eq_two_pow_sub_of_half_lt M d hd2 hhalf hdM

theorem localPrefixQuotient_succ
    {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D (M + 1) =
      2 * localPrefixQuotient D M +
        endpointDivisorContribution D (M + 1) := @Erdos249257.localPrefixQuotient_succ D M hD

theorem two_mem_of_exact_localMersenneQuotient
    {D : Finset ℕ} {n : ℕ}
    (hn : 3 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) :
    2 ∈ D := @Erdos249257.two_mem_of_exact_localMersenneQuotient D n hn hD hquot

theorem channelProduct_coprime_mobiusNumerator_of_one_le
    {P : Finset ℕ} {t r : ℕ} (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    Nat.Coprime (∏ p ∈ P, mersenne p)
      (mobiusNumerator r).natAbs := @ErdosProblems.Erdos257.PaperCompleteR21.channelProduct_coprime_mobiusNumerator_of_one_le P t r hr hprime hpr hupper hcut

theorem paperA_eq_mobiusNumerator {r : ℕ} (hr : Squarefree r) :
    paperA r = mobiusNumerator r := @ErdosProblems.Erdos257.PaperCompleteR21.paperA_eq_mobiusNumerator r hr

theorem paperB_eq_baseMobiusShadow {r : ℕ} (hr : Squarefree r) :
    paperB r = baseMobiusShadow r := @ErdosProblems.Erdos257.PaperCompleteR21.paperB_eq_baseMobiusShadow r hr

theorem paperB_eq_divInt_paperA {r : ℕ} (hr : Squarefree r) :
    paperB r = Rat.divInt (paperA r) (mersenne r : ℤ) := @ErdosProblems.Erdos257.PaperCompleteR21.paperB_eq_divInt_paperA r hr

theorem paper_channel_factor_gcd_eq_one
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 2 ^ Nat.gcd p q - 1 ∧
      Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 1 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_channel_factor_gcd_eq_one p q hp hq hpq

theorem paper_channel_factors_pairwise_coprime
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime) :
    (P : Set ℕ).Pairwise fun p q => Nat.Coprime (2 ^ p - 1) (2 ^ q - 1) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_channel_factors_pairwise_coprime P hprime

theorem paper_consecutive_not_both_divisible {d m : ℕ} (hd : 2 ≤ d) :
    ¬ (d ∣ m + 1 ∧ d ∣ m + 2) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_consecutive_not_both_divisible d m hd

theorem paper_finite_sum_inv_odd_den_odd {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hodd : ∀ i ∈ s, Odd (f i)) :
    Odd (∑ i ∈ s, (1 : ℚ) / ((f i : ℤ) : ℚ)).den := by
  apply ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_sum_inv_odd_den_odd <;> assumption

theorem paper_finite_sum_inv_odd_ne_half {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hodd : ∀ i ∈ s, Odd (f i)) :
    (∑ i ∈ s, (1 : ℚ) / ((f i : ℤ) : ℚ)) ≠ (1 : ℚ) / 2 := by
  apply ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_sum_inv_odd_ne_half <;> assumption

theorem paper_isRowLower_unique {n : ℕ} (hn : 5 ≤ n) {D D₀ : Finset ℕ}
    (hD : IsRowLower n D) (hD₀ : IsRowLower n D₀) : D = D₀ := by
  apply ErdosProblems.Erdos257.PaperCompleteR21.paper_isRowLower_unique <;> assumption

theorem paper_isRowUpper_unique {n : ℕ} (hn : 5 ≤ n) {B B₀ : Finset ℕ}
    (hB : IsRowUpper n B) (hB₀ : IsRowUpper n B₀) : B = B₀ := by
  apply ErdosProblems.Erdos257.PaperCompleteR21.paper_isRowUpper_unique <;> assumption

theorem paper_mersenne_channel_survival
    (P : Finset ℕ) {t h r : ℕ}
    (ht : 1 ≤ t) (hh : 1 ≤ h) (hr1 : 1 ≤ r) (hrsf : Squarefree r)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p) :
    (∏ p ∈ P, (2 ^ p - 1)) / Nat.gcd (∏ p ∈ P, (2 ^ p - 1)) h ∣
      ((h : ℚ) * paperB r).den := @ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_channel_survival P t h r ht hh hr1 hrsf hcut hprime hpr hupper

theorem paper_mersenne_channel_survival_of_coprime_scale
    (P : Finset ℕ) {t h r : ℕ}
    (ht : 1 ≤ t) (hh : 1 ≤ h) (hr1 : 1 ≤ r) (hrsf : Squarefree r)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hscale : Nat.gcd (∏ p ∈ P, (2 ^ p - 1)) h = 1) :
    (∏ p ∈ P, (2 ^ p - 1)) ∣ ((h : ℚ) * paperB r).den := @ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_channel_survival_of_coprime_scale P t h r ht hh hr1 hrsf hcut hprime hpr hupper hscale

theorem paper_rowLower_existsUnique {n : ℕ} (hn : 5 ≤ n) :
    ∃! D : Finset ℕ, IsRowLower n D := @ErdosProblems.Erdos257.PaperCompleteR21.paper_rowLower_existsUnique n hn

theorem paper_rowPulse_eq_indicators (n d : ℕ) :
    rowPulse n d =
      2 * (if d ∣ 2 * n + 1 then 1 else 0) +
        (if d ∣ 2 * n + 2 then 1 else 0) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_rowPulse_eq_indicators n d

theorem paper_rowQuotient_eq_weightSum (n : ℕ) (S : Finset ℕ) :
    localPrefixQuotient S (2 * n) = ∑ d ∈ S, truncatedMersenneWeight n d := @ErdosProblems.Erdos257.PaperCompleteR21.paper_rowQuotient_eq_weightSum n S

theorem paper_rowTarget_eq (n : ℕ) :
    seamSubsetTarget n = 2 ^ (2 * n - 1) - 2 ^ n := @ErdosProblems.Erdos257.PaperCompleteR21.paper_rowTarget_eq n

theorem paper_rowUpper_existsUnique {n : ℕ} (hn : 5 ≤ n) :
    ∃! B : Finset ℕ, IsRowUpper n B := @ErdosProblems.Erdos257.PaperCompleteR21.paper_rowUpper_existsUnique n hn

theorem paper_rowWeight_eq_floor (n d : ℕ) :
    truncatedMersenneWeight n d = 4 ^ n / (2 ^ d - 1) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_rowWeight_eq_floor n d

theorem upperHalfChannel_survivorProduct_dvd_den_of_one_le
    (P : Finset ℕ) {t r h : ℕ} (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    (∏ p ∈ P, mersenne p) /
        Nat.gcd (∏ p ∈ P, mersenne p) h ∣
      (Rat.divInt ((h : ℤ) * mobiusNumerator r)
        (mersenne r : ℤ)).den := @ErdosProblems.Erdos257.PaperCompleteR21.upperHalfChannel_survivorProduct_dvd_den_of_one_le P t r h hr hprime hpr hupper hcut

end PalomarCorpus.E257.PaperStatementsAD
