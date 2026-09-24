/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, record section 6.1: conditional membership tests (part 6 of 6)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open Filter
open Topology
open scoped BigOperators

namespace PalomarCorpus.E257.PaperStatementsAG
open Filter
open Topology
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- **The signed weighted divisor coefficient** `∑_{d ∣ n} w d` for an integer weight `w : ℕ → ℤ`, the Dirichlet incidence `w * 1` with signs. At a Nat weight (cast) this is `weightedCoeff`. Local copy of Erdos249257.intWeightedCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def intWeightedCoeff (w : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, w d
/-- **The signed weighted Erdős series** `∑_a w(a)/(b^a - 1)` for an integer weight. The `a = 0` term is junk-safe (`w(0)/0 = 0`). At a cast Nat weight this is `weightedErdosSeries`; mixed-sign rational coefficient series reduce to it by clearing denominators. Local copy of Erdos249257.intWeightedErdosSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def intWeightedErdosSeries (b : ℕ) (w : ℕ → ℤ) : ℝ :=
  ∑' a : ℕ, ((w a : ℤ) : ℝ) / ((b : ℝ) ^ a - 1)
/-- States thm:multiples-support from the long record for Erdős problem #257. Transported from Erdos249257.erdosSupportSeries_multiples_eq_pow_base_full_support in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem erdosSupportSeries_multiples_eq_pow_base_full_support
    (b d : ℕ) (hb : 2 ≤ b) (hd : 1 ≤ d) :
    erdosSupportSeries b {n : ℕ | d ∣ n}
      = ∑' k : ℕ, (1 : ℝ) / (((b : ℝ) ^ d) ^ (k + 1) - 1) := by
  sorry
/-- States thm:factorial-twopow-support from the long record for Erdős problem #257. Transported from Erdos249257.irrational_erdosSum_two_pow_support in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosSum_two_pow_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (2 ^ k) - 1)) := by
  sorry
/-- States thm:multiples-support from the long record for Erdős problem #257. Transported from Erdos249257.irrational_erdosSupportSeries_multiples in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosSupportSeries_multiples (b d : ℕ) (hb : 2 ≤ b) (hd : 1 ≤ d) :
    Irrational (erdosSupportSeries b {n : ℕ | d ∣ n}) := by
  sorry
/-- States thm:residue-odd from the long record for Erdős problem #257. Transported from Erdos249257.irrational_erdosSupportSeries_residueClass in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosSupportSeries_residueClass
    (b m c : ℕ) (hb : 2 ≤ b) (hm : 0 < m) :
    Irrational (erdosSupportSeries b {n : ℕ | n % m = c % m}) := by
  sorry
/-- States thm:signed-periodic from the long record for Erdős problem #257. Transported from Erdos249257.irrational_intWeightedErdosSeries_periodic_of_coeff_nonneg_of_frequently_ne_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_intWeightedErdosSeries_periodic_of_coeff_nonneg_of_frequently_ne_zero
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n)
    (hc0 : ∀ n : ℕ, 0 < n → 0 ≤ intWeightedCoeff w n)
    (hne : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ intWeightedCoeff w n ≠ 0) :
    Irrational (intWeightedErdosSeries b w) := by
  sorry
/-- States thm:signed-periodic from the long record for Erdős problem #257. Transported from Erdos249257.irrational_intWeightedErdosSeries_periodic_of_coeff_nonpos_of_frequently_ne_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_intWeightedErdosSeries_periodic_of_coeff_nonpos_of_frequently_ne_zero
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n)
    (hc0 : ∀ n : ℕ, 0 < n → intWeightedCoeff w n ≤ 0)
    (hne : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ intWeightedCoeff w n ≠ 0) :
    Irrational (intWeightedErdosSeries b w) := by
  sorry
/-- States thm:signed-periodic from the long record for Erdős problem #257. Transported from Erdos249257.irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n) :
    Irrational (intWeightedErdosSeries b w)
      ∨ ∃ (k : ℕ) (z : ℤ), (b : ℝ) ^ k * intWeightedErdosSeries b w = (z : ℝ) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAG

namespace PalomarCorpus.E257.PaperStatementsAD
open scoped BigOperators
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
