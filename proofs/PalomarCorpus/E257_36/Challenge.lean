/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257: restrictions on a support with rational value; the first crossing of the half-value; gap lengths and the measure of their union

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open ArithmeticFunction
open Filter
open Set
open Topology
open scoped ArithmeticFunction.Omega
open scoped ENNReal
open MeasureTheory
open scoped BigOperators

namespace PalomarCorpus.E257_36.Shared
/-- The three-channel Lambert lower bound for the Mersenne tail `T (k + 1)`. `T (k + 1) = ∑_{v ≥ 1} 2 ^ (-k * v) / (2 ^ v - 1)`; truncating that expansion after `v = 3` gives this rational function of `t = 2 ^ k`, namely `1/t + 1/(3 * t ^ 2) + 1/(7 * t ^ 3)` (equivalently `1 / 2 ^ k + 1 / (3 * 4 ^ k) + 1 / (7 * 8 ^ k)`). Local copy of Erdos249257.HalfGreedyFatalGap.mersenneTailLB3, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTailLB3 (k : ℕ) : ℝ :=
  1 / 2 ^ k + 1 / (3 * (2 ^ k) ^ 2) + 1 / (7 * (2 ^ k) ^ 3)
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The Mersenne tail beyond rank n, namely the sum over k at least 0 of the Mersenne weight at n+k+1. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
end PalomarCorpus.E257_36.Shared

namespace PalomarCorpus.E257.PaperStatementsAV
open ArithmeticFunction
open Filter
open Set
open Topology
export PalomarCorpus.E257_36.Shared (supportCoeff)
/-- States record:257rig-i3 from the long record for Erdős problem #257. Transported from Erdos249257.one_add_mul_card_le_two_mul_shifted_state in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_add_mul_card_le_two_mul_shifted_state
    (A : Set ℕ) (F : Finset ℕ) (c v L : ℕ) (u : ℕ → ℕ)
    (hcL : c < L) (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n)
    (hFA : ∀ a ∈ F, a ∈ A) (hFdvd : ∀ a ∈ F, a ∣ L) :
    1 + v * F.card ≤ 2 * u (L - c - 1) := by
  sorry
/-- States record:257rig-i3 from the long record for Erdős problem #257. Transported from Erdos249257.shifted_state_unbounded_of_infinite_support in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem shifted_state_unbounded_of_infinite_support
    (A : Set ℕ) (hAinf : A.Infinite) (c v : ℕ) (hv : 0 < v)
    (u : ℕ → ℕ) (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n) :
    ∀ B : ℕ, ∃ n : ℕ, B < u n := by
  sorry
end PalomarCorpus.E257.PaperStatementsAV

namespace PalomarCorpus.E257.PaperStatementsAL
open Filter
open Set
open Topology
export PalomarCorpus.E257_36.Shared (supportCoeff)
/-- `f` vanishes at the `h` positive offsets after `N`, namely `N + 1, ..., N + h`. Local copy of Erdos249257.CoeffZeroWindow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CoeffZeroWindow (f : ℕ → ℕ) (N h : ℕ) : Prop :=
  ∀ j : ℕ, j < h → f (N + j + 1) = 0
/-- `supportCoeff A` vanishes on the `h` positive indices immediately after `N`, namely `N + 1, ..., N + h`. Local copy of Erdos249257.SupportCoeffZeroWindow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SupportCoeffZeroWindow (A : Set ℕ) (N h : ℕ) : Prop :=
  CoeffZeroWindow (supportCoeff A) N h
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- States record:257rig-i4a from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_zero_run_le_eps_logb in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_zero_run_le_eps_logb
    (A : Set ℕ) (hinf : A.Infinite) (hzero : 0 ∉ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v) (_hvodd : Odd v)
    (hvalue : erdosSupportSeries 2 A = (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ N h : ℕ, 1 ≤ N →
        SupportCoeffZeroWindow A (c + N) h →
        (h : ℝ) ≤ ε * Real.logb 2 (N : ℝ) + B := by
  sorry
/-- States record:257rig-i4a from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_zero_run_le_of_mem in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_zero_run_le_of_mem
    (A : Set ℕ) {a : ℕ} (hapos : 0 < a) (haA : a ∈ A) {N h : ℕ}
    (hwindow : SupportCoeffZeroWindow A N h) :
    h ≤ a - 1 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAL

namespace PalomarCorpus.E257.PaperStatementsAF
open Set
/-- Completely explicit constant for the fixed-`k` divisor bound. Local copy of Erdos249257.divisorSubpowerConst, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def divisorSubpowerConst (k : ℕ) : ℕ := k ^ (2 ^ k)
/-- States record:257rig-i4b from the long record for Erdős problem #257. Transported from Erdos249257.card_divisors_le_divisorSubpowerConst_mul_rpow in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem card_divisors_le_divisorSubpowerConst_mul_rpow
    (n k : ℕ) (hk : 1 ≤ k) :
    (n.divisors.card : ℝ) ≤
      (divisorSubpowerConst k : ℝ) *
        (n : ℝ) ^ ((k : ℝ)⁻¹) := by
  sorry
/-- States record:257rig-i4b from the long record for Erdős problem #257. Transported from Erdos249257.card_divisors_pow_le_divisorSubpowerConst_pow_mul in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem card_divisors_pow_le_divisorSubpowerConst_pow_mul
    (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) :
    n.divisors.card ^ k ≤ divisorSubpowerConst k ^ k * n := by
  sorry
end PalomarCorpus.E257.PaperStatementsAF

namespace PalomarCorpus.E257.PaperStatementsAO
open Filter
open Topology
open scoped ArithmeticFunction.Omega
export PalomarCorpus.E257_36.Shared (supportCoeff)
/-- The signed coefficient layer between exact `p`-adic levels `e-1` and `e`. Local copy of Erdos249257.MaximalOmegaLayer.primePowerLayer, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primePowerLayer (p e : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  g (p ^ e * n) - g (p ^ (e - 1) * n)
/-- The two-signature mixed layer. Further list-level iteration can use this as its checked algebraic step without committing to a factorization API. Local copy of Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mixedPrimePowerLayerTwo
    (p e q f : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  primePowerLayer q f (primePowerLayer p e g) n
/-- Integer-valued packaging of the support divisor-count coefficient. Local copy of Erdos249257.SupportDilationDifferences.supportCoeffInt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeffInt (A : Set ℕ) (n : ℕ) : ℤ :=
  supportCoeff A n
/-- States record:257rig-i5 from the long record for Erdős problem #257. Transported from Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo_twelve_fixture in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mixedPrimePowerLayerTwo_twelve_fixture :
    mixedPrimePowerLayerTwo 2 2 3 1
      (supportCoeffInt ({12} : Set ℕ)) 1 = 1 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAO

namespace PalomarCorpus.E257.PaperStatementsAR
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators
/-- The exact rational Mersenne weight `1 / (2^n - 1)`. Its meaningful support indices are positive; at index zero Lean's division convention gives zero. Local copy of Erdos249257.mersenneWeightRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
/-- The exact finite Mersenne value of a Boolean lower support. Local copy of Erdos249257.localMersennePrefixValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d
/-- States record:257bm-i-cross2 from the long record for Erdős problem #257. Transported from Erdos249257.exists_first_localMersenne_crossing in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_first_localMersenne_crossing
    {E : Finset ℕ}
    (hE : ∀ d ∈ E, 2 ≤ d)
    (habove : (1 / 2 : ℚ) < localMersennePrefixValue E) :
    ∃ c : ℕ,
      c ∈ E ∧
      4 ≤ c ∧
      localMersennePrefixValue (E.filter fun d ↦ d < c) < (1 / 2 : ℚ) ∧
      (1 / 2 : ℚ) <
        localMersennePrefixValue (insert c (E.filter fun d ↦ d < c)) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAR

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_36.Shared (mersenneTail mersenneWeight)
/-- The positive gap between one Mersenne weight and the tail after it. Local copy of Erdos249257.mersenneGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneGap (n : ℕ) : ℝ :=
  mersenneWeight n - mersenneTail n
/-- States record:257hg-i2 from the long record for Erdős problem #257. Transported from Erdos249257.mersenneGap_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneGap_le {n : ℕ} (hn : 0 < n) :
    mersenneGap n ≤ (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n + 3 * ((1 : ℝ) / 8) ^ n := by
  sorry
/-- States record:257hg-i2 from the long record for Erdős problem #257. Transported from Erdos249257.summable_mersenneGap_shift in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem summable_mersenneGap_shift (N : ℕ) :
    Summable (fun k : ℕ => mersenneGap (N + k + 1)) := by
  sorry
/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_mass_threshold in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_exact_mass_threshold {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) :
    ((u : ℝ) / (2 * L) ≤ mersenneTail k ↔
        (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) ≤ (a : ℝ) / u) ∧
      0 < (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) ∧
      (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) < 2 / 3 := by
  sorry
/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_skip_safe_actual_tail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_sharp_skip_safe_actual_tail {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) < mersenneTail k := by
  sorry
end PalomarCorpus.E257.PaperStatementsAM

namespace PalomarCorpus.E257.PaperStatementsAA
export PalomarCorpus.E257_36.Shared (mersenneTailLB3)
/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_dyadic_skip_test_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_dyadic_skip_test_iff {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) :
    ((u : ℝ) / (2 * L) ≤ 1 / 2 ^ k) ↔ u ≤ a := by
  sorry
/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_gives_three_over_three_t_sub_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_sharp_gives_three_over_three_t_sub_one {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) ≤ 3 / (3 * (2 : ℝ) ^ k - 1) := by
  sorry
/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_skip_safe_lb3 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_sharp_skip_safe_lb3 {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) < mersenneTailLB3 k := by
  sorry
/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_strictly_weaker_realizable in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_sharp_strictly_weaker_realizable :
    ∃ k u L a : ℕ, 1 ≤ k ∧ 0 < u ∧ 0 < a ∧
      2 ^ k * u + a = 2 * L + u ∧ 2 * u ≤ 3 * a ∧ ¬ u ≤ a := by
  sorry
/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_weaker_than_dyadic in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_sharp_weaker_than_dyadic {u a : ℕ} (h : u ≤ a) : 2 * u ≤ 3 * a := by
  sorry
/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_three_channel_margin_identity in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_three_channel_margin_identity {t : ℝ} (ht : 2 ≤ t) :
    (1 / t + 1 / (3 * t ^ 2) + 1 / (7 * t ^ 3)) - 3 / (3 * t - 1) =
        (2 * t - 3) / (21 * t ^ 3 * (3 * t - 1)) ∧
      0 < (2 * t - 3) / (21 * t ^ 3 * (3 * t - 1)) := by
  sorry
/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_two_channels_insufficient in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_two_channels_insufficient :
    1 / (2 : ℝ) + 1 / (3 * (2 : ℝ) ^ 2) < 3 / (3 * (2 : ℝ) - 1) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAA

namespace PalomarCorpus.E257.PaperStructuresH
export PalomarCorpus.E257_36.Shared (mersenneTailLB3)
/-- States record:257hg-i5 from the long record for Erdős problem #257. Transported from Erdos249257.HalfGreedyFatalGap.three_le_of_fatal_of_odd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem three_le_of_fatal_of_odd {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a) (hodd : Odd u)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    3 ≤ u := by
  sorry
/-- States record:257hg-i5 from the long record for Erdős problem #257. Transported from Erdos249257.HalfGreedyFatalGap.two_le_of_fatal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_le_of_fatal {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    2 ≤ u := by
  sorry
/-- States record:257hg-i5 from the long record for Erdős problem #257. Transported from Erdos249257.HalfGreedyFatalGap.unitNumerator_skipSafe in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem unitNumerator_skipSafe {k u L a : ℕ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTailLB3 k := by
  sorry
end PalomarCorpus.E257.PaperStructuresH

namespace PalomarCorpus.E257.PaperStructuresV
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_36.Shared (mersenneTail mersenneWeight)
/-- States record:257hg-i5 from the long record for Erdős problem #257. Transported from Erdos249257.HalfGreedyFatalGap.unitNumerator_skipSafe_actualTail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem unitNumerator_skipSafe_actualTail {k u L a : ℕ}
    {k L a : ℕ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTail k := by
  sorry
end PalomarCorpus.E257.PaperStructuresV
