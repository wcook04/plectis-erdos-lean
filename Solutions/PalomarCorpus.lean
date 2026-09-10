/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos1041.CriticalTwoRootProximity
import Mathlib
import ErdosProblems.Erdos1041.CyclicTrinomialFiberCase
import ErdosProblems.Erdos1041.FirstMergeCriticalValueSeparation
import ErdosProblems.Erdos1041.QuarticQuotientFiberCase
import ErdosProblems.Erdos1041.CubicQuotientFiberCase
import ErdosProblems.Erdos1041.PrimitiveQuinticInteriorTail
import ErdosProblems.Erdos1041.SharpCollinearChebyshev
import ErdosProblems.Erdos1041.CyclicTetranomialCoefficientCase
import ErdosProblems.Erdos1041.TetranomialL2Selector
import ErdosProblems.Erdos1049.AdelicHeightBridge
import ErdosProblems.Erdos1049.HermitePadeNoGo
import ErdosProblems.Erdos1049.QAperyTailDenominator
import ErdosProblems.Erdos1049.TwoSelectorRemainderEscape
import ErdosProblems.Erdos1049.RationalBaseLambert
import ErdosProblems.Erdos243.ReciprocalTailRigidity
import ErdosProblems.Erdos243.ProtectedEpochEnergy
import ErdosProblems.Erdos243.RecordIncrementBarrier
import ErdosProblems.Erdos243.SaturatedSquareTransport
import ErdosProblems.Erdos243.SlowRiseBarrier
import ErdosProblems.Erdos249.CyclotomicAnchoredKill
import Erdos257PeriodNoncollapse.TotientMahlerDefect
import Erdos257PeriodNoncollapse.SignedQMomentObstruction
import ErdosProblems.Erdos249.MobiusMersenneLadderSeparation
import ErdosProblems.Erdos249.RankOneSharpFloor
import ErdosProblems.Erdos249.ResidueClassTotientSeries
import Erdos257PeriodNoncollapse.AllBaseTotientKernel
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos251.FreePairReduction
import ErdosProblems.Erdos251.KernelDenominatorFloor
import ErdosProblems.Erdos251.PolynomialGapSeriesValue
import ErdosProblems.Erdos257.MersenneSubseriesRigidity
import Erdos257PeriodNoncollapse.CertificateKernel
import Erdos257PeriodNoncollapse.SublogDivisorCoverage
import Erdos257PeriodNoncollapse.AllBaseReciprocalSupportIrrationality
import ErdosProblems.Erdos269.DyadicShellSummability
import ErdosProblems.Erdos269.KernelCarryRank
import ErdosProblems.Erdos269.ThreePrimeRunningLcm
import ErdosProblems.Erdos269.CofinalWindowEscapeEquivalence
import ErdosProblems.Erdos68.ChannelIntegralCongruence
import ErdosProblems.Erdos68.CompanionOrbitRationality
import ErdosProblems.Erdos68.PrimeUnitTranslator

import ErdosProblems.Erdos1041.CriticalTwoRootProximity

namespace PalomarCorpus.ExternalVerification1041CriticalGeometry

open Finset

theorem criticalGeometricMean_twoRootProximity
    {n : ℕ} (hn : 2 ≤ n) (z : Fin n → ℂ) (c : ℂ)
    (hne : ∀ k, c - z k ≠ 0)
    (hcrit : ∑ k, (c - z k)⁻¹ = 0)
    {r : ℝ} (hr : 0 < r) (hrn : r ^ n = ∏ k, ‖c - z k‖) :
    ∃ i j : Fin n, i ≠ j ∧ ‖c - z i‖ + ‖c - z j‖ ≤ 2 * r := by
  exact ErdosProblems.Erdos1041.exists_two_roots_dist_sum_le_two_mul_geomMean
    hn z c hne hcrit hr hrn

theorem criticalDiskInverseBalance_twoRootProximity
    {N t δ e : ℝ}
    (hN : 2 ≤ N) (ht1 : t < 1)
    (hδ : 0 < δ) (hδe : δ ≤ e) (hδ1 : δ ≤ 1)
    (hemax : e ≤ 1 + t) (hbal : e ≤ (N - 1) * δ)
    (hstar : N ≤ (1 - t ^ 2) * (1 / δ ^ 2 + (N - 1) / e ^ 2)) :
    δ + e ≤ 2 := by
  exact ErdosProblems.Erdos1041.two_add_le_two_of_disk_inverse_balance
    hN ht1 hδ hδe hδ1 hemax hbal hstar

theorem criticalDiskInverseBalance_twoRootProximity_strict
    {N t δ e : ℝ}
    (hN : 2 ≤ N) (ht1 : t < 1)
    (hδ : 0 < δ) (hδe : δ ≤ e) (hδ1 : δ ≤ 1)
    (hemax : e < 1 + t) (hbal : e ≤ (N - 1) * δ)
    (hstar : N ≤ (1 - t ^ 2) * (1 / δ ^ 2 + (N - 1) / e ^ 2)) :
    δ + e < 2 := by
  exact ErdosProblems.Erdos1041.two_add_lt_two_of_disk_inverse_balance_of_strict_diameter
    hN ht1 hδ hδe hδ1 hemax hbal hstar

noncomputable def nearestSpokeP : ℂ := (999 : ℂ) / 1000

noncomputable def nearestSpokeA : ℂ := ((901 : ℂ) / 902) * nearestSpokeP

noncomputable def nearestSpokeUPlus : ℂ := ((-451 : ℂ) + 780 * Complex.I) / 901

noncomputable def nearestSpokeUMinus : ℂ := ((-451 : ℂ) - 780 * Complex.I) / 901

noncomputable def nearestSpokeRoot : Fin 5 → ℂ
  | 0 => nearestSpokeA
  | 1 => Complex.I * nearestSpokeP
  | 2 => -Complex.I * nearestSpokeP
  | 3 => nearestSpokeP * nearestSpokeUPlus
  | 4 => nearestSpokeP * nearestSpokeUMinus

theorem nearestSpoke_reciprocal_balance :
    ∑ k, (nearestSpokeRoot k)⁻¹ = 0 := by
  simp [Fin.sum_univ_succ, nearestSpokeRoot, nearestSpokeA, nearestSpokeP,
    nearestSpokeUPlus, nearestSpokeUMinus]
  apply Complex.ext <;>
    norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply]

theorem nearestSpoke_unique_nearest_normSq :
    (∀ k : Fin 5, k ≠ 0 →
      Complex.normSq (nearestSpokeRoot 0) < Complex.normSq (nearestSpokeRoot k)) := by
  intro k hk
  fin_cases k <;> norm_num [nearestSpokeRoot, nearestSpokeA, nearestSpokeP,
    nearestSpokeUPlus, nearestSpokeUMinus, Complex.normSq_apply] at *

theorem nearestSpoke_unique_nearest_spoke_escapes :
    (1 : ℝ) <
      (900099 / 902000 : ℝ) * (1 - 1 / 10) *
        (((1 / 10 : ℝ) * (900099 / 902000)) ^ 2 + (999 / 1000) ^ 2) *
        (((1 / 10 : ℝ) * (900099 / 902000)) ^ 2 +
          (1 / 10) * (999 / 1000) ^ 2 + (999 / 1000) ^ 2) := by
  exact ErdosProblems.Erdos1041.nearestSpoke_unique_nearest_spoke_escapes

noncomputable def allStraightRadius : ℂ := (99 : ℂ) / 100

noncomputable def allStraightOmega : ℂ :=
  (-1 : ℂ) / 2 + ((Real.sqrt 3 : ℂ) / 2) * Complex.I

noncomputable def allStraightRoot : Fin 3 → ℂ
  | 0 => allStraightRadius
  | 1 => allStraightRadius * allStraightOmega
  | 2 => allStraightRadius * allStraightOmega ^ 2

noncomputable def allStraightCubic (z : ℂ) : ℂ :=
  z ^ 3 - allStraightRadius ^ 3

private theorem allStraightOmega_quadratic :
    allStraightOmega ^ 2 + allStraightOmega + 1 = 0 := by
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    norm_num [allStraightOmega, pow_two, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> nlinarith

private theorem allStraightOmega_cube : allStraightOmega ^ 3 = 1 := by
  apply sub_eq_zero.mp
  calc allStraightOmega ^ 3 - 1 =
        (allStraightOmega - 1) *
          (allStraightOmega ^ 2 + allStraightOmega + 1) := by ring
    _ = 0 := by rw [allStraightOmega_quadratic, mul_zero]

private theorem allStraightOmega_normSq :
    Complex.normSq allStraightOmega = 1 := by
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  simp [allStraightOmega, Complex.normSq_apply]
  ring_nf
  nlinarith

theorem allStraightCubic_roots :
    ∀ k : Fin 3, allStraightCubic (allStraightRoot k) = 0 := by
  intro k
  fin_cases k
  · simp [allStraightCubic, allStraightRoot]
  · simp [allStraightCubic, allStraightRoot, mul_pow, allStraightOmega_cube]
  · simp [allStraightCubic, allStraightRoot, mul_pow, allStraightOmega_cube]
    rw [show (allStraightOmega ^ 2) ^ 3 =
      (allStraightOmega ^ 3) ^ 2 by ring]
    rw [allStraightOmega_cube]
    ring

theorem allStraightCubic_roots_in_unitDisk :
    ∀ k : Fin 3, ‖allStraightRoot k‖ < 1 := by
  intro k
  have homega : ‖allStraightOmega‖ = 1 := by
    rw [Complex.norm_def, allStraightOmega_normSq]
    norm_num
  fin_cases k <;>
    simp [allStraightRoot, allStraightRadius, homega, norm_pow] <;> norm_num

private theorem allStraight_midpoint_value_of_unit
    (u : ℂ) (hu : u ^ 3 = 1) :
    allStraightCubic (-(allStraightRadius * u) / 2) =
      -(9 / 8 : ℂ) * allStraightRadius ^ 3 := by
  unfold allStraightCubic
  rw [div_pow, neg_pow, mul_pow, hu]
  ring

private theorem allStraight_pair_zero_one :
    allStraightCubic ((allStraightRoot 0 + allStraightRoot 1) / 2) =
      -(9 / 8 : ℂ) * allStraightRadius ^ 3 := by
  rw [show (allStraightRoot 0 + allStraightRoot 1) / 2 =
      -(allStraightRadius * allStraightOmega ^ 2) / 2 by
        simp only [allStraightRoot]
        linear_combination (allStraightRadius / 2) * allStraightOmega_quadratic]
  apply allStraight_midpoint_value_of_unit
  rw [show (allStraightOmega ^ 2) ^ 3 =
    (allStraightOmega ^ 3) ^ 2 by ring]
  rw [allStraightOmega_cube]
  norm_num

private theorem allStraight_pair_zero_two :
    allStraightCubic ((allStraightRoot 0 + allStraightRoot 2) / 2) =
      -(9 / 8 : ℂ) * allStraightRadius ^ 3 := by
  rw [show (allStraightRoot 0 + allStraightRoot 2) / 2 =
      -(allStraightRadius * allStraightOmega) / 2 by
        simp only [allStraightRoot]
        linear_combination (allStraightRadius / 2) * allStraightOmega_quadratic]
  exact allStraight_midpoint_value_of_unit allStraightOmega allStraightOmega_cube

private theorem allStraight_pair_one_two :
    allStraightCubic ((allStraightRoot 1 + allStraightRoot 2) / 2) =
      -(9 / 8 : ℂ) * allStraightRadius ^ 3 := by
  rw [show (allStraightRoot 1 + allStraightRoot 2) / 2 =
      -(allStraightRadius * 1) / 2 by
        simp only [allStraightRoot]
        linear_combination (allStraightRadius / 2) * allStraightOmega_quadratic]
  exact allStraight_midpoint_value_of_unit 1 (by norm_num)

private theorem allStraight_pair_midpoint_value
    (i j : Fin 3) (hij : i ≠ j) :
    allStraightCubic ((allStraightRoot i + allStraightRoot j) / 2) =
      -(9 / 8 : ℂ) * allStraightRadius ^ 3 := by
  fin_cases i <;> fin_cases j <;> simp_all
  · simpa only [neg_mul] using allStraight_pair_zero_one
  · simpa only [neg_mul] using allStraight_pair_zero_two
  · convert allStraight_pair_zero_one using 1 <;> ring
  · simpa only [neg_mul] using allStraight_pair_one_two
  · convert allStraight_pair_zero_two using 1 <;> ring
  · convert allStraight_pair_one_two using 1 <;> ring

theorem allStraightCubic_every_pair_midpoint_escapes :
    ∀ i j : Fin 3, i ≠ j →
      1 < ‖allStraightCubic ((allStraightRoot i + allStraightRoot j) / 2)‖ := by
  intro i j hij
  rw [allStraight_pair_midpoint_value i j hij, norm_mul, norm_neg]
  norm_num [allStraightRadius, norm_pow]

end PalomarCorpus.ExternalVerification1041CriticalGeometry

import Mathlib
import ErdosProblems.Erdos1041.CyclicTrinomialFiberCase

namespace PalomarCorpus.ExternalVerification1041CyclicTrinomialFiber

theorem trinomialRoot_spoke_factorization
    {m r : ℕ} {a c w : ℂ} {u : ℝ}
    (hroot : w ^ m + a * w ^ r + c = 0) :
    (u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c =
      ((1 - u ^ r : ℝ) : ℂ) * c -
        ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m :=
  ErdosProblems.Erdos1041.trinomialRoot_spoke_factorization hroot

theorem trinomialRoot_spoke_norm_le_constant
    {m r : ℕ} (hrm : r ≤ m) {a c w : ℂ}
    (hroot : w ^ m + a * w ^ r + c = 0)
    (hw : ‖w‖ ^ m ≤ ‖c‖) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ ≤ ‖c‖ :=
  ErdosProblems.Erdos1041.trinomialRoot_spoke_norm_le_constant
    hrm hroot hw hu0 hu1

theorem trinomialRoot_spoke_norm_lt_one
    {m r : ℕ} (hrm : r ≤ m) {a c w : ℂ}
    (hroot : w ^ m + a * w ^ r + c = 0)
    (hw : ‖w‖ ^ m ≤ ‖c‖) (hc : ‖c‖ < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ < 1 :=
  ErdosProblems.Erdos1041.trinomialRoot_spoke_norm_lt_one
    hrm hroot hw hc hu0 hu1

theorem trinomialRoot_spoke_norm_lt_one_of_norm_lt_one
    {m r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m) {a c w : ℂ}
    (hroot : w ^ m + a * w ^ r + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ < 1 :=
  ErdosProblems.Erdos1041.trinomialRoot_spoke_norm_lt_one_of_norm_lt_one
    hr hrm hroot hw hc hu0 hu1

theorem cyclicTrinomial_two_short_fiber_displacements {y₁ y₂ : ℂ}
    (hy₁ : ‖y₁‖ < 1) (hy₂ : ‖y₂‖ < 1) :
    ‖y₁‖ + ‖y₂‖ < 2 :=
  ErdosProblems.Erdos1041.cyclicTrinomial_two_short_fiber_displacements hy₁ hy₂

end PalomarCorpus.ExternalVerification1041CyclicTrinomialFiber

import ErdosProblems.Erdos1041.FirstMergeCriticalValueSeparation

namespace PalomarCorpus.ExternalVerification1041FirstMergeCriticalValueSeparation

noncomputable def firstMergeSquaredCoefficient (n : ℕ) (S : ℝ) : ℝ :=
  (1 + S) ^ ((2 : ℝ) / (n : ℝ)) * Real.log (S / (S - 1))

theorem firstMerge_exact_convenient_thresholds :
    (∀ n : ℕ, 3 ≤ n → firstMergeSquaredCoefficient n 4 < 1) ∧
    (∀ n : ℕ, 4 ≤ n → firstMergeSquaredCoefficient n 3 < 1) ∧
    (∀ n : ℕ, 6 ≤ n → firstMergeSquaredCoefficient n 2 < 1) := by
  simpa [firstMergeSquaredCoefficient,
    ErdosProblems.Erdos1041.firstMergeSquaredCoefficient] using
    ErdosProblems.Erdos1041.firstMerge_exact_convenient_thresholds

theorem firstMerge_length_lt_two_of_squared_bound
    {n : ℕ} {S length : ℝ}
    (hbound : length ^ 2 ≤ 4 * firstMergeSquaredCoefficient n S)
    (hthreshold : firstMergeSquaredCoefficient n S < 1) :
    length < 2 := by
  apply ErdosProblems.Erdos1041.firstMerge_length_lt_two_of_squared_bound
  · simpa [firstMergeSquaredCoefficient,
      ErdosProblems.Erdos1041.firstMergeSquaredCoefficient] using hbound
  · simpa [firstMergeSquaredCoefficient,
      ErdosProblems.Erdos1041.firstMergeSquaredCoefficient] using hthreshold

end PalomarCorpus.ExternalVerification1041FirstMergeCriticalValueSeparation

import Mathlib
import ErdosProblems.Erdos1041.QuarticQuotientFiberCase

namespace PalomarCorpus.ExternalVerification1041QuarticQuotientFiber

theorem rootLift_kernel_le_axis {alpha d x : ℝ}
    (halpha : alpha ≤ 1) (hx : 0 < x) :
    (Real.sqrt (d ^ 2 + x ^ 2)) ^ (alpha - 1) ≤ x ^ (alpha - 1) :=
  ErdosProblems.Erdos1041.rootLift_kernel_le_axis halpha hx

theorem rootLift_axis_integral {alpha A : ℝ}
    (halpha : 0 < alpha) (hA : 0 ≤ A) :
    alpha * (∫ x in (0 : ℝ)..A, x ^ (alpha - 1)) = A ^ alpha :=
  ErdosProblems.Erdos1041.rootLift_axis_integral halpha hA

theorem rootLift_endpoint_budget_lt_two {alpha a b : ℝ}
    (halpha : 0 < alpha)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    a ^ alpha + b ^ alpha < 2 :=
  ErdosProblems.Erdos1041.rootLift_endpoint_budget_lt_two
    halpha ha0 ha1 hb0 hb1

theorem rootLift_length_lt_two_of_le_endpoint_budget
    {alpha a b length : ℝ}
    (halpha : 0 < alpha)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hlength : length ≤ a ^ alpha + b ^ alpha) :
    length < 2 :=
  ErdosProblems.Erdos1041.rootLift_length_lt_two_of_le_endpoint_budget
    halpha ha0 ha1 hb0 hb1 hlength

end PalomarCorpus.ExternalVerification1041QuarticQuotientFiber

import ErdosProblems.Erdos1041.CubicQuotientFiberCase
import ErdosProblems.Erdos1041.PrimitiveQuinticInteriorTail
import ErdosProblems.Erdos1041.SharpCollinearChebyshev

open Polynomial

namespace PalomarCorpus.ExternalVerification1041SolvedFamilies

theorem cubic_safeRootSpoke {r s v : ℂ}
    (hr : ‖r‖ < 1) (hs : ‖s‖ < 1) (hv : ‖v‖ < 1) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * r - r) * ((t : ℂ) * r - s) * ((t : ℂ) * r - v)‖ ≤ 1) ∨
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * s - s) * ((t : ℂ) * s - r) * ((t : ℂ) * s - v)‖ ≤ 1) ∨
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * v - v) * ((t : ℂ) * v - r) * ((t : ℂ) * v - s)‖ ≤ 1) := by
  exact ErdosProblems.Erdos1041.cubic_has_safe_root_spoke hr hs hv

theorem primitiveQuintic_twoStrictTailEnergies
    {r : ℝ}
    {x0 x1 x2 x3 x4 s0 s1 s2 s3 s4 : ℝ}
    (hr : 0 < r) (hr2 : r < 2)
    (hs0 : 0 ≤ s0) (hs0one : s0 ≤ 1) (hx0s : x0 ^ 2 ≤ s0)
    (hs1 : 0 ≤ s1) (hs1one : s1 ≤ 1) (hx1s : x1 ^ 2 ≤ s1)
    (hs2 : 0 ≤ s2) (hs2one : s2 ≤ 1) (hx2s : x2 ^ 2 ≤ s2)
    (hs3 : 0 ≤ s3) (hs3one : s3 ≤ 1) (hx3s : x3 ^ 2 ≤ s3)
    (hs4 : 0 ≤ s4) (hs4one : s4 ≤ 1) (hx4s : x4 ^ 2 ≤ s4)
    (hm1 : x0 + x1 + x2 + x3 + x4 = -r)
    (hm2 : (2 * x0 ^ 2 - s0) + (2 * x1 ^ 2 - s1) +
        (2 * x2 ^ 2 - s2) + (2 * x3 ^ 2 - s3) +
        (2 * x4 ^ 2 - s4) = r ^ 2)
    (hm3 : (4 * x0 ^ 3 - 3 * s0 * x0) +
        (4 * x1 ^ 3 - 3 * s1 * x1) +
        (4 * x2 ^ 3 - 3 * s2 * x2) +
        (4 * x3 ^ 3 - 3 * s3 * x3) +
        (4 * x4 ^ 3 - 3 * s4 * x4) = -r ^ 3) :
    (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) := by
  exact ErdosProblems.Erdos1041.primitiveInterior_exists_two_tailEnergy_lt_one
    hr hr2 hs0 hs0one hx0s hs1 hs1one hx1s hs2 hs2one hx2s
    hs3 hs3one hx3s hs4 hs4one hx4s hm1 hm2 hm3

namespace SharpCollinear

noncomputable def endpointScale (n : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 * (n : ℝ)))

noncomputable def comparisonBound (n : ℕ) : ℝ :=
  |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|

theorem existsPeakLeComparisonBound
    {m : ℕ} {p : ℝ[X]} {c : Fin (m + 1) → ℝ}
    (hp : p.IsMonicOfDegree (m + 2))
    (hc : StrictMono c) (ha : -1 < c 0) (hb : c (Fin.last m) < 1)
    (hpa : p.eval (-1) = 0) (hpb : p.eval 1 = 0)
    (hpalt : ∀ i : Fin m,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hc_mem : ∀ i : Fin (m + 1), |c i| ≤ 1) :
    ∃ i : Fin (m + 1), |p.eval (c i)| ≤ comparisonBound (m + 2) := by
  simpa [comparisonBound, endpointScale,
    ErdosProblems.Erdos1041.SharpCollinearChebyshev.comparisonBound,
    ErdosProblems.Erdos1041.SharpCollinearChebyshev.endpointScale] using
    (ErdosProblems.Erdos1041.SharpCollinearChebyshev.exists_peak_le_comparisonBound
      hp hc ha hb hpa hpb hpalt hc_mem)

end SharpCollinear
end PalomarCorpus.ExternalVerification1041SolvedFamilies

import Mathlib
import ErdosProblems.Erdos1041.CyclicTetranomialCoefficientCase
import ErdosProblems.Erdos1041.TetranomialL2Selector

open scoped ComplexConjugate

namespace PalomarCorpus.ExternalVerification1041TetranomialSpokes

theorem tetranomialRoot_spoke_factorization
    {m r s : ℕ} {a b c w : ℂ} {u : ℝ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0) :
    (u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c =
      ((1 - u ^ s : ℝ) : ℂ) * c -
        ((u ^ s - u ^ r : ℝ) : ℂ) * (a * w ^ r + w ^ m) -
          ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m :=
  ErdosProblems.Erdos1041.tetranomialRoot_spoke_factorization hroot

theorem tetranomialRoot_spoke_norm_lt_one_of_rootBudget
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c w : ℂ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1)
    (hbudget : ‖c‖ + ‖b‖ * ‖w‖ ^ s < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c‖ < 1 :=
  ErdosProblems.Erdos1041.tetranomialRoot_spoke_norm_lt_one_of_rootBudget
    hs hsr hrm hroot hw hc hbudget hu0 hu1

theorem tetranomialRoot_spoke_norm_lt_one_of_lowCoeffBudget
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c w : ℂ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1)
    (hbudget : ‖b‖ + ‖c‖ ≤ 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c‖ < 1 :=
  ErdosProblems.Erdos1041.tetranomialRoot_spoke_norm_lt_one_of_lowCoeffBudget
    hs hsr hrm hroot hw hc hbudget hu0 hu1

theorem sum_normSq_const_add_mul
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (b c : ℂ) :
    ∑ i ∈ S, Complex.normSq (c + b * v i) =
      (S.card : ℝ) * Complex.normSq c +
        Complex.normSq b * ∑ i ∈ S, Complex.normSq (v i) +
          2 * (conj c * b * (∑ i ∈ S, v i)).re :=
  ErdosProblems.Erdos1041.sum_normSq_const_add_mul S v b c

theorem exists_two_tails_norm_lt_one_of_exact_L2_budget
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (b c : ℂ)
    (hcard : 2 ≤ S.card)
    (hbudget :
      (S.card : ℝ) * Complex.normSq c +
          Complex.normSq b * ∑ i ∈ S, Complex.normSq (v i) +
            2 * (conj c * b * (∑ i ∈ S, v i)).re <
        (S.card : ℝ) - 1) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
      ‖c + b * v i‖ < 1 ∧ ‖c + b * v j‖ < 1 :=
  ErdosProblems.Erdos1041.exists_two_tails_norm_lt_one_of_exact_L2_budget
    S v b c hcard hbudget

theorem exists_two_tetranomialRoot_safeSpokes_of_moment_coeff_budget
    {ι : Type*} (S : Finset ι) (w : ι → ℂ)
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c moment : ℂ}
    (hcard : 2 ≤ S.card)
    (hroot : ∀ i ∈ S, w i ^ m + a * w i ^ r + b * w i ^ s + c = 0)
    (hw : ∀ i ∈ S, ‖w i‖ < 1) (hc : ‖c‖ < 1)
    (hmoment : ∑ i ∈ S, w i ^ s = moment)
    (hcoeff :
      (S.card : ℝ) * (Complex.normSq b + Complex.normSq c) +
          2 * (conj c * b * moment).re <
        (S.card : ℝ) - 1) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(u : ℂ) ^ m * w i ^ m + a * (u : ℂ) ^ r * w i ^ r +
          b * (u : ℂ) ^ s * w i ^ s + c‖ < 1) ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(u : ℂ) ^ m * w j ^ m + a * (u : ℂ) ^ r * w j ^ r +
          b * (u : ℂ) ^ s * w j ^ s + c‖ < 1) :=
  ErdosProblems.Erdos1041.exists_two_tetranomialRoot_safeSpokes_of_moment_coeff_budget
    S w hs hsr hrm hcard hroot hw hc hmoment hcoeff

end PalomarCorpus.ExternalVerification1041TetranomialSpokes

import ErdosProblems.Erdos1049.AdelicHeightBridge

namespace PalomarCorpus.ExternalVerification1049AdelicHeightBridge

open Polynomial

noncomputable def hpDecay (rho sigma : ℝ) : ℝ :=
  (1 + rho ^ 2) / 2 + sigma

noncomputable def hpHeight (rho sigma : ℝ) : ℝ :=
  (1 + rho) ^ 2 / 2 + sigma * (1 + rho)

noncomputable def hpCyclotomicSaving (sigma : ℝ) : ℝ :=
  3 * sigma ^ 2 / Real.pi ^ 2

noncomputable def hpThreshold (rho sigma : ℝ) : ℝ :=
  (hpDecay rho sigma - hpCyclotomicSaving sigma) /
    (hpHeight rho sigma + hpDecay rho sigma)

def homEvalThreeTwo (W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * 3 ^ i * 2 ^ (W - i)

def bottomJet3 (R W : ℕ) (P : Polynomial ℤ) : ZMod (3 ^ R) :=
  homEvalThreeTwo W P

def topJet2 (S W : ℕ) (P : Polynomial ℤ) : ZMod (2 ^ S) :=
  homEvalThreeTwo W P

abbrev FourJetSignature (R S : ℕ) :=
  (ZMod (3 ^ R) × ZMod (3 ^ R)) ×
    (ZMod (2 ^ S) × ZMod (2 ^ S))

def fourJetSignature (R S W : ℕ) (U V : Polynomial ℤ) :
    FourJetSignature R S :=
  ((bottomJet3 R W U, bottomJet3 R W V),
    (topJet2 S W U, topJet2 S W V))

def selectedFourJetSum {n : ℕ} (R S W : ℕ)
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ)
    (ε : Fin n → Bool) : FourJetSignature R S :=
  ∑ i, if ε i then
    fourJetSignature R S W (forms i).1 (forms i).2
  else 0

noncomputable def zudilinPochhammerPS (start len : ℕ) : PowerSeries ℤ :=
  ∏ r ∈ Finset.range len,
    (1 - PowerSeries.X ^ (start + r) : PowerSeries ℤ)

noncomputable def zudilinNormalizedTailUnit (n t : ℕ) : PowerSeries ℤ :=
  zudilinPochhammerPS 1 n ^ 3 * zudilinPochhammerPS (t + 1) n *
    PowerSeries.invOfUnit (zudilinPochhammerPS (n + 1 + t) (n + 1)) 1

noncomputable def zudilinNormalizedTail (n t : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ ((n + 1) * t) * zudilinNormalizedTailUnit n t

noncomputable def zudilinNormalizedMoment (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d =>
    ∑ t ∈ Finset.range (d / (n + 1) + 1),
      PowerSeries.coeff d (zudilinNormalizedTail n t)

noncomputable def zudilinFirstTransformedRow (l : ℕ) : PowerSeries ℤ :=
  zudilinNormalizedMoment (l + 1) - zudilinNormalizedMoment l

theorem zudilin_firstTransformedRow_initialMonomial (l : ℕ) :
    PowerSeries.order (zudilinFirstTransformedRow l) = l + 1 ∧
      PowerSeries.coeff (l + 1) (zudilinFirstTransformedRow l) = -6 := by
  have hmoment (n : ℕ) :
      zudilinNormalizedMoment n =
        ErdosProblems.Erdos1049.zudilinNormalizedMoment n := by
    rfl
  have hrow :
      ErdosProblems.Erdos1049.zudilinTransformedNormalizedMoment 1 l =
        ErdosProblems.Erdos1049.zudilinNormalizedMoment (l + 1) -
          ErdosProblems.Erdos1049.zudilinNormalizedMoment l := by
    simpa using
      (ErdosProblems.Erdos1049.zudilinTransformedNormalizedMoment_succ 0 l)
  rw [zudilinFirstTransformedRow, hmoment, hmoment, ← hrow]
  exact
    ErdosProblems.Erdos1049.zudilinTransformedNormalizedMoment_one_initialMonomial l

def zudilinSharpHankelQOrder (N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range N, (j : ℤ) ^ 2

def zudilinTransformedRowCoeff (j : ℕ) : ℕ :=
  ((j + 1) ^ 2 * (j + 2)) / 2

theorem zudilinSharpHankelOrderAndCoeff_algebraicAssembly (N : ℕ) :
    6 * zudilinSharpHankelQOrder N =
        (N : ℤ) * ((N : ℤ) - 1) * (2 * (N : ℤ) - 1) ∧
      2 ^ N * (∏ j ∈ Finset.range N, zudilinTransformedRowCoeff j) =
        (N.factorial) ^ 2 * (N + 1).factorial := by
  have horder :
      zudilinSharpHankelQOrder =
        ErdosProblems.Erdos1049.zudilinSharpHankelQOrder := rfl
  have hcoeff :
      zudilinTransformedRowCoeff =
        ErdosProblems.Erdos1049.zudilinTransformedRowCoeff := rfl
  rw [horder, hcoeff]
  exact
    ErdosProblems.Erdos1049.zudilinSharpHankelOrderAndCoeff_algebraicAssembly N

theorem threePow_fortyOne_lt_twoPow_sixtyFive : 3 ^ 41 < 2 ^ 65 := by
  exact ErdosProblems.Erdos1049.threePow_fortyOne_lt_twoPow_sixtyFive

theorem twoPow_sixtyFour_lt_threePow_fortyOne : 2 ^ 64 < 3 ^ 41 := by
  exact ErdosProblems.Erdos1049.twoPow_sixtyFour_lt_threePow_fortyOne

theorem threeHalves_rectangular_hp_gap_gt_threeThirteenths (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - hpThreshold rho sigma := by
  simpa [hpThreshold, hpDecay, hpHeight, hpCyclotomicSaving,
    ErdosProblems.Erdos1049.hpThreshold, ErdosProblems.Erdos1049.hpDecay,
    ErdosProblems.Erdos1049.hpHeight,
    ErdosProblems.Erdos1049.hpCyclotomicSaving] using
    ErdosProblems.Erdos1049.threeHalves_rectangular_hp_gap_gt_threeThirteenths
      rho sigma hrho hsigma

theorem threeHalves_hankelChargeThreshold_lt_eightFortyOne :
    (Real.log 3 / Real.log 2 - 1) / 3 < (8 : ℝ) / 41 := by
  exact ErdosProblems.Erdos1049.threeHalves_hankelChargeThreshold_lt_eightFortyOne

theorem zudilinScalarContent_cannot_meet_required_charge
    (N extractedDegree : ℤ) (hN : 0 < N)
    (hextracted : extractedDegree ≤ N ^ 3 - N) :
    41 * extractedDegree < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  exact ErdosProblems.Erdos1049.zudilinScalarContent_cannot_meet_required_charge
    N extractedDegree hN hextracted

theorem zudilinScalarPlusBorder_cannot_meet_required_charge
    (N extractedDegree : ℤ) (hN : 2 ≤ N)
    (hextracted : extractedDegree ≤ 2 * N ^ 3 - N) :
    41 * extractedDegree < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  exact ErdosProblems.Erdos1049.zudilinScalarPlusBorder_cannot_meet_required_charge
    N extractedDegree hN hextracted

theorem three_two_scalar_margin_lt_explicit {C0 C1 : ℝ}
    (hC0 : 0 < C0) (hsource : 2 * C0 ≤ C1) :
    C0 * Real.log 3 - C1 * Real.log 2 <
      -((17 : ℝ) / 41) * C0 * Real.log 2 := by
  exact ErdosProblems.Erdos1049.three_two_scalar_margin_lt_explicit hC0 hsource

theorem exists_distinct_binary_selectors_same_fourJet_of_power_certificate
    {n p q T S W : ℕ}
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ)
    (hpq : (3 : ℕ) ^ p < (2 : ℕ) ^ q) (hT : 0 < T)
    (hrank : 2 * q * T + 2 * S ≤ n) :
    ∃ ε η : Fin n → Bool, ε ≠ η ∧
      selectedFourJetSum (p * T) S W forms ε =
        selectedFourJetSum (p * T) S W forms η := by
  simpa [selectedFourJetSum, fourJetSignature, bottomJet3, topJet2,
    homEvalThreeTwo, ErdosProblems.Erdos1049.selectedFourJetSum,
    ErdosProblems.Erdos1049.fourJetSignature,
    ErdosProblems.Erdos1049.bottomJet3, ErdosProblems.Erdos1049.topJet2,
    ErdosProblems.Erdos1049.homEvalThreeTwo] using
    ErdosProblems.Erdos1049.exists_distinct_binary_selectors_same_fourJet_of_power_certificate
      forms hpq hT hrank

theorem exists_distinct_binary_selectors_same_fourJet_of_rank_41
    {n T S W : ℕ}
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ) (hT : 0 < T)
    (hrank : 130 * T + 2 * S ≤ n) :
    ∃ ε η : Fin n → Bool, ε ≠ η ∧
      selectedFourJetSum (41 * T) S W forms ε =
        selectedFourJetSum (41 * T) S W forms η := by
  simpa [selectedFourJetSum, fourJetSignature, bottomJet3, topJet2,
    homEvalThreeTwo, ErdosProblems.Erdos1049.selectedFourJetSum,
    ErdosProblems.Erdos1049.fourJetSignature,
    ErdosProblems.Erdos1049.bottomJet3, ErdosProblems.Erdos1049.topJet2,
    ErdosProblems.Erdos1049.homEvalThreeTwo] using
    ErdosProblems.Erdos1049.exists_distinct_binary_selectors_same_fourJet_of_rank_41
      forms hT hrank

theorem fourJet_card_gt_two_pow_of_rank_41 (S : ℕ) :
    2 ^ (129 + 2 * S) < Fintype.card (FourJetSignature 41 S) := by
  exact ErdosProblems.Erdos1049.fourJet_card_gt_two_pow_of_rank_41 S

theorem exists_ne_map_eq_map_ne_of_card_mul_lt {α β γ : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : α → γ) (k : ℕ)
    (hg : ∀ x : α, (Finset.univ.filter fun y => g y = g x).card ≤ k)
    (hcard : Fintype.card β * k < Fintype.card α) :
    ∃ x y : α, x ≠ y ∧ f x = f y ∧ g x ≠ g y := by
  exact ErdosProblems.Erdos1049.exists_ne_map_eq_map_ne_of_card_mul_lt
    f g k hg hcard

end PalomarCorpus.ExternalVerification1049AdelicHeightBridge

import ErdosProblems.Erdos1049.HermitePadeNoGo

namespace PalomarCorpus.ExternalVerification1049HermitePadeNoGo

noncomputable abbrev hpDecay := ErdosProblems.Erdos1049.hpDecay
noncomputable abbrev hpHeight := ErdosProblems.Erdos1049.hpHeight
noncomputable abbrev hpCyclotomicSaving := ErdosProblems.Erdos1049.hpCyclotomicSaving
noncomputable abbrev hpThreshold := ErdosProblems.Erdos1049.hpThreshold
noncomputable abbrev hpClearedGap := ErdosProblems.Erdos1049.hpClearedGap

theorem hpClearedGap_expansion (rho u : ℝ) :
    hpClearedGap rho (1 + rho + u) =
      -Real.pi ^ 2 * rho ^ 2 - Real.pi ^ 2 * rho * u -
        2 * Real.pi ^ 2 * rho - 2 * rho ^ 2 - 10 * rho * u -
        4 * rho - 6 * u ^ 2 - 8 * u :=
  ErdosProblems.Erdos1049.hpClearedGap_expansion rho u

theorem hpClearedGap_nonpos (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpClearedGap rho sigma ≤ 0 :=
  ErdosProblems.Erdos1049.hpClearedGap_nonpos rho sigma hrho hsigma

theorem hpClearedGap_eq_zero_iff (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpClearedGap rho sigma = 0 ↔ rho = 0 ∧ sigma = 1 :=
  ErdosProblems.Erdos1049.hpClearedGap_eq_zero_iff rho sigma hrho hsigma

theorem rectangular_hp_threshold_le_classical (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpThreshold rho sigma ≤ 1 / 2 - 1 / Real.pi ^ 2 :=
  ErdosProblems.Erdos1049.rectangular_hp_threshold_le_classical
    rho sigma hrho hsigma

theorem rectangular_hp_threshold_eq_classical_iff (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpThreshold rho sigma = 1 / 2 - 1 / Real.pi ^ 2 ↔
      rho = 0 ∧ sigma = 1 :=
  ErdosProblems.Erdos1049.rectangular_hp_threshold_eq_classical_iff
    rho sigma hrho hsigma

end PalomarCorpus.ExternalVerification1049HermitePadeNoGo

import ErdosProblems.Erdos1049.QAperyTailDenominator
import ErdosProblems.Erdos1049.TwoSelectorRemainderEscape

namespace PalomarCorpus.ExternalVerification1049PrimeSupportSelectors

open Filter

theorem twoSelector_rationalGap
    (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q)
    (hdet : A₁ * B₂ - A₂ * B₁ ≠ 0) :
    (1 : ℝ) / q ≤
        |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨
      (1 : ℝ) / q ≤
        |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| :=
  ErdosProblems.Erdos1049.rational_twoSelector_remainder_gap
    a q A₁ B₁ A₂ B₂ hq hdet

theorem integerLinearForm_rationalGap
    (a q A B : ℤ) (hq : 0 < q)
    (hne : (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) ≠ 0) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| :=
  ErdosProblems.Erdos1049.rational_integerLinearForm_gap a q A B hq hne

theorem rationalTwoSelector_notBothTendstoZero
    (a q : ℤ) (hq : 0 < q)
    (A₁ B₁ A₂ B₂ : ℕ → ℤ)
    (hdet : ∀ n, A₁ n * B₂ n - A₂ n * B₁ n ≠ 0) :
    ¬(Tendsto
        (fun n ↦ (B₁ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ n : ℝ))
        atTop (nhds 0) ∧
      Tendsto
        (fun n ↦ (B₂ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ n : ℝ))
        atTop (nhds 0)) :=
  ErdosProblems.Erdos1049.rational_twoSelector_not_both_tendsto_zero
    a q hq A₁ B₁ A₂ B₂ hdet

theorem twoSelector_detHeightDecay_tradeoff
    (A₁ B₁ A₂ B₂ F ε : ℝ)
    (h₁ : |B₁ * F - A₁| ≤ ε) (h₂ : |B₂ * F - A₂| ≤ ε) :
    |A₁ * B₂ - A₂ * B₁| ≤ ε * (|B₁| + |B₂|) :=
  ErdosProblems.Erdos1049.twoSelector_det_height_decay_tradeoff
    A₁ B₁ A₂ B₂ F ε h₁ h₂

theorem twoSelector_unimodularHeightDecay_tradeoff
    (A₁ B₁ A₂ B₂ u v w z F H ε : ℝ)
    (hunimod : |u * z - v * w| = 1)
    (hε : 0 ≤ ε)
    (hu : |u| ≤ H) (hv : |v| ≤ H) (hw : |w| ≤ H) (hz : |z| ≤ H)
    (h₁ : |(u * B₁ + v * B₂) * F - (u * A₁ + v * A₂)| ≤ ε)
    (h₂ : |(w * B₁ + z * B₂) * F - (w * A₁ + z * A₂)| ≤ ε) :
    |A₁ * B₂ - A₂ * B₁| ≤
      2 * H * ε * (|B₁| + |B₂|) :=
  ErdosProblems.Erdos1049.twoSelector_unimodular_height_decay_tradeoff
    A₁ B₁ A₂ B₂ u v w z F H ε hunimod hε hu hv hw hz h₁ h₂

theorem primeSupportedTwoSelector_rationalGap
    {ell : ℕ} (hell : ell.Prime)
    (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q)
    (hellq : ¬ (ell : ℤ) ∣ q)
    (hellB₁ : (ell : ℤ) ∣ B₁)
    (hellB₂ : (ell : ℤ) ∣ B₂)
    (hdet : ¬ (ell : ℤ) ^ 2 ∣ A₁ * B₂ - A₂ * B₁) :
    (1 : ℝ) / q ≤
        |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨
      (1 : ℝ) / q ≤
        |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| :=
  ErdosProblems.Erdos1049.rational_twoSelector_gap_of_prime_tail_support
    hell a q A₁ B₁ A₂ B₂ hq hellq hellB₁ hellB₂ hdet

theorem primeSupportedOneRow_rationalGap
    {ell : ℕ} (hell : ell.Prime)
    (a q A B : ℤ) (hq : 0 < q)
    (hellB : (ell : ℤ) ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| :=
  ErdosProblems.Erdos1049.rational_integerLinearForm_gap_of_prime_support
    hell a q A B hq hellB hellA hellq

theorem primePowerSupportedOneRow_rationalGap
    {ell r : ℕ} (hell : ell.Prime) (hr : r ≠ 0)
    (a q A B : ℤ) (hq : 0 < q)
    (hellPowB : (ell : ℤ) ^ r ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| :=
  ErdosProblems.Erdos1049.rational_integerLinearForm_gap_of_prime_power_support
    hell hr a q A B hq hellPowB hellA hellq

theorem zeroDenominatorCoordinates_binaryCollision
    {N k : ℕ} [NeZero N]
    (w : Fin k → ZMod N × ZMod N)
    (hzero : ∀ i, (w i).2 = 0)
    (hcard : N < 2 ^ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 :=
  ErdosProblems.Erdos1049.zmod_binary_collision_of_zero_denominator_coordinates
    w hzero hcard

end PalomarCorpus.ExternalVerification1049PrimeSupportSelectors

import Mathlib
import ErdosProblems.Erdos1049.RationalBaseLambert

namespace PalomarCorpus.ExternalVerification1049RationalBaseBarrier

open scoped BigOperators

def CoordinatewiseCorridor
    (a b N K Q digit : ℕ) : Prop :=
  0 < a ∧ 0 < Q ∧ 0 < digit ∧ digit ≤ N + K ∧
    a ^ K ∣ Q * digit ∧
    Q * b ^ (N + K + 1) < a ^ (K + 1)

def rationalBasePrefixQ
    (r s : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ m ∈ Finset.range N,
    coeff (m + 1) * s ^ (m + 1) / r ^ (m + 1)

def rationalBaseClearedTailQ
    (r s B F : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  B * r ^ N * (F - rationalBasePrefixQ r s coeff N)

def rationalBaseForcingNat
    (s B : ℕ) (coeff : ℕ → ℕ) (N : ℕ) : ℕ :=
  B * coeff (N + 1) * s ^ (N + 1)

theorem rationalBaseClearedTailQ_succ
    {r s B F : ℚ} {coeff : ℕ → ℚ} (hr : r ≠ 0) (N : ℕ) :
    rationalBaseClearedTailQ r s B F coeff (N + 1) =
      r * rationalBaseClearedTailQ r s B F coeff N -
        B * coeff (N + 1) * s ^ (N + 1) := by
  simpa [rationalBaseClearedTailQ, rationalBasePrefixQ,
    ErdosProblems.Erdos1049.rationalBaseClearedTailQ,
    ErdosProblems.Erdos1049.rationalBasePrefixQ] using
    ErdosProblems.Erdos1049.rationalBaseClearedTailQ_succ hr N

theorem twoPow_le_rationalBaseForcingNat
    {s B : ℕ} {coeff : ℕ → ℕ} {N : ℕ}
    (hs : 2 ≤ s) (hB : 1 ≤ B) (hc : 1 ≤ coeff (N + 1)) :
    2 ^ (N + 1) ≤ rationalBaseForcingNat s B coeff N := by
  simpa [rationalBaseForcingNat,
    ErdosProblems.Erdos1049.rationalBaseForcingNat] using
    ErdosProblems.Erdos1049.twoPow_le_rationalBaseForcingNat hs hB hc

theorem threeHalves_no_coordinatewiseCorridor
    {N K Q digit : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    ¬ CoordinatewiseCorridor 3 2 N K Q digit := by
  simpa [CoordinatewiseCorridor,
    ErdosProblems.Erdos1049.CoordinatewiseCorridor] using
    ErdosProblems.Erdos1049.threeHalves_no_coordinatewiseCorridor
      (Q := Q) (digit := digit) hN hK

end PalomarCorpus.ExternalVerification1049RationalBaseBarrier

import Mathlib
import ErdosProblems.Erdos243.ReciprocalTailRigidity

namespace PalomarCorpus.ExternalVerification243BoundedNegativePartRigidity

def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

theorem boundedNegativePart_completeRigidity
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E n) < C n) :
    (∃ N, ∀ n, N ≤ n → E n = 0) ∧
      ∃ N, ∀ n, N ≤ n →
        (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  have hE' : ∀ n, E n = ErdosProblems.Erdos243.centeredState
      (a n : ℤ) (D n : ℤ) (C n : ℤ) := by
    intro n
    simpa [centeredState, ErdosProblems.Erdos243.centeredState] using hE n
  have hzero : ∃ N, ∀ n, N ≤ n → E n = 0 :=
    ErdosProblems.Erdos243.eventuallyBoundedNegativePart_eventually_zero
      a C D E ha hCpos hC hD hE' hbound hvanish
  have hrec : ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
    simpa [sylvesterNext, ErdosProblems.Erdos243.sylvesterNext] using
      ErdosProblems.Erdos243.boundedNegativePart_sylvesterNext_eventually
        a C D E ha hCpos hC hD hE' hbound hvanish
  exact ⟨hzero, hrec⟩

end PalomarCorpus.ExternalVerification243BoundedNegativePartRigidity

import Mathlib
import ErdosProblems.Erdos243.ReciprocalTailRigidity

namespace PalomarCorpus.ExternalVerification243BoundedRiseReducedTail

theorem no_boundedRise_of_tailAvoidance
    (u m : ℕ → ℕ) (N B : ℕ)
    (hB : 0 < B)
    (hm : ∀ n, N ≤ n → 1 < m n)
    (hpair : ∀ {i j : ℕ}, N ≤ i → N ≤ j → i ≠ j →
      Nat.Coprime (m i) (m j))
    (havoid : ∀ {i t : ℕ}, N ≤ i → i < t →
      Nat.Coprime (m i) (u t))
    (hrise : ∀ n, N ≤ n → u (n + 1) ≤ u n + B)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False := by
  apply ErdosProblems.Erdos243.no_boundedRise_of_tailAvoidance u m N B hB hm
  · intro i j hi hj hij
    exact hpair hi hj hij
  · intro i t hi hit
    exact havoid hi hit
  · exact hrise
  · exact huTop

theorem no_boundedRise_reducedTail
    (a u v : ℕ → ℕ) (B : ℕ)
    (hB : 0 < B)
    (ha : ∀ n, 1 < a n)
    (hred : ∀ n, Nat.Coprime (u n) (v n))
    (hu : ∀ n, u (n + 1) + v n = a n * u n)
    (hv : ∀ n, v (n + 1) = a n * v n)
    (hrise : ∀ n, u (n + 1) ≤ u n + B)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False := by
  exact ErdosProblems.Erdos243.no_boundedRise_reducedTail
    a u v B hB ha hred hu hv hrise huTop

theorem no_eventuallyBoundedRise_reducedTail
    (a u v : ℕ → ℕ) (N B : ℕ)
    (hB : 0 < B)
    (ha : ∀ n, N ≤ n → 1 < a n)
    (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n))
    (hu : ∀ n, N ≤ n → u (n + 1) + v n = a n * u n)
    (hv : ∀ n, N ≤ n → v (n + 1) = a n * v n)
    (hrise : ∀ n, N ≤ n → u (n + 1) ≤ u n + B)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False := by
  exact ErdosProblems.Erdos243.no_eventuallyBoundedRise_reducedTail
    a u v N B hB ha hred hu hv hrise huTop

end PalomarCorpus.ExternalVerification243BoundedRiseReducedTail

import Mathlib
import ErdosProblems.Erdos243.ReciprocalTailRigidity

namespace PalomarCorpus.ExternalVerification243PeriodicNegativeOrbit

theorem no_phasePrimitivePeriodicNegative_orbit
    (a D C e : ℕ → ℕ) (h M : ℕ)
    (hh : 0 < h)
    (hM : 0 < M)
    (ha : ∀ n, 2 ≤ a n)
    (hepos : ∀ n, 0 < e n)
    (helt : ∀ n, e n < a n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hC : ∀ n, C (n + 1) = C n + e n)
    (hshape : ∀ n, D n + e n = (a n - 1) * C n)
    (hperiod : ∀ n, e (n + h) = e n)
    (hphase : ∀ n, C (n + h) = C n + M)
    (hprimitive : ∀ p, p.Prime → p ∣ M →
      ¬ (p ∣ C 0 ∧ ∀ n, p ∣ e n)) :
    False := by
  exact ErdosProblems.Erdos243.no_phasePrimitivePeriodicNegative_orbit
    a D C e h M hh hM ha hepos helt hD hC hshape hperiod hphase hprimitive

theorem no_periodicNegative_orbit
    (a D C e : ℕ → ℕ) (h M : ℕ)
    (hh : 0 < h)
    (hM : 0 < M)
    (ha : ∀ n, 2 ≤ a n)
    (hepos : ∀ n, 0 < e n)
    (helt : ∀ n, e n < a n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hC : ∀ n, C (n + 1) = C n + e n)
    (hshape : ∀ n, D n + e n = (a n - 1) * C n)
    (hperiod : ∀ n, e (n + h) = e n)
    (hphase : ∀ n, C (n + h) = C n + M) :
    False := by
  exact ErdosProblems.Erdos243.no_periodicNegative_orbit
    a D C e h M hh hM ha hepos helt hD hC hshape hperiod hphase

theorem no_eventuallyPeriodicNegative_orbit
    (a D C e : ℕ → ℕ) (N h M : ℕ)
    (hh : 0 < h)
    (hM : 0 < M)
    (ha : ∀ n, N ≤ n → 2 ≤ a n)
    (hepos : ∀ n, 0 < e (N + n))
    (helt : ∀ n, e (N + n) < a (N + n))
    (hD : ∀ n, N ≤ n → D (n + 1) = a n * D n)
    (hC : ∀ n, N ≤ n → C (n + 1) = C n + e n)
    (hshape : ∀ n, N ≤ n → D n + e n = (a n - 1) * C n)
    (hperiod : ∀ n, e (N + n + h) = e (N + n))
    (hphase : ∀ n, C (N + n + h) = C (N + n) + M) :
    False := by
  exact ErdosProblems.Erdos243.no_eventuallyPeriodicNegative_orbit
    a D C e N h M hh hM ha hepos helt hD hC hshape hperiod hphase

end PalomarCorpus.ExternalVerification243PeriodicNegativeOrbit

import Mathlib
import ErdosProblems.Erdos243.ProtectedEpochEnergy

namespace PalomarCorpus.ExternalVerification243ProtectedEpochEnergy

def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

/-- The local `runningMax` is the corpus `runningMax`: both are the primitive
recursion `| 0 => u 0 | n+1 => max (running u n) (u (n+1))`. -/
theorem runningMax_eq (u : ℕ → ℕ) (n : ℕ) :
    runningMax u n = ErdosProblems.Erdos243.runningMax u n := by
  induction n with
  | zero => simp [runningMax, ErdosProblems.Erdos243.runningMax]
  | succ k ih => simp [runningMax, ErdosProblems.Erdos243.runningMax, ih]

theorem protected_epoch_energy_integer
    (a u v w hc : ℕ → ℕ) (p l s τ : ℕ)
    (hp : p.Prime)
    (hpodd : Odd p)
    (hl : 1 ≤ l)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hprot : p ^ l ∣ v s)
    (hQ : 16 ≤ p ^ l)
    (hRs : 4 * runningMax u s < p * p ^ l)
    (hsτ : s < τ)
    (hτ : p * p ^ l ≤ 2 * u τ) :
    ∃ J : Finset ℕ,
      (∀ n ∈ J, s ≤ n ∧ n < τ ∧ runningMax u n < u (n + 1) ∧
          u n + 3 ≤ u (n + 1) ∧ hc n = 1) ∧
      p * p ^ l ≤ (8 * p + 8) * J.card
        + 4 * ∑ n ∈ J, (u (n + 1) - u n - 2) + 8 * p := by
  have hRs' : 4 * ErdosProblems.Erdos243.runningMax u s < p * p ^ l := by
    simpa [runningMax_eq] using hRs
  obtain ⟨J, hJ, hbound⟩ :=
    ErdosProblems.Erdos243.protected_epoch_energy_integer a u v w hc p l s τ hp
      hpodd hl hred hvpos hw hwpos hnum hden hslow hprot hQ hRs' hsτ hτ
  exact ⟨J, fun n hn => by simpa [runningMax_eq] using hJ n hn, hbound⟩

end PalomarCorpus.ExternalVerification243ProtectedEpochEnergy

import Mathlib
import ErdosProblems.Erdos243.RecordIncrementBarrier

namespace PalomarCorpus.ExternalVerification243RecordIncrementBarrier

def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

/-- The local `runningMax` is the same function as the corpus `runningMax`:
both are the primitive recursion `| 0 => u 0 | n+1 => max (running u n) (u (n+1))`. -/
theorem runningMax_eq (u : ℕ → ℕ) (n : ℕ) :
    runningMax u n = ErdosProblems.Erdos243.runningMax u n := by
  induction n with
  | zero => simp [runningMax, ErdosProblems.Erdos243.runningMax]
  | succ k ih => simp [runningMax, ErdosProblems.Erdos243.runningMax, ih]

theorem recordIncrementOne_sylvesterNext_eventually
    (a u v w hc : ℕ → ℕ) (e : ℕ → ℤ) (N : ℕ)
    (hvpos : ∀ n, N ≤ n → 0 < v n)
    (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n))
    (hw : ∀ n, N ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, N ≤ n → 0 < w n)
    (hnum : ∀ n, N ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, N ≤ n → a n * v n = hc n * v (n + 1))
    (he : ∀ n, N ≤ n → e n = (v n : ℤ) - ((a n : ℤ) - 1) * (u n : ℤ))
    (hcentre : ∀ n, N ≤ n → 2 * (e n).natAbs < u n)
    (hvanish : ∀ K, ∃ M, ∀ n, M ≤ n → K * (e n).natAbs < u n)
    (hinc : ∀ n, N ≤ n → runningMax u (n + 1) ≤ runningMax u n + 1)
    (hsupply : ∀ M, ∃ s, M ≤ s ∧ ∃ p l, p.Prime ∧ 1 ≤ l ∧
      p ^ l ∣ v s ∧ runningMax u s + 3 ≤ p ^ l) :
    ∃ M, ∀ n, M ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  have hinc' : ∀ n, N ≤ n →
      ErdosProblems.Erdos243.runningMax u (n + 1)
        ≤ ErdosProblems.Erdos243.runningMax u n + 1 := by
    intro n hn
    simpa [runningMax_eq] using hinc n hn
  have hsupply' : ∀ M, ∃ s, M ≤ s ∧ ∃ p l, p.Prime ∧ 1 ≤ l ∧
      p ^ l ∣ v s ∧ ErdosProblems.Erdos243.runningMax u s + 3 ≤ p ^ l := by
    intro M
    obtain ⟨s, hMs, p, l, hp, hl, hpl, hbig⟩ := hsupply M
    exact ⟨s, hMs, p, l, hp, hl, hpl, by simpa [runningMax_eq] using hbig⟩
  simpa [sylvesterNext, ErdosProblems.Erdos243.sylvesterNext] using
    ErdosProblems.Erdos243.recordIncrementOne_sylvesterNext_eventually
      a u v w hc e N hvpos hred hw hwpos hnum hden he hcentre hvanish hinc' hsupply'

end PalomarCorpus.ExternalVerification243RecordIncrementBarrier

import Mathlib
import ErdosProblems.Erdos243.SaturatedSquareTransport

namespace PalomarCorpus.ExternalVerification243SaturatedSquareTransport

/-- **Saturated square transport, unnormalised form.**  The whole next reduced
numerator divides `hc * e * e' - v ^ 2`, with no hypothesis beyond the two
cocycle equations and the two centred-error definitions. -/
theorem saturated_square_transport_raw
    {a u v w hc u' v' : ℕ} {a' e e' : ℤ}
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hden : a * v = hc * v')
    (he : e = (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ))
    (he' : e' = (v' : ℤ) - (a' - 1) * (u' : ℤ)) :
    (u' : ℤ) ∣ (hc : ℤ) * e * e' - (v : ℤ) ^ 2 :=
  ErdosProblems.Erdos243.saturated_square_transport_raw hq hnum hden he he'

/-- **The Legendre defect obstructs a unit non-square part, and nothing more.**
If the centred-error product is a quadratic non-residue modulo a prime dividing
the next numerator, then the non-square part `b` of the removed content is not
`1`. No bound on the content follows. -/
theorem legendre_defect_forces_nonsquare_content
    {b s u' p : ℕ} {e e' : ℤ}
    (hdvd : (u' : ℤ) ∣ (b : ℤ) * e * e' - ((b : ℤ) * (s : ℤ)) ^ 2)
    (hpu : p ∣ u')
    (hnr : ¬ IsSquare ((e : ZMod p) * (e' : ZMod p))) :
    b ≠ 1 :=
  ErdosProblems.Erdos243.legendre_defect_forces_nonsquare_content hdvd hpu hnr

end PalomarCorpus.ExternalVerification243SaturatedSquareTransport

import Mathlib
import ErdosProblems.Erdos243.SlowRiseBarrier

namespace PalomarCorpus.ExternalVerification243SlowRiseBarrier

theorem no_slowRise_reducedTail
    (a u v : ℕ → ℕ) (N B : ℕ)
    (ha : ∀ n, N ≤ n → 1 < a n)
    (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n))
    (hu : ∀ n, N ≤ n → u (n + 1) + v n = a n * u n)
    (hv : ∀ n, N ≤ n → v (n + 1) = a n * v n)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop)
    (hstart : u (N + B) < ∏ i : Fin B, a (N + i.1))
    (hrise : ∀ n, N + B ≤ n → u n < 2 * ∏ i : Fin B, a (N + i.1) →
      u (n + 1) ≤ u n + B) :
    False :=
  ErdosProblems.Erdos243.no_slowRise_reducedTail a u v N B ha hred hu hv huTop
    hstart hrise

end PalomarCorpus.ExternalVerification243SlowRiseBarrier

import Mathlib
import ErdosProblems.Erdos249.CyclotomicAnchoredKill

namespace PalomarCorpus.ExternalVerification249BinaryCyclotomicAnchors

open scoped BigOperators

noncomputable def binaryCyclotomicLayer (n : ℕ) : ℕ :=
  ((Polynomial.cyclotomic n ℤ).eval (2 : ℤ)).natAbs

def UnboundedPrimeDivisorSupply (C : ℕ → ℕ) (h : ℕ) : Prop :=
  ∀ B N₀ : ℕ, ∃ q p : ℕ,
    q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (h * q) ∧ B < p

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) -
      (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

def CyclotomicAnchoredKillSupply (C : ℕ → ℕ) : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ q p L : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ C (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 ∧
      certifiedKill (h * q) (p - 1) L

theorem exists_clean_binaryCyclotomicAnchor
    (h N₀ : ℕ) (hh : 0 < h) :
    ∃ q p : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ binaryCyclotomicLayer (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 := by
  simpa [binaryCyclotomicLayer,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.exists_clean_binaryCyclotomicAnchor
      h N₀ hh

theorem binaryCyclotomicLayer_unboundedPrimeDivisorSupply
    (h : ℕ) (hh : 0 < h) :
    UnboundedPrimeDivisorSupply binaryCyclotomicLayer h := by
  simpa [UnboundedPrimeDivisorSupply, binaryCyclotomicLayer,
    ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.UnboundedPrimeDivisorSupply,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer_unboundedPrimeDivisorSupply
      h hh

theorem binaryCyclotomicAnchoredKillSupply_iff_irrational :
    CyclotomicAnchoredKillSupply binaryCyclotomicLayer ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  simpa [CyclotomicAnchoredKillSupply, certifiedKill, windowDiscrepancy,
    binaryCyclotomicLayer,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.CyclotomicAnchoredKillSupply,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.certifiedKill,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.windowDiscrepancy] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicAnchoredKillSupply_iff_irrational

theorem exists_unbounded_binaryCyclotomicSupport_with_periodLock_of_not_irrational
    (hrat : ¬ Irrational
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧
      UnboundedPrimeDivisorSupply binaryCyclotomicLayer h ∧
      ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
        totientTail (N + h) - totientTail N ∈
          Set.range ((↑) : ℤ → ℝ) := by
  simpa [UnboundedPrimeDivisorSupply, binaryCyclotomicLayer, totientTail,
    ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.UnboundedPrimeDivisorSupply,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientTail] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.exists_unbounded_binaryCyclotomicSupport_with_periodLock_of_not_irrational
      hrat

end PalomarCorpus.ExternalVerification249BinaryCyclotomicAnchors

import Mathlib
import Erdos257PeriodNoncollapse.TotientMahlerDefect

namespace PalomarCorpus.ExternalVerification249DyadicTotientKernel

open Module

def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)

abbrev TotientCanonicalIndex (e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)

def canonicalTotientKernelFamily (e : ℕ) :
    TotientCanonicalIndex e → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j.val + 1) (2 * r.val + 1)

abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)

def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val

abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)

def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val

abbrev TotientOddCoreIndex := Fin 2 ⊕ Σ j : ℕ, Fin (2 ^ j)

def oddCoreTotientKernelFamily : TotientOddCoreIndex → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j + 1) (2 * r.val + 1)

theorem dyadicTotientKernelOddCoreBasisAndFiniteRanks :
    LinearIndependent ℚ oddCoreTotientKernelFamily ∧
      Submodule.span ℚ (Set.range fullTotientKernelFamily) =
        Submodule.span ℚ (Set.range oddCoreTotientKernelFamily) ∧
      ∀ e : ℕ, 1 ≤ e →
        Submodule.span ℚ
            (Set.range (totientKernelThroughLevelFamily e)) =
          Submodule.span ℚ
            (Set.range (canonicalTotientKernelFamily e)) ∧
        finrank ℚ
            (Submodule.span ℚ
              (Set.range (totientKernelThroughLevelFamily e))) = 2 ^ e + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [oddCoreTotientKernelFamily, totientKernelSeq,
      Erdos257PeriodNoncollapse.oddCoreTotientKernelFamily,
      Erdos257PeriodNoncollapse.totientKernelSeq] using
      Erdos257PeriodNoncollapse.linearIndependent_oddCoreTotientKernelFamily
  · simpa [fullTotientKernelFamily, oddCoreTotientKernelFamily,
      totientKernelSeq, Erdos257PeriodNoncollapse.fullTotientKernelFamily,
      Erdos257PeriodNoncollapse.oddCoreTotientKernelFamily,
      Erdos257PeriodNoncollapse.totientKernelSeq] using
      Erdos257PeriodNoncollapse.span_range_fullTotientKernel_eq_span_range_oddCore
  · intro e he
    constructor
    · simpa [totientKernelThroughLevelFamily,
        canonicalTotientKernelFamily, totientKernelSeq,
        Erdos257PeriodNoncollapse.totientKernelThroughLevelFamily,
        Erdos257PeriodNoncollapse.canonicalTotientKernelFamily,
        Erdos257PeriodNoncollapse.totientKernelSeq] using
        Erdos257PeriodNoncollapse.span_totientKernelThroughLevelFamily_eq_canonical
          e he
    · simpa [totientKernelThroughLevelFamily, totientKernelSeq,
        Erdos257PeriodNoncollapse.totientKernelThroughLevelFamily,
        Erdos257PeriodNoncollapse.totientKernelSeq] using
        Erdos257PeriodNoncollapse.finrank_totientKernelThroughLevelFamily_eq e he

end PalomarCorpus.ExternalVerification249DyadicTotientKernel

import Mathlib
import Erdos257PeriodNoncollapse.SignedQMomentObstruction
import ErdosProblems.Erdos249.MobiusMersenneLadderSeparation

namespace PalomarCorpus.ExternalVerification249MobiusMersenneLadderStructure

open scoped BigOperators
open ArithmeticFunction

noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)

noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n

noncomputable def mobiusMersenneLambertRung (r : ℕ) : ℝ :=
  ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (r * (d : ℕ)) - 1)

private lemma theta_eq (r : ℕ) :
    mobiusMersenneTheta r =
      _root_.Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta r :=
  rfl

private lemma rung_eq (r : ℕ) :
    mobiusMersenneLambertRung r =
      _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.mobiusMersenneLambertRung r :=
  rfl

theorem mobiusMersenneTheta_no_linearRecurrence_of_eventually
    {m : ℕ} (c : Fin (m + 1) → ℝ) (n₀ : ℕ) (hc : ∃ k, c k ≠ 0)
    (hrec : ∀ n : ℕ, n₀ ≤ n →
      ∑ k : Fin (m + 1), c k * mobiusMersenneTheta (n + (k : ℕ)) = 0) : False := by
  refine _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.mobiusMersenneTheta_no_linearRecurrence_of_eventually
    c n₀ hc (fun n hn => ?_)
  simpa only [theta_eq] using hrec n hn

theorem mobiusMersenneTheta_no_linearRecurrence :
    ¬ ∃ (m : ℕ) (c : Fin (m + 1) → ℝ), (∃ k, c k ≠ 0) ∧
        ∀ n : ℕ, 1 ≤ n →
          ∑ k : Fin (m + 1), c k * mobiusMersenneTheta (n + (k : ℕ)) = 0 := by
  simpa only [theta_eq] using
    _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.mobiusMersenneTheta_no_linearRecurrence

theorem mobiusMersenneTheta_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) <
      mobiusMersenneTheta (r + 1) ^ 2 := by
  simpa only [theta_eq] using
    _root_.Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta_strict_logConcave
      r hr

theorem mobiusMersenneTheta_hankel_two_neg (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) -
      mobiusMersenneTheta (r + 1) ^ 2 < 0 := by
  simpa only [theta_eq] using
    _root_.Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta_hankel_two_neg
      r hr

theorem mobiusMersenneLambertRung_eq (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneLambertRung r = ((1 : ℝ) / 2) ^ r := by
  simpa only [rung_eq] using
    _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.mobiusMersenneLambertRung_eq r hr

theorem lambertRung_shifted_hankelDet_eq_zero (s N : ℕ) (hs : 1 ≤ s) (hN : 2 ≤ N) :
    Matrix.det (Matrix.of fun i j : Fin N =>
      mobiusMersenneLambertRung (s + (i : ℕ) + (j : ℕ))) = 0 := by
  simpa only [rung_eq] using
    _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.lambertRung_shifted_hankelDet_eq_zero
      s N hs hN

theorem mobiusMersenneTheta_ne_mobiusMersenneLambertRung :
    ¬ ∀ r : ℕ, 1 ≤ r → mobiusMersenneTheta r = mobiusMersenneLambertRung r := by
  simpa only [theta_eq, rung_eq] using
    _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.mobiusMersenneTheta_ne_mobiusMersenneLambertRung

end PalomarCorpus.ExternalVerification249MobiusMersenneLadderStructure

import Mathlib
import ErdosProblems.Erdos249.RankOneSharpFloor

namespace PalomarCorpus.ExternalVerification249RankOneSharpFloor

open scoped BigOperators
open ArithmeticFunction

noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) / (((2 : ℝ) ^ (n + 1) - 1) ^ r)

noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n

noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n

noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ :=
  mobiusMersennePrefix Y (e + 2) ^ 2 /
    mobiusMersennePrefix Y (2 * e + 2)

theorem rankOneSubrankQuotient_ge_one_five
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    rankOneSubrankQuotient 1 5 ≤ rankOneSubrankQuotient e Y := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_ge_one_five
      he hY

theorem rankOneSubrankQuotient_eq_one_five_iff
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    rankOneSubrankQuotient e Y = rankOneSubrankQuotient 1 5 ↔
      e = 1 ∧ Y = 5 := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_eq_one_five_iff
      he hY

theorem rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (21 : ℝ) / 320 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty
      he hY

theorem rankOneSubrankQuotient_sub_theta_two_gt_one_div_sixteen
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 16 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_sub_theta_two_gt_one_div_sixteen
      he hY

theorem not_forall_rankOneSubrankQuotient_sub_theta_two_gt_one_div_fifteen :
    ¬ ∀ {e Y : ℕ}, 1 ≤ e → 4 ≤ Y →
      (1 : ℝ) / 15 <
        rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.not_forall_rankOneSubrankQuotient_sub_theta_two_gt_one_div_fifteen

theorem positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (e Y : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < w i)
    (he : ∀ i ∈ s, 1 ≤ e i)
    (hY : ∀ i ∈ s, 4 ≤ Y i) :
    (21 : ℝ) / 320 <
      (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) /
          (∑ i ∈ s, w i) -
        mobiusMersenneTheta 2 := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty
      s hs w e Y hw he hY

theorem primitive_form_abs_gt_twentyOne_div_threeTwenty
    {e Y q : ℕ} {p : ℤ}
    (he : 1 ≤ e) (hY : 4 ≤ Y) (hq : 1 ≤ q)
    (hquot : rankOneSubrankQuotient e Y = (p : ℝ) / q) :
    (q : ℝ) * (21 : ℝ) / 320 <
      |(q : ℝ) * mobiusMersenneTheta 2 - p| := by
  have hquot' :
      ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient e Y =
        (p : ℝ) / q := by
    simpa [rankOneSubrankQuotient, mobiusMersennePrefix, mobiusMersenneTerm,
      ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
      ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
      Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using hquot
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.primitive_form_abs_gt_twentyOne_div_threeTwenty
      he hY hq hquot'

end PalomarCorpus.ExternalVerification249RankOneSharpFloor

import Mathlib
import ErdosProblems.Erdos249.ResidueClassTotientSeries

namespace PalomarCorpus.ExternalVerification249ResidueClassTotientSeries

noncomputable def dyadicValue (a : ℕ → ℤ) : ℝ := ∑' n : ℕ, (a n : ℝ) / 2 ^ n

noncomputable def totientObservableValue (f : ℕ → ℤ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((f (Nat.totient n % m) : ℤ) : ℝ) / 2 ^ n

noncomputable def totientResidueValue (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((Nat.totient n % m : ℕ) : ℝ) / 2 ^ n

theorem isolated_pulse_separation {a : ℕ → ℤ} {C : ℝ} (hC : ∀ n, |(a n : ℝ)| ≤ C)
    {N L q : ℕ} {t : ℤ} (hq : 1 ≤ q) (hL : 2 * (q : ℝ) * C < 2 ^ L)
    (hcentre : a (N + 1 + L) = t) (ht : t ≠ 0)
    (hzero : ∀ i, i ≤ 2 * L → i ≠ L → a (N + 1 + i) = 0) (k : ℤ) :
    (q : ℝ) * (|(t : ℝ)| - C / 2 ^ L) / 2 ^ (N + 1 + L)
      ≤ |(q : ℝ) * dyadicValue a - (k : ℝ)| := by
  simpa only [dyadicValue, ErdosProblems.Erdos249.dyadicValue] using
    ErdosProblems.Erdos249.isolated_pulse_separation hC hq hL hcentre ht hzero k

theorem irrational_dyadicValue_of_pulses {a : ℕ → ℤ} {C : ℝ} (hC : ∀ n, |(a n : ℝ)| ≤ C)
    (hpulse : ∀ L : ℕ, ∃ p : ℕ, L + 1 < p ∧ a p ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (p - j) = 0 ∧ a (p + j) = 0) :
    Irrational (dyadicValue a) := by
  simpa only [dyadicValue, ErdosProblems.Erdos249.dyadicValue] using
    ErdosProblems.Erdos249.irrational_dyadicValue_of_pulses hC hpulse

theorem two_sided_prime_isolation {m : ℕ} (hm : 2 ≤ m) (L N r : ℕ)
    (hr : Nat.Coprime (r + 1) m) :
    ∃ p : ℕ, N < p ∧ L + 1 < p ∧ p.Prime ∧ Nat.totient p ≡ r [MOD m] ∧
      ∀ j, 0 < j → j ≤ L → m ∣ Nat.totient (p - j) ∧ m ∣ Nat.totient (p + j) :=
  ErdosProblems.Erdos249.two_sided_prime_isolation hm L N r hr

theorem irrational_totientObservable {m : ℕ} (hm : 2 ≤ m) (f : ℕ → ℤ) (hf0 : f 0 = 0)
    {r : ℕ} (hr : r < m) (hcop : Nat.Coprime (r + 1) m) (hfr : f r ≠ 0) :
    Irrational (totientObservableValue f m) := by
  simpa only [totientObservableValue,
    ErdosProblems.Erdos249.totientObservableValue] using
    ErdosProblems.Erdos249.irrational_totientObservable hm f hf0 hr hcop hfr

theorem fixed_resolution_observable_irrational {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℤ)
    (hf0 : f 0 = 0) {r : ℕ} (hr : r < 2 ^ k) (hreven : r % 2 = 0) (hfr : f r ≠ 0) :
    Irrational (totientObservableValue f (2 ^ k)) := by
  simpa only [totientObservableValue,
    ErdosProblems.Erdos249.totientObservableValue] using
    ErdosProblems.Erdos249.fixed_resolution_observable_irrational hk f hf0 hr hreven hfr

theorem residue_series_irrational {m : ℕ} (hm : 3 ≤ m) :
    Irrational (totientResidueValue m) := by
  simpa only [totientResidueValue,
    ErdosProblems.Erdos249.totientResidueValue] using
    ErdosProblems.Erdos249.residue_series_irrational hm

end PalomarCorpus.ExternalVerification249ResidueClassTotientSeries

import Mathlib
import Erdos257PeriodNoncollapse.AllBaseTotientKernel

namespace PalomarCorpus.ExternalVerification249TotientKernelBasis

open Module

theorem allSlopeAffineTotientFormsLinearIndependent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i) :
    LinearIndependent ℚ (fun (i : ι) (n : ℕ) => (Nat.totient (a i * n + b i) : ℚ)) :=
  Erdos257PeriodNoncollapse.linearIndependent_totientAffineForms a b ha hb hcross

def kernelSeq (k j r : ℕ) : ℕ → ℚ := fun n =>
  (Nat.totient (k ^ j * n + r) : ℚ)

abbrev CanonicalIndex (k e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)

def canonicalResidue (k : ℕ) {e : ℕ}
    (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) : ℕ :=
  k * x.2.1.val + (x.2.2.val + 1)

def canonicalFamily (k e : ℕ) : CanonicalIndex k e → ℕ → ℚ
  | Sum.inl i => kernelSeq k i.val 0
  | Sum.inr x => kernelSeq k (x.1.val + 1) (canonicalResidue k x)

abbrev ThroughLevelIndex (k e : ℕ) := Σ j : Fin (e + 1), Fin (k ^ j.val)

def throughLevelFamily (k e : ℕ) : ThroughLevelIndex k e → ℕ → ℚ
  | ⟨j, r⟩ => kernelSeq k j.val r.val

noncomputable def relationMap (k e : ℕ) :
    (ThroughLevelIndex k e → ℚ) →ₗ[ℚ] (ℕ → ℚ) :=
  Fintype.linearCombination ℚ (throughLevelFamily k e)

theorem kernelSeq_eq (k j r : ℕ) :
    kernelSeq k j r = Erdos257PeriodNoncollapse.allBaseTotientKernelSeq k j r := rfl

theorem canonicalResidue_eq (k : ℕ) {e : ℕ}
    (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) :
    canonicalResidue k x = Erdos257PeriodNoncollapse.allBaseCanonicalResidue k x := rfl

theorem canonicalFamily_eq (k e : ℕ) :
    canonicalFamily k e = Erdos257PeriodNoncollapse.allBaseCanonicalFamily k e := by
  funext i
  cases i with
  | inl i => rfl
  | inr x => rfl

theorem throughLevelFamily_eq (k e : ℕ) :
    throughLevelFamily k e = Erdos257PeriodNoncollapse.allBaseThroughLevelFamily k e := by
  funext x
  rcases x with ⟨j, r⟩
  rfl

theorem relationMap_eq (k e : ℕ) :
    relationMap k e = Erdos257PeriodNoncollapse.allBaseRelationMap k e := by
  simp only [relationMap, Erdos257PeriodNoncollapse.allBaseRelationMap,
    throughLevelFamily_eq]

theorem allBaseTotientKernelBasisRankAndRelationDimension
    (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    LinearIndependent ℚ (canonicalFamily k e) ∧
      Submodule.span ℚ (Set.range (throughLevelFamily k e)) =
        Submodule.span ℚ (Set.range (canonicalFamily k e)) ∧
      Nonempty (Basis (CanonicalIndex k e) ℚ
        (Submodule.span ℚ (Set.range (throughLevelFamily k e)))) ∧
      finrank ℚ (Submodule.span ℚ (Set.range (throughLevelFamily k e))) =
        k ^ e + 1 ∧
      finrank ℚ (LinearMap.ker (relationMap k e)) =
        ∑ j ∈ Finset.Ico 1 e, k ^ j := by
  rw [canonicalFamily_eq, throughLevelFamily_eq, relationMap_eq]
  exact ⟨Erdos257PeriodNoncollapse.linearIndependent_allBaseCanonicalFamily k e hk,
    Erdos257PeriodNoncollapse.span_allBaseThroughLevelFamily_eq k e hk he,
    ⟨Erdos257PeriodNoncollapse.allBaseTotientKernelBasis k e hk he⟩,
    Erdos257PeriodNoncollapse.finrank_allBaseThroughLevelFamily_eq k e hk he,
    Erdos257PeriodNoncollapse.finrank_allBaseRelationModule_eq k e hk he⟩

end PalomarCorpus.ExternalVerification249TotientKernelBasis

import ErdosProblems.Erdos251.PrimeGapDyadicTail

open scoped BigOperators

namespace PalomarCorpus.ExternalVerification251ActualPrimeGapTail

noncomputable abbrev prime0 := ErdosProblems.Erdos251.prime0
noncomputable abbrev primeGap0 := ErdosProblems.Erdos251.primeGap0
noncomputable abbrev primeGapDyadicTerm := ErdosProblems.Erdos251.primeGapDyadicTerm
noncomputable abbrev primeGapPartialSumQ := ErdosProblems.Erdos251.primeGapPartialSumQ
abbrev DyadicTailRecurrence := ErdosProblems.Erdos251.DyadicTailRecurrence
noncomputable abbrev rationalPrimeGapTailState :=
  ErdosProblems.Erdos251.rationalPrimeGapTailState
abbrev tailShift := ErdosProblems.Erdos251.tailShift
abbrev RatIntegral := ErdosProblems.Erdos251.RatIntegral

theorem exists_rationalPrimeGapTailState_representation_of_not_irrational
    (h : ¬ Irrational (∑' n : ℕ, primeGapDyadicTerm n)) :
    ∃ S : ℚ,
      (S : ℝ) = ∑' n : ℕ, primeGapDyadicTerm n ∧
      ∀ N,
        ((rationalPrimeGapTailState S N : ℚ) : ℝ) =
          2 ^ (N + 1) *
            ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1)) :=
  ErdosProblems.Erdos251.exists_rationalPrimeGapTailState_representation_of_not_irrational h

theorem rationalPrimeGapTailState_recurrence (S : ℚ) :
    DyadicTailRecurrence (fun n => (primeGap0 n : ℤ))
      (rationalPrimeGapTailState S) :=
  ErdosProblems.Erdos251.rationalPrimeGapTailState_recurrence S

theorem rationalPrimeGapTailShift_eventuallyIntegral
    (S : ℚ) :
    ∃ h, 0 < h ∧
      ∃ N₀, ∀ N, N₀ ≤ N →
        RatIntegral
          (tailShift (rationalPrimeGapTailState S) h N) :=
  ErdosProblems.Erdos251.rationalPrimeGapTailShift_eventuallyIntegral S

theorem rationalPrimeGapTail_has_positive_shift_not_eventually_small
    (S : ℚ) :
    ∃ h, 0 < h ∧
      ¬ ∃ N₀, ∀ N, N₀ ≤ N →
        -1 < tailShift (rationalPrimeGapTailState S) h N ∧
          tailShift (rationalPrimeGapTailState S) h N < 1 :=
  ErdosProblems.Erdos251.rationalPrimeGapTail_has_positive_shift_not_eventually_small S

end PalomarCorpus.ExternalVerification251ActualPrimeGapTail

import Mathlib
import ErdosProblems.Erdos251.FreePairReduction

open scoped BigOperators

namespace PalomarCorpus.ExternalVerification251FreePairEquivalence

noncomputable abbrev prime0 := ErdosProblems.Erdos251.prime0
noncomputable abbrev primeGap0 := ErdosProblems.Erdos251.primeGap0
noncomputable abbrev primeGapDyadicTerm := ErdosProblems.Erdos251.primeGapDyadicTerm
abbrev DyadicTailRecurrence := ErdosProblems.Erdos251.DyadicTailRecurrence
abbrev RealDyadicTailRecurrence := ErdosProblems.Erdos251.RealDyadicTailRecurrence
abbrev realTailShift := ErdosProblems.Erdos251.realTailShift
abbrev RatIntegral := ErdosProblems.Erdos251.RatIntegral
abbrev RealIntegral := ErdosProblems.Erdos251.RealIntegral
abbrev CofinalNonintegralTailShifts := ErdosProblems.Erdos251.CofinalNonintegralTailShifts
abbrev CofinalFreePairNonintegral := ErdosProblems.Erdos251.CofinalFreePairNonintegral
noncomputable abbrev primeGapRealTail := ErdosProblems.Erdos251.primeGapRealTail

theorem irrational_primeGap_tsum_iff_cofinalFreePairNonintegral :
    Irrational (∑' n : ℕ, primeGapDyadicTerm n) ↔
      CofinalFreePairNonintegral primeGapRealTail :=
  ErdosProblems.Erdos251.irrational_primeGap_tsum_iff_cofinalFreePairNonintegral

theorem irrational_initial_iff_cofinalFreePairNonintegral {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔ CofinalFreePairNonintegral T :=
  ErdosProblems.Erdos251.irrational_initial_iff_cofinalFreePairNonintegral hrec

theorem cofinalFreePairNonintegral_iff_cofinalNonintegralTailShifts
    {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T) :
    CofinalFreePairNonintegral T ↔ CofinalNonintegralTailShifts T :=
  ErdosProblems.Erdos251.cofinalFreePairNonintegral_iff_cofinalNonintegralTailShifts hrec

theorem exists_free_pair_lattice {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    ∃ N₀ t : ℕ, 0 < t ∧ ∀ N M : ℕ, N₀ ≤ N → N₀ ≤ M →
      (RatIntegral (T M - T N) ↔ N ≡ M [MOD t]) :=
  ErdosProblems.Erdos251.exists_free_pair_lattice hrec

theorem free_pair_integral_iff_modEq {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) {N₀ : ℕ} (hodd : Odd (T N₀).den)
    {N M : ℕ} (hN : N₀ ≤ N) (hM : N₀ ≤ M) :
    RatIntegral (T M - T N) ↔ N ≡ M [MOD orderOf (2 : ZMod (T N₀).den)] :=
  ErdosProblems.Erdos251.free_pair_integral_iff_modEq hrec hodd hN hM

theorem primeGapRealTail_recurrence :
    RealDyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) primeGapRealTail :=
  ErdosProblems.Erdos251.primeGapRealTail_recurrence

theorem primeGapRealTail_zero :
    primeGapRealTail 0 = 2 * (∑' n : ℕ, primeGapDyadicTerm n) - 1 :=
  ErdosProblems.Erdos251.primeGapRealTail_zero

end PalomarCorpus.ExternalVerification251FreePairEquivalence

import ErdosProblems.Erdos251.KernelDenominatorFloor

open scoped BigOperators

namespace PalomarCorpus.ExternalVerification251KernelDenominatorFloor

noncomputable abbrev prime0 := ErdosProblems.Erdos251.prime0
noncomputable abbrev primeGap0 := ErdosProblems.Erdos251.primeGap0
noncomputable abbrev primeDyadicTerm := ErdosProblems.Erdos251.primeDyadicTerm
noncomputable abbrev primeGapDyadicTerm := ErdosProblems.Erdos251.primeGapDyadicTerm
abbrev noSmallDivisor := ErdosProblems.Erdos251.noSmallDivisor
abbrev isPrimeTD := ErdosProblems.Erdos251.isPrimeTD
abbrev primeSumLoop := ErdosProblems.Erdos251.primeSumLoop
abbrev certCheck := ErdosProblems.Erdos251.certCheck
abbrev certX := ErdosProblems.Erdos251.certX
abbrev certC := ErdosProblems.Erdos251.certC
abbrev certU := ErdosProblems.Erdos251.certU
abbrev certV := ErdosProblems.Erdos251.certV
abbrev certU' := ErdosProblems.Erdos251.certU'
abbrev certV' := ErdosProblems.Erdos251.certV'

/-- The kernel re-runs the `10^4` trial-division sieve and decides the six
conditions on the certificate literals. -/
theorem cert_10000 : certCheck certC certU certV certU' certV' certX = true :=
  ErdosProblems.Erdos251.cert_10000

/-- A passing certificate at any truncation index `c ≥ 9` forces every rational
`a / b` equal to the prime series to satisfy `v + v' ≤ b`. -/
theorem den_bound_of_certCheck (c u v u' v' X : ℕ) (hc : 9 ≤ c)
    (h : certCheck c u v u' v' X = true) :
    ∀ (a : ℤ) (b : ℕ), 0 < b → (∑' n, primeDyadicTerm n) = a / b → v + v' ≤ b :=
  ErdosProblems.Erdos251.den_bound_of_certCheck c u v u' v' X hc h

/-- Every rational `a / b` equal to `S` has `b ≥ 2^589 > 10^177`. -/
theorem kernel_denominator_floor (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b :=
  ErdosProblems.Erdos251.kernel_denominator_floor a b hb hS

/-- The same floor for the prime-gap series `S - 2` of Erdős #251. -/
theorem kernel_denominator_floor_primeGap (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeGapDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b :=
  ErdosProblems.Erdos251.kernel_denominator_floor_primeGap a b hb hS

end PalomarCorpus.ExternalVerification251KernelDenominatorFloor

import Mathlib
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos251.PolynomialGapSeriesValue

namespace PalomarCorpus.ExternalVerification251PolynomialShiftCountermodel

def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N

def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z

def polynomialTailOrbit (n : ℕ) : ℚ :=
  (2 * (n + 4) ^ 2 : ℕ)

def polynomialGapWord (n : ℕ) : ℤ :=
  (2 * (n ^ 2 + 4 * n + 2) : ℕ)

noncomputable def polynomialGapDyadicTerm (n : ℕ) : ℝ :=
  (polynomialGapWord (n + 1) : ℝ) / 2 ^ (n + 1)

/-- The Comparator vocabulary word is the source word. -/
theorem polynomialGapWord_eq_source :
    polynomialGapWord = ErdosProblems.Erdos251.polynomialGapWord := rfl

/-- The Comparator vocabulary series term is the source series term. -/
theorem polynomialGapDyadicTerm_eq_source :
    polynomialGapDyadicTerm = ErdosProblems.Erdos251.polynomialGapDyadicTerm := rfl

theorem polynomialGapTailCountermodel :
    DyadicTailRecurrence polynomialGapWord polynomialTailOrbit ∧
      (∀ n, 0 < polynomialGapWord n) ∧
      (∀ n, ∃ k : ℤ, polynomialGapWord n = 2 * k) ∧
      StrictMono polynomialGapWord ∧
      (∀ h N, RatIntegral (tailShift polynomialTailOrbit h N)) ∧
      (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n = ((4 * n + 10 : ℕ) : ℤ)) ∧
      (∀ n,
        polynomialGapWord (n + 1) - polynomialGapWord n ≠ 2 ∧
        polynomialGapWord (n + 1) - polynomialGapWord n ≠ -2) ∧
      (∑' n : ℕ, polynomialGapDyadicTerm n) = 32 ∧
      ¬ Irrational (∑' n : ℕ, polynomialGapDyadicTerm n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [DyadicTailRecurrence, polynomialGapWord, polynomialTailOrbit,
      ErdosProblems.Erdos251.DyadicTailRecurrence,
      ErdosProblems.Erdos251.polynomialGapWord,
      ErdosProblems.Erdos251.polynomialTailOrbit] using
      ErdosProblems.Erdos251.polynomialTailOrbit_recurrence
  · intro n
    simpa [polynomialGapWord, ErdosProblems.Erdos251.polynomialGapWord] using
      ErdosProblems.Erdos251.polynomialGapWord_pos n
  · intro n
    simpa [polynomialGapWord, ErdosProblems.Erdos251.polynomialGapWord] using
      ErdosProblems.Erdos251.polynomialGapWord_even n
  · simpa [polynomialGapWord, ErdosProblems.Erdos251.polynomialGapWord] using
      ErdosProblems.Erdos251.polynomialGapWord_strictMono
  · intro h N
    simpa [tailShift, RatIntegral, polynomialTailOrbit,
      ErdosProblems.Erdos251.tailShift,
      ErdosProblems.Erdos251.RatIntegral,
      ErdosProblems.Erdos251.polynomialTailOrbit] using
      ErdosProblems.Erdos251.polynomialTailOrbit_shift_integral h N
  · intro n
    rw [polynomialGapWord_eq_source]
    exact ErdosProblems.Erdos251.polynomialGapWord_succ_sub n
  · intro n
    rw [polynomialGapWord_eq_source]
    exact ⟨ErdosProblems.Erdos251.polynomialGapWord_adjacent_difference_ne_two n,
      ErdosProblems.Erdos251.polynomialGapWord_adjacent_difference_ne_neg_two n⟩
  · rw [polynomialGapDyadicTerm_eq_source]
    exact ErdosProblems.Erdos251.tsum_polynomialGapDyadicTerm_eq
  · rw [polynomialGapDyadicTerm_eq_source]
    exact ErdosProblems.Erdos251.not_irrational_tsum_polynomialGapDyadicTerm

end PalomarCorpus.ExternalVerification251PolynomialShiftCountermodel

import ErdosProblems.Erdos251.PrimeGapDyadicTail

namespace PalomarCorpus.ExternalVerification251PrimeGapIdentity

noncomputable abbrev prime0 := ErdosProblems.Erdos251.prime0
noncomputable abbrev primeGap0 := ErdosProblems.Erdos251.primeGap0
noncomputable abbrev primeDyadicTerm := ErdosProblems.Erdos251.primeDyadicTerm
noncomputable abbrev primeDisplayedDyadicTerm :=
  ErdosProblems.Erdos251.primeDisplayedDyadicTerm
noncomputable abbrev primeGapDyadicTerm :=
  ErdosProblems.Erdos251.primeGapDyadicTerm

theorem prime0_le_polynomial (n : ℕ) :
    prime0 n ≤ 1250 * (n + 1) ^ 4 :=
  ErdosProblems.Erdos251.prime0_le_polynomial n

theorem primeSeries_summable : Summable primeDyadicTerm :=
  ErdosProblems.Erdos251.summable_primeDyadicTerm

theorem primeGapSeries_summable : Summable primeGapDyadicTerm :=
  ErdosProblems.Erdos251.summable_primeGapDyadicTerm

theorem primeSeries_eq_two_add_primeGapSeries :
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n :=
  ErdosProblems.Erdos251.tsum_primeDyadicTerm_eq_two_add_primeGap_unconditional

theorem primeSeries_irrational_iff_primeGapSeries :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) :=
  ErdosProblems.Erdos251.irrational_tsum_primeDyadicTerm_iff_primeGap
    ErdosProblems.Erdos251.summable_primeDyadicTerm

theorem primeDisplayedSeries_eq_four_add_two_primeGapSeries :
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
      4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n :=
  ErdosProblems.Erdos251.tsum_primeDisplayedDyadicTerm_eq_four_add_two_primeGap
    ErdosProblems.Erdos251.summable_primeDyadicTerm

theorem primeDisplayedSeries_irrational_iff_primeGapSeries :
    Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) :=
  ErdosProblems.Erdos251.irrational_tsum_primeDisplayedDyadicTerm_iff_primeGap
    ErdosProblems.Erdos251.summable_primeDyadicTerm

end PalomarCorpus.ExternalVerification251PrimeGapIdentity

import Mathlib
import ErdosProblems.Erdos257.MersenneSubseriesRigidity

namespace PalomarCorpus.ExternalVerification257AchievementSetGeometry

open scoped ENNReal

open Set MeasureTheory

noncomputable section

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)

noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

def SupportedMersenneDigits (J : Set ℕ) :=
  {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0}

noncomputable def supportedMersenneDigitValue
    (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ :=
  positiveMersenneDigitValue b.1

def supportedMersenneAchievementSet (J : Set ℕ) : Set ℝ :=
  Set.range (supportedMersenneDigitValue J)

theorem volume_supportedMersenneAchievementSet_eq_zero_of_rat_value
    {J : Set ℕ} (hJ0 : 0 ∉ J) {q : ℚ}
    (hvalue : positiveMersenneSupportValue J = (q : ℝ)) :
    volume (supportedMersenneAchievementSet J) = 0 := by
  have hsrc : Erdos257PeriodNoncollapse.positiveMersenneSupportValue J = (q : ℝ) := by
    first
      | exact hvalue
      | simpa [positiveMersenneSupportValue, mersenneWeight,
          Erdos257PeriodNoncollapse.positiveMersenneSupportValue,
          Erdos257PeriodNoncollapse.mersenneWeight] using hvalue
  first
    | exact ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_eq_zero_of_rat_value
        hJ0 hsrc
    | simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
        SupportedMersenneDigits, positiveMersenneDigitValue,
        mersenneDigitTerm, mersenneWeight,
        ErdosProblems.Erdos257.supportedMersenneAchievementSet,
        ErdosProblems.Erdos257.supportedMersenneDigitValue,
        ErdosProblems.Erdos257.SupportedMersenneDigits,
        Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
        Erdos257PeriodNoncollapse.mersenneDigitTerm,
        Erdos257PeriodNoncollapse.mersenneWeight] using
        ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_eq_zero_of_rat_value
          hJ0 hsrc

theorem supportedMersenneAchievementSet_geometry_and_volume (J : Set ℕ) :
    Function.Injective (supportedMersenneDigitValue J) ∧
      IsCompact (supportedMersenneAchievementSet J) ∧
      IsNowhereDense (supportedMersenneAchievementSet J) ∧
      (J.Infinite → Perfect (supportedMersenneAchievementSet J)) ∧
      ((∃ F : Finset ℕ,
          J = (↑F : Set ℕ)ᶜ ∧
            volume (supportedMersenneAchievementSet J) =
              ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
        (Jᶜ.Infinite ∧
          volume (supportedMersenneAchievementSet J) = 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · first
      | exact ErdosProblems.Erdos257.supportedMersenneDigitValue_injective J
      | simpa [supportedMersenneDigitValue, SupportedMersenneDigits,
          positiveMersenneDigitValue, mersenneDigitTerm, mersenneWeight,
          ErdosProblems.Erdos257.supportedMersenneDigitValue,
          ErdosProblems.Erdos257.SupportedMersenneDigits,
          Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
          Erdos257PeriodNoncollapse.mersenneDigitTerm,
          Erdos257PeriodNoncollapse.mersenneWeight] using
          ErdosProblems.Erdos257.supportedMersenneDigitValue_injective J
  · first
      | exact ErdosProblems.Erdos257.isCompact_supportedMersenneAchievementSet J
      | simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
          SupportedMersenneDigits, positiveMersenneDigitValue,
          mersenneDigitTerm, mersenneWeight,
          ErdosProblems.Erdos257.supportedMersenneAchievementSet,
          ErdosProblems.Erdos257.supportedMersenneDigitValue,
          ErdosProblems.Erdos257.SupportedMersenneDigits,
          Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
          Erdos257PeriodNoncollapse.mersenneDigitTerm,
          Erdos257PeriodNoncollapse.mersenneWeight] using
          ErdosProblems.Erdos257.isCompact_supportedMersenneAchievementSet J
  · first
      | exact ErdosProblems.Erdos257.isNowhereDense_supportedMersenneAchievementSet J
      | simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
          SupportedMersenneDigits, positiveMersenneDigitValue,
          mersenneDigitTerm, mersenneWeight,
          ErdosProblems.Erdos257.supportedMersenneAchievementSet,
          ErdosProblems.Erdos257.supportedMersenneDigitValue,
          ErdosProblems.Erdos257.SupportedMersenneDigits,
          Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
          Erdos257PeriodNoncollapse.mersenneDigitTerm,
          Erdos257PeriodNoncollapse.mersenneWeight] using
          ErdosProblems.Erdos257.isNowhereDense_supportedMersenneAchievementSet J
  · intro hJ
    first
      | exact ErdosProblems.Erdos257.perfect_supportedMersenneAchievementSet hJ
      | simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
          SupportedMersenneDigits, positiveMersenneDigitValue,
          mersenneDigitTerm, mersenneWeight,
          ErdosProblems.Erdos257.supportedMersenneAchievementSet,
          ErdosProblems.Erdos257.supportedMersenneDigitValue,
          ErdosProblems.Erdos257.SupportedMersenneDigits,
          Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
          Erdos257PeriodNoncollapse.mersenneDigitTerm,
          Erdos257PeriodNoncollapse.mersenneWeight] using
          ErdosProblems.Erdos257.perfect_supportedMersenneAchievementSet hJ
  · first
      | exact ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_dichotomy J
      | simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
          SupportedMersenneDigits, positiveMersenneDigitValue,
          mersenneDigitTerm, mersenneWeight,
          ErdosProblems.Erdos257.supportedMersenneAchievementSet,
          ErdosProblems.Erdos257.supportedMersenneDigitValue,
          ErdosProblems.Erdos257.SupportedMersenneDigits,
          Erdos257PeriodNoncollapse.positiveMersenneDigitValue,
          Erdos257PeriodNoncollapse.mersenneDigitTerm,
          Erdos257PeriodNoncollapse.mersenneWeight] using
          ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_dichotomy J

end

end PalomarCorpus.ExternalVerification257AchievementSetGeometry

import Mathlib
import Erdos257PeriodNoncollapse.CertificateKernel

namespace PalomarCorpus.ExternalVerification257FinitePeriodNoncollapse

def finiteErdosSum (F : Finset ℕ) (b : ℕ) : ℚ :=
  ∑ n ∈ F, 1 / ((b : ℚ) ^ n - 1)

theorem finite_period_noncollapse_rat_den
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    ∃ hcop : Nat.Coprime b (finiteErdosSum F b).den,
      orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id := by
  have hcop : Nat.Coprime b (finiteErdosSum F b).den := by
    simpa [finiteErdosSum,
      Erdos257PeriodNoncollapse.finiteErdosSum] using
      Erdos257PeriodNoncollapse.coprime_base_den_finiteErdosSum
        F b h0 hb
  refine ⟨hcop, ?_⟩
  simpa [finiteErdosSum,
      Erdos257PeriodNoncollapse.finiteErdosSum] using
      Erdos257PeriodNoncollapse.finite_period_noncollapse_rat_den
        F b hF h0 hb

theorem lcm_lt_den_finiteErdosSum
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (h2 : 2 ≤ F.lcm id) :
    F.lcm id < (finiteErdosSum F b).den := by
  simpa [finiteErdosSum,
      Erdos257PeriodNoncollapse.finiteErdosSum] using
      Erdos257PeriodNoncollapse.lcm_lt_den_finiteErdosSum
        F b hF h0 hb h2

end PalomarCorpus.ExternalVerification257FinitePeriodNoncollapse

import Erdos257PeriodNoncollapse.SublogDivisorCoverage

namespace PalomarCorpus.ExternalVerification257RationalTailRigidity

open Filter Set

noncomputable section

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

def CoeffZeroWindow (f : ℕ → ℕ) (N h : ℕ) : Prop :=
  ∀ j : ℕ, j < h → f (N + j + 1) = 0

def SupportCoeffZeroWindow (A : Set ℕ) (N h : ℕ) : Prop :=
  CoeffZeroWindow (supportCoeff A) N h

noncomputable def reciprocalSupportTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a

noncomputable def reciprocalMass (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, reciprocalSupportTerm A a

noncomputable def oddDoublingOrder (v : ℕ) (hvodd : Odd v) : ℕ :=
  orderOf (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hvodd))

theorem exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ∃ u : ℕ → ℕ,
      (∀ n : ℕ, (u n : ℝ) =
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
      (∀ n : ℕ, 0 < u n) ∧
      (∀ n : ℕ, u (n + 1) +
        v * supportCoeff A (c + n + 1) = 2 * u n) ∧
      (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v]) ∧
      (∀ B : ℕ, ∃ n : ℕ, B < u n) := by
  simpa [supportCoeff, erdosSupportSeries, binaryCoeffTail,
    Erdos257PeriodNoncollapse.supportCoeff,
    Erdos257PeriodNoncollapse.erdosSupportSeries,
    Erdos257PeriodNoncollapse.binaryCoeffTail] using
      Erdos257PeriodNoncollapse.exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction
        A hAinf p c v hv (by
          simpa [erdosSupportSeries,
            Erdos257PeriodNoncollapse.erdosSupportSeries] using hvalue)

theorem supportCoeffZeroWindow_length_le_eps_logb_add
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ N h : ℕ,
        SupportCoeffZeroWindow A (c + N) h →
        (h : ℝ) ≤ ε * Real.logb 2 (N + 1 : ℝ) + B := by
  simpa [SupportCoeffZeroWindow, CoeffZeroWindow, supportCoeff,
    erdosSupportSeries,
    Erdos257PeriodNoncollapse.SupportCoeffZeroWindow,
    Erdos257PeriodNoncollapse.CoeffZeroWindow,
    Erdos257PeriodNoncollapse.supportCoeff,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
      Erdos257PeriodNoncollapse.supportCoeffZeroWindow_length_le_eps_logb_add
        A hA p c v hv (by
          simpa [erdosSupportSeries,
            Erdos257PeriodNoncollapse.erdosSupportSeries] using hvalue) ε hε

theorem one_div_oddOrder_le_reciprocalMass_of_support_fraction
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (hsum : Summable (reciprocalSupportTerm A))
    (p : ℤ) (c : ℕ) {v : ℕ} (hv : 1 < v) (hvodd : Odd v)
    (hpv : p.toNat.Coprime v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    (1 : ℝ) / (oddDoublingOrder v hvodd : ℝ) ≤ reciprocalMass A := by
  simpa [reciprocalSupportTerm, reciprocalMass, oddDoublingOrder,
    erdosSupportSeries,
    Erdos257PeriodNoncollapse.reciprocalSupportTerm,
    Erdos257PeriodNoncollapse.reciprocalMass,
    Erdos257PeriodNoncollapse.oddDoublingOrder,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
      Erdos257PeriodNoncollapse.one_div_oddOrder_le_reciprocalMass_of_support_fraction
        A hA (by
          simpa [reciprocalSupportTerm,
            Erdos257PeriodNoncollapse.reciprocalSupportTerm] using hsum)
        p c hv hvodd hpv (by
          simpa [erdosSupportSeries,
            Erdos257PeriodNoncollapse.erdosSupportSeries] using hvalue)

theorem dyadic_support_fraction_reciprocalMass_diverges_or_gt_one
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c : ℕ)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    ¬ Summable (reciprocalSupportTerm A) ∨ 1 < reciprocalMass A := by
  simpa [reciprocalSupportTerm, reciprocalMass, erdosSupportSeries,
    Erdos257PeriodNoncollapse.reciprocalSupportTerm,
    Erdos257PeriodNoncollapse.reciprocalMass,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
      Erdos257PeriodNoncollapse.dyadic_support_fraction_reciprocalMass_diverges_or_gt_one
        A hAinf p c (by
          simpa [erdosSupportSeries,
            Erdos257PeriodNoncollapse.erdosSupportSeries] using hvalue)

end

end PalomarCorpus.ExternalVerification257RationalTailRigidity

import Mathlib
import Erdos257PeriodNoncollapse.AllBaseReciprocalSupportIrrationality

namespace PalomarCorpus.ExternalVerification257ReciprocalSupport

noncomputable section

noncomputable def supportReciprocalTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a

noncomputable def supportPowerSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a : ℕ => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

theorem irrational_supportPowerSeries_of_summable_reciprocal
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable (supportReciprocalTerm A)) :
    Irrational (supportPowerSeries b A) := by
  simpa [supportReciprocalTerm, supportPowerSeries,
    Erdos257PeriodNoncollapse.reciprocalSupportTerm,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
    Erdos257PeriodNoncollapse.irrational_erdosSupportSeries_of_summable_reciprocal
      b A hb hA hsum

end

end PalomarCorpus.ExternalVerification257ReciprocalSupport

import Mathlib
import ErdosProblems.Erdos269.DyadicShellSummability

namespace PalomarCorpus.ExternalVerification269ActualShellOrbit

open scoped BigOperators

noncomputable section

def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k

def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

def strictSmoothExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range x).product ((Finset.range x).product (Finset.range x))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 < x

def strictSmoothShell (p q r x y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothExponents p q r y \ strictSmoothExponents p q r x

def dyadicSmoothShell235 (a : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothShell 2 3 5 (2 ^ a) (2 ^ (a + 1))

def dyadicShellMassQ235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    ((threePrimeHeight 2 3 5
      (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹)

def dyadicShellMassR235 (a : ℕ) : ℝ :=
  dyadicShellMassQ235 a

def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)

noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 *
        (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
        (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)

def dyadicBeforeThresholdCount235 (p a : ℕ) : ℕ :=
  ((dyadicSmoothShell235 a).filter fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      p ^ Nat.log p (2 ^ (a + 1))).card

def dyadicOrderedBlockDigit235 (a : ℕ) : ℕ :=
  if 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤ 5 ^ Nat.log 5 (2 ^ (a + 1)) then
    (dyadicSmoothShell235 a).card +
      10 * dyadicBeforeThresholdCount235 3 a +
      4 * dyadicBeforeThresholdCount235 5 a
  else
    (dyadicSmoothShell235 a).card +
      2 * dyadicBeforeThresholdCount235 3 a +
      12 * dyadicBeforeThresholdCount235 5 a

noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ :=
  ∑' n : ℕ, dyadicShellMassR235 (a + n)

noncomputable def dyadicNormalizedTailStateR235
    (tail : ℕ → ℝ) (a : ℕ) : ℝ :=
  ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a

def FarFromIntegers (x δ : ℝ) : Prop :=
  ∀ z : ℤ, δ ≤ |x - (z : ℝ)|

theorem actual_dyadicShellOrbit_recurrence_and_escape :
    Summable dyadicShellMassR235 ∧
      (∀ a : ℕ,
        dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (a + 1) =
          dyadicBlockBase235 a *
              dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a -
            dyadicOrderedBlockDigit235 a) ∧
      ((∃ a : ℕ, ∃ z : ℤ,
          dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a = (z : ℝ)) ∨
        ∀ a₀, ∃ a, a₀ ≤ a ∧
          FarFromIntegers
            (dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a)
            ((1 : ℝ) / 31)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [dyadicShellMassR235, dyadicShellMassQ235,
      dyadicSmoothShell235, strictSmoothShell, strictSmoothExponents,
      threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.dyadicShellMassR235,
      ErdosProblems.Erdos269.dyadicShellMassQ235,
      ErdosProblems.Erdos269.dyadicSmoothShell235,
      ErdosProblems.Erdos269.strictSmoothShell,
      ErdosProblems.Erdos269.strictSmoothExponents,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.summable_dyadicShellMassR235
  · intro a
    simpa [dyadicNormalizedTailStateR235, dyadicShellTsumTailR235,
      dyadicShellMassR235, dyadicShellMassQ235, dyadicBlockBase235,
      DyadicInternalPower, dyadicOrderedBlockDigit235,
      dyadicBeforeThresholdCount235, dyadicSmoothShell235,
      strictSmoothShell, strictSmoothExponents, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.dyadicNormalizedTailStateR235,
      ErdosProblems.Erdos269.dyadicShellTsumTailR235,
      ErdosProblems.Erdos269.dyadicShellMassR235,
      ErdosProblems.Erdos269.dyadicShellMassQ235,
      ErdosProblems.Erdos269.dyadicBlockBase235,
      ErdosProblems.Erdos269.DyadicInternalPower,
      ErdosProblems.Erdos269.dyadicOrderedBlockDigit235,
      ErdosProblems.Erdos269.dyadicBeforeThresholdCount235,
      ErdosProblems.Erdos269.dyadicSmoothShell235,
      ErdosProblems.Erdos269.strictSmoothShell,
      ErdosProblems.Erdos269.strictSmoothExponents,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.dyadicNormalizedShellTsumTailR235_succ a
  · simpa [FarFromIntegers, dyadicNormalizedTailStateR235,
      dyadicShellTsumTailR235, dyadicShellMassR235, dyadicShellMassQ235,
      dyadicBlockBase235, DyadicInternalPower, dyadicOrderedBlockDigit235,
      dyadicBeforeThresholdCount235, dyadicSmoothShell235,
      strictSmoothShell, strictSmoothExponents, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.FarFromIntegers,
      ErdosProblems.Erdos269.dyadicNormalizedTailStateR235,
      ErdosProblems.Erdos269.dyadicShellTsumTailR235,
      ErdosProblems.Erdos269.dyadicShellMassR235,
      ErdosProblems.Erdos269.dyadicShellMassQ235,
      ErdosProblems.Erdos269.dyadicBlockBase235,
      ErdosProblems.Erdos269.DyadicInternalPower,
      ErdosProblems.Erdos269.dyadicOrderedBlockDigit235,
      ErdosProblems.Erdos269.dyadicBeforeThresholdCount235,
      ErdosProblems.Erdos269.dyadicSmoothShell235,
      ErdosProblems.Erdos269.strictSmoothShell,
      ErdosProblems.Erdos269.strictSmoothExponents,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.dyadicShellTsumTail_integer_or_cofinal_far

end

end PalomarCorpus.ExternalVerification269ActualShellOrbit

import Mathlib
import ErdosProblems.Erdos269.KernelCarryRank
import ErdosProblems.Erdos269.ThreePrimeRunningLcm

namespace PalomarCorpus.ExternalVerification269ThreePrimeStructure

def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k

def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹

def smoothPrefixExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (Nat.log p x + 1)).product
      ((Finset.range (Nat.log q x + 1)).product
        (Finset.range (Nat.log r x + 1)))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 ≤ x

def smoothPrefixLcm (p q r x : ℕ) : ℕ :=
  (smoothPrefixExponents p q r x).lcm
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2

def SameThreePrimeLogCell (p q r x y : ℕ) : Prop :=
  Nat.log p x = Nat.log p y ∧
    Nat.log q x = Nat.log q y ∧
      Nat.log r x = Nat.log r y

def positivePrimePowers (p count : ℕ) : Finset ℕ :=
  (Finset.range count).image fun e => p ^ (e + 1)

def threePrimePositiveJumpSet (p q r count : ℕ) : Finset ℕ :=
  (positivePrimePowers p count ∪ positivePrimePowers q count) ∪
    positivePrimePowers r count

def smoothExponentBox (hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (hp + 1)).product
    ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))

def smoothPointHeight (p q r : ℕ) (e : ℕ × ℕ × ℕ) : ℕ :=
  threePrimeHeight p q r (smooth3Val p q r e.1 e.2.1 e.2.2)

def smoothHeightFiber
    (p q r hp hq hr H : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (smoothExponentBox hp hq hr).filter fun e => smoothPointHeight p q r e = H

def smoothExponentShell
    (p q r lo hi hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (hp + 1)).product
      ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))).filter
    fun e => lo ≤ smooth3Val p q r e.1 e.2.1 e.2.2 ∧
      smooth3Val p q r e.1 e.2.1 e.2.2 < hi

theorem smoothPrefixLcm_eq_threePrimeHeight
    {p q r x : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hx : x ≠ 0) :
    smoothPrefixLcm p q r x = threePrimeHeight p q r x := by
  simpa [smoothPrefixLcm, smoothPrefixExponents, smooth3Val,
    threePrimeHeight, ErdosProblems.Erdos269.smoothPrefixLcm,
    ErdosProblems.Erdos269.smoothPrefixExponents,
    ErdosProblems.Erdos269.smooth3Val,
    ErdosProblems.Erdos269.threePrimeHeight] using
    ErdosProblems.Erdos269.smoothPrefixLcm_eq_threePrimeHeight
      hp hq hr hpq hpr hqr hx

theorem threePrimeKernelQ_eq_of_sameLogCell
    {p q r i j k i' j' k' : ℕ}
    (hcell : SameThreePrimeLogCell p q r
      (smooth3Val p q r i j k) (smooth3Val p q r i' j' k')) :
    threePrimeKernelQ p q r i j k =
      threePrimeKernelQ p q r i' j' k' := by
  have hcell' : ErdosProblems.Erdos269.SameThreePrimeLogCell p q r
      (ErdosProblems.Erdos269.smooth3Val p q r i j k)
      (ErdosProblems.Erdos269.smooth3Val p q r i' j' k') := by
    simpa [SameThreePrimeLogCell, smooth3Val,
      ErdosProblems.Erdos269.SameThreePrimeLogCell,
      ErdosProblems.Erdos269.smooth3Val] using hcell
  simpa [SameThreePrimeLogCell, smooth3Val, threePrimeHeight,
    threePrimeKernelQ, ErdosProblems.Erdos269.SameThreePrimeLogCell,
    ErdosProblems.Erdos269.smooth3Val,
    ErdosProblems.Erdos269.threePrimeHeight,
    ErdosProblems.Erdos269.threePrimeKernelQ] using
    ErdosProblems.Erdos269.threePrimeKernelQ_eq_of_sameLogCell hcell'

theorem threePrimePositiveJumpSet_card
    {p q r count : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (threePrimePositiveJumpSet p q r count).card = 3 * count := by
  simpa [threePrimePositiveJumpSet, positivePrimePowers,
    ErdosProblems.Erdos269.threePrimePositiveJumpSet,
    ErdosProblems.Erdos269.positivePrimePowers] using
    ErdosProblems.Erdos269.threePrimePositiveJumpSet_card
      hp hq hr hpq hpr hqr

theorem finiteSmoothKernelSum_groupedByHeight
    (p q r hp hq hr : ℕ) :
    (∑ e ∈ smoothExponentBox hp hq hr,
      threePrimeKernelQ p q r e.1 e.2.1 e.2.2) =
      ∑ H ∈ (smoothExponentBox hp hq hr).image (smoothPointHeight p q r),
        (smoothHeightFiber p q r hp hq hr H).card • ((H : ℚ)⁻¹) := by
  simpa [smoothExponentBox, smoothPointHeight, smoothHeightFiber,
    smooth3Val, threePrimeHeight, threePrimeKernelQ,
    ErdosProblems.Erdos269.smoothExponentBox,
    ErdosProblems.Erdos269.smoothPointHeight,
    ErdosProblems.Erdos269.smoothHeightFiber,
    ErdosProblems.Erdos269.smooth3Val,
    ErdosProblems.Erdos269.threePrimeHeight,
    ErdosProblems.Erdos269.threePrimeKernelQ] using
    ErdosProblems.Erdos269.finiteSmoothKernelSum_groupedByHeight
      p q r hp hq hr

theorem smoothExponentShell_card_quadratic
    {p q r lo hi hp hq hr j : ℕ}
    (hrPos : 0 < r) (hwidth : hi ≤ r * lo)
    (hpq : hp ≤ hq) (hqr : hq ≤ hr)
    (hsum : hp + hq + hr = j) :
    9 * (smoothExponentShell p q r lo hi hp hq hr).card ≤
      (j + 3) ^ 2 := by
  simpa [smoothExponentShell, smooth3Val,
    ErdosProblems.Erdos269.smoothExponentShell,
    ErdosProblems.Erdos269.smooth3Val] using
    ErdosProblems.Erdos269.smoothExponentShell_card_quadratic
      hrPos hwidth hpq hqr hsum

theorem kernel_235_minor_eq_neg_one_fifteen :
    threePrimeKernelQ 2 3 5 0 0 0 *
          threePrimeKernelQ 2 3 5 1 1 0 -
        threePrimeKernelQ 2 3 5 1 0 0 *
          threePrimeKernelQ 2 3 5 0 1 0 =
      -(1 / 15 : ℚ) := by
  simpa [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    ErdosProblems.Erdos269.threePrimeKernelQ,
    ErdosProblems.Erdos269.threePrimeHeight,
    ErdosProblems.Erdos269.smooth3Val] using
    ErdosProblems.Erdos269.kernel_235_minor_eq_neg_one_fifteen

def NoIntegerOrbit (α : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → Int.fract ((n : ℝ) * α) ≠ 0

theorem exists_uniform_nonsingular_threePrimeKernel_minor
    {p q r : ℕ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hα : NoIntegerOrbit (Real.logb r p)) (hβ : NoIntegerOrbit (Real.logb r q))
    (n : ℕ) :
    ∃ I J : Fin n → ℕ,
      Function.Injective I ∧ Function.Injective J ∧
        ∀ k : ℕ,
          (Matrix.det fun a b : Fin n =>
            threePrimeKernelQ p q r (I a) (J b) k) ≠ 0 := by
  have hα' : ErdosProblems.Shared.NoIntegerOrbit (Real.logb r p) := hα
  have hβ' : ErdosProblems.Shared.NoIntegerOrbit (Real.logb r q) := hβ
  simpa [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    ErdosProblems.Erdos269.threePrimeKernelQ,
    ErdosProblems.Erdos269.threePrimeHeight,
    ErdosProblems.Erdos269.smooth3Val] using
    ErdosProblems.Erdos269.exists_uniform_nonsingular_threePrimeKernel_minor
      hp hq hr hα' hβ' n

theorem threePrimeKernel_infiniteRank_and_noFiniteSeparation
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    (∀ n : ℕ,
      ∃ I J : Fin n → ℕ,
        Function.Injective I ∧ Function.Injective J ∧
          ∀ k : ℕ,
            (Matrix.det fun a b : Fin n =>
              threePrimeKernelQ p q r (I a) (J b) k) ≠ 0) ∧
      (∀ d : ℕ,
        ¬ ∃ (f : Fin d → ℕ → ℚ) (G : Fin d → ℕ → ℕ → ℚ),
            ∀ i j k,
              threePrimeKernelQ p q r i j k =
                ∑ l : Fin d, f l i * G l j k) := by
  constructor
  · intro n
    simpa [threePrimeKernelQ, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.threePrimeKernelQ,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.exists_uniform_nonsingular_threePrimeKernel_minor_of_prime
        hp hq hr hpr hqr n
  · intro d
    simpa [threePrimeKernelQ, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.threePrimeKernelQ,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.not_finite_separable_threePrimeKernel
        hp hq hr hpr hqr d

end PalomarCorpus.ExternalVerification269ThreePrimeStructure

import Mathlib
import ErdosProblems.Erdos269.CofinalWindowEscapeEquivalence

namespace PalomarCorpus.ExternalVerification269WindowEscapeEquivalence

abbrev smooth3Val := ErdosProblems.Erdos269.smooth3Val
abbrev threePrimeHeight := ErdosProblems.Erdos269.threePrimeHeight
abbrev strictSmoothExponents := ErdosProblems.Erdos269.strictSmoothExponents
abbrev strictSmoothShell := ErdosProblems.Erdos269.strictSmoothShell
abbrev dyadicSmoothShell235 := ErdosProblems.Erdos269.dyadicSmoothShell235
abbrev dyadicShellMassQ235 := ErdosProblems.Erdos269.dyadicShellMassQ235
abbrev dyadicShellMassR235 := ErdosProblems.Erdos269.dyadicShellMassR235
abbrev DyadicInternalPower := ErdosProblems.Erdos269.DyadicInternalPower
noncomputable abbrev dyadicBlockBase235 := ErdosProblems.Erdos269.dyadicBlockBase235
abbrev dyadicBeforeThresholdCount235 :=
  ErdosProblems.Erdos269.dyadicBeforeThresholdCount235
abbrev dyadicOrderedBlockDigit235 :=
  ErdosProblems.Erdos269.dyadicOrderedBlockDigit235
noncomputable abbrev dyadicShellTsumTailR235 := ErdosProblems.Erdos269.dyadicShellTsumTailR235
noncomputable abbrev dyadicNormalizedTailStateR235 :=
  ErdosProblems.Erdos269.dyadicNormalizedTailStateR235
noncomputable abbrev trueNormalizedState := ErdosProblems.Erdos269.trueNormalizedState
abbrev leastPositiveResidue := ErdosProblems.Erdos269.leastPositiveResidue
abbrev windowBase := ErdosProblems.Erdos269.windowBase
abbrev windowForcing := ErdosProblems.Erdos269.windowForcing
abbrev CofinalLocalWindowEscape :=
  ErdosProblems.Erdos269.CofinalLocalWindowEscape
abbrev bridgeWidth := ErdosProblems.Erdos269.bridgeWidth
abbrev ActualCofinalLocalWindowEscape :=
  ErdosProblems.Erdos269.ActualCofinalLocalWindowEscape

theorem actualCofinalLocalWindowEscape_iff_irrational_value :
    ActualCofinalLocalWindowEscape ↔ Irrational (dyadicShellTsumTailR235 0) :=
  ErdosProblems.Erdos269.actualCofinalLocalWindowEscape_iff_irrational_value

theorem actualCofinalLocalWindowEscape_iff :
    ActualCofinalLocalWindowEscape ↔ Irrational (dyadicShellTsumTailR235 1) :=
  ErdosProblems.Erdos269.actualCofinalLocalWindowEscape_iff

theorem cofinalLocalWindowEscape_of_irrational
    (h : Irrational (dyadicShellTsumTailR235 1)) :
    ActualCofinalLocalWindowEscape :=
  ErdosProblems.Erdos269.cofinalLocalWindowEscape_of_irrational h

theorem cofinalLocalWindowEscape_of_irrational_of_quadratic
    (h : Irrational (dyadicShellTsumTailR235 1)) (sb : ℕ → ℕ → ℕ) (c : ℕ → ℕ)
    (hsb : ∀ B n, sb B n ≤ c B * (n + 1) ^ 2) :
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 sb :=
  ErdosProblems.Erdos269.cofinalLocalWindowEscape_of_irrational_of_quadratic
    h sb c hsb

theorem exists_reducedCarry_of_value_eq_rat
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) :
    ∃ (B a₀ : ℕ) (d : ℕ → ℤ), 0 < B ∧ Nat.Coprime B 30 ∧
      (∀ n, a₀ ≤ n →
        d (n + 1) = (dyadicBlockBase235 n : ℤ) * d n
          - (B : ℤ) * (dyadicOrderedBlockDigit235 n : ℤ)) ∧
      (∀ n, a₀ ≤ n → 0 < d n) ∧
      (∀ n, a₀ ≤ n → Int.natAbs (d n) ≤ B * bridgeWidth n) :=
  ErdosProblems.Erdos269.exists_reducedCarry_of_value_eq_rat hq hval

theorem trueNormalizedState_window (lo len : ℕ) :
    trueNormalizedState (lo + len)
      = ((windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len : ℤ) : ℝ)
          * trueNormalizedState lo
        - ((windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
              (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len : ℤ) : ℝ) :=
  ErdosProblems.Erdos269.trueNormalizedState_window lo len

theorem near_integer_of_residue_le_general
    (B lo len K : ℕ) (hB : 0 < B)
    (hKle : B * bridgeWidth (lo + len) ≤ K)
    (hres : leastPositiveResidue
        (Int.natAbs (windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len))
        (-((B : ℤ) * windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
             (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len))
      ≤ K) :
    ∃ k : ℤ, |(B : ℝ) * trueNormalizedState lo - (k : ℝ)|
      ≤ ((K : ℕ) : ℝ) / 2 ^ len :=
  ErdosProblems.Erdos269.near_integer_of_residue_le_general
    B lo len K hB hKle hres

theorem exists_pow_gt_quadratic (c lo : ℕ) :
    ∃ len : ℕ, 0 < len ∧ c * (lo + len + 1) ^ 2 < 2 ^ len :=
  ErdosProblems.Erdos269.exists_pow_gt_quadratic c lo

end PalomarCorpus.ExternalVerification269WindowEscapeEquivalence

import Mathlib
import ErdosProblems.Erdos68.ChannelIntegralCongruence

namespace PalomarCorpus.ExternalVerification68ChannelRadius

def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)

theorem square_subsequence_radius_three_halves_lower
    {t M R : ℕ} (ht : 2 ^ 32 ≤ t)
    (hMpos : 0 < M)
    (hdiv : channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    3 * t ^ 3 < 2 * (R + 1) := by
  apply Erdos68.square_subsequence_radius_three_halves_lower ht hMpos
  · simpa [channelLCM, Erdos68.channelLCM] using hdiv
  · exact hsmall

theorem no_eventual_square_subsequence_three_halves_upper
    (M R : ℕ → ℕ)
    (hMpos : ∀ t, 2 ^ 32 ≤ t → 0 < M t)
    (hdiv : ∀ t, 2 ^ 32 ≤ t → channelLCM (2 * t ^ 2) ∣ M t)
    (hsmall : ∀ t, 2 ^ 32 ≤ t →
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T, ∀ t, T ≤ t → 2 * (R t + 1) ≤ 3 * t ^ 3 := by
  apply Erdos68.no_eventual_square_subsequence_three_halves_upper M R hMpos
  · intro t ht
    simpa [channelLCM, Erdos68.channelLCM] using hdiv t ht
  · exact hsmall

theorem not_isLittleO_square_subsequence_radius
    (M R : ℕ → ℕ)
    (hMpos : ∀ t, 4096 ≤ t → 0 < M t)
    (hdiv : ∀ t, 4096 ≤ t → channelLCM (2 * t ^ 2) ∣ M t)
    (hsmall : ∀ t, 4096 ≤ t →
      M t < (R t + 1).factorial - 1) :
    ¬ (fun t : ℕ => ((R t + 1 : ℕ) : ℝ)) =o[Filter.atTop]
        (fun t : ℕ => (t : ℝ) ^ 3) := by
  apply Erdos68.not_isLittleO_square_subsequence_radius M R hMpos
  · intro t ht
    simpa [channelLCM, Erdos68.channelLCM] using hdiv t ht
  · exact hsmall

theorem square_subsequence_radius_cubic_lower
    {t M R : ℕ} (ht : 4096 ≤ t)
    (hMpos : 0 < M)
    (hdiv : channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    t ^ 3 < 8 * (R + 1) := by
  apply Erdos68.square_subsequence_radius_cubic_lower ht hMpos
  · simpa [channelLCM, Erdos68.channelLCM] using hdiv
  · exact hsmall

theorem no_eventual_square_subsequence_cubic_upper
    (M R : ℕ → ℕ)
    (hMpos : ∀ t, 4096 ≤ t → 0 < M t)
    (hdiv : ∀ t, 4096 ≤ t → channelLCM (2 * t ^ 2) ∣ M t)
    (hsmall : ∀ t, 4096 ≤ t →
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T, ∀ t, T ≤ t → 8 * (R t + 1) ≤ t ^ 3 := by
  apply Erdos68.no_eventual_square_subsequence_cubic_upper M R hMpos
  · intro t ht
    simpa [channelLCM, Erdos68.channelLCM] using hdiv t ht
  · exact hsmall

theorem sharp_radius_satisfies_square_log_constraint
    {t R : ℕ} (ht : 4 ≤ t) (hsharp : 9 * (R + 1) = 16 * t ^ 3) :
    (2 * t : ℝ) *
          (((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) *
              Real.log ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) -
            (2 * t ^ 2 + 1 - 2 * t : ℕ) - Real.log 2) <
        ((R + 1 : ℕ) : ℝ) * Real.log (R + 1 : ℝ) +
          (((2 * t + 1).choose 3 : ℕ) : ℝ) *
            Real.log ((2 * t ^ 2 : ℕ) : ℝ) :=
  Erdos68.sharp_radius_satisfies_square_log_constraint ht hsharp

end PalomarCorpus.ExternalVerification68ChannelRadius

import Mathlib
import ErdosProblems.Erdos68.CompanionOrbitRationality

namespace PalomarCorpus.ExternalVerification68CompanionOrbitBoundary

noncomputable section

noncomputable def factorialGapSeries : ℝ :=
  ∑' d : ℕ, if 1 < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))
  else 0

noncomputable def companionConstant : ℝ :=
  ∑' n : ℕ, if 2 ≤ n then
    (1 : ℝ) /
      ((n.factorial : ℝ) * ((((n.factorial : ℤ) - 1 : ℤ) : ℝ)))
  else 0

noncomputable def unitFactTerm (n : ℕ) : ℝ :=
  if 2 ≤ n then (1 : ℝ) / ((n.factorial : ℝ)) else 0

noncomputable def facFloor (x : ℝ) (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℝ) * x⌋

noncomputable def canonicalDigit (x : ℝ) (m : ℕ) : ℤ :=
  facFloor x m - (m : ℤ) * facFloor x (m - 1)

def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)

noncomputable def strictFacTop (x : ℝ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℝ) * x⌋ + 1

def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1

noncomputable def factorialGapPredecessorGap (m : ℕ) : ℝ :=
  (strictFacTop
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℝ) -
    ((m - 1).factorial : ℝ) *
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ)

noncomputable def factorialGapStepCarry (m : ℕ) : ℤ :=
  -⌊1 + 1 / ((m.factorial : ℝ) - 1) -
      (m : ℝ) * factorialGapPredecessorGap m⌋

private theorem unitFactTerm_eq :
    unitFactTerm = ErdosProblems.Erdos68.unitFactTerm := rfl

private theorem facFloor_eq :
    facFloor = ErdosProblems.Erdos68.facFloor := rfl

private theorem canonicalDigit_eq :
    canonicalDigit = ErdosProblems.Erdos68.canonicalDigit := rfl

private theorem companionConstant_eq :
    companionConstant = ErdosProblems.Erdos68.companionConstant := rfl

private theorem factorialGapSeries_eq :
    factorialGapSeries = Erdos68.factorialGapSeries := rfl

theorem companionOrbitBoundary_strictSuccessorCarry :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → factorialGapStepCarry m = 1) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧ factorialGapStepCarry m ≠ 1) ∧
    (∀ m : ℕ, 3 ≤ m →
      (factorialGapStepCarry m = 1 ↔
        (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m)) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬((m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [factorialGapSeries, Erdos68.factorialGapSeries,
      Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
      factorialGapStepCarry, factorialGapPredecessorGap, strictFacTop,
      factorialGapPrefix,
      ErdosProblems.Erdos68.factorialGapStepCarry,
      ErdosProblems.Erdos68.factorialGapPredecessorGap,
      ErdosProblems.Erdos68.strictFacTop,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.not_irrational_factorialGapSeries_iff_eventually_unit_carries
  · simpa [factorialGapSeries, Erdos68.factorialGapSeries,
      Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
      factorialGapStepCarry, factorialGapPredecessorGap, strictFacTop,
      factorialGapPrefix,
      ErdosProblems.Erdos68.factorialGapStepCarry,
      ErdosProblems.Erdos68.factorialGapPredecessorGap,
      ErdosProblems.Erdos68.strictFacTop,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_nonunit_carries
  · intro m hm
    simpa [factorialGapStepCarry, factorialGapPredecessorGap, strictFacTop,
      strictFacTopRat, factorialGapPrefix,
      ErdosProblems.Erdos68.factorialGapStepCarry,
      ErdosProblems.Erdos68.factorialGapPredecessorGap,
      ErdosProblems.Erdos68.strictFacTop,
      ErdosProblems.Erdos68.strictFacTopRat,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat hm
  · simpa [factorialGapSeries, Erdos68.factorialGapSeries,
      Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
      strictFacTopRat, factorialGapPrefix,
      ErdosProblems.Erdos68.strictFacTopRat,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses

theorem companionOrbitBoundary_genericShift (x : ℝ) :
    (¬Irrational (x + ∑' n : ℕ, unitFactTerm n) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → canonicalDigit x m = (m : ℤ) - 2) ∧
    (¬Irrational (x + ∑' n : ℕ, unitFactTerm n) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((facFloor x m + 2 : ℤ) % (m : ℤ)) = 0) := by
  rw [unitFactTerm_eq, canonicalDigit_eq, facFloor_eq]
  exact
    ⟨ErdosProblems.Erdos68.not_irrational_add_unitFact_iff_eventually_canonicalDigit_eq_sub_two x,
      ErdosProblems.Erdos68.not_irrational_add_unitFact_iff_eventually_facFloor_mod_neg_two x⟩

theorem companionOrbitBoundary_factorialGapSeries :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) = 0) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) ≠ 0) := by
  rw [factorialGapSeries_eq, companionConstant_eq, facFloor_eq]
  exact
    ⟨ErdosProblems.Erdos68.not_irrational_factorialGapSeries_iff_eventually_companion_floor_neg_two,
      ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_companion_floor_misses⟩

theorem tsum_unitFactTerm_eq_exp_one_sub_two :
    (∑' n : ℕ, unitFactTerm n) = Real.exp 1 - 2 := by
  rw [unitFactTerm_eq]
  exact ErdosProblems.Erdos68.tsum_unitFactTerm_eq_exp_one_sub_two

end

end PalomarCorpus.ExternalVerification68CompanionOrbitBoundary

import Mathlib
import ErdosProblems.Erdos68.PrimeUnitTranslator

namespace PalomarCorpus.ExternalVerification68PrimeUnitTranslator

/-- The factorial moment of an integer coefficient vector. -/
def factorialMoment {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) : ℤ :=
  ∑ j, coeff j * (index j).factorial

/-- The integer numerator of the `d`-th divisor channel. -/
def channelNumerator {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℤ :=
  ∑ j, coeff j * ((index j).factorial /
    d.factorial ^ (index j / d) : ℕ)

/-- Coefficients `(p, -1)` of the prime-pair translator. -/
def primeTranslatorCoeff (p : ℕ) : Fin 2 → ℤ := ![(p : ℤ), -1]

/-- Support indices `(p - 1, p)` of the prime-pair translator. -/
def primeTranslatorIndex (p : ℕ) : Fin 2 → ℕ := ![p - 1, p]

/-- The real contribution of one channel to the tail beyond `D`. -/
noncomputable def channelResidualTerm {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℝ :=
  if D < d then
    (channelNumerator coeff index d : ℝ) /
      (((d.factorial : ℤ) - 1 : ℤ) : ℝ)
  else 0

/-- The full normalized residual beyond the cutoff `D`. -/
noncomputable def channelResidual {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) : ℝ :=
  ∑' d : ℕ, channelResidualTerm D coeff index d

/-- Coefficients for a support enlarged by a scaled prime translator. -/
def appendPrimeTranslatorCoeff {ι : Type*}
    (coeff : ι → ℤ) (p : ℕ) (z : ℤ) : Sum ι (Fin 2) → ℤ :=
  Sum.elim coeff (fun j => z * primeTranslatorCoeff p j)

/-- Indices for a support enlarged by the prime translator. -/
def appendPrimeTranslatorIndex {ι : Type*}
    (index : ι → ℕ) (p : ℕ) : Sum ι (Fin 2) → ℕ :=
  Sum.elim index (primeTranslatorIndex p)

/-- The moment row together with the consecutive channel rows. -/
def augmentedChannelMomentMatrix {n : ℕ}
    (index : Fin (n + 1) → ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun r j =>
    Fin.cases ((index j).factorial : ℤ)
      (fun d : Fin n =>
        ((index j).factorial /
          (d.val + 2).factorial ^ (index j / (d.val + 2)) : ℕ)) r

/-- Cramer's-rule coefficient vector for unit factorial moment and zero
consecutive channels. -/
def cramerChannelKernelCoeff {n : ℕ}
    (index : Fin (n + 1) → ℕ) : Fin (n + 1) → ℤ :=
  (augmentedChannelMomentMatrix index).cramer (Pi.single 0 1)

/-- The common scale of the factorial grid at cutoff `D`. -/
def factorialGridScale (D : ℕ) : ℕ := D.factorial ^ 2

/-- The factorial grid of `n + 2` indices starting at `t`. -/
def factorialGridIndex (n t : ℕ) (j : Fin (n + 2)) : ℕ :=
  (t + j.val) * factorialGridScale (n + 2)

/-- The prime-pair translator has zero factorial moment. -/
theorem primeTranslator_moment_zero
    {p : ℕ} (hp : 0 < p) :
    factorialMoment (primeTranslatorCoeff p) (primeTranslatorIndex p) = 0 := by
  simpa [factorialMoment, primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.factorialMoment, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using Erdos68.primeTranslator_moment_zero hp

/-- Every channel strictly below `p` annihilates the prime translator. -/
theorem primeTranslator_channel_zero_of_lt_p
    {p d : ℕ} (hp : p.Prime) (hd2 : 2 ≤ d) (hdp : d < p) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by
  simpa [channelNumerator, primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.channelNumerator, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using
    Erdos68.primeTranslator_channel_zero_of_lt_p hp hd2 hdp

/-- At the prime itself the sole surviving channel numerator is exactly its
normalizing modulus `p! - 1`. -/
theorem primeTranslator_channel_at_prime
    {p : ℕ} (hp : p.Prime) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) p =
      (p.factorial : ℤ) - 1 := by
  simpa [channelNumerator, primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.channelNumerator, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using
    Erdos68.primeTranslator_channel_at_prime hp

/-- Every channel strictly beyond `p` annihilates the prime translator. -/
theorem primeTranslator_channel_zero_of_p_lt
    {p d : ℕ} (hp : 0 < p) (hpd : p < d) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by
  simpa [channelNumerator, primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.channelNumerator, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using
    Erdos68.primeTranslator_channel_zero_of_p_lt hp hpd

/-- The prime-pair translator is an exact unit direction for the full
infinite channel residual. -/
theorem primeTranslator_channelResidual_eq_one
    {D p : ℕ} (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (primeTranslatorCoeff p) (primeTranslatorIndex p) = 1 := by
  simpa [channelResidual, channelResidualTerm, channelNumerator,
    primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.channelResidual, Erdos68.channelResidualTerm,
    Erdos68.channelNumerator, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using
    Erdos68.primeTranslator_channelResidual_eq_one hD hp hDp

/-- Appending a scaled prime translator shifts the full residual by that
integer and changes nothing else in the original support. -/
theorem channelResidual_appendPrimeTranslator
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) {D p : ℕ} (z : ℤ)
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (appendPrimeTranslatorCoeff coeff p z)
        (appendPrimeTranslatorIndex index p) =
      channelResidual D coeff index + (z : ℝ) := by
  simpa [channelResidual, channelResidualTerm, channelNumerator,
    appendPrimeTranslatorCoeff, appendPrimeTranslatorIndex,
    primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.channelResidual, Erdos68.channelResidualTerm,
    Erdos68.channelNumerator, Erdos68.appendPrimeTranslatorCoeff,
    Erdos68.appendPrimeTranslatorIndex, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using
    Erdos68.channelResidual_appendPrimeTranslator coeff index z hD hp hDp

/-- For every cutoff and support threshold, a factorial-grid block and a
prime translator pair can be chosen entirely above the threshold, with the
stated zero-channel, nonzero-moment, and residual bounds. -/
theorem exists_remote_factorialGrid_primeTranslator_reduction
    (n B : ℕ) :
    ∃ p : ℕ, ∃ z : ℤ,
      p.Prime ∧
      (∀ j : Sum (Fin (n + 2)) (Fin 2),
        B < appendPrimeTranslatorIndex
          (factorialGridIndex n (B + 1)) p j) ∧
      (∀ d ∈ Finset.Icc 2 (n + 2),
        channelNumerator
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p) d = 0) ∧
      factorialMoment
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p) ≠ 0 ∧
      |channelResidual (n + 2)
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p)| ≤ (1 : ℝ) / 2 := by
  simpa [factorialMoment, channelNumerator, primeTranslatorCoeff,
    primeTranslatorIndex, channelResidual, channelResidualTerm,
    appendPrimeTranslatorCoeff, appendPrimeTranslatorIndex,
    augmentedChannelMomentMatrix, cramerChannelKernelCoeff,
    factorialGridScale, factorialGridIndex,
    Erdos68.factorialMoment, Erdos68.channelNumerator,
    Erdos68.primeTranslatorCoeff, Erdos68.primeTranslatorIndex,
    Erdos68.channelResidual, Erdos68.channelResidualTerm,
    Erdos68.appendPrimeTranslatorCoeff, Erdos68.appendPrimeTranslatorIndex,
    Erdos68.augmentedChannelMomentMatrix, Erdos68.cramerChannelKernelCoeff,
    Erdos68.factorialGridScale, Erdos68.factorialGridIndex] using
    Erdos68.exists_remote_factorialGrid_primeTranslator_reduction n B

end PalomarCorpus.ExternalVerification68PrimeUnitTranslator
