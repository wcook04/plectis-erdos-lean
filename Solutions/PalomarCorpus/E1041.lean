/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos1041.CriticalTwoRootProximity
import ErdosProblems.Erdos1041.PaperCubicCompletion
import ErdosProblems.Erdos1041.PaperCubicMonic
import Mathlib
import ErdosProblems.Erdos1041.CyclicTrinomialFiberCase
import ErdosProblems.Erdos1041.FirstMergeCriticalValueSeparation
import ErdosProblems.Erdos1041.QuarticQuotientFiberCase
import ErdosProblems.Erdos1041.CubicQuotientFiberCase
import ErdosProblems.Erdos1041.PrimitiveQuinticInteriorTail
import ErdosProblems.Erdos1041.SharpCollinearChebyshev
import ErdosProblems.Erdos1041.CyclicTetranomialCoefficientCase
import ErdosProblems.Erdos1041.TetranomialL2Selector

open Finset
open Polynomial Set
open scoped BigOperators
open Polynomial
open scoped ComplexConjugate

namespace PalomarCorpus.E1041.CriticalGeometry

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

end PalomarCorpus.E1041.CriticalGeometry

namespace PalomarCorpus.E1041.CubicPath

noncomputable section
open Polynomial Set
open scoped BigOperators

/-- The two-segment path with endpoints at times zero and two. -/
noncomputable def hub (a c b : ℂ) (t : ℝ) : ℂ :=
  c + ((max (1 - t) 0 : ℝ) : ℂ) * (a - c) +
    ((max (t - 1) 0 : ℝ) : ℂ) * (b - c)
theorem cubic_paper_complete (p : ℂ[X]) (z : Fin 3 → ℂ)
    (hp : p = ∏ i, (X - C (z i))) (hz : ∀ i, ‖z i‖ < 1) :
    ∃ i j : Fin 3, ∃ c : ℂ, i ≠ j ∧
      Continuous (hub (z i) c (z j)) ∧
      BoundedVariationOn (hub (z i) c (z j)) (Icc (0 : ℝ) 2) ∧
      ((∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (hub (z i) c (z j) t)‖ < 1) ∧
        eVariationOn (hub (z i) c (z j)) (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
        γ 0 = z i ∧ γ 2 = z j ∧
        (∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (γ t)‖ < 1) ∧
        BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
        eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (Squarefree p → z i ≠ z j) := by
  simpa only [hub, ErdosProblems.Erdos1041.PaperCurve.hub,
    ErdosProblems.Erdos1041.PaperCurve.HubBelow,
    ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow] using
    (ErdosProblems.Erdos1041.PaperCubicCompletion.cubic_paper_complete p z hp hz)

theorem monic_cubic_connector (p : ℂ[X]) (hm : p.Monic)
    (hd : p.natDegree = 3) (hz : ∀ z : ℂ, p.eval z = 0 → ‖z‖ < 1) :
    ∃ a b c : ℂ, p.eval a = 0 ∧ p.eval b = 0 ∧
      Continuous (hub a c b) ∧
      BoundedVariationOn (hub a c b) (Icc (0 : ℝ) 2) ∧
      ((∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (hub a c b t)‖ < 1) ∧
        eVariationOn (hub a c b) (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
        γ 0 = a ∧ γ 2 = b ∧
        (∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (γ t)‖ < 1) ∧
        BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
        eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (Squarefree p → a ≠ b) := by
  simpa only [hub, ErdosProblems.Erdos1041.PaperCurve.hub,
    ErdosProblems.Erdos1041.PaperCurve.HubBelow,
    ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow] using
    (ErdosProblems.Erdos1041.PaperCubicMonic.monic_cubic_connector p hm hd hz)

end

end PalomarCorpus.E1041.CubicPath

namespace PalomarCorpus.E1041.CyclicTrinomialFiber

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

end PalomarCorpus.E1041.CyclicTrinomialFiber

namespace PalomarCorpus.E1041.FirstMergeCriticalValueSeparation

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

end PalomarCorpus.E1041.FirstMergeCriticalValueSeparation

namespace PalomarCorpus.E1041.QuarticQuotientFiber

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

end PalomarCorpus.E1041.QuarticQuotientFiber

open Polynomial

namespace PalomarCorpus.E1041.SolvedFamilies

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
end PalomarCorpus.E1041.SolvedFamilies

open scoped ComplexConjugate

namespace PalomarCorpus.E1041.TetranomialSpokes

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

end PalomarCorpus.E1041.TetranomialSpokes
