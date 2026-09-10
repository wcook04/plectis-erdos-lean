/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

/-!
# Palomar corpus challenge

Independent Comparator restatement of the paper-linked Lean that actually has
Comparator-grade proof coverage across Erdős problems #68, #243, #249, #251,
#257, #269, #1041, and #1049. Parent problems remain open. Narrative, paper
loci, and evidence class live in `PalomarCorpus/README.md`.
-/

namespace PalomarCorpus.ExternalVerification1041CriticalGeometry
open Finset
theorem criticalGeometricMean_twoRootProximity {n : ℕ} (hn : 2 ≤ n) (z : Fin n → ℂ) (c : ℂ) (hne : ∀ k, c - z k ≠ 0) (hcrit : ∑ k, (c - z k)⁻¹ = 0) {r : ℝ} (hr : 0 < r) (hrn : r ^ n = ∏ k, ‖c - z k‖) : ∃ i j : Fin n, i ≠ j ∧ ‖c - z i‖ + ‖c - z j‖ ≤ 2 * r := by sorry

theorem criticalDiskInverseBalance_twoRootProximity {N t δ e : ℝ} (hN : 2 ≤ N) (ht1 : t < 1) (hδ : 0 < δ) (hδe : δ ≤ e) (hδ1 : δ ≤ 1) (hemax : e ≤ 1 + t) (hbal : e ≤ (N - 1) * δ) (hstar : N ≤ (1 - t ^ 2) * (1 / δ ^ 2 + (N - 1) / e ^ 2)) : δ + e ≤ 2 := by sorry

theorem criticalDiskInverseBalance_twoRootProximity_strict {N t δ e : ℝ} (hN : 2 ≤ N) (ht1 : t < 1) (hδ : 0 < δ) (hδe : δ ≤ e) (hδ1 : δ ≤ 1) (hemax : e < 1 + t) (hbal : e ≤ (N - 1) * δ) (hstar : N ≤ (1 - t ^ 2) * (1 / δ ^ 2 + (N - 1) / e ^ 2)) : δ + e < 2 := by sorry

noncomputable def nearestSpokeP : ℂ := (999 : ℂ) / 1000

noncomputable def nearestSpokeA : ℂ := ((901 : ℂ) / 902) * nearestSpokeP

noncomputable def nearestSpokeUPlus : ℂ := ((-451 : ℂ) + 780 * Complex.I) / 901

noncomputable def nearestSpokeUMinus : ℂ := ((-451 : ℂ) - 780 * Complex.I) / 901

noncomputable def nearestSpokeRoot : Fin 5 → ℂ | 0 => nearestSpokeA | 1 => Complex.I * nearestSpokeP | 2 => -Complex.I * nearestSpokeP | 3 => nearestSpokeP * nearestSpokeUPlus | 4 => nearestSpokeP * nearestSpokeUMinus /-- The five explicit quintic roots have critical-point balance at the origin. -/

theorem nearestSpoke_reciprocal_balance : ∑ k, (nearestSpokeRoot k)⁻¹ = 0 := by sorry

theorem nearestSpoke_unique_nearest_normSq : (∀ k : Fin 5, k ≠ 0 → Complex.normSq (nearestSpokeRoot 0) < Complex.normSq (nearestSpokeRoot k)) := by sorry

theorem nearestSpoke_unique_nearest_spoke_escapes : (1 : ℝ) < (900099 / 902000 : ℝ) * (1 - 1 / 10) * (((1 / 10 : ℝ) * (900099 / 902000)) ^ 2 + (999 / 1000) ^ 2) * (((1 / 10 : ℝ) * (900099 / 902000)) ^ 2 + (1 / 10) * (999 / 1000) ^ 2 + (999 / 1000) ^ 2) := by sorry

noncomputable def allStraightRadius : ℂ := (99 : ℂ) / 100

noncomputable def allStraightOmega : ℂ := (-1 : ℂ) / 2 + ((Real.sqrt 3 : ℂ) / 2) * Complex.I

noncomputable def allStraightRoot : Fin 3 → ℂ | 0 => allStraightRadius | 1 => allStraightRadius * allStraightOmega | 2 => allStraightRadius * allStraightOmega ^ 2

noncomputable def allStraightCubic (z : ℂ) : ℂ := z ^ 3 - allStraightRadius ^ 3 /-- The three displayed points are roots of `z³ - (99/100)³`. -/

theorem allStraightCubic_roots : ∀ k : Fin 3, allStraightCubic (allStraightRoot k) = 0 := by sorry

theorem allStraightCubic_roots_in_unitDisk : ∀ k : Fin 3, ‖allStraightRoot k‖ < 1 := by sorry

theorem allStraightCubic_every_pair_midpoint_escapes : ∀ i j : Fin 3, i ≠ j → 1 < ‖allStraightCubic ((allStraightRoot i + allStraightRoot j) / 2)‖ := by sorry

end PalomarCorpus.ExternalVerification1041CriticalGeometry

namespace PalomarCorpus.ExternalVerification1041CyclicTrinomialFiber
theorem trinomialRoot_spoke_factorization {m r : ℕ} {a c w : ℂ} {u : ℝ} (hroot : w ^ m + a * w ^ r + c = 0) : (u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c = ((1 - u ^ r : ℝ) : ℂ) * c - ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m := by sorry

theorem trinomialRoot_spoke_norm_le_constant {m r : ℕ} (hrm : r ≤ m) {a c w : ℂ} (hroot : w ^ m + a * w ^ r + c = 0) (hw : ‖w‖ ^ m ≤ ‖c‖) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ ≤ ‖c‖ := by sorry

theorem trinomialRoot_spoke_norm_lt_one {m r : ℕ} (hrm : r ≤ m) {a c w : ℂ} (hroot : w ^ m + a * w ^ r + c = 0) (hw : ‖w‖ ^ m ≤ ‖c‖) (hc : ‖c‖ < 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ < 1 := by sorry

theorem trinomialRoot_spoke_norm_lt_one_of_norm_lt_one {m r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m) {a c w : ℂ} (hroot : w ^ m + a * w ^ r + c = 0) (hw : ‖w‖ < 1) (hc : ‖c‖ < 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ < 1 := by sorry

theorem cyclicTrinomial_two_short_fiber_displacements {y₁ y₂ : ℂ} (hy₁ : ‖y₁‖ < 1) (hy₂ : ‖y₂‖ < 1) : ‖y₁‖ + ‖y₂‖ < 2 := by sorry

end PalomarCorpus.ExternalVerification1041CyclicTrinomialFiber

namespace PalomarCorpus.ExternalVerification1041FirstMergeCriticalValueSeparation
noncomputable def firstMergeSquaredCoefficient (n : ℕ) (S : ℝ) : ℝ := (1 + S) ^ ((2 : ℝ) / (n : ℝ)) * Real.log (S / (S - 1)) /-- The three exact convenient separation regimes. -/

theorem firstMerge_exact_convenient_thresholds : (∀ n : ℕ, 3 ≤ n → firstMergeSquaredCoefficient n 4 < 1) ∧ (∀ n : ℕ, 4 ≤ n → firstMergeSquaredCoefficient n 3 < 1) ∧ (∀ n : ℕ, 6 ≤ n → firstMergeSquaredCoefficient n 2 < 1) := by sorry

theorem firstMerge_length_lt_two_of_squared_bound {n : ℕ} {S length : ℝ} (hbound : length ^ 2 ≤ 4 * firstMergeSquaredCoefficient n S) (hthreshold : firstMergeSquaredCoefficient n S < 1) : length < 2 := by sorry

end PalomarCorpus.ExternalVerification1041FirstMergeCriticalValueSeparation

namespace PalomarCorpus.ExternalVerification1041QuarticQuotientFiber
theorem rootLift_kernel_le_axis {alpha d x : ℝ} (halpha : alpha ≤ 1) (hx : 0 < x) : (Real.sqrt (d ^ 2 + x ^ 2)) ^ (alpha - 1) ≤ x ^ (alpha - 1) := by sorry

theorem rootLift_axis_integral {alpha A : ℝ} (halpha : 0 < alpha) (hA : 0 ≤ A) : alpha * (∫ x in (0 : ℝ)..A, x ^ (alpha - 1)) = A ^ alpha := by sorry

theorem rootLift_endpoint_budget_lt_two {alpha a b : ℝ} (halpha : 0 < alpha) (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1) : a ^ alpha + b ^ alpha < 2 := by sorry

theorem rootLift_length_lt_two_of_le_endpoint_budget {alpha a b length : ℝ} (halpha : 0 < alpha) (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1) (hlength : length ≤ a ^ alpha + b ^ alpha) : length < 2 := by sorry

end PalomarCorpus.ExternalVerification1041QuarticQuotientFiber

namespace PalomarCorpus.ExternalVerification1041SolvedFamilies
open Polynomial
theorem cubic_safeRootSpoke {r s v : ℂ} (hr : ‖r‖ < 1) (hs : ‖s‖ < 1) (hv : ‖v‖ < 1) : (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖((t : ℂ) * r - r) * ((t : ℂ) * r - s) * ((t : ℂ) * r - v)‖ ≤ 1) ∨ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖((t : ℂ) * s - s) * ((t : ℂ) * s - r) * ((t : ℂ) * s - v)‖ ≤ 1) ∨ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖((t : ℂ) * v - v) * ((t : ℂ) * v - r) * ((t : ℂ) * v - s)‖ ≤ 1) := by sorry

theorem primitiveQuintic_twoStrictTailEnergies {r : ℝ} {x0 x1 x2 x3 x4 s0 s1 s2 s3 s4 : ℝ} (hr : 0 < r) (hr2 : r < 2) (hs0 : 0 ≤ s0) (hs0one : s0 ≤ 1) (hx0s : x0 ^ 2 ≤ s0) (hs1 : 0 ≤ s1) (hs1one : s1 ≤ 1) (hx1s : x1 ^ 2 ≤ s1) (hs2 : 0 ≤ s2) (hs2one : s2 ≤ 1) (hx2s : x2 ^ 2 ≤ s2) (hs3 : 0 ≤ s3) (hs3one : s3 ≤ 1) (hx3s : x3 ^ 2 ≤ s3) (hs4 : 0 ≤ s4) (hs4one : s4 ≤ 1) (hx4s : x4 ^ 2 ≤ s4) (hm1 : x0 + x1 + x2 + x3 + x4 = -r) (hm2 : (2 * x0 ^ 2 - s0) + (2 * x1 ^ 2 - s1) + (2 * x2 ^ 2 - s2) + (2 * x3 ^ 2 - s3) + (2 * x4 ^ 2 - s4) = r ^ 2) (hm3 : (4 * x0 ^ 3 - 3 * s0 * x0) + (4 * x1 ^ 3 - 3 * s1 * x1) + (4 * x2 ^ 3 - 3 * s2 * x2) + (4 * x3 ^ 3 - 3 * s3 * x3) + (4 * x4 ^ 3 - 3 * s4 * x4) = -r ^ 3) : (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧ s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1) ∨ (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧ s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1) ∨ (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧ s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨ (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧ s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨ (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧ s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1) ∨ (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧ s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨ (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧ s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨ (s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1 ∧ s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨ (s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1 ∧ s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨ (s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1 ∧ s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) := by sorry

namespace SharpCollinear
noncomputable def comparisonBound (n : ℕ) : ℝ := |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n| /-- The checked sharp Chebyshev endpoint after collinear affine normalisation: one alternating peak is no higher than the comparison bound. -/

theorem existsPeakLeComparisonBound {m : ℕ} {p : ℝ[X]} {c : Fin (m + 1) → ℝ} (hp : p.IsMonicOfDegree (m + 2)) (hc : StrictMono c) (ha : -1 < c 0) (hb : c (Fin.last m) < 1) (hpa : p.eval (-1) = 0) (hpb : p.eval 1 = 0) (hpalt : ∀ i : Fin m, p.eval (c i.castSucc) * p.eval (c i.succ) < 0) (hc_mem : ∀ i : Fin (m + 1), |c i| ≤ 1) : ∃ i : Fin (m + 1), |p.eval (c i)| ≤ comparisonBound (m + 2) := by sorry

end SharpCollinear
end PalomarCorpus.ExternalVerification1041SolvedFamilies

namespace PalomarCorpus.ExternalVerification1041TetranomialSpokes
open scoped ComplexConjugate
theorem tetranomialRoot_spoke_factorization {m r s : ℕ} {a b c w : ℂ} {u : ℝ} (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0) : (u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + b * (u : ℂ) ^ s * w ^ s + c = ((1 - u ^ s : ℝ) : ℂ) * c - ((u ^ s - u ^ r : ℝ) : ℂ) * (a * w ^ r + w ^ m) - ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m := by sorry

theorem tetranomialRoot_spoke_norm_lt_one_of_rootBudget {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m) {a b c w : ℂ} (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0) (hw : ‖w‖ < 1) (hc : ‖c‖ < 1) (hbudget : ‖c‖ + ‖b‖ * ‖w‖ ^ s < 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + b * (u : ℂ) ^ s * w ^ s + c‖ < 1 := by sorry

theorem tetranomialRoot_spoke_norm_lt_one_of_lowCoeffBudget {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m) {a b c w : ℂ} (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0) (hw : ‖w‖ < 1) (hc : ‖c‖ < 1) (hbudget : ‖b‖ + ‖c‖ ≤ 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + b * (u : ℂ) ^ s * w ^ s + c‖ < 1 := by sorry

theorem sum_normSq_const_add_mul {ι : Type*} (S : Finset ι) (v : ι → ℂ) (b c : ℂ) : ∑ i ∈ S, Complex.normSq (c + b * v i) = (S.card : ℝ) * Complex.normSq c + Complex.normSq b * ∑ i ∈ S, Complex.normSq (v i) + 2 * (conj c * b * (∑ i ∈ S, v i)).re := by sorry

theorem exists_two_tails_norm_lt_one_of_exact_L2_budget {ι : Type*} (S : Finset ι) (v : ι → ℂ) (b c : ℂ) (hcard : 2 ≤ S.card) (hbudget : (S.card : ℝ) * Complex.normSq c + Complex.normSq b * ∑ i ∈ S, Complex.normSq (v i) + 2 * (conj c * b * (∑ i ∈ S, v i)).re < (S.card : ℝ) - 1) : ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ ‖c + b * v i‖ < 1 ∧ ‖c + b * v j‖ < 1 := by sorry

theorem exists_two_tetranomialRoot_safeSpokes_of_moment_coeff_budget {ι : Type*} (S : Finset ι) (w : ι → ℂ) {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m) {a b c moment : ℂ} (hcard : 2 ≤ S.card) (hroot : ∀ i ∈ S, w i ^ m + a * w i ^ r + b * w i ^ s + c = 0) (hw : ∀ i ∈ S, ‖w i‖ < 1) (hc : ‖c‖ < 1) (hmoment : ∑ i ∈ S, w i ^ s = moment) (hcoeff : (S.card : ℝ) * (Complex.normSq b + Complex.normSq c) + 2 * (conj c * b * moment).re < (S.card : ℝ) - 1) : ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ (∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖(u : ℂ) ^ m * w i ^ m + a * (u : ℂ) ^ r * w i ^ r + b * (u : ℂ) ^ s * w i ^ s + c‖ < 1) ∧ (∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖(u : ℂ) ^ m * w j ^ m + a * (u : ℂ) ^ r * w j ^ r + b * (u : ℂ) ^ s * w j ^ s + c‖ < 1) := by sorry

end PalomarCorpus.ExternalVerification1041TetranomialSpokes

namespace PalomarCorpus.ExternalVerification1049AdelicHeightBridge
open Polynomial
noncomputable def hpThreshold (rho sigma : ℝ) : ℝ := (hpDecay rho sigma - hpCyclotomicSaving sigma) / (hpHeight rho sigma + hpDecay rho sigma)

abbrev FourJetSignature (R S : ℕ) := (ZMod (3 ^ R) × ZMod (3 ^ R)) × (ZMod (2 ^ S) × ZMod (2 ^ S))

def selectedFourJetSum {n : ℕ} (R S W : ℕ) (forms : Fin n → Polynomial ℤ × Polynomial ℤ) (ε : Fin n → Bool) : FourJetSignature R S := ∑ i, if ε i then fourJetSignature R S W (forms i).1 (forms i).2 else 0 /-- Finite `q`-Pochhammer product `(q^start;q)_len`. -/

noncomputable def zudilinFirstTransformedRow (l : ℕ) : PowerSeries ℤ := zudilinNormalizedMoment (l + 1) - zudilinNormalizedMoment l /-- In every column, the complete initial monomial of the first nontrivial transformed row is `-6 X^(l+1)`.  This is an unconditional all-column partial result; no assertion about transformed rows `j ≥ 2` is included. -/

theorem zudilin_firstTransformedRow_initialMonomial (l : ℕ) : PowerSeries.order (zudilinFirstTransformedRow l) = l + 1 ∧ PowerSeries.coeff (l + 1) (zudilinFirstTransformedRow l) = -6 := by sorry

def zudilinSharpHankelQOrder (N : ℕ) : ℤ := ∑ j ∈ Finset.range N, (j : ℤ) ^ 2 /-- Positive magnitude of the leading coefficient contributed by transformed row `j`. -/

def zudilinTransformedRowCoeff (j : ℕ) : ℕ := ((j + 1) ^ 2 * (j + 2)) / 2 /-- The two division-free closed forms carried by the sharp-Hankel endpoint. Six times the sum of squares equals `N (N - 1) (2 N - 1)`, and `2 ^ N` times the product of the transformed-row coefficients equals `(N !) ^ 2 (N + 1)!`. This is an algebraic assembly; it identifies no formal power-series determinant with these data. -/

theorem zudilinSharpHankelOrderAndCoeff_algebraicAssembly (N : ℕ) : 6 * zudilinSharpHankelQOrder N = (N : ℤ) * ((N : ℤ) - 1) * (2 * (N : ℤ) - 1) ∧ 2 ^ N * (∏ j ∈ Finset.range N, zudilinTransformedRowCoeff j) = (N.factorial) ^ 2 * (N + 1).factorial := by sorry

theorem threePow_fortyOne_lt_twoPow_sixtyFive : 3 ^ 41 < 2 ^ 65 := by sorry

theorem twoPow_sixtyFour_lt_threePow_fortyOne : 2 ^ 64 < 3 ^ 41 := by sorry

theorem threeHalves_rectangular_hp_gap_gt_threeThirteenths (rho sigma : ℝ) (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) : (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - hpThreshold rho sigma := by sorry

theorem threeHalves_hankelChargeThreshold_lt_eightFortyOne : (Real.log 3 / Real.log 2 - 1) / 3 < (8 : ℝ) / 41 := by sorry

theorem zudilinScalarContent_cannot_meet_required_charge (N extractedDegree : ℤ) (hN : 0 < N) (hextracted : extractedDegree ≤ N ^ 3 - N) : 41 * extractedDegree < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by sorry

theorem zudilinScalarPlusBorder_cannot_meet_required_charge (N extractedDegree : ℤ) (hN : 2 ≤ N) (hextracted : extractedDegree ≤ 2 * N ^ 3 - N) : 41 * extractedDegree < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by sorry

theorem three_two_scalar_margin_lt_explicit {C0 C1 : ℝ} (hC0 : 0 < C0) (hsource : 2 * C0 ≤ C1) : C0 * Real.log 3 - C1 * Real.log 2 < -((17 : ℝ) / 41) * C0 * Real.log 2 := by sorry

theorem exists_distinct_binary_selectors_same_fourJet_of_power_certificate {n p q T S W : ℕ} (forms : Fin n → Polynomial ℤ × Polynomial ℤ) (hpq : (3 : ℕ) ^ p < (2 : ℕ) ^ q) (hT : 0 < T) (hrank : 2 * q * T + 2 * S ≤ n) : ∃ ε η : Fin n → Bool, ε ≠ η ∧ selectedFourJetSum (p * T) S W forms ε = selectedFourJetSum (p * T) S W forms η := by sorry

theorem exists_distinct_binary_selectors_same_fourJet_of_rank_41 {n T S W : ℕ} (forms : Fin n → Polynomial ℤ × Polynomial ℤ) (hT : 0 < T) (hrank : 130 * T + 2 * S ≤ n) : ∃ ε η : Fin n → Bool, ε ≠ η ∧ selectedFourJetSum (41 * T) S W forms ε = selectedFourJetSum (41 * T) S W forms η := by sorry

theorem fourJet_card_gt_two_pow_of_rank_41 (S : ℕ) : 2 ^ (129 + 2 * S) < Fintype.card (FourJetSignature 41 S) := by sorry

theorem exists_ne_map_eq_map_ne_of_card_mul_lt {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (f : α → β) (g : α → γ) (k : ℕ) (hg : ∀ x : α, (Finset.univ.filter fun y => g y = g x).card ≤ k) (hcard : Fintype.card β * k < Fintype.card α) : ∃ x y : α, x ≠ y ∧ f x = f y ∧ g x ≠ g y := by sorry

end PalomarCorpus.ExternalVerification1049AdelicHeightBridge

namespace PalomarCorpus.ExternalVerification1049HermitePadeNoGo
noncomputable def hpThreshold (rho sigma : ℝ) : ℝ := (hpDecay rho sigma - hpCyclotomicSaving sigma) / (hpHeight rho sigma + hpDecay rho sigma)

noncomputable def hpClearedGap (rho sigma : ℝ) : ℝ := (Real.pi ^ 2 + 2) * hpDecay rho sigma - 6 * sigma ^ 2 - (Real.pi ^ 2 - 2) * hpHeight rho sigma /-- Exact polynomial identity after writing `sigma = 1 + rho + u`. -/

theorem hpClearedGap_expansion (rho u : ℝ) : hpClearedGap rho (1 + rho + u) = -Real.pi ^ 2 * rho ^ 2 - Real.pi ^ 2 * rho * u - 2 * Real.pi ^ 2 * rho - 2 * rho ^ 2 - 10 * rho * u - 4 * rho - 6 * u ^ 2 - 8 * u := by sorry

theorem hpClearedGap_nonpos (rho sigma : ℝ) (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) : hpClearedGap rho sigma ≤ 0 := by sorry

theorem hpClearedGap_eq_zero_iff (rho sigma : ℝ) (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) : hpClearedGap rho sigma = 0 ↔ rho = 0 ∧ sigma = 1 := by sorry

theorem rectangular_hp_threshold_le_classical (rho sigma : ℝ) (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) : hpThreshold rho sigma ≤ 1 / 2 - 1 / Real.pi ^ 2 := by sorry

theorem rectangular_hp_threshold_eq_classical_iff (rho sigma : ℝ) (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) : hpThreshold rho sigma = 1 / 2 - 1 / Real.pi ^ 2 ↔ rho = 0 ∧ sigma = 1 := by sorry

end PalomarCorpus.ExternalVerification1049HermitePadeNoGo

namespace PalomarCorpus.ExternalVerification1049PrimeSupportSelectors
open Filter
theorem twoSelector_rationalGap (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q) (hdet : A₁ * B₂ - A₂ * B₁ ≠ 0) : (1 : ℝ) / q ≤ |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨ (1 : ℝ) / q ≤ |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| := by sorry

theorem integerLinearForm_rationalGap (a q A B : ℤ) (hq : 0 < q) (hne : (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) ≠ 0) : (1 : ℝ) / q ≤ |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by sorry

theorem rationalTwoSelector_notBothTendstoZero (a q : ℤ) (hq : 0 < q) (A₁ B₁ A₂ B₂ : ℕ → ℤ) (hdet : ∀ n, A₁ n * B₂ n - A₂ n * B₁ n ≠ 0) : ¬(Tendsto (fun n ↦ (B₁ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ n : ℝ)) atTop (nhds 0) ∧ Tendsto (fun n ↦ (B₂ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ n : ℝ)) atTop (nhds 0)) := by sorry

theorem twoSelector_detHeightDecay_tradeoff (A₁ B₁ A₂ B₂ F ε : ℝ) (h₁ : |B₁ * F - A₁| ≤ ε) (h₂ : |B₂ * F - A₂| ≤ ε) : |A₁ * B₂ - A₂ * B₁| ≤ ε * (|B₁| + |B₂|) := by sorry

theorem twoSelector_unimodularHeightDecay_tradeoff (A₁ B₁ A₂ B₂ u v w z F H ε : ℝ) (hunimod : |u * z - v * w| = 1) (hε : 0 ≤ ε) (hu : |u| ≤ H) (hv : |v| ≤ H) (hw : |w| ≤ H) (hz : |z| ≤ H) (h₁ : |(u * B₁ + v * B₂) * F - (u * A₁ + v * A₂)| ≤ ε) (h₂ : |(w * B₁ + z * B₂) * F - (w * A₁ + z * A₂)| ≤ ε) : |A₁ * B₂ - A₂ * B₁| ≤ 2 * H * ε * (|B₁| + |B₂|) := by sorry

theorem primeSupportedTwoSelector_rationalGap {ell : ℕ} (hell : ell.Prime) (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q) (hellq : ¬ (ell : ℤ) ∣ q) (hellB₁ : (ell : ℤ) ∣ B₁) (hellB₂ : (ell : ℤ) ∣ B₂) (hdet : ¬ (ell : ℤ) ^ 2 ∣ A₁ * B₂ - A₂ * B₁) : (1 : ℝ) / q ≤ |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨ (1 : ℝ) / q ≤ |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| := by sorry

theorem primeSupportedOneRow_rationalGap {ell : ℕ} (hell : ell.Prime) (a q A B : ℤ) (hq : 0 < q) (hellB : (ell : ℤ) ∣ B) (hellA : ¬ (ell : ℤ) ∣ A) (hellq : ¬ (ell : ℤ) ∣ q) : (1 : ℝ) / q ≤ |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by sorry

theorem primePowerSupportedOneRow_rationalGap {ell r : ℕ} (hell : ell.Prime) (hr : r ≠ 0) (a q A B : ℤ) (hq : 0 < q) (hellPowB : (ell : ℤ) ^ r ∣ B) (hellA : ¬ (ell : ℤ) ∣ A) (hellq : ¬ (ell : ℤ) ∣ q) : (1 : ℝ) / q ≤ |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by sorry

theorem zeroDenominatorCoordinates_binaryCollision {N k : ℕ} [NeZero N] (w : Fin k → ZMod N × ZMod N) (hzero : ∀ i, (w i).2 = 0) (hcard : N < 2 ^ k) : ∃ s t : Fin k → Bool, s ≠ t ∧ (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by sorry

end PalomarCorpus.ExternalVerification1049PrimeSupportSelectors

namespace PalomarCorpus.ExternalVerification1049RationalBaseBarrier
open scoped BigOperators
def CoordinatewiseCorridor (a b N K Q digit : ℕ) : Prop := 0 < a ∧ 0 < Q ∧ 0 < digit ∧ digit ≤ N + K ∧ a ^ K ∣ Q * digit ∧ Q * b ^ (N + K + 1) < a ^ (K + 1) /-- The first `N` rational-base divisor-series coordinates. -/

def rationalBaseClearedTailQ (r s B F : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ := B * r ^ N * (F - rationalBasePrefixQ r s coeff N) /-- Natural-valued magnitude of the recurrence forcing term. -/

def rationalBaseForcingNat (s B : ℕ) (coeff : ℕ → ℕ) (N : ℕ) : ℕ := B * coeff (N + 1) * s ^ (N + 1) /-- Exact rational-base cleared-tail recurrence. -/

theorem rationalBaseClearedTailQ_succ {r s B F : ℚ} {coeff : ℕ → ℚ} (hr : r ≠ 0) (N : ℕ) : rationalBaseClearedTailQ r s B F coeff (N + 1) = r * rationalBaseClearedTailQ r s B F coeff N - B * coeff (N + 1) * s ^ (N + 1) := by sorry

theorem twoPow_le_rationalBaseForcingNat {s B : ℕ} {coeff : ℕ → ℕ} {N : ℕ} (hs : 2 ≤ s) (hB : 1 ≤ B) (hc : 1 ≤ coeff (N + 1)) : 2 ^ (N + 1) ≤ rationalBaseForcingNat s B coeff N := by sorry

theorem threeHalves_no_coordinatewiseCorridor {N K Q digit : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) : ¬ CoordinatewiseCorridor 3 2 N K Q digit := by sorry

end PalomarCorpus.ExternalVerification1049RationalBaseBarrier

namespace PalomarCorpus.ExternalVerification243BoundedNegativePartRigidity
def sylvesterNext (a : ℤ) : ℤ := a ^ 2 - a + 1 /-- Centered reciprocal-tail error. -/

def centeredState (a D C : ℤ) : ℤ := D - (a - 1) * C /-- Complete rigidity of the bounded-negative centered-error branch: the centered defect vanishes eventually and the denominator orbit consequently follows the exact Sylvester recurrence eventually. -/

theorem boundedNegativePart_completeRigidity (a C D : ℕ → ℕ) (E : ℕ → ℤ) (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n) (hC : ∀ n, C (n + 1) + D n = a n * C n) (hD : ∀ n, D (n + 1) = a n * D n) (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)) (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n) (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n) : (∃ N, ∀ n, N ≤ n → E n = 0) ∧ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by sorry

end PalomarCorpus.ExternalVerification243BoundedNegativePartRigidity

namespace PalomarCorpus.ExternalVerification243BoundedRiseReducedTail
theorem no_boundedRise_reducedTail (a u v : ℕ → ℕ) (B : ℕ) (hB : 0 < B) (ha : ∀ n, 1 < a n) (hred : ∀ n, Nat.Coprime (u n) (v n)) (hu : ∀ n, u (n + 1) + v n = a n * u n) (hv : ∀ n, v (n + 1) = a n * v n) (hrise : ∀ n, u (n + 1) ≤ u n + B) (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) : False := by sorry

end PalomarCorpus.ExternalVerification243BoundedRiseReducedTail

namespace PalomarCorpus.ExternalVerification243PeriodicNegativeOrbit
theorem no_phasePrimitivePeriodicNegative_orbit (a D C e : ℕ → ℕ) (h M : ℕ) (hh : 0 < h) (hM : 0 < M) (ha : ∀ n, 2 ≤ a n) (hepos : ∀ n, 0 < e n) (helt : ∀ n, e n < a n) (hD : ∀ n, D (n + 1) = a n * D n) (hC : ∀ n, C (n + 1) = C n + e n) (hshape : ∀ n, D n + e n = (a n - 1) * C n) (hperiod : ∀ n, e (n + h) = e n) (hphase : ∀ n, C (n + h) = C n + M) (hprimitive : ∀ p, p.Prime → p ∣ M → ¬ (p ∣ C 0 ∧ ∀ n, p ∣ e n)) : False := by sorry

theorem no_periodicNegative_orbit (a D C e : ℕ → ℕ) (h M : ℕ) (hh : 0 < h) (hM : 0 < M) (ha : ∀ n, 2 ≤ a n) (hepos : ∀ n, 0 < e n) (helt : ∀ n, e n < a n) (hD : ∀ n, D (n + 1) = a n * D n) (hC : ∀ n, C (n + 1) = C n + e n) (hshape : ∀ n, D n + e n = (a n - 1) * C n) (hperiod : ∀ n, e (n + h) = e n) (hphase : ∀ n, C (n + h) = C n + M) : False := by sorry

theorem no_eventuallyPeriodicNegative_orbit (a D C e : ℕ → ℕ) (N h M : ℕ) (hh : 0 < h) (hM : 0 < M) (ha : ∀ n, N ≤ n → 2 ≤ a n) (hepos : ∀ n, 0 < e (N + n)) (helt : ∀ n, e (N + n) < a (N + n)) (hD : ∀ n, N ≤ n → D (n + 1) = a n * D n) (hC : ∀ n, N ≤ n → C (n + 1) = C n + e n) (hshape : ∀ n, N ≤ n → D n + e n = (a n - 1) * C n) (hperiod : ∀ n, e (N + n + h) = e (N + n)) (hphase : ∀ n, C (N + n + h) = C (N + n) + M) : False := by sorry

end PalomarCorpus.ExternalVerification243PeriodicNegativeOrbit

namespace PalomarCorpus.ExternalVerification243ProtectedEpochEnergy
def runningMax (u : ℕ → ℕ) : ℕ → ℕ | 0 => u 0 | n + 1 => max (runningMax u n) (u (n + 1)) /-- **Protected-epoch record energy.**  One odd prime power dividing a single denominator state forces an explicit lower bound on the record energy spent before the numerator reaches half of `p * Q`, uniformly in the cancellation factors. -/

theorem protected_epoch_energy_integer (a u v w hc : ℕ → ℕ) (p l s τ : ℕ) (hp : p.Prime) (hpodd : Odd p) (hl : 1 ≤ l) (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n)) (hvpos : ∀ n, s ≤ n → 0 < v n) (hw : ∀ n, s ≤ n → w n + v n = a n * u n) (hwpos : ∀ n, s ≤ n → 0 < w n) (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1)) (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1)) (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n) (hprot : p ^ l ∣ v s) (hQ : 16 ≤ p ^ l) (hRs : 4 * runningMax u s < p * p ^ l) (hsτ : s < τ) (hτ : p * p ^ l ≤ 2 * u τ) : ∃ J : Finset ℕ, (∀ n ∈ J, s ≤ n ∧ n < τ ∧ runningMax u n < u (n + 1) ∧ u n + 3 ≤ u (n + 1) ∧ hc n = 1) ∧ p * p ^ l ≤ (8 * p + 8) * J.card + 4 * ∑ n ∈ J, (u (n + 1) - u n - 2) + 8 * p := by sorry

end PalomarCorpus.ExternalVerification243ProtectedEpochEnergy

namespace PalomarCorpus.ExternalVerification243RecordIncrementBarrier
def sylvesterNext (a : ℤ) : ℤ := a ^ 2 - a + 1 /-- The running maximum of a natural-valued sequence. -/

def runningMax (u : ℕ → ℕ) : ℕ → ℕ | 0 => u 0 | n + 1 => max (runningMax u n) (u (n + 1)) /-- **True-record-increment rigidity, conditional on the fresh prime-power supply.** Along a dynamically reduced primitive reciprocal tail with arbitrary cancellation, if the nearest-integer normalisation holds eventually, the normalised error vanishes, the running maximum increases by at most one at every late step, and fresh prime powers recur at arbitrarily late indices dominating the current record, then the multipliers eventually satisfy the exact Sylvester recurrence. -/

theorem recordIncrementOne_sylvesterNext_eventually (a u v w hc : ℕ → ℕ) (e : ℕ → ℤ) (N : ℕ) (hvpos : ∀ n, N ≤ n → 0 < v n) (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n)) (hw : ∀ n, N ≤ n → w n + v n = a n * u n) (hwpos : ∀ n, N ≤ n → 0 < w n) (hnum : ∀ n, N ≤ n → w n = hc n * u (n + 1)) (hden : ∀ n, N ≤ n → a n * v n = hc n * v (n + 1)) (he : ∀ n, N ≤ n → e n = (v n : ℤ) - ((a n : ℤ) - 1) * (u n : ℤ)) (hcentre : ∀ n, N ≤ n → 2 * (e n).natAbs < u n) (hvanish : ∀ K, ∃ M, ∀ n, M ≤ n → K * (e n).natAbs < u n) (hinc : ∀ n, N ≤ n → runningMax u (n + 1) ≤ runningMax u n + 1) (hsupply : ∀ M, ∃ s, M ≤ s ∧ ∃ p l, p.Prime ∧ 1 ≤ l ∧ p ^ l ∣ v s ∧ runningMax u s + 3 ≤ p ^ l) : ∃ M, ∀ n, M ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by sorry

end PalomarCorpus.ExternalVerification243RecordIncrementBarrier

namespace PalomarCorpus.ExternalVerification243SaturatedSquareTransport
theorem saturated_square_transport_raw {a u v w hc u' v' : ℕ} {a' e e' : ℤ} (hq : w + v = a * u) (hnum : w = hc * u') (hden : a * v = hc * v') (he : e = (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ)) (he' : e' = (v' : ℤ) - (a' - 1) * (u' : ℤ)) : (u' : ℤ) ∣ (hc : ℤ) * e * e' - (v : ℤ) ^ 2 := by sorry

theorem legendre_defect_forces_nonsquare_content {b s u' p : ℕ} {e e' : ℤ} (hdvd : (u' : ℤ) ∣ (b : ℤ) * e * e' - ((b : ℤ) * (s : ℤ)) ^ 2) (hpu : p ∣ u') (hnr : ¬ IsSquare ((e : ZMod p) * (e' : ZMod p))) : b ≠ 1 := by sorry

end PalomarCorpus.ExternalVerification243SaturatedSquareTransport

namespace PalomarCorpus.ExternalVerification243SlowRiseBarrier
theorem no_slowRise_reducedTail (a u v : ℕ → ℕ) (N B : ℕ) (ha : ∀ n, N ≤ n → 1 < a n) (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n)) (hu : ∀ n, N ≤ n → u (n + 1) + v n = a n * u n) (hv : ∀ n, N ≤ n → v (n + 1) = a n * v n) (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) (hstart : u (N + B) < ∏ i : Fin B, a (N + i.1)) (hrise : ∀ n, N + B ≤ n → u n < 2 * ∏ i : Fin B, a (N + i.1) → u (n + 1) ≤ u n + B) : False := by sorry

end PalomarCorpus.ExternalVerification243SlowRiseBarrier

namespace PalomarCorpus.ExternalVerification249BinaryCyclotomicAnchors
open scoped BigOperators
noncomputable def binaryCyclotomicLayer (n : ℕ) : ℕ := ((Polynomial.cyclotomic n ℤ).eval (2 : ℤ)).natAbs

def UnboundedPrimeDivisorSupply (C : ℕ → ℕ) (h : ℕ) : Prop := ∀ B N₀ : ℕ, ∃ q p : ℕ, q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (h * q) ∧ B < p

noncomputable def totientTail (N : ℕ) : ℝ := ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

def CyclotomicAnchoredKillSupply (C : ℕ → ℕ) : Prop := ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ q p L : ℕ, q.Prime ∧ p.Prime ∧ Nat.Coprime p (h * q) ∧ p ∣ C (h * q) ∧ h * q ∣ p - 1 ∧ N₀ ≤ p - 1 ∧ certifiedKill (h * q) (p - 1) L

theorem exists_clean_binaryCyclotomicAnchor (h N₀ : ℕ) (hh : 0 < h) : ∃ q p : ℕ, q.Prime ∧ p.Prime ∧ Nat.Coprime p (h * q) ∧ p ∣ binaryCyclotomicLayer (h * q) ∧ h * q ∣ p - 1 ∧ N₀ ≤ p - 1 := by sorry

theorem binaryCyclotomicLayer_unboundedPrimeDivisorSupply (h : ℕ) (hh : 0 < h) : UnboundedPrimeDivisorSupply binaryCyclotomicLayer h := by sorry

theorem binaryCyclotomicAnchoredKillSupply_iff_irrational : CyclotomicAnchoredKillSupply binaryCyclotomicLayer ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by sorry

theorem exists_unbounded_binaryCyclotomicSupport_with_periodLock_of_not_irrational (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) : ∃ h : ℕ, 0 < h ∧ UnboundedPrimeDivisorSupply binaryCyclotomicLayer h ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by sorry

end PalomarCorpus.ExternalVerification249BinaryCyclotomicAnchors

namespace PalomarCorpus.ExternalVerification249DyadicTotientKernel
open Module
def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n => Nat.totient (2 ^ j * n + r) /-- The duplicate-free channels through level `e`. -/

abbrev TotientCanonicalIndex (e : ℕ) := Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)

def canonicalTotientKernelFamily (e : ℕ) : TotientCanonicalIndex e → ℕ → ℚ | Sum.inl i => totientKernelSeq i.val 0 | Sum.inr ⟨j, r⟩ => totientKernelSeq (j.val + 1) (2 * r.val + 1) /-- Every dyadic totient channel at levels `0,...,e`. -/

abbrev TotientKernelThroughLevelIndex (e : ℕ) := Σ j : Fin (e + 1), Fin (2 ^ j.val) /-- The complete finite dyadic kernel through level `e`. -/

def totientKernelThroughLevelFamily (e : ℕ) : TotientKernelThroughLevelIndex e → ℕ → ℚ | ⟨j, r⟩ => totientKernelSeq j.val r.val /-- All canonical dyadic sections. -/

abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)

def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ | ⟨j, r⟩ => totientKernelSeq j r.val /-- The two zero-residue base channels and one odd residue per positive level. -/

abbrev TotientOddCoreIndex := Fin 2 ⊕ Σ j : ℕ, Fin (2 ^ j)

def oddCoreTotientKernelFamily : TotientOddCoreIndex → ℕ → ℚ | Sum.inl i => totientKernelSeq i.val 0 | Sum.inr ⟨j, r⟩ => totientKernelSeq (j + 1) (2 * r.val + 1) /-- The odd-core sections form the complete independent spanning family, and the unreduced finite kernel through level `e` has exact rank `2^e+1`. -/

theorem dyadicTotientKernelOddCoreBasisAndFiniteRanks : LinearIndependent ℚ oddCoreTotientKernelFamily ∧ Submodule.span ℚ (Set.range fullTotientKernelFamily) = Submodule.span ℚ (Set.range oddCoreTotientKernelFamily) ∧ ∀ e : ℕ, 1 ≤ e → Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)) = Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e)) ∧ finrank ℚ (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) = 2 ^ e + 1 := by sorry

end PalomarCorpus.ExternalVerification249DyadicTotientKernel

namespace PalomarCorpus.ExternalVerification249MobiusMersenneLadderStructure
open scoped BigOperators
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ := ∑' n : ℕ, mobiusMersenneTerm r n /-- The literal Möbius–Lambert rung `Θ̂ᵣ = ∑_{d ≥ 1} μ(d) / (2^(r·d) - 1)`. -/

theorem mobiusMersenneTheta_strict_logConcave (r : ℕ) (hr : 1 ≤ r) : mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) < mobiusMersenneTheta (r + 1) ^ 2 := by sorry

theorem mobiusMersenneTheta_hankel_two_neg (r : ℕ) (hr : 1 ≤ r) : mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) - mobiusMersenneTheta (r + 1) ^ 2 < 0 := by sorry

end PalomarCorpus.ExternalVerification249MobiusMersenneLadderStructure

namespace PalomarCorpus.ExternalVerification249RankOneSharpFloor
open scoped BigOperators
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ := ∑' n : ℕ, mobiusMersenneTerm r n /-- The first `Y` atoms of rung `r`. -/

noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ := mobiusMersennePrefix Y (e + 2) ^ 2 / mobiusMersennePrefix Y (2 * e + 2) /-- The five-atom first-depth kernel minimises the admissible quotient. -/

theorem rankOneSubrankQuotient_ge_one_five {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) : rankOneSubrankQuotient 1 5 ≤ rankOneSubrankQuotient e Y := by sorry

theorem rankOneSubrankQuotient_eq_one_five_iff {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) : rankOneSubrankQuotient e Y = rankOneSubrankQuotient 1 5 ↔ e = 1 ∧ Y = 5 := by sorry

theorem rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) : (21 : ℝ) / 320 < rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by sorry

theorem rankOneSubrankQuotient_sub_theta_two_gt_one_div_sixteen {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) : (1 : ℝ) / 16 < rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by sorry

theorem not_forall_rankOneSubrankQuotient_sub_theta_two_gt_one_div_fifteen : ¬ ∀ {e Y : ℕ}, 1 ≤ e → 4 ≤ Y → (1 : ℝ) / 15 < rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by sorry

theorem positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ) (e Y : ι → ℕ) (hw : ∀ i ∈ s, 0 < w i) (he : ∀ i ∈ s, 1 ≤ e i) (hY : ∀ i ∈ s, 4 ≤ Y i) : (21 : ℝ) / 320 < (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) / (∑ i ∈ s, w i) - mobiusMersenneTheta 2 := by sorry

theorem primitive_form_abs_gt_twentyOne_div_threeTwenty {e Y q : ℕ} {p : ℤ} (he : 1 ≤ e) (hY : 4 ≤ Y) (hq : 1 ≤ q) (hquot : rankOneSubrankQuotient e Y = (p : ℝ) / q) : (q : ℝ) * (21 : ℝ) / 320 < |(q : ℝ) * mobiusMersenneTheta 2 - p| := by sorry

end PalomarCorpus.ExternalVerification249RankOneSharpFloor

namespace PalomarCorpus.ExternalVerification249ResidueClassTotientSeries
noncomputable def dyadicValue (a : ℕ → ℤ) : ℝ := ∑' n : ℕ, (a n : ℝ) / 2 ^ n /-- The binary value of a fixed-resolution observable of the totient word. -/

noncomputable def totientObservableValue (f : ℕ → ℤ) (m : ℕ) : ℝ := ∑' n : ℕ, ((f (Nat.totient n % m) : ℤ) : ℝ) / 2 ^ n /-- `A_m = ∑_{n} (φ n mod m) / 2 ^ n`, least nonnegative residues. -/

noncomputable def totientResidueValue (m : ℕ) : ℝ := ∑' n : ℕ, ((Nat.totient n % m : ℕ) : ℝ) / 2 ^ n /-- **Isolated pulse separation.**  A bounded integer sequence with a nonzero letter `t` at `p = N + 1 + L` and a two-sided block of `L` zeros around it keeps `q * dyadicValue a` at an explicit distance from every integer. -/

theorem isolated_pulse_separation {a : ℕ → ℤ} {C : ℝ} (hC : ∀ n, |(a n : ℝ)| ≤ C) {N L q : ℕ} {t : ℤ} (hq : 1 ≤ q) (hL : 2 * (q : ℝ) * C < 2 ^ L) (hcentre : a (N + 1 + L) = t) (ht : t ≠ 0) (hzero : ∀ i, i ≤ 2 * L → i ≠ L → a (N + 1 + i) = 0) (k : ℤ) : (q : ℝ) * (|(t : ℝ)| - C / 2 ^ L) / 2 ^ (N + 1 + L) ≤ |(q : ℝ) * dyadicValue a - (k : ℝ)| := by sorry

theorem irrational_dyadicValue_of_pulses {a : ℕ → ℤ} {C : ℝ} (hC : ∀ n, |(a n : ℝ)| ≤ C) (hpulse : ∀ L : ℕ, ∃ p : ℕ, L + 1 < p ∧ a p ≠ 0 ∧ ∀ j, 0 < j → j ≤ L → a (p - j) = 0 ∧ a (p + j) = 0) : Irrational (dyadicValue a) := by sorry

theorem two_sided_prime_isolation {m : ℕ} (hm : 2 ≤ m) (L N r : ℕ) (hr : Nat.Coprime (r + 1) m) : ∃ p : ℕ, N < p ∧ L + 1 < p ∧ p.Prime ∧ Nat.totient p ≡ r [MOD m] ∧ ∀ j, 0 < j → j ≤ L → m ∣ Nat.totient (p - j) ∧ m ∣ Nat.totient (p + j) := by sorry

theorem irrational_totientObservable {m : ℕ} (hm : 2 ≤ m) (f : ℕ → ℤ) (hf0 : f 0 = 0) {r : ℕ} (hr : r < m) (hcop : Nat.Coprime (r + 1) m) (hfr : f r ≠ 0) : Irrational (totientObservableValue f m) := by sorry

theorem fixed_resolution_observable_irrational {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℤ) (hf0 : f 0 = 0) {r : ℕ} (hr : r < 2 ^ k) (hreven : r % 2 = 0) (hfr : f r ≠ 0) : Irrational (totientObservableValue f (2 ^ k)) := by sorry

theorem residue_series_irrational {m : ℕ} (hm : 3 ≤ m) : Irrational (totientResidueValue m) := by sorry

end PalomarCorpus.ExternalVerification249ResidueClassTotientSeries

namespace PalomarCorpus.ExternalVerification249TotientKernelBasis
open Module
theorem allSlopeAffineTotientFormsLinearIndependent {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i) : LinearIndependent ℚ (fun (i : ι) (n : ℕ) => (Nat.totient (a i * n + b i) : ℚ)) := by sorry

def kernelSeq (k j r : ℕ) : ℕ → ℚ := fun n => (Nat.totient (k ^ j * n + r) : ℚ) /-- The canonical level-`e` index: two zero-residue base channels, and one channel per canonical residue at each level `1, …, e`.  A canonical residue at level `j + 1` is written `k * s + (u + 1)` with `s < k^j` and `u < k - 1`, which is exactly the parametrisation of `1 ≤ r < k^(j+1)` with `k ∤ r`. -/

abbrev CanonicalIndex (k e : ℕ) := Fin 2 ⊕ Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1) /-- The canonical residue `k * s + (u + 1)` named by a positive-level index. -/

def canonicalResidue (k : ℕ) {e : ℕ} (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) : ℕ := k * x.2.1.val + (x.2.2.val + 1) /-- The canonical level-`e` family of base-`k` totient channels. -/

def canonicalFamily (k e : ℕ) : CanonicalIndex k e → ℕ → ℚ | Sum.inl i => kernelSeq k i.val 0 | Sum.inr x => kernelSeq k (x.1.val + 1) (canonicalResidue k x) /-- The complete base-`k` kernel index through level `e`, before any reduction: every pair `(j, r)` with `j ≤ e` and `r < k^j`. -/

abbrev ThroughLevelIndex (k e : ℕ) := Σ j : Fin (e + 1), Fin (k ^ j.val) /-- Every base-`k` section `n ↦ φ(k^j n + r)` at levels `0, …, e`. -/

def throughLevelFamily (k e : ℕ) : ThroughLevelIndex k e → ℕ → ℚ | ⟨j, r⟩ => kernelSeq k j.val r.val /-- Evaluation of a formal `ℚ`-combination of the symbols `E_{j,r}`, `j ≤ e`, `r < k^j`, at the corresponding kernel channels.  Its kernel is the module of `ℚ`-linear relations among the unreduced level-`e` channels. -/

noncomputable def relationMap (k e : ℕ) : (ThroughLevelIndex k e → ℚ) →ₗ[ℚ] (ℕ → ℚ) := Fintype.linearCombination ℚ (throughLevelFamily k e) /-- **The all-base totient kernel structure theorem.**  For every integer base `k ≥ 2` and every depth `e ≥ 1`: 1. the canonical family is `ℚ`-linearly independent; 2. it spans the whole unreduced level-`e` kernel; 3. it therefore indexes a basis of that span; 4. the span has dimension exactly `k^e + 1`; 5. the relation module has dimension exactly `∑_{1 ≤ j < e} k^j`. Part 5 is the complement of part 4 inside the `∑_{j ≤ e} k^j` unreduced channels.  It states the dimension of the relation space only; it does not assert that any particular family of relations generates it. -/

theorem allBaseTotientKernelBasisRankAndRelationDimension (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) : LinearIndependent ℚ (canonicalFamily k e) ∧ Submodule.span ℚ (Set.range (throughLevelFamily k e)) = Submodule.span ℚ (Set.range (canonicalFamily k e)) ∧ Nonempty (Basis (CanonicalIndex k e) ℚ (Submodule.span ℚ (Set.range (throughLevelFamily k e)))) ∧ finrank ℚ (Submodule.span ℚ (Set.range (throughLevelFamily k e))) = k ^ e + 1 ∧ finrank ℚ (LinearMap.ker (relationMap k e)) = ∑ j ∈ Finset.Ico 1 e, k ^ j := by sorry

end PalomarCorpus.ExternalVerification249TotientKernelBasis

namespace PalomarCorpus.ExternalVerification251ActualPrimeGapTail
open scoped BigOperators
noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ := (primeGap0 n : ℝ) / 2 ^ (n + 1)

def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop := ∀ N, T (N + 1) = 2 * T N - g (N + 1)

noncomputable def rationalPrimeGapTailState (S : ℚ) (N : ℕ) : ℚ := 2 ^ (N + 1) * (S - primeGapPartialSumQ (N + 1))

def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ := T (N + h) - T N

def RatIntegral (x : ℚ) : Prop := ∃ z : ℤ, x = z /-- Hypothetical non-irrationality produces one rational candidate whose algebraic states are every scaled real tail of the actual gap series. -/

theorem exists_rationalPrimeGapTailState_representation_of_not_irrational (h : ¬ Irrational (∑' n : ℕ, primeGapDyadicTerm n)) : ∃ S : ℚ, (S : ℝ) = ∑' n : ℕ, primeGapDyadicTerm n ∧ ∀ N, ((rationalPrimeGapTailState S N : ℚ) : ℝ) = 2 ^ (N + 1) * ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1)) := by sorry

theorem rationalPrimeGapTailState_recurrence (S : ℚ) : DyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) (rationalPrimeGapTailState S) := by sorry

theorem rationalPrimeGapTailShift_eventuallyIntegral (S : ℚ) : ∃ h, 0 < h ∧ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift (rationalPrimeGapTailState S) h N) := by sorry

theorem rationalPrimeGapTail_has_positive_shift_not_eventually_small (S : ℚ) : ∃ h, 0 < h ∧ ¬ ∃ N₀, ∀ N, N₀ ≤ N → -1 < tailShift (rationalPrimeGapTailState S) h N ∧ tailShift (rationalPrimeGapTailState S) h N < 1 := by sorry

end PalomarCorpus.ExternalVerification251ActualPrimeGapTail

namespace PalomarCorpus.ExternalVerification251FreePairEquivalence
open scoped BigOperators
noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ := (primeGap0 n : ℝ) / 2 ^ (n + 1)

def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop := ∀ N, T (N + 1) = 2 * T N - g (N + 1)

def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop := ∀ N, T (N + 1) = 2 * T N - g (N + 1)

def RatIntegral (x : ℚ) : Prop := ∃ z : ℤ, x = z

def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop := ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧ ¬RealIntegral (realTailShift T h N) /-- The free-pair criterion: for every positive modulus and every cutoff, some pair of indices beyond the cutoff, congruent modulo the modulus, has a nonintegral tail difference. -/

def CofinalFreePairNonintegral (T : ℕ → ℝ) : Prop := ∀ t : ℕ, 0 < t → ∀ N₀ : ℕ, ∃ N M : ℕ, N₀ ≤ N ∧ N₀ ≤ M ∧ N ≡ M [MOD t] ∧ ¬ RealIntegral (T M - T N) /-- The real scaled tail of the actual prime-gap series after the first `N+1` gaps. -/

noncomputable def primeGapRealTail (N : ℕ) : ℝ := 2 ^ (N + 1) * ∑' k : ℕ, primeGapDyadicTerm (k + (N + 1)) /-- **Erdős #251 in free-pair form.**  The consecutive-prime-gap dyadic series is irrational exactly when, for every positive modulus `t` and every cutoff, two tail indices beyond the cutoff and congruent modulo `t` have a nonintegral scaled-tail difference.  Nothing here produces such pairs. -/

theorem irrational_primeGap_tsum_iff_cofinalFreePairNonintegral : Irrational (∑' n : ℕ, primeGapDyadicTerm n) ↔ CofinalFreePairNonintegral primeGapRealTail := by sorry

theorem irrational_initial_iff_cofinalFreePairNonintegral {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T) : Irrational (T 0) ↔ CofinalFreePairNonintegral T := by sorry

theorem cofinalFreePairNonintegral_iff_cofinalNonintegralTailShifts {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T) : CofinalFreePairNonintegral T ↔ CofinalNonintegralTailShifts T := by sorry

theorem exists_free_pair_lattice {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) : ∃ N₀ t : ℕ, 0 < t ∧ ∀ N M : ℕ, N₀ ≤ N → N₀ ≤ M → (RatIntegral (T M - T N) ↔ N ≡ M [MOD t]) := by sorry

theorem free_pair_integral_iff_modEq {g : ℕ → ℤ} {T : ℕ → ℚ} (hrec : DyadicTailRecurrence g T) {N₀ : ℕ} (hodd : Odd (T N₀).den) {N M : ℕ} (hN : N₀ ≤ N) (hM : N₀ ≤ M) : RatIntegral (T M - T N) ↔ N ≡ M [MOD orderOf (2 : ZMod (T N₀).den)] := by sorry

theorem primeGapRealTail_recurrence : RealDyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) primeGapRealTail := by sorry

theorem primeGapRealTail_zero : primeGapRealTail 0 = 2 * (∑' n : ℕ, primeGapDyadicTerm n) - 1 := by sorry

end PalomarCorpus.ExternalVerification251FreePairEquivalence

namespace PalomarCorpus.ExternalVerification251KernelDenominatorFloor
open scoped BigOperators
noncomputable def primeDyadicTerm (n : ℕ) : ℝ := (prime0 n : ℝ) / 2 ^ (n + 1) /-- The real term in the corresponding consecutive-prime-gap series. -/

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ := (primeGap0 n : ℝ) / 2 ^ (n + 1) /-- `noSmallDivisor m fuel k = true` iff no `j` with `k ≤ j < k + fuel` and `j * j ≤ m` divides `m`. -/

def certCheck (c u v u' v' X : ℕ) : Bool := let s := primeSumLoop c X (s.1 == c) && decide (0 < v) && decide (0 < v') && (u' * v == u * v' + 1) && decide (u * 2 ^ c < s.2 * v) && decide ((2 * s.2 + 5000 * (c + 1) ^ 4) * v' < u' * 2 ^ (c + 1))

def certX : ℕ := 10000

def certC : ℕ := 1229

def certU : ℕ := 8065641857152652932176019632186898003271162829171466334827308360779441527871744503350940785598890336998852555074615973558897922500842023448210201391609566636587897181681526620217

def certV : ℕ := 2194945124413663232143970924541263312422069524635615360518424707735195822181683072018928990483166295508439269024868312162917239885377332351730406072544968385302138677814423351745

theorem cert_10000 : certCheck certC certU certV certU' certV' certX = true := by sorry

theorem den_bound_of_certCheck (c u v u' v' X : ℕ) (hc : 9 ≤ c) (h : certCheck c u v u' v' X = true) : ∀ (a : ℤ) (b : ℕ), 0 < b → (∑' n, primeDyadicTerm n) = a / b → v + v' ≤ b := by sorry

theorem kernel_denominator_floor (a : ℤ) (b : ℕ) (hb : 0 < b) (hS : (∑' n, primeDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b := by sorry

theorem kernel_denominator_floor_primeGap (a : ℤ) (b : ℕ) (hb : 0 < b) (hS : (∑' n, primeGapDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b := by sorry

end PalomarCorpus.ExternalVerification251KernelDenominatorFloor

namespace PalomarCorpus.ExternalVerification251PolynomialShiftCountermodel
def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop := ∀ N, T (N + 1) = 2 * T N - g (N + 1) /-- Difference between tail states separated by `h` steps. -/

def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ := T (N + h) - T N /-- A rational number is integral when it is the cast of an integer. -/

def RatIntegral (x : ℚ) : Prop := ∃ z : ℤ, x = z /-- The rational polynomial tail orbit in the exact #251 countermodel. -/

def polynomialTailOrbit (n : ℕ) : ℚ := (2 * (n + 4) ^ 2 : ℕ) /-- The positive-even quadratic word paired with `polynomialTailOrbit`. -/

def polynomialGapWord (n : ℕ) : ℤ := (2 * (n ^ 2 + 4 * n + 2) : ℕ) /-- The real dyadic term of the countermodel series, indexed so that `n = 0` carries the digit `g 1 / 2`.  The zero-index digit is the initial carry and is not part of the series. -/

noncomputable def polynomialGapDyadicTerm (n : ℕ) : ℝ := (polynomialGapWord (n + 1) : ℝ) / 2 ^ (n + 1) /-- A positive, even, strictly growing polynomial digit word satisfies the dyadic recurrence while every fixed tail shift remains integral and every adjacent digit difference equals `4n + 10`, and its dyadic series sums to the rational number `32`. -/

theorem polynomialGapTailCountermodel : DyadicTailRecurrence polynomialGapWord polynomialTailOrbit ∧ (∀ n, 0 < polynomialGapWord n) ∧ (∀ n, ∃ k : ℤ, polynomialGapWord n = 2 * k) ∧ StrictMono polynomialGapWord ∧ (∀ h N, RatIntegral (tailShift polynomialTailOrbit h N)) ∧ (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n = ((4 * n + 10 : ℕ) : ℤ)) ∧ (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n ≠ 2 ∧ polynomialGapWord (n + 1) - polynomialGapWord n ≠ -2) ∧ (∑' n : ℕ, polynomialGapDyadicTerm n) = 32 ∧ ¬ Irrational (∑' n : ℕ, polynomialGapDyadicTerm n) := by sorry

end PalomarCorpus.ExternalVerification251PolynomialShiftCountermodel

namespace PalomarCorpus.ExternalVerification251PrimeGapIdentity
noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n /-- Zero-based consecutive prime gap. -/

noncomputable def primeDyadicTerm (n : ℕ) : ℝ := (prime0 n : ℝ) / 2 ^ (n + 1) /-- The term of the displayed prime series, with denominator `2^n`. -/

noncomputable def primeDisplayedDyadicTerm (n : ℕ) : ℝ := (prime0 n : ℝ) / 2 ^ n /-- The term of the corresponding consecutive-prime-gap series. -/

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ := (primeGap0 n : ℝ) / 2 ^ (n + 1) /-- An explicit elementary polynomial upper bound for the zero-based `n`th prime. -/

theorem prime0_le_polynomial (n : ℕ) : prime0 n ≤ 1250 * (n + 1) ^ 4 := by sorry

theorem primeSeries_summable : Summable primeDyadicTerm := by sorry

theorem primeGapSeries_summable : Summable primeGapDyadicTerm := by sorry

theorem primeSeries_eq_two_add_primeGapSeries : (∑' n : ℕ, primeDyadicTerm n) = 2 + ∑' n : ℕ, primeGapDyadicTerm n := by sorry

theorem primeSeries_irrational_iff_primeGapSeries : Irrational (∑' n : ℕ, primeDyadicTerm n) ↔ Irrational (∑' n : ℕ, primeGapDyadicTerm n) := by sorry

theorem primeDisplayedSeries_eq_four_add_two_primeGapSeries : (∑' n : ℕ, primeDisplayedDyadicTerm n) = 4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n := by sorry

theorem primeDisplayedSeries_irrational_iff_primeGapSeries : Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔ Irrational (∑' n : ℕ, primeGapDyadicTerm n) := by sorry

end PalomarCorpus.ExternalVerification251PrimeGapIdentity

namespace PalomarCorpus.ExternalVerification257AchievementSetGeometry
open scoped ENNReal
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ := ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1) /-- Binary digit strings supported on `J`. -/

def SupportedMersenneDigits (J : Set ℕ) := {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0} /-- The Mersenne digit map restricted to the selected support. -/

noncomputable def supportedMersenneDigitValue (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ := positiveMersenneDigitValue b.1 /-- The achievement set obtained by allowing binary digits only on `J`. -/

def supportedMersenneAchievementSet (J : Set ℕ) : Set ℝ := Set.range (supportedMersenneDigitValue J) /-- A Boolean support with rational Mersenne value has a Lebesgue-null orientation space. -/

theorem volume_supportedMersenneAchievementSet_eq_zero_of_rat_value {J : Set ℕ} (hJ0 : 0 ∉ J) {q : ℚ} (hvalue : positiveMersenneSupportValue J = (q : ℝ)) : volume (supportedMersenneAchievementSet J) = 0 := by sorry

theorem supportedMersenneAchievementSet_geometry_and_volume (J : Set ℕ) : Function.Injective (supportedMersenneDigitValue J) ∧ IsCompact (supportedMersenneAchievementSet J) ∧ IsNowhereDense (supportedMersenneAchievementSet J) ∧ (J.Infinite → Perfect (supportedMersenneAchievementSet J)) ∧ ((∃ F : Finset ℕ, J = (↑F : Set ℕ)ᶜ ∧ volume (supportedMersenneAchievementSet J) = ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨ (Jᶜ.Infinite ∧ volume (supportedMersenneAchievementSet J) = 0)) := by sorry

end PalomarCorpus.ExternalVerification257AchievementSetGeometry

namespace PalomarCorpus.ExternalVerification257FinitePeriodNoncollapse
def finiteErdosSum (F : Finset ℕ) (b : ℕ) : ℚ := ∑ n ∈ F, 1 / ((b : ℚ) ^ n - 1) /-- Exact finite-period noncollapse over the actual reduced denominator, including production of the coprimality witness needed to state the order. -/

theorem finite_period_noncollapse_rat_den (F : Finset ℕ) (b : ℕ) (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b) : ∃ hcop : Nat.Coprime b (finiteErdosSum F b).den, orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id := by sorry

theorem lcm_lt_den_finiteErdosSum (F : Finset ℕ) (b : ℕ) (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b) (h2 : 2 ≤ F.lcm id) : F.lcm id < (finiteErdosSum F b).den := by sorry

end PalomarCorpus.ExternalVerification257FinitePeriodNoncollapse

namespace PalomarCorpus.ExternalVerification257RationalTailRigidity
open Filter Set
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ := letI := Classical.decPred fun d : ℕ => d ∈ A (n.divisors.filter fun d => d ∈ A).card

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ := ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ := ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

def SupportCoeffZeroWindow (A : Set ℕ) (N h : ℕ) : Prop := CoeffZeroWindow (supportCoeff A) N h

noncomputable def reciprocalSupportTerm (A : Set ℕ) (a : ℕ) : ℝ := Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a

noncomputable def reciprocalMass (A : Set ℕ) : ℝ := ∑' a : ℕ, reciprocalSupportTerm A a

noncomputable def oddDoublingOrder (v : ℕ) (hvodd : Odd v) : ℕ := orderOf (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hvodd)) /-- Every infinite rational-valued support produces an unbounded positive natural tail orbit with exact recurrence and residue dynamics. -/

theorem exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c v : ℕ) (hv : 0 < v) (hvalue : erdosSupportSeries 2 A = (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) : ∃ u : ℕ → ℕ, (∀ n : ℕ, (u n : ℝ) = (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧ (∀ n : ℕ, 0 < u n) ∧ (∀ n : ℕ, u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n) ∧ (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v]) ∧ (∀ B : ℕ, ∃ n : ℕ, B < u n) := by sorry

theorem supportCoeffZeroWindow_length_le_eps_logb_add (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A) (p : ℤ) (c v : ℕ) (hv : 0 < v) (hvalue : erdosSupportSeries 2 A = (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) (ε : ℝ) (hε : 0 < ε) : ∃ B : ℝ, 0 ≤ B ∧ ∀ N h : ℕ, SupportCoeffZeroWindow A (c + N) h → (h : ℝ) ≤ ε * Real.logb 2 (N + 1 : ℝ) + B := by sorry

theorem one_div_oddOrder_le_reciprocalMass_of_support_fraction (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A) (hsum : Summable (reciprocalSupportTerm A)) (p : ℤ) (c : ℕ) {v : ℕ} (hv : 1 < v) (hvodd : Odd v) (hpv : p.toNat.Coprime v) (hvalue : erdosSupportSeries 2 A = (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) : (1 : ℝ) / (oddDoublingOrder v hvodd : ℝ) ≤ reciprocalMass A := by sorry

theorem dyadic_support_fraction_reciprocalMass_diverges_or_gt_one (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c : ℕ) (hvalue : erdosSupportSeries 2 A = (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) : ¬ Summable (reciprocalSupportTerm A) ∨ 1 < reciprocalMass A := by sorry

end PalomarCorpus.ExternalVerification257RationalTailRigidity

namespace PalomarCorpus.ExternalVerification257ReciprocalSupport
noncomputable def supportReciprocalTerm (A : Set ℕ) (a : ℕ) : ℝ := Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a /-- The reciprocal-power subseries at base b supported on A. -/

noncomputable def supportPowerSeries (b : ℕ) (A : Set ℕ) : ℝ := ∑' a : ℕ, Set.indicator A (fun a : ℕ => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a /-- Every infinite reciprocal-summable support gives an irrational reciprocal-power subseries at every integer base at least two. -/

theorem irrational_supportPowerSeries_of_summable_reciprocal (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable (supportReciprocalTerm A)) : Irrational (supportPowerSeries b A) := by sorry

end PalomarCorpus.ExternalVerification257ReciprocalSupport

namespace PalomarCorpus.ExternalVerification269ActualShellOrbit
open scoped BigOperators
def dyadicShellMassR235 (a : ℕ) : ℝ := dyadicShellMassQ235 a

noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ := by classical exact 2 * (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) * (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)

def dyadicOrderedBlockDigit235 (a : ℕ) : ℕ := if 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤ 5 ^ Nat.log 5 (2 ^ (a + 1)) then (dyadicSmoothShell235 a).card + 10 * dyadicBeforeThresholdCount235 3 a + 4 * dyadicBeforeThresholdCount235 5 a else (dyadicSmoothShell235 a).card + 2 * dyadicBeforeThresholdCount235 3 a + 12 * dyadicBeforeThresholdCount235 5 a

noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ := ∑' n : ℕ, dyadicShellMassR235 (a + n)

noncomputable def dyadicNormalizedTailStateR235 (tail : ℕ → ℝ) (a : ℕ) : ℝ := ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a

def FarFromIntegers (x δ : ℝ) : Prop := ∀ z : ℤ, δ ≤ |x - (z : ℝ)| /-- The actual infinite shell tail is summable, follows the exact ordered affine orbit, and satisfies the integral-or-cofinally-far alternative. -/

theorem actual_dyadicShellOrbit_recurrence_and_escape : Summable dyadicShellMassR235 ∧ (∀ a : ℕ, dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (a + 1) = dyadicBlockBase235 a * dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a - dyadicOrderedBlockDigit235 a) ∧ ((∃ a : ℕ, ∃ z : ℤ, dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a = (z : ℝ)) ∨ ∀ a₀, ∃ a, a₀ ≤ a ∧ FarFromIntegers (dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a) ((1 : ℝ) / 31)) := by sorry

end PalomarCorpus.ExternalVerification269ActualShellOrbit

namespace PalomarCorpus.ExternalVerification269ThreePrimeStructure
def smooth3Val (p q r i j k : ℕ) : ℕ := p ^ i * q ^ j * r ^ k

def threePrimeHeight (p q r x : ℕ) : ℕ := p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

def threePrimeKernelQ (p q r i j k : ℕ) : ℚ := (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹

def smoothPrefixLcm (p q r x : ℕ) : ℕ := (smoothPrefixExponents p q r x).lcm fun e => smooth3Val p q r e.1 e.2.1 e.2.2

def SameThreePrimeLogCell (p q r x y : ℕ) : Prop := Nat.log p x = Nat.log p y ∧ Nat.log q x = Nat.log q y ∧ Nat.log r x = Nat.log r y

def threePrimePositiveJumpSet (p q r count : ℕ) : Finset ℕ := (positivePrimePowers p count ∪ positivePrimePowers q count) ∪ positivePrimePowers r count

def smoothExponentBox (hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) := (Finset.range (hp + 1)).product ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))

def smoothPointHeight (p q r : ℕ) (e : ℕ × ℕ × ℕ) : ℕ := threePrimeHeight p q r (smooth3Val p q r e.1 e.2.1 e.2.2)

def smoothHeightFiber (p q r hp hq hr H : ℕ) : Finset (ℕ × ℕ × ℕ) := (smoothExponentBox hp hq hr).filter fun e => smoothPointHeight p q r e = H

def smoothExponentShell (p q r lo hi hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) := ((Finset.range (hp + 1)).product ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))).filter fun e => lo ≤ smooth3Val p q r e.1 e.2.1 e.2.2 ∧ smooth3Val p q r e.1 e.2.1 e.2.2 < hi /-- The literal LCM of the smooth prefix is exactly the product of the three maximal pure prime powers. -/

theorem smoothPrefixLcm_eq_threePrimeHeight {p q r x : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hx : x ≠ 0) : smoothPrefixLcm p q r x = threePrimeHeight p q r x := by sorry

theorem threePrimeKernelQ_eq_of_sameLogCell {p q r i j k i' j' k' : ℕ} (hcell : SameThreePrimeLogCell p q r (smooth3Val p q r i j k) (smooth3Val p q r i' j' k')) : threePrimeKernelQ p q r i j k = threePrimeKernelQ p q r i' j' k' := by sorry

theorem threePrimePositiveJumpSet_card {p q r count : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : (threePrimePositiveJumpSet p q r count).card = 3 * count := by sorry

theorem finiteSmoothKernelSum_groupedByHeight (p q r hp hq hr : ℕ) : (∑ e ∈ smoothExponentBox hp hq hr, threePrimeKernelQ p q r e.1 e.2.1 e.2.2) = ∑ H ∈ (smoothExponentBox hp hq hr).image (smoothPointHeight p q r), (smoothHeightFiber p q r hp hq hr H).card • ((H : ℚ)⁻¹) := by sorry

theorem smoothExponentShell_card_quadratic {p q r lo hi hp hq hr j : ℕ} (hrPos : 0 < r) (hwidth : hi ≤ r * lo) (hpq : hp ≤ hq) (hqr : hq ≤ hr) (hsum : hp + hq + hr = j) : 9 * (smoothExponentShell p q r lo hi hp hq hr).card ≤ (j + 3) ^ 2 := by sorry

theorem kernel_235_minor_eq_neg_one_fifteen : threePrimeKernelQ 2 3 5 0 0 0 * threePrimeKernelQ 2 3 5 1 1 0 - threePrimeKernelQ 2 3 5 1 0 0 * threePrimeKernelQ 2 3 5 0 1 0 = -(1 / 15 : ℚ) := by sorry

def NoIntegerOrbit (α : ℝ) : Prop := ∀ n : ℕ, 0 < n → Int.fract ((n : ℝ) * α) ≠ 0 /-- Generators `1 < p, q, r` whose logarithmic ratios `Real.logb r p` and `Real.logb r q` have no integer orbit force nonsingular kernel minors of every order, simultaneously in every third-coordinate layer. -/

theorem exists_uniform_nonsingular_threePrimeKernel_minor {p q r : ℕ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hα : NoIntegerOrbit (Real.logb r p)) (hβ : NoIntegerOrbit (Real.logb r q)) (n : ℕ) : ∃ I J : Fin n → ℕ, Function.Injective I ∧ Function.Injective J ∧ ∀ k : ℕ, (Matrix.det fun a b : Fin n => threePrimeKernelQ p q r (I a) (J b) k) ≠ 0 := by sorry

theorem threePrimeKernel_infiniteRank_and_noFiniteSeparation {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpr : p ≠ r) (hqr : q ≠ r) : (∀ n : ℕ, ∃ I J : Fin n → ℕ, Function.Injective I ∧ Function.Injective J ∧ ∀ k : ℕ, (Matrix.det fun a b : Fin n => threePrimeKernelQ p q r (I a) (J b) k) ≠ 0) ∧ (∀ d : ℕ, ¬ ∃ (f : Fin d → ℕ → ℚ) (G : Fin d → ℕ → ℕ → ℚ), ∀ i j k, threePrimeKernelQ p q r i j k = ∑ l : Fin d, f l i * G l j k) := by sorry

end PalomarCorpus.ExternalVerification269ThreePrimeStructure

namespace PalomarCorpus.ExternalVerification269WindowEscapeEquivalence
open scoped BigOperators
noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ := by classical exact 2 * (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) * (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)

def dyadicOrderedBlockDigit235 (a : ℕ) : ℕ := if 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤ 5 ^ Nat.log 5 (2 ^ (a + 1)) then (dyadicSmoothShell235 a).card + 10 * dyadicBeforeThresholdCount235 3 a + 4 * dyadicBeforeThresholdCount235 5 a else (dyadicSmoothShell235 a).card + 2 * dyadicBeforeThresholdCount235 3 a + 12 * dyadicBeforeThresholdCount235 5 a

noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ := ∑' n : ℕ, dyadicShellMassR235 (a + n)

noncomputable def trueNormalizedState (a : ℕ) : ℝ := dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a

def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ := if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))

def windowBase (b : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ | 0 => 1 | len + 1 => b (lo + len) * windowBase b lo len

def windowForcing (b e : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ | 0 => 0 | len + 1 => b (lo + len) * windowForcing b e lo len + e (lo + len) /-- The exact denominator-dependent producer consumed by the local-window contradiction.  It is named as a proposition, not asserted. -/

def CofinalLocalWindowEscape (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ) : Prop := ∀ B : ℕ, 0 < B → Nat.Coprime B 30 → ∀ lo₀ : ℕ, ∃ lo len : ℕ, lo₀ ≤ lo ∧ 0 < len ∧ 0 < Int.natAbs (windowBase (fun n => b n) lo len) ∧ shortBound B (lo + len) < leastPositiveResidue (Int.natAbs (windowBase (fun n => b n) lo len)) (-((B : ℤ) * windowForcing (fun n => b n) (fun n => m n) lo len)) /-- The width used as the short bound of the bridge. -/

def bridgeWidth (n : ℕ) : ℕ := 90 * (n + 1) ^ 2 /-- The producer stated for the actual radix word, the actual ordered digit and the short bound `B · 90 (n+1)^2`. -/

def ActualCofinalLocalWindowEscape : Prop := CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 (fun B n => B * bridgeWidth n) /-- The actual cofinal local-window escape is equivalent to irrationality of the `{2,3,5}` running-LCM value. -/

theorem actualCofinalLocalWindowEscape_iff_irrational_value : ActualCofinalLocalWindowEscape ↔ Irrational (dyadicShellTsumTailR235 0) := by sorry

theorem actualCofinalLocalWindowEscape_iff : ActualCofinalLocalWindowEscape ↔ Irrational (dyadicShellTsumTailR235 1) := by sorry

theorem cofinalLocalWindowEscape_of_irrational (h : Irrational (dyadicShellTsumTailR235 1)) : ActualCofinalLocalWindowEscape := by sorry

theorem cofinalLocalWindowEscape_of_irrational_of_quadratic (h : Irrational (dyadicShellTsumTailR235 1)) (sb : ℕ → ℕ → ℕ) (c : ℕ → ℕ) (hsb : ∀ B n, sb B n ≤ c B * (n + 1) ^ 2) : CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 sb := by sorry

theorem exists_reducedCarry_of_value_eq_rat {p q : ℤ} (hq : 0 < q) (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) : ∃ (B a₀ : ℕ) (d : ℕ → ℤ), 0 < B ∧ Nat.Coprime B 30 ∧ (∀ n, a₀ ≤ n → d (n + 1) = (dyadicBlockBase235 n : ℤ) * d n - (B : ℤ) * (dyadicOrderedBlockDigit235 n : ℤ)) ∧ (∀ n, a₀ ≤ n → 0 < d n) ∧ (∀ n, a₀ ≤ n → Int.natAbs (d n) ≤ B * bridgeWidth n) := by sorry

theorem trueNormalizedState_window (lo len : ℕ) : trueNormalizedState (lo + len) = ((windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len : ℤ) : ℝ) * trueNormalizedState lo - ((windowForcing (fun n => (dyadicBlockBase235 n : ℤ)) (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len : ℤ) : ℝ) := by sorry

theorem near_integer_of_residue_le_general (B lo len K : ℕ) (hB : 0 < B) (hKle : B * bridgeWidth (lo + len) ≤ K) (hres : leastPositiveResidue (Int.natAbs (windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len)) (-((B : ℤ) * windowForcing (fun n => (dyadicBlockBase235 n : ℤ)) (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len)) ≤ K) : ∃ k : ℤ, |(B : ℝ) * trueNormalizedState lo - (k : ℝ)| ≤ ((K : ℕ) : ℝ) / 2 ^ len := by sorry

theorem exists_pow_gt_quadratic (c lo : ℕ) : ∃ len : ℕ, 0 < len ∧ c * (lo + len + 1) ^ 2 < 2 ^ len := by sorry

end PalomarCorpus.ExternalVerification269WindowEscapeEquivalence

namespace PalomarCorpus.ExternalVerification68ChannelRadius
def channelLCM (D : ℕ) : ℕ := (Finset.Icc 2 D).lcm (fun d => d.factorial - 1) /-- Sharp explicit cubic radius bound on the square subsequence. -/

theorem square_subsequence_radius_three_halves_lower {t M R : ℕ} (ht : 2 ^ 32 ≤ t) (hMpos : 0 < M) (hdiv : channelLCM (2 * t ^ 2) ∣ M) (hsmall : M < (R + 1).factorial - 1) : 3 * t ^ 3 < 2 * (R + 1) := by sorry

theorem no_eventual_square_subsequence_three_halves_upper (M R : ℕ → ℕ) (hMpos : ∀ t, 2 ^ 32 ≤ t → 0 < M t) (hdiv : ∀ t, 2 ^ 32 ≤ t → channelLCM (2 * t ^ 2) ∣ M t) (hsmall : ∀ t, 2 ^ 32 ≤ t → M t < (R t + 1).factorial - 1) : ¬ ∃ T, ∀ t, T ≤ t → 2 * (R t + 1) ≤ 3 * t ^ 3 := by sorry

theorem not_isLittleO_square_subsequence_radius (M R : ℕ → ℕ) (hMpos : ∀ t, 4096 ≤ t → 0 < M t) (hdiv : ∀ t, 4096 ≤ t → channelLCM (2 * t ^ 2) ∣ M t) (hsmall : ∀ t, 4096 ≤ t → M t < (R t + 1).factorial - 1) : ¬ (fun t : ℕ => ((R t + 1 : ℕ) : ℝ)) =o[Filter.atTop] (fun t : ℕ => (t : ℝ) ^ 3) := by sorry

theorem square_subsequence_radius_cubic_lower {t M R : ℕ} (ht : 4096 ≤ t) (hMpos : 0 < M) (hdiv : channelLCM (2 * t ^ 2) ∣ M) (hsmall : M < (R + 1).factorial - 1) : t ^ 3 < 8 * (R + 1) := by sorry

theorem no_eventual_square_subsequence_cubic_upper (M R : ℕ → ℕ) (hMpos : ∀ t, 4096 ≤ t → 0 < M t) (hdiv : ∀ t, 4096 ≤ t → channelLCM (2 * t ^ 2) ∣ M t) (hsmall : ∀ t, 4096 ≤ t → M t < (R t + 1).factorial - 1) : ¬ ∃ T, ∀ t, T ≤ t → 8 * (R t + 1) ≤ t ^ 3 := by sorry

theorem sharp_radius_satisfies_square_log_constraint {t R : ℕ} (ht : 4 ≤ t) (hsharp : 9 * (R + 1) = 16 * t ^ 3) : (2 * t : ℝ) * (((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) * Real.log ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) - (2 * t ^ 2 + 1 - 2 * t : ℕ) - Real.log 2) < ((R + 1 : ℕ) : ℝ) * Real.log (R + 1 : ℝ) + (((2 * t + 1).choose 3 : ℕ) : ℝ) * Real.log ((2 * t ^ 2 : ℕ) : ℝ) := by sorry

end PalomarCorpus.ExternalVerification68ChannelRadius

namespace PalomarCorpus.ExternalVerification68CompanionOrbitBoundary
noncomputable def factorialGapSeries : ℝ := ∑' d : ℕ, if 1 < d then (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ) : ℝ)) else 0 /-- The fixed companion constant `C = ∑_{n≥2} 1/(n!(n! - 1))`. -/

noncomputable def companionConstant : ℝ := ∑' n : ℕ, if 2 ≤ n then (1 : ℝ) / ((n.factorial : ℝ) * ((((n.factorial : ℤ) - 1 : ℤ) : ℝ))) else 0 /-- The anchored unit-factorial term `1/n!`, supported on `n ≥ 2`. -/

noncomputable def unitFactTerm (n : ℕ) : ℝ := if 2 ≤ n then (1 : ℝ) / ((n.factorial : ℝ)) else 0 /-- Floor of the factorially scaled real number. -/

noncomputable def facFloor (x : ℝ) (m : ℕ) : ℤ := ⌊(m.factorial : ℝ) * x⌋ /-- The canonical mixed-radix factorial digit at radix `m`. -/

noncomputable def canonicalDigit (x : ℝ) (m : ℕ) : ℤ := facFloor x m - (m : ℤ) * facFloor x (m - 1) /-- The exact rational prefix through index `n`. -/

def factorialGapPrefix (n : ℕ) : ℚ := ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1) /-- The first integer strictly above the factorially scaled real prefix. -/

def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ := ⌊(n.factorial : ℚ) * x⌋ + 1 /-- Distance from the preceding scaled prefix to its strict successor. -/

noncomputable def factorialGapStepCarry (m : ℕ) : ℤ := -⌊1 + 1 / ((m.factorial : ℝ) - 1) - (m : ℝ) * factorialGapPredecessorGap m⌋ /-- The strict-successor carry boundary for the Erdős #68 series. The four conjuncts record respectively the rationality criterion in terms of eventual unit carries, its cofinal dual for irrationality, the pointwise carry and divisibility equivalence at every index `m ≥ 3`, and the resulting purely integral cofinal reformulation over the exact rational prefixes. -/

theorem companionOrbitBoundary_strictSuccessorCarry : (¬Irrational factorialGapSeries ↔ ∃ M : ℕ, ∀ m : ℕ, M ≤ m → factorialGapStepCarry m = 1) ∧ (Irrational factorialGapSeries ↔ ∀ B : ℕ, ∃ m : ℕ, B < m ∧ factorialGapStepCarry m ≠ 1) ∧ (∀ m : ℕ, 3 ≤ m → (factorialGapStepCarry m = 1 ↔ (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m)) ∧ (Irrational factorialGapSeries ↔ ∀ B : ℕ, ∃ m : ℕ, B < m ∧ ¬((m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m)) := by sorry

theorem companionOrbitBoundary_genericShift (x : ℝ) : (¬Irrational (x + ∑' n : ℕ, unitFactTerm n) ↔ ∃ M : ℕ, ∀ m : ℕ, M ≤ m → canonicalDigit x m = (m : ℤ) - 2) ∧ (¬Irrational (x + ∑' n : ℕ, unitFactTerm n) ↔ ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ((facFloor x m + 2 : ℤ) % (m : ℤ)) = 0) := by sorry

theorem companionOrbitBoundary_factorialGapSeries : (¬Irrational factorialGapSeries ↔ ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) = 0) ∧ (Irrational factorialGapSeries ↔ ∀ B : ℕ, ∃ m : ℕ, B < m ∧ ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) ≠ 0) := by sorry

theorem tsum_unitFactTerm_eq_exp_one_sub_two : (∑' n : ℕ, unitFactTerm n) = Real.exp 1 - 2 := by sorry

end PalomarCorpus.ExternalVerification68CompanionOrbitBoundary

namespace PalomarCorpus.ExternalVerification68PrimeUnitTranslator
def factorialMoment {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (index : ι → ℕ) : ℤ := ∑ j, coeff j * (index j).factorial /-- The integer numerator of the `d`-th divisor channel. -/

def channelNumerator {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℤ := ∑ j, coeff j * ((index j).factorial / d.factorial ^ (index j / d) : ℕ) /-- Coefficients `(p, -1)` of the prime-pair translator. -/

def primeTranslatorCoeff (p : ℕ) : Fin 2 → ℤ := ![(p : ℤ), -1] /-- Support indices `(p - 1, p)` of the prime-pair translator. -/

def primeTranslatorIndex (p : ℕ) : Fin 2 → ℕ := ![p - 1, p] /-- The real contribution of one channel to the tail beyond `D`. -/

noncomputable def channelResidual {ι : Type*} [Fintype ι] (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) : ℝ := ∑' d : ℕ, channelResidualTerm D coeff index d /-- Coefficients for a support enlarged by a scaled prime translator. -/

def appendPrimeTranslatorCoeff {ι : Type*} (coeff : ι → ℤ) (p : ℕ) (z : ℤ) : Sum ι (Fin 2) → ℤ := Sum.elim coeff (fun j => z * primeTranslatorCoeff p j) /-- Indices for a support enlarged by the prime translator. -/

def appendPrimeTranslatorIndex {ι : Type*} (index : ι → ℕ) (p : ℕ) : Sum ι (Fin 2) → ℕ := Sum.elim index (primeTranslatorIndex p) /-- The moment row together with the consecutive channel rows. -/

def cramerChannelKernelCoeff {n : ℕ} (index : Fin (n + 1) → ℕ) : Fin (n + 1) → ℤ := (augmentedChannelMomentMatrix index).cramer (Pi.single 0 1) /-- The common scale of the factorial grid at cutoff `D`. -/

def factorialGridIndex (n t : ℕ) (j : Fin (n + 2)) : ℕ := (t + j.val) * factorialGridScale (n + 2) /-- The prime-pair translator has zero factorial moment. -/

theorem primeTranslator_moment_zero {p : ℕ} (hp : 0 < p) : factorialMoment (primeTranslatorCoeff p) (primeTranslatorIndex p) = 0 := by sorry

theorem primeTranslator_channel_zero_of_lt_p {p d : ℕ} (hp : p.Prime) (hd2 : 2 ≤ d) (hdp : d < p) : channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by sorry

theorem primeTranslator_channel_at_prime {p : ℕ} (hp : p.Prime) : channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) p = (p.factorial : ℤ) - 1 := by sorry

theorem primeTranslator_channel_zero_of_p_lt {p d : ℕ} (hp : 0 < p) (hpd : p < d) : channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by sorry

theorem primeTranslator_channelResidual_eq_one {D p : ℕ} (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) : channelResidual D (primeTranslatorCoeff p) (primeTranslatorIndex p) = 1 := by sorry

theorem channelResidual_appendPrimeTranslator {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (index : ι → ℕ) {D p : ℕ} (z : ℤ) (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) : channelResidual D (appendPrimeTranslatorCoeff coeff p z) (appendPrimeTranslatorIndex index p) = channelResidual D coeff index + (z : ℝ) := by sorry

theorem exists_remote_factorialGrid_primeTranslator_reduction (n B : ℕ) : ∃ p : ℕ, ∃ z : ℤ, p.Prime ∧ (∀ j : Sum (Fin (n + 2)) (Fin 2), B < appendPrimeTranslatorIndex (factorialGridIndex n (B + 1)) p j) ∧ (∀ d ∈ Finset.Icc 2 (n + 2), channelNumerator (appendPrimeTranslatorCoeff (cramerChannelKernelCoeff (factorialGridIndex n (B + 1))) p z) (appendPrimeTranslatorIndex (factorialGridIndex n (B + 1)) p) d = 0) ∧ factorialMoment (appendPrimeTranslatorCoeff (cramerChannelKernelCoeff (factorialGridIndex n (B + 1))) p z) (appendPrimeTranslatorIndex (factorialGridIndex n (B + 1)) p) ≠ 0 ∧ |channelResidual (n + 2) (appendPrimeTranslatorCoeff (cramerChannelKernelCoeff (factorialGridIndex n (B + 1))) p z) (appendPrimeTranslatorIndex (factorialGridIndex n (B + 1)) p)| ≤ (1 : ℝ) / 2 := by sorry

end PalomarCorpus.ExternalVerification68PrimeUnitTranslator
