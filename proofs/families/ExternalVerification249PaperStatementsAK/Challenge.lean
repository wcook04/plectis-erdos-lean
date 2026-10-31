/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.GapFareyBound`, `Erdos249257.GcdMomentCalculus`,
`Erdos249257.GeometricCoprimality`,
`ErdosProblems.Erdos249.PaperCompleteR21.ActualLcmShortWindowArithmetic`,
`ErdosProblems.Erdos249.PaperCompleteR21.CoprimeLatticeSumsAndLambert`,
`ErdosProblems.Erdos249.PaperCompleteR21.FareyDenominatorFloorExtension`,
`ErdosProblems.Erdos249.PaperCompleteR21.FareyExactRangeAndDenominatorExclusion`,
`ErdosProblems.Erdos249.PaperCompleteR21.GeneralIrrationalityCriteriaAndGapBounds`,
`ErdosProblems.Erdos249.PaperCompleteR21.MersennePrimeSupportAnchors`,
`ErdosProblems.Erdos249.PaperCompleteR21.MobiusMersenneLadderLogConcavity`,
`ErdosProblems.Erdos249.PaperCompleteR21.RationalTailPeriodWitnesses`,
`ErdosProblems.Erdos249.PaperCompleteR21.ShortWindowSupplyAndSixteenShifts`,
`ErdosProblems.Erdos249.PaperCompleteR21.ThreeParticularEquivalences`,
`ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeCorridorAndSeparation`,
`ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicPulseCertificateFailure`,
`ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature`.
-/

namespace Erdos249257.ExternalVerification249PaperStatementsAK

noncomputable def FinitePrimeSupportEscape (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ,
    q.Prime → Q₀ ≤ q →
      ∀ p ∈ S, p.Prime → ¬ p ∣ C (m * q)

noncomputable def IsFirstGapFailure (V K H qstar : ℕ) : Prop :=
  (∀ q : ℕ, 0 < q → q < qstar → (q * V) % 2 ^ K + q * H < 2 ^ K) ∧
    ¬ ((qstar * V) % 2 ^ K + qstar * H < 2 ^ K)

noncomputable def cylinderMass (a b : ℕ+) : ℝ :=
  1 / (((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1))

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_ne_rat_of_den_dvd_two_pow_fourteen_mul_mersenne
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem totientSeries_ne_rat_of_den_dvd_two_pow_fourteen_mul_mersenne
    (r : ℚ) (h : ℕ) (h1 : 1 ≤ h) (h16 : h ≤ 16)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 14 * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_rational_den_gt_fareyBound in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totientSeries_rational_den_gt_fareyBound (q : ℚ)
    (hq : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (q : ℝ)) :
    79639646646701375323355774875831053 < q.den := by
  sorry

/-- States prop:AR-04-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.totient_mul_eq_totient_mul_gcd_div_totient_gcd in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totient_mul_eq_totient_mul_gcd_div_totient_gcd {j x : ℕ} (hj : 0 < j)
    (hx : 0 < x) :
    (Nat.totient (j * x) : ℚ)
      = (Nat.totient j : ℚ) * (Nat.totient x : ℚ) * (Nat.gcd j x : ℚ)
          / (Nat.totient (Nat.gcd j x) : ℚ) := by
  sorry

/-- States prop:A9-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.totient_one_eq_one in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_one_eq_one : Nat.totient 1 = 1 := by
  sorry

/-- States prop:C3-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.totient_series_ne_int_div_of_small_denominator in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totient_series_ne_int_div_of_small_denominator (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hle : q ≤ 79639646646701375323355774875831053) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (a : ℝ) / (q : ℝ) := by
  sorry

/-- States prop:C3-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.totient_series_ne_reduced_fraction_of_small_denominator
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem totient_series_ne_reduced_fraction_of_small_denominator (p : ℚ)
    (hden : p.den ≤ 79639646646701375323355774875831053) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (p : ℝ) := by
  sorry

/-- States prop:C1-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.totient_zero_eq_zero in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_zero_eq_zero : Nat.totient 0 = 0 := by
  sorry

/-- States prop:C1-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_coprime_pairs_eq_series_sub_half in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem tsum_pos_coprime_pairs_eq_series_sub_half :
    (∑' q : ℕ × ℕ, if 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2
        then 1 / (2 : ℝ) ^ (q.1 + q.2) else 0)
      = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 := by
  sorry

/-- States prop:C1-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_coprime_pairs_product_form in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem tsum_pos_coprime_pairs_product_form :
    (∑' q : ℕ × ℕ, if 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2
        then (1 / (2 : ℝ) ^ q.1) * (1 / (2 : ℝ) ^ q.2) else 0)
      = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.tsum_totient_pow_shift in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem tsum_totient_pow_shift {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, (Nat.totient n : ℝ) * r ^ n)
      = ∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1) := by
  sorry

/-- States prop:b4 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_defining_congruence in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem twoAdic_pulse_defining_congruence (H K B : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ H + K < p ∧ p.Prime ∧
      p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K] ∧ 1 + 2 ^ (K - 1) ≤ p := by
  sorry

/-- States prop:b4 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_error_bound in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem twoAdic_pulse_error_bound (H K p : ℕ) (hKp : K ≤ p)
    (hp : 2 ^ (K - 1) < p) :
    (p - K) + H + K + 2 = p + H + 2 ∧ 2 ^ (K - 1) < p + H + 2 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.twoAtom_hankel_gap in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem twoAtom_hankel_gap (r : ℕ) :
    (1 - 1 / (3 : ℝ) ^ (r + 1)) ^ 2
        - (1 - 1 / (3 : ℝ) ^ r) * (1 - 1 / (3 : ℝ) ^ (r + 2))
      = 4 / (3 : ℝ) ^ (r + 2) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.twoAtom_strict_logConcave in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem twoAtom_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    (1 - 1 / (3 : ℝ) ^ r) * (1 - 1 / (3 : ℝ) ^ (r + 2))
      < (1 - 1 / (3 : ℝ) ^ (r + 1)) ^ 2 := by
  sorry

/-- States prop:b2 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.two_point_sample_numerical_requirement in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem two_point_sample_numerical_requirement :
    2 * ((2 : ℝ)) ^ 2 / 5 = 8 / 5 ∧ (8 : ℝ) / 5 ≤ 2 * (9 / 10) ^ 2 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.two_pow_odd_eq in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_pow_odd_eq (q : ℕ) : (2 : ℝ) ^ (2 * q + 1) = 2 * (4 : ℝ) ^ q := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.unbounded_prime_divisors_of_escape_of_nontrivial in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem unbounded_prime_divisors_of_escape_of_nontrivial {C : ℕ → ℕ} {m : ℕ}
    (hnontrivial : ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q → 1 < C (m * q))
    (hescape : FinitePrimeSupportEscape C m) :
    ∀ B N₀ : ℕ, ∃ q p : ℕ,
      q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p := by
  sorry

/-- States prop:C1-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.visible_antidiagonal_one in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem visible_antidiagonal_one :
    ((Finset.antidiagonal 1).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ Nat.Coprime q.1 q.2)
      = {((1 : ℕ), (0 : ℕ))} := by
  sorry

/-- States catalogue:cert:c1, lem:farey from the long record for Erdős problem #249. Transported
from GapFareyBound.farey_gap in the substantive development, whose statement was refereed
against the paper in the coverage ledger. -/
theorem farey_gap {a b c d r s : ℤ}
    (hb : 0 < b) (hd : 0 < d)
    (hdet : b * c - a * d = 1)
    (hleft : a * s < r * b)
    (hright : r * d < c * s) :
    b + d ≤ s := by
  sorry

/-- States prop:gapwindow, thm:denom from the long record for Erdős problem #249. Transported
from GapFareyBound.gap_check_window_1_240_first_failure in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem gap_check_window_1_240_first_failure :
    IsFirstGapFailure
      1299094806818720335611738031537456208600423915562142231419225521361164904
      240 243 79639646646701375323355774875831054 := by
  sorry

/-- States prop:gapwindow from the long record for Erdős problem #249. Transported from
GapFareyBound.gap_check_window_1_240_le_79639646646701375323355774875831053 in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem gap_check_window_1_240_le_79639646646701375323355774875831053
    (q : ℕ) (hq : 0 < q) (hqQ : q ≤ 79639646646701375323355774875831053) :
    (q * 1299094806818720335611738031537456208600423915562142231419225521361164904) % 2 ^ 240 + q * 243 < 2 ^ 240 := by
  sorry

/-- States catalogue:mob:a9b from the long record for Erdős problem #249. Transported from
GcdMomentCalculus.cylinderMass_children_le in the substantive development, whose statement
was refereed against the paper in the coverage ledger. -/
theorem cylinderMass_children_le (a b : ℕ+) :
    cylinderMass (a + b) b + cylinderMass a (a + b) ≤ (2 / 3) * cylinderMass a b := by
  sorry

/-- States catalogue:mob:a2, prop:lambertengine from the long record for Erdős problem #249.
Transported from GcdMomentCalculus.tsum_lambert_linear_weight_sq_pure in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_lambert_linear_weight_sq_pure
    (w : ℕ → ℝ) (hw : ∀ d : ℕ, 0 < d → |w d| ≤ (d : ℝ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ))) ^ 2
      = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e * ((((n : ℕ) / e : ℕ) : ℝ) - 1))
          * r ^ (n : ℕ) := by
  sorry

/-- States catalogue:mob:a8 from the long record for Erdős problem #249. Transported from
GcdMomentCalculus.tsum_pos_coprime_inv_mersenne_eq_one in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem tsum_pos_coprime_inv_mersenne_eq_one :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then 1 / ((2 : ℝ) ^ (p.1 + p.2) - 1) else 0) = 1 := by
  sorry

/-- States catalogue:mob:a7, prop:gcdlayer from the long record for Erdős problem #249.
Transported from GcdMomentCalculus.tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq (d : ℕ) (hd : 0 < d) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = 1 / ((2 : ℝ) ^ d - 1) ^ 2 := by
  sorry

/-- States catalogue:mob:a5, prop:pillai from the long record for Erdős problem #249.
Transported from GcdMomentCalculus.tsum_totient_div_mersenne_sq_eq_gcd_moment_series in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem tsum_totient_div_mersenne_sq_eq_gcd_moment_series :
    ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ))
            - ((n : ℕ) : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  sorry

/-- States prop:gcdlayer from the long record for Erdős problem #249. Transported from
GeometricCoprimality.tsum_gcd_layer_pos_coprime_half_eq_one in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_gcd_layer_pos_coprime_half_eq_one :
    ∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then (((1 : ℝ) / 2) ^ (g + 1)) ^ (p.1 + p.2) else 0)
      = 1 := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsAK
