/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.GapFareyBound
import Erdos249257.GcdMomentCalculus
import Erdos249257.GeometricCoprimality
import ErdosProblems.Erdos249.PaperCompleteR21.ActualLcmShortWindowArithmetic
import ErdosProblems.Erdos249.PaperCompleteR21.CoprimeLatticeSumsAndLambert
import ErdosProblems.Erdos249.PaperCompleteR21.FareyDenominatorFloorExtension
import ErdosProblems.Erdos249.PaperCompleteR21.FareyExactRangeAndDenominatorExclusion
import ErdosProblems.Erdos249.PaperCompleteR21.GeneralIrrationalityCriteriaAndGapBounds
import ErdosProblems.Erdos249.PaperCompleteR21.MersennePrimeSupportAnchors
import ErdosProblems.Erdos249.PaperCompleteR21.MobiusMersenneLadderLogConcavity
import ErdosProblems.Erdos249.PaperCompleteR21.RationalTailPeriodWitnesses
import ErdosProblems.Erdos249.PaperCompleteR21.ShortWindowSupplyAndSixteenShifts
import ErdosProblems.Erdos249.PaperCompleteR21.ThreeParticularEquivalences
import ErdosProblems.Erdos249.PaperCompleteR21.TopEdgeCorridorAndSeparation
import ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicPulseCertificateFailure
import ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature
import Solutions.PalomarCorpus.E249_04.Statement

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsAK

noncomputable def FinitePrimeSupportEscape (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ,
    q.Prime → Q₀ ≤ q →
      ∀ p ∈ S, p.Prime → ¬ p ∣ C (m * q)

noncomputable def IsFirstGapFailure (V K H qstar : ℕ) : Prop :=
  (∀ q : ℕ, 0 < q → q < qstar → (q * V) % 2 ^ K + q * H < 2 ^ K) ∧
    ¬ ((qstar * V) % 2 ^ K + qstar * H < 2 ^ K)

noncomputable def cylinderMass (a b : ℕ+) : ℝ :=
  1 / (((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1))

theorem totientSeries_ne_rat_of_den_dvd_two_pow_fourteen_mul_mersenne
    (r : ℚ) (h : ℕ) (h1 : 1 ≤ h) (h16 : h ≤ 16)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 14 * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_ne_rat_of_den_dvd_two_pow_fourteen_mul_mersenne r h h1 h16 hdvd

theorem totientSeries_rational_den_gt_fareyBound (q : ℚ)
    (hq : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (q : ℝ)) :
    79639646646701375323355774875831053 < q.den := @ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_rational_den_gt_fareyBound q hq

theorem totient_mul_eq_totient_mul_gcd_div_totient_gcd {j x : ℕ} (hj : 0 < j)
    (hx : 0 < x) :
    (Nat.totient (j * x) : ℚ)
      = (Nat.totient j : ℚ) * (Nat.totient x : ℚ) * (Nat.gcd j x : ℚ)
          / (Nat.totient (Nat.gcd j x) : ℚ) := @ErdosProblems.Erdos249.PaperCompleteR21.totient_mul_eq_totient_mul_gcd_div_totient_gcd j x hj hx

theorem totient_one_eq_one : Nat.totient 1 = 1 := @ErdosProblems.Erdos249.PaperCompleteR21.totient_one_eq_one

theorem totient_series_ne_int_div_of_small_denominator (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hle : q ≤ 79639646646701375323355774875831053) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (a : ℝ) / (q : ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.totient_series_ne_int_div_of_small_denominator a q hq hle

theorem totient_series_ne_reduced_fraction_of_small_denominator (p : ℚ)
    (hden : p.den ≤ 79639646646701375323355774875831053) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (p : ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.totient_series_ne_reduced_fraction_of_small_denominator p hden

theorem totient_zero_eq_zero : Nat.totient 0 = 0 := @ErdosProblems.Erdos249.PaperCompleteR21.totient_zero_eq_zero

theorem tsum_pos_coprime_pairs_eq_series_sub_half :
    (∑' q : ℕ × ℕ, if 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2
        then 1 / (2 : ℝ) ^ (q.1 + q.2) else 0)
      = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 := @ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_coprime_pairs_eq_series_sub_half

theorem tsum_pos_coprime_pairs_product_form :
    (∑' q : ℕ × ℕ, if 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2
        then (1 / (2 : ℝ) ^ q.1) * (1 / (2 : ℝ) ^ q.2) else 0)
      = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 := @ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_coprime_pairs_product_form

theorem tsum_totient_pow_shift {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, (Nat.totient n : ℝ) * r ^ n)
      = ∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1) := @ErdosProblems.Erdos249.PaperCompleteR21.tsum_totient_pow_shift r hr0 hr1

theorem twoAdic_pulse_defining_congruence (H K B : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ H + K < p ∧ p.Prime ∧
      p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K] ∧ 1 + 2 ^ (K - 1) ≤ p := @ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_defining_congruence H K B hK hHK

theorem twoAdic_pulse_error_bound (H K p : ℕ) (hKp : K ≤ p)
    (hp : 2 ^ (K - 1) < p) :
    (p - K) + H + K + 2 = p + H + 2 ∧ 2 ^ (K - 1) < p + H + 2 := @ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_error_bound H K p hKp hp

theorem twoAtom_hankel_gap (r : ℕ) :
    (1 - 1 / (3 : ℝ) ^ (r + 1)) ^ 2
        - (1 - 1 / (3 : ℝ) ^ r) * (1 - 1 / (3 : ℝ) ^ (r + 2))
      = 4 / (3 : ℝ) ^ (r + 2) := @ErdosProblems.Erdos249.PaperCompleteR21.twoAtom_hankel_gap r

theorem twoAtom_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    (1 - 1 / (3 : ℝ) ^ r) * (1 - 1 / (3 : ℝ) ^ (r + 2))
      < (1 - 1 / (3 : ℝ) ^ (r + 1)) ^ 2 := @ErdosProblems.Erdos249.PaperCompleteR21.twoAtom_strict_logConcave r hr

theorem two_point_sample_numerical_requirement :
    2 * ((2 : ℝ)) ^ 2 / 5 = 8 / 5 ∧ (8 : ℝ) / 5 ≤ 2 * (9 / 10) ^ 2 := @ErdosProblems.Erdos249.PaperCompleteR21.two_point_sample_numerical_requirement

theorem two_pow_odd_eq (q : ℕ) : (2 : ℝ) ^ (2 * q + 1) = 2 * (4 : ℝ) ^ q := @ErdosProblems.Erdos249.PaperCompleteR21.two_pow_odd_eq q

theorem unbounded_prime_divisors_of_escape_of_nontrivial {C : ℕ → ℕ} {m : ℕ}
    (hnontrivial : ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q → 1 < C (m * q))
    (hescape : FinitePrimeSupportEscape C m) :
    ∀ B N₀ : ℕ, ∃ q p : ℕ,
      q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p := @ErdosProblems.Erdos249.PaperCompleteR21.unbounded_prime_divisors_of_escape_of_nontrivial C m hnontrivial hescape

theorem visible_antidiagonal_one :
    ((Finset.antidiagonal 1).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ Nat.Coprime q.1 q.2)
      = {((1 : ℕ), (0 : ℕ))} := @ErdosProblems.Erdos249.PaperCompleteR21.visible_antidiagonal_one

theorem farey_gap {a b c d r s : ℤ}
    (hb : 0 < b) (hd : 0 < d)
    (hdet : b * c - a * d = 1)
    (hleft : a * s < r * b)
    (hright : r * d < c * s) :
    b + d ≤ s := @GapFareyBound.farey_gap a b c d r s hb hd hdet hleft hright

theorem gap_check_window_1_240_first_failure :
    IsFirstGapFailure
      1299094806818720335611738031537456208600423915562142231419225521361164904
      240 243 79639646646701375323355774875831054 := @GapFareyBound.gap_check_window_1_240_first_failure

theorem gap_check_window_1_240_le_79639646646701375323355774875831053
    (q : ℕ) (hq : 0 < q) (hqQ : q ≤ 79639646646701375323355774875831053) :
    (q * 1299094806818720335611738031537456208600423915562142231419225521361164904) % 2 ^ 240 + q * 243 < 2 ^ 240 := @GapFareyBound.gap_check_window_1_240_le_79639646646701375323355774875831053 q hq hqQ

theorem cylinderMass_children_le (a b : ℕ+) :
    cylinderMass (a + b) b + cylinderMass a (a + b) ≤ (2 / 3) * cylinderMass a b := @GcdMomentCalculus.cylinderMass_children_le a b

theorem tsum_lambert_linear_weight_sq_pure
    (w : ℕ → ℝ) (hw : ∀ d : ℕ, 0 < d → |w d| ≤ (d : ℝ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ))) ^ 2
      = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e * ((((n : ℕ) / e : ℕ) : ℝ) - 1))
          * r ^ (n : ℕ) := @GcdMomentCalculus.tsum_lambert_linear_weight_sq_pure w hw r hr0 hr1

theorem tsum_pos_coprime_inv_mersenne_eq_one :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then 1 / ((2 : ℝ) ^ (p.1 + p.2) - 1) else 0) = 1 := @GcdMomentCalculus.tsum_pos_coprime_inv_mersenne_eq_one

theorem tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq (d : ℕ) (hd : 0 < d) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = 1 / ((2 : ℝ) ^ d - 1) ^ 2 := @GcdMomentCalculus.tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq d hd

theorem tsum_totient_div_mersenne_sq_eq_gcd_moment_series :
    ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ))
            - ((n : ℕ) : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ) := @GcdMomentCalculus.tsum_totient_div_mersenne_sq_eq_gcd_moment_series

theorem tsum_gcd_layer_pos_coprime_half_eq_one :
    ∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then (((1 : ℝ) / 2) ^ (g + 1)) ^ (p.1 + p.2) else 0)
      = 1 := @GeometricCoprimality.tsum_gcd_layer_pos_coprime_half_eq_one

end PalomarCorpus.E249.PaperStatementsAK
