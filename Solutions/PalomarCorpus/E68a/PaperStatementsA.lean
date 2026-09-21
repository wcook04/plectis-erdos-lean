/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.CanonicalFactorialDigits
import ErdosProblems.Erdos68.CompanionConstantBridge
import ErdosProblems.Erdos68.ConstantOnlyMissCertificates
import ErdosProblems.Erdos68.DivisorChannelBasis
import ErdosProblems.Erdos68.EndpointWeightedPrivateSupport
import ErdosProblems.Erdos68.FactorialChannelCertificate
import ErdosProblems.Erdos68.FactorialGapPlateauCore
import ErdosProblems.Erdos68.PaperCompleteDivisorCoordinates
import ErdosProblems.Erdos68.PaperCompleteExisting
import ErdosProblems.Erdos68.PaperCompleteMomentHorizon
import ErdosProblems.Erdos68.PaperCompletePrimePole
import ErdosProblems.Erdos68.PrimeUnitTranslator
import ErdosProblems.Erdos68.PrimeZeroBranch
import Solutions.PalomarCorpus.E68a.Statement

open scoped BigOperators
open Finsupp

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E68.PaperStatementsA

theorem carry_characterisation :
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧ factorialGapStepCarry m ≠ 1) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) := @ErdosProblems.Erdos68.PaperComplete.carry_characterisation

theorem cofinal_first_prime_occurrences :
    ∀ B : ℕ, ∃ q m : ℕ, B < m ∧ q.Prime ∧ m < q ∧
      q ∣ m.factorial - 1 ∧
      ∀ k : ℕ, 2 ≤ k → k < m → Nat.Coprime q (k.factorial - 1) := @ErdosProblems.Erdos68.PaperComplete.cofinal_first_prime_occurrences

theorem companion_orbit :
    ¬ Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (facFloor companionConstant m + 2) % (m : ℤ) = 0 := @ErdosProblems.Erdos68.PaperComplete.companion_orbit

theorem companion_orbit_boundary :
    (¬ Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (facFloor companionConstant m + 2) % (m : ℤ) = 0) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        (facFloor companionConstant m + 2) % (m : ℤ) ≠ 0) := @ErdosProblems.Erdos68.PaperComplete.companion_orbit_boundary

theorem divisor_channel_coordinates :
    (∀ n : ℕ, 2 ≤ n → factorialMoment (isolatedChannelUnit n) = 0) ∧
    (∀ n d : ℕ, 2 ≤ n → 2 ≤ d →
      channelNumerator (isolatedChannelUnit n) d =
        if d = n then (n.factorial : ℤ) - 1 else 0) ∧
    (∀ f : ℕ →₀ ℤ, f 0 = 0 →
      ∃! a : ℕ →₀ ℤ, channelSynthesis a = f) ∧
    (∀ a f : ℕ →₀ ℤ, channelSynthesis a = f →
      a 0 = factorialMoment f ∧
      ∀ d : ℕ, 2 ≤ d → a (d - 1) =
        (channelNumerator f d - factorialMoment f) / ((d.factorial : ℤ) - 1)) := @ErdosProblems.Erdos68.PaperComplete.divisor_channel_coordinates

theorem finite_channel_moment_certificate {D p : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    let H := D * (2 * p - 1)
    0 < finiteScalarGcd D H ∧
      IsScalarTailGcd D (finiteScalarGcd D H) ∧ H < 2 * D ^ 2 := @ErdosProblems.Erdos68.PaperComplete.finite_channel_moment_certificate D p hD hp hDp hpD

theorem finite_channel_moment_certificate_eq {D p G : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D)
    (hG : IsScalarTailGcd D G) :
    G = finiteScalarGcd D (D * (2 * p - 1)) := @ErdosProblems.Erdos68.PaperComplete.finite_channel_moment_certificate_eq D p G hD hp hDp hpD hG

theorem global_complementary_criterion_nat
    (hcert : ∀ B : ℕ, ∃ p : ℕ,
      3 ≤ p ∧ B < p ∧ 1 < factorialBlockPrivateModulus p ∧
      factorialBlockBudget p * factorialBlockEndpointLcm p <
        factorialBlockScale p * complementaryProjectedResidue
          (factorialBlockTailNumerator p) (factorialBlockPrivateModulus p)) :
    Irrational factorialGapSeries := @ErdosProblems.Erdos68.PaperComplete.global_complementary_criterion_nat hcert

theorem global_complementary_criterion_prime
    (hcert : ∀ B : ℕ, ∃ p : ℕ,
      p.Prime ∧ B < p ∧ 1 < factorialBlockPrivateModulus p ∧
      factorialBlockBudget p * factorialBlockEndpointLcm p <
        factorialBlockScale p * complementaryProjectedResidue
          (factorialBlockTailNumerator p) (factorialBlockPrivateModulus p)) :
    Irrational factorialGapSeries := @ErdosProblems.Erdos68.PaperComplete.global_complementary_criterion_prime hcert

theorem lower_interval_criterion :
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        factorialGapScaledTail m ≤
          (m : ℝ) * canonicalRemainder factorialGapSeries (m - 1)) ∧
    (∀ m : ℕ, 3 ≤ m →
      ((m : ℝ) * factorialGapPredecessorGap m ≤ 1 + 1 / ((m.factorial : ℝ) - 1) ∨
        1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
          (m : ℝ) * factorialGapPredecessorGap m) →
      factorialGapScaledTail m ≤
        (m : ℝ) * canonicalRemainder factorialGapSeries (m - 1)) ∧
    ((∀ B : ℕ, ∃ m : ℕ, 3 ≤ m ∧ B < m ∧
      ((m : ℝ) * factorialGapPredecessorGap m ≤ 1 + 1 / ((m.factorial : ℝ) - 1) ∨
        1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
          (m : ℝ) * factorialGapPredecessorGap m)) →
      Irrational factorialGapSeries) := @ErdosProblems.Erdos68.PaperComplete.lower_interval_criterion

theorem maximal_prime_power_survival {M p : ℕ} (_hM : 2 ≤ M)
    (hp : p.Prime) (hpL : p ∣ factorialGapPrefixLCM M) :
    (factorialGapPrefix M).den.factorization p =
        (factorialGapPrefixLCM M).factorization p ↔
      (∑ n ∈ (Finset.Icc 2 M).filter
          (fun n => (n.factorial - 1).factorization p =
            (factorialGapPrefixLCM M).factorization p),
        (((n.factorial - 1) /
          p ^ (factorialGapPrefixLCM M).factorization p : ℕ) : ZMod p)⁻¹) ≠ 0 := @ErdosProblems.Erdos68.PaperComplete.maximal_prime_power_survival M p _hM hp hpL

end PalomarCorpus.E68.PaperStatementsA
