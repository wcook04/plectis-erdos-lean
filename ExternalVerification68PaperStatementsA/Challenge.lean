/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #68

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos68.CanonicalFactorialDigits`,
`ErdosProblems.Erdos68.CompanionConstantBridge`,
`ErdosProblems.Erdos68.ConstantOnlyMissCertificates`,
`ErdosProblems.Erdos68.DivisorChannelBasis`,
`ErdosProblems.Erdos68.EndpointWeightedPrivateSupport`,
`ErdosProblems.Erdos68.FactorialChannelCertificate`,
`ErdosProblems.Erdos68.FactorialGapPlateauCore`,
`ErdosProblems.Erdos68.PaperCompleteDivisorCoordinates`,
`ErdosProblems.Erdos68.PaperCompleteExisting`,
`ErdosProblems.Erdos68.PaperCompleteMomentHorizon`,
`ErdosProblems.Erdos68.PaperCompletePrimePole`, `ErdosProblems.Erdos68.PrimeUnitTranslator`,
`ErdosProblems.Erdos68.PrimeZeroBranch`.
-/

open scoped BigOperators
open Finsupp

namespace Erdos249257.ExternalVerification68PaperStatementsA

noncomputable def factorialGapTailTerm (D d : ℕ) : ℝ :=
  if D < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)
  else 0

noncomputable def factorialGapTail (D : ℕ) : ℝ :=
  ∑' d : ℕ, factorialGapTailTerm D d

noncomputable def factorialGapSeries : ℝ :=
  factorialGapTail 1

noncomputable def adjacentDifference (n : ℕ) : ℕ →₀ ℤ :=
  single (n - 1) (n : ℤ) - single n 1

noncomputable def channelWeight (i d : ℕ) : ℕ :=
  i.factorial / (d.factorial ^ (i / d))

noncomputable def isolatedChannelUnit (n : ℕ) : ℕ →₀ ℤ :=
  n.strongRecOn' fun n rec =>
    if n ≤ 1 then 0
    else
      adjacentDifference n -
        ∑ d ∈ (Finset.Ico 2 n).attach,
          if d.1 ∣ n then
            (channelWeight n d.1 : ℤ) • rec d.1 (Finset.mem_Ico.mp d.2).2
          else 0

noncomputable def channelScalar (n : ℕ) : ℤ := isolatedChannelUnit n 1

noncomputable def IsScalarTailGcd (D G : ℕ) : Prop :=
  ∀ b : ℕ, b ∣ G ↔ ∀ n : ℕ, D < n → (b : ℤ) ∣ channelScalar n

noncomputable def channelBasisColumn (j : ℕ) : ℕ →₀ ℤ :=
  if j = 0 then single 1 1 else isolatedChannelUnit (j + 1)

noncomputable def channelSynthesis (a : ℕ →₀ ℤ) : ℕ →₀ ℤ :=
  a.sum (fun j z => z • channelBasisColumn j)

noncomputable def finiteScalarGcd (D N : ℕ) : ℕ :=
  (Finset.Icc (D + 1) N).gcd (fun n => (channelScalar n).natAbs)

noncomputable def facFloor (x : ℝ) (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℝ) * x⌋

noncomputable def canonicalRemainder (x : ℝ) (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * x - (facFloor x m : ℝ)

noncomputable def channelNumerator (lam : ℕ →₀ ℤ) (d : ℕ) : ℤ :=
  lam.sum fun i z => z * (channelWeight i d : ℤ)

noncomputable def pairwiseCollisionCore
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.lcm fun i =>
    (s.erase i).lcm fun j => Nat.gcd (d i) (d j)

noncomputable def collisionCore
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  Nat.lcm base (pairwiseCollisionCore s d)

noncomputable def compConstTerm (n : ℕ) : ℝ :=
  if 2 ≤ n then
    (1 : ℝ) /
      ((((n.factorial : ℕ) : ℝ)) *
        ((((n.factorial : ℤ) - 1 : ℤ) : ℝ)))
  else 0

noncomputable def companionConstant : ℝ :=
  ∑' n : ℕ, compConstTerm n

noncomputable def projectedResidue (T Q : ℕ) : ℕ :=
  T % Q

noncomputable def complementaryProjectedResidue (T Q : ℕ) : ℕ :=
  projectedResidue (Q - projectedResidue T Q) Q

noncomputable def endpointDenominatorLcm
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  Nat.lcm base (s.lcm d)

noncomputable def endpointTailNumerator
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.sum fun i => endpointDenominatorLcm base s d / d i

noncomputable def factorialBlockBase (p : ℕ) : ℕ :=
  (p - 1).factorial

noncomputable def factorialBlockBudget (p : ℕ) : ℕ :=
  2 * p + 1

noncomputable def factorialGapDenominator (n : ℕ) : ℕ :=
  n.factorial - 1

noncomputable def factorialBlockIndices (p : ℕ) : Finset ℕ :=
  Finset.Icc 2 (2 * p - 1)

noncomputable def factorialBlockEndpointLcm (p : ℕ) : ℕ :=
  endpointDenominatorLcm
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

noncomputable def privateQuotient
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) (i : ι) : ℕ :=
  d i / Nat.gcd (d i) (collisionCore base s d)

noncomputable def privateModulus
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.prod (privateQuotient base s d)

noncomputable def factorialBlockPrivateModulus (p : ℕ) : ℕ :=
  privateModulus
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

noncomputable def factorialBlockScale (p : ℕ) : ℕ :=
  2 * p ^ 2 * (2 * p - 1).factorial

noncomputable def factorialBlockTailNumerator (p : ℕ) : ℕ :=
  endpointTailNumerator
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

noncomputable def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)

noncomputable def strictFacTop (x : ℝ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℝ) * x⌋ + 1

noncomputable def factorialGapPredecessorGap (m : ℕ) : ℝ :=
  (strictFacTop
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℝ) -
    ((m - 1).factorial : ℝ) *
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ)

noncomputable def factorialGapPrefixLCM (n : ℕ) : ℕ :=
  (Finset.Icc 2 n).lcm fun k => k.factorial - 1

noncomputable def factorialGapScaledTail (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * factorialGapTail m

noncomputable def factorialGapStepCarry (m : ℕ) : ℤ :=
  -⌊1 + 1 / ((m.factorial : ℝ) - 1) -
      (m : ℝ) * factorialGapPredecessorGap m⌋

noncomputable def factorialMoment (lam : ℕ →₀ ℤ) : ℤ :=
  lam.sum fun i z => z * (i.factorial : ℤ)

noncomputable def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1

/-- States res:carry-characterization, res:strict-successor-complete-characterization from the
short record for Erdős problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.carry_characterisation in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem carry_characterisation :
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧ factorialGapStepCarry m ≠ 1) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) := by
  sorry

/-- States long68:res:wilson-cofinality from the long record for Erdős problem #68. Transported
from ErdosProblems.Erdos68.PaperComplete.cofinal_first_prime_occurrences in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cofinal_first_prime_occurrences :
    ∀ B : ℕ, ∃ q m : ℕ, B < m ∧ q.Prime ∧ m < q ∧
      q ∣ m.factorial - 1 ∧
      ∀ k : ℕ, 2 ≤ k → k < m → Nat.Coprime q (k.factorial - 1) := by
  sorry

/-- States long68:res:companion-orbit from the long record for Erdős problem #68. Transported
from ErdosProblems.Erdos68.PaperComplete.companion_orbit in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem companion_orbit :
    ¬ Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (facFloor companionConstant m + 2) % (m : ℤ) = 0 := by
  sorry

/-- States eq:companion-cofinal, res:companion-orbit-rationality-boundary from the short record
for Erdős problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.companion_orbit_boundary in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem companion_orbit_boundary :
    (¬ Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (facFloor companionConstant m + 2) % (m : ℤ) = 0) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        (facFloor companionConstant m + 2) % (m : ℤ) ≠ 0) := by
  sorry

/-- States eq:channel-basis-expansion, res:divisor-channel-coordinates from the short record for
Erdős problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.divisor_channel_coordinates in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
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
        (channelNumerator f d - factorialMoment f) / ((d.factorial : ℤ) - 1)) := by
  sorry

/-- States res:finite-channel-moment-certificate from the short record for Erdős problem #68.
Transported from ErdosProblems.Erdos68.PaperComplete.finite_channel_moment_certificate in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem finite_channel_moment_certificate {D p : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    let H := D * (2 * p - 1)
    0 < finiteScalarGcd D H ∧
      IsScalarTailGcd D (finiteScalarGcd D H) ∧ H < 2 * D ^ 2 := by
  sorry

/-- States res:finite-channel-moment-certificate from the short record for Erdős problem #68.
Transported from ErdosProblems.Erdos68.PaperComplete.finite_channel_moment_certificate_eq in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem finite_channel_moment_certificate_eq {D p G : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D)
    (hG : IsScalarTailGcd D G) :
    G = finiteScalarGcd D (D * (2 * p - 1)) := by
  sorry

/-- States eq:global-complementary-target, res:global-complementary-criterion from the short
record for Erdős problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.global_complementary_criterion_nat in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem global_complementary_criterion_nat
    (hcert : ∀ B : ℕ, ∃ p : ℕ,
      3 ≤ p ∧ B < p ∧ 1 < factorialBlockPrivateModulus p ∧
      factorialBlockBudget p * factorialBlockEndpointLcm p <
        factorialBlockScale p * complementaryProjectedResidue
          (factorialBlockTailNumerator p) (factorialBlockPrivateModulus p)) :
    Irrational factorialGapSeries := by
  sorry

/-- States long68:eq:global-scale, long68:res:global-residue from the long record for Erdős
problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.global_complementary_criterion_prime in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem global_complementary_criterion_prime
    (hcert : ∀ B : ℕ, ∃ p : ℕ,
      p.Prime ∧ B < p ∧ 1 < factorialBlockPrivateModulus p ∧
      factorialBlockBudget p * factorialBlockEndpointLcm p <
        factorialBlockScale p * complementaryProjectedResidue
          (factorialBlockTailNumerator p) (factorialBlockPrivateModulus p)) :
    Irrational factorialGapSeries := by
  sorry

/-- States long68:eq:finite-escape, long68:eq:lower-escape, long68:res:lower-escape from the
long record for Erdős problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.lower_interval_criterion in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
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
      Irrational factorialGapSeries) := by
  sorry

/-- States long68:eq:prime-pole-survival, long68:res:prime-pole from the long record for Erdős
problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.maximal_prime_power_survival in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem maximal_prime_power_survival {M p : ℕ} (_hM : 2 ≤ M)
    (hp : p.Prime) (hpL : p ∣ factorialGapPrefixLCM M) :
    (factorialGapPrefix M).den.factorization p =
        (factorialGapPrefixLCM M).factorization p ↔
      (∑ n ∈ (Finset.Icc 2 M).filter
          (fun n => (n.factorial - 1).factorization p =
            (factorialGapPrefixLCM M).factorization p),
        (((n.factorial - 1) /
          p ^ (factorialGapPrefixLCM M).factorization p : ℕ) : ZMod p)⁻¹) ≠ 0 := by
  sorry

end Erdos249257.ExternalVerification68PaperStatementsA
