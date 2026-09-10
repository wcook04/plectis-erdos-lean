/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

/-!
# Palomar challenge for Erdős problem #68

Independent Comparator restatement of the paper-linked Lean that actually has
Comparator-grade proof coverage for this problem. Parent problem remains open.
Narrative lives in `PalomarCorpus/README.md`.
-/

namespace PalomarCorpus.E68.Shared
noncomputable def adjacentDifference (n : ℕ) : ℕ →₀ ℤ := single (n - 1) (n : ℤ) - single n 1

noncomputable def channelLCM (D : ℕ) : ℕ := (Finset.Icc 2 D).lcm (fun d => d.factorial - 1) /-- Sharp explicit cubic radius bound on the square subsequence. -/

noncomputable def channelWeight (i d : ℕ) : ℕ := i.factorial / (d.factorial ^ (i / d))

noncomputable def channelNumerator (lam : ℕ →₀ ℤ) (d : ℕ) : ℤ := lam.sum fun i z => z * (channelWeight i d : ℤ)

noncomputable def companionConstant : ℝ := ∑' n : ℕ, if 2 ≤ n then (1 : ℝ) / ((n.factorial : ℝ) * ((((n.factorial : ℤ) - 1 : ℤ) : ℝ))) else 0 /-- The anchored unit-factorial term `1/n!`, supported on `n ≥ 2`. -/

noncomputable def facFloor (x : ℝ) (m : ℕ) : ℤ := ⌊(m.factorial : ℝ) * x⌋ /-- The canonical mixed-radix factorial digit at radix `m`. -/

noncomputable def factorialGapPrefix (n : ℕ) : ℚ := ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)

noncomputable def factorialGapSeries : ℝ := ∑' n : ℕ, if 1 < n then (1 : ℝ) / (((n.factorial : ℤ) - 1 : ℤ) : ℝ) else 0

noncomputable def factorialMoment (lam : ℕ →₀ ℤ) : ℤ := lam.sum fun i z => z * (i.factorial : ℤ)

noncomputable def isolatedChannelUnit (n : ℕ) : ℕ →₀ ℤ := n.strongRecOn' fun n rec => if n ≤ 1 then 0 else adjacentDifference n - ∑ d ∈ (Finset.Ico 2 n).attach, if d.1 ∣ n then (channelWeight n d.1 : ℤ) • rec d.1 (Finset.mem_Ico.mp d.2).2 else 0

noncomputable def channelBasisColumn (j : ℕ) : ℕ →₀ ℤ := if j = 0 then single 1 1 else isolatedChannelUnit (j + 1)

noncomputable def channelSynthesis (a : ℕ →₀ ℤ) : ℕ →₀ ℤ := a.sum (fun j z => z • channelBasisColumn j)

noncomputable def kernelCoordinates (D : ℕ) : ℕ →₀ ℤ := single 0 (channelLCM D : ℤ) - ∑ d ∈ Finset.Icc 2 D, single (d - 1) ((channelLCM D : ℤ) / ((d.factorial : ℤ) - 1))

noncomputable def canonicalKernel (D : ℕ) : ℕ →₀ ℤ := channelSynthesis (kernelCoordinates D)

noncomputable def strictFacTop (x : ℝ) (n : ℕ) : ℤ := ⌊(n.factorial : ℝ) * x⌋ + 1 /-- Exact rational implementation of the same strict successor. -/

noncomputable def factorialGapPredecessorGap (m : ℕ) : ℝ := (strictFacTop ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℝ) - ((m - 1).factorial : ℝ) * ((factorialGapPrefix (m - 1) : ℚ) : ℝ) /-- Exact integer carry in the strict-successor recurrence. -/

noncomputable def factorialGapStepCarry (m : ℕ) : ℤ := -⌊1 + 1 / ((m.factorial : ℝ) - 1) - (m : ℝ) * factorialGapPredecessorGap m⌋ /-- The strict-successor carry boundary for the Erdős #68 series. The four conjuncts record respectively the rationality criterion in terms of eventual unit carries, its cofinal dual for irrationality, the pointwise carry and divisibility equivalence at every index `m ≥ 3`, and the resulting purely integral cofinal reformulation over the exact rational prefixes. -/

noncomputable def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ := ⌊(n.factorial : ℚ) * x⌋ + 1

end PalomarCorpus.E68.Shared

namespace PalomarCorpus.E68.AdjacentUnitCarryWindow
export PalomarCorpus.E68.Shared (factorialGapPrefix strictFacTopRat)
def predecessorScaled (m : ℕ) : ℚ :=
  ((m - 1).factorial : ℚ) * factorialGapPrefix (m - 1)

def predecessorNumerator (m : ℕ) : ℤ :=
  let q := predecessorScaled m; (⌊q⌋ + 1) * q.den - q.num

def transitionNormalizer (m : ℕ) : ℕ :=
  (predecessorScaled m).den * (m.factorial - 1) / (predecessorScaled (m + 1)).den

noncomputable def predecessorGap (m : ℕ) : ℝ :=
  (strictFacTopRat (factorialGapPrefix (m - 1)) (m - 1) : ℝ) -
    ((m - 1).factorial : ℝ) * (factorialGapPrefix (m - 1) : ℝ)

noncomputable def stepCarry (m : ℕ) : ℤ :=
  -⌊1 + 1 / ((m.factorial : ℝ) - 1) - (m : ℝ) * predecessorGap m⌋

def windowDen (m : ℕ) : ℤ :=
  ((predecessorScaled m).den : ℤ) * ((m.factorial : ℤ) - 1) *
    (((m + 1).factorial : ℤ) - 1)

def windowLower (m : ℕ) : ℤ :=
  (m + 2 : ℤ) * windowDen m + (m + 1 : ℤ) *
    ((predecessorScaled m).den : ℤ) * (((m + 1).factorial : ℤ) - 1) +
    ((predecessorScaled m).den : ℤ) * ((m.factorial : ℤ) - 1)

def windowState (m : ℕ) : ℤ :=
  (m : ℤ) * (m + 1 : ℤ) * predecessorNumerator m *
    ((m.factorial : ℤ) - 1) * (((m + 1).factorial : ℤ) - 1)

def windowOffset (m : ℕ) : ℤ := windowState m - windowLower m

theorem consecutive_unit_carries_iff_positive_offset_le_den {m : ℕ} (hm : 3 ≤ m) :
    (stepCarry m = 1 ∧ stepCarry (m + 1) = 1) ↔
      0 < windowOffset m ∧ windowOffset m ≤ windowDen m := by
  sorry

theorem twoStep_den_mul_transitionNormalizers {m : ℕ} (hm : 3 ≤ m) :
    (predecessorScaled (m + 2)).den * transitionNormalizer (m + 1) *
      transitionNormalizer m = (predecessorScaled m).den *
        (m.factorial - 1) * ((m + 1).factorial - 1) := by
  sorry

theorem adjacentUnitCarryWindowDen_eq_twoStep_den {m : ℕ} (hm : 3 ≤ m) :
    windowDen m = ((predecessorScaled (m + 2)).den : ℤ) *
      transitionNormalizer (m + 1) * transitionNormalizer m := by
  sorry

theorem adjacentUnitCarryWindowOffset_eq_twoStep_factorization {m : ℕ} (hm : 3 ≤ m) :
    windowOffset m = predecessorNumerator (m + 2) * transitionNormalizer (m + 1) *
      transitionNormalizer m + windowDen m *
        (((m + 1 : ℕ) : ℤ) * stepCarry m + stepCarry (m + 1) - (m + 2 : ℤ)) := by
  sorry

end PalomarCorpus.E68.AdjacentUnitCarryWindow

namespace PalomarCorpus.E68.ChannelRadius
export PalomarCorpus.E68.Shared (channelLCM)
theorem square_subsequence_radius_three_halves_lower
    {t M R : ℕ} (ht : 2 ^ 32 ≤ t)
    (hMpos : 0 < M)
    (hdiv : channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    3 * t ^ 3 < 2 * (R + 1) := by
  sorry

theorem no_eventual_square_subsequence_three_halves_upper
    (M R : ℕ → ℕ)
    (hMpos : ∀ t, 2 ^ 32 ≤ t → 0 < M t)
    (hdiv : ∀ t, 2 ^ 32 ≤ t → channelLCM (2 * t ^ 2) ∣ M t)
    (hsmall : ∀ t, 2 ^ 32 ≤ t →
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T, ∀ t, T ≤ t → 2 * (R t + 1) ≤ 3 * t ^ 3 := by
  sorry

theorem not_isLittleO_square_subsequence_radius
    (M R : ℕ → ℕ)
    (hMpos : ∀ t, 4096 ≤ t → 0 < M t)
    (hdiv : ∀ t, 4096 ≤ t → channelLCM (2 * t ^ 2) ∣ M t)
    (hsmall : ∀ t, 4096 ≤ t →
      M t < (R t + 1).factorial - 1) :
    ¬ (fun t : ℕ => ((R t + 1 : ℕ) : ℝ)) =o[Filter.atTop]
        (fun t : ℕ => (t : ℝ) ^ 3) := by
  sorry

theorem square_subsequence_radius_cubic_lower
    {t M R : ℕ} (ht : 4096 ≤ t)
    (hMpos : 0 < M)
    (hdiv : channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    t ^ 3 < 8 * (R + 1) := by
  sorry

theorem no_eventual_square_subsequence_cubic_upper
    (M R : ℕ → ℕ)
    (hMpos : ∀ t, 4096 ≤ t → 0 < M t)
    (hdiv : ∀ t, 4096 ≤ t → channelLCM (2 * t ^ 2) ∣ M t)
    (hsmall : ∀ t, 4096 ≤ t →
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T, ∀ t, T ≤ t → 8 * (R t + 1) ≤ t ^ 3 := by
  sorry

theorem sharp_radius_satisfies_square_log_constraint
    {t R : ℕ} (ht : 4 ≤ t) (hsharp : 9 * (R + 1) = 16 * t ^ 3) :
    (2 * t : ℝ) *
          (((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) *
              Real.log ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) -
            (2 * t ^ 2 + 1 - 2 * t : ℕ) - Real.log 2) <
        ((R + 1 : ℕ) : ℝ) * Real.log (R + 1 : ℝ) +
          (((2 * t + 1).choose 3 : ℕ) : ℝ) *
            Real.log ((2 * t ^ 2 : ℕ) : ℝ) := by
  sorry

end PalomarCorpus.E68.ChannelRadius

namespace PalomarCorpus.E68.CompanionOrbitBoundary
export PalomarCorpus.E68.Shared (companionConstant facFloor factorialGapPredecessorGap factorialGapPrefix factorialGapStepCarry strictFacTop strictFacTopRat)
noncomputable def factorialGapSeries : ℝ :=
  ∑' d : ℕ, if 1 < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))
  else 0
/-- The fixed companion constant `C = ∑_{n≥2} 1/(n!(n! - 1))`. -/

noncomputable def unitFactTerm (n : ℕ) : ℝ :=
  if 2 ≤ n then (1 : ℝ) / ((n.factorial : ℝ)) else 0
/-- Floor of the factorially scaled real number. -/

noncomputable def canonicalDigit (x : ℝ) (m : ℕ) : ℤ :=
  facFloor x m - (m : ℤ) * facFloor x (m - 1)
/-- The exact rational prefix through index `n`. -/

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
  sorry

theorem companionOrbitBoundary_genericShift (x : ℝ) :
    (¬Irrational (x + ∑' n : ℕ, unitFactTerm n) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → canonicalDigit x m = (m : ℤ) - 2) ∧
    (¬Irrational (x + ∑' n : ℕ, unitFactTerm n) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((facFloor x m + 2 : ℤ) % (m : ℤ)) = 0) := by
  sorry

theorem companionOrbitBoundary_factorialGapSeries :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) = 0) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) ≠ 0) := by
  sorry

theorem tsum_unitFactTerm_eq_exp_one_sub_two :
    (∑' n : ℕ, unitFactTerm n) = Real.exp 1 - 2 := by
  sorry

end PalomarCorpus.E68.CompanionOrbitBoundary

namespace PalomarCorpus.E68.FiniteDenominator
export PalomarCorpus.E68.Shared (factorialGapSeries)
theorem finite_denominator_exclusion (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hS : factorialGapSeries = (a : ℝ) / q) :
    (2 : ℕ) ^ 39990 ≤ q ∧ (10 : ℕ) ^ 12040 < q := by
  sorry

end PalomarCorpus.E68.FiniteDenominator

namespace PalomarCorpus.E68.KempnerIndex
open scoped BigOperators
export PalomarCorpus.E68.Shared (factorialGapPredecessorGap factorialGapPrefix factorialGapSeries factorialGapStepCarry strictFacTop)
theorem rational_denominator_not_dvd_pred_factorial_of_nonunit_carry
    {m q : ℕ} {a : ℤ}
    (hm : 3 ≤ m)
    (hmiss : factorialGapStepCarry m ≠ 1)
    (hq : 0 < q)
    (hseries :
      factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    ¬ (q ∣ (m - 1).factorial) := by
  sorry

theorem rational_denominator_not_dvd_fiftynine_factorial
    {q : ℕ} {a : ℤ}
    (hq : 0 < q)
    (hseries :
      factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    ¬ (q ∣ Nat.factorial 59) := by
  sorry

end PalomarCorpus.E68.KempnerIndex

namespace PalomarCorpus.E68.MomentIdeal
open scoped BigOperators
export PalomarCorpus.E68.Shared (adjacentDifference canonicalKernel channelBasisColumn channelLCM channelNumerator channelSynthesis channelWeight factorialMoment isolatedChannelUnit kernelCoordinates)
noncomputable def channelScalar (n : ℕ) : ℤ := isolatedChannelUnit n 1

noncomputable def finiteScalarGcd (D N : ℕ) : ℕ :=
  (Finset.Icc (D + 1) N).gcd (fun n => (channelScalar n).natAbs)

noncomputable def kernelOne (D : ℕ) : ℤ := canonicalKernel D 1

def Admissible (f : ℕ →₀ ℤ) : Prop :=
  ∀ n ∈ f.support, 2 ≤ n

def LowChannels (D : ℕ) (f : ℕ →₀ ℤ) : Prop :=
  ∀ d ∈ Finset.Icc 2 D, channelNumerator f d = 0

def AttainsMoment (D : ℕ) (m : ℤ) : Prop :=
  ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧ factorialMoment f = m

noncomputable def minimumMoment (D p : ℕ) : ℤ :=
  let G : ℤ := finiteScalarGcd D (D * (2 * p - 1))
  (channelLCM D : ℤ) * (G / (Int.gcd G (kernelOne D) : ℤ))

def PrimitiveVector (f : ℕ →₀ ℤ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ¬ ∃ g : ℕ →₀ ℤ, f = (k : ℤ) • g

noncomputable def coefficientContent (f : ℕ →₀ ℤ) : ℕ :=
  f.support.gcd (fun n => (f n).natAbs)

theorem attainable_moment_ideal {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) (m : ℤ) :
    AttainsMoment D m ↔ minimumMoment D p ∣ m := by
  sorry

theorem exact_moment_ideal_with_primitive_attainment {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    0 < minimumMoment D p ∧
    (∀ m : ℤ, AttainsMoment D m ↔ minimumMoment D p ∣ m) ∧
    ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧
      factorialMoment f = minimumMoment D p ∧ PrimitiveVector f := by
  sorry

theorem minimum_moment_content_one {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧
      factorialMoment f = minimumMoment D p ∧ coefficientContent f = 1 := by
  sorry

theorem minimumMoment_independent_prime {D p q : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D)
    (hq : q.Prime) (hDq : D / 2 < q) (hqD : q ≤ D) :
    minimumMoment D p = minimumMoment D q := by
  sorry

end PalomarCorpus.E68.MomentIdeal

namespace PalomarCorpus.E68.MovingFactorScaleSplit
open scoped BigOperators
noncomputable def factorialGapSeries : ℝ :=
  ∑' d : ℕ, if 1 < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))
  else 0
/-- The canonical large prefix-private primes of `m! - 1`. -/

def factorialGapLargePrefixPrivatePrimes (m : ℕ) : Finset ℕ :=
  (m.factorial - 1).primeFactors.filter fun q =>
    m + 1 < q ∧
      ∀ k ∈ Finset.Ico 2 m,
        Nat.Coprime q (k.factorial - 1)

def factorialBlockIndices (p : ℕ) : Finset ℕ :=
  Finset.Icc 2 (2 * p - 1)

def factorialGapDenominator (n : ℕ) : ℕ :=
  n.factorial - 1

def factorialBlockBase (p : ℕ) : ℕ :=
  (p - 1).factorial

def pairwiseCollisionCore
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.lcm fun i =>
    (s.erase i).lcm fun j => Nat.gcd (d i) (d j)

def collisionCore
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  Nat.lcm base (pairwiseCollisionCore s d)

def endpointDenominatorLcm
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  Nat.lcm base (s.lcm d)

def endpointTailNumerator
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.sum fun i => endpointDenominatorLcm base s d / d i

def privateQuotient
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) (i : ι) : ℕ :=
  d i / Nat.gcd (d i) (collisionCore base s d)

def privateModulus
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.prod (privateQuotient base s d)

def projectedResidue (T Q : ℕ) : ℕ :=
  T % Q

def complementaryProjectedResidue (T Q : ℕ) : ℕ :=
  projectedResidue (Q - projectedResidue T Q) Q

def leaveOneOutModulus (R r : ℕ) : ℕ :=
  R / r

def factorialBlockEndpointLcm (p : ℕ) : ℕ :=
  endpointDenominatorLcm
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

def factorialBlockCollisionCore (p : ℕ) : ℕ :=
  collisionCore
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

def factorialBlockNormalizedCollisionCore (p : ℕ) : ℕ :=
  factorialBlockCollisionCore p / factorialBlockBase p

def factorialBlockUpperDescFactorial (p : ℕ) : ℕ :=
  (2 * p - 1).descFactorial p

def factorialBlockPrivateModulus (p : ℕ) : ℕ :=
  privateModulus
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

def factorialBlockTailNumerator (p : ℕ) : ℕ :=
  endpointTailNumerator
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

def factorialBlockPrivateQuotient (p n : ℕ) : ℕ :=
  privateQuotient
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator n

def factorialBlockFactorProjectionModulus (p a : ℕ) : ℕ :=
  leaveOneOutModulus (factorialBlockPrivateModulus p) a

def factorialBlockScale (p : ℕ) : ℕ :=
  2 * p ^ 2 * (2 * p - 1).factorial

def factorialBlockBudget (p : ℕ) : ℕ :=
  2 * p + 1
/-- One moving prefix-private prime, together with the exact global and local
scale bounds, is enough to prove irrationality. -/

theorem movingPrivateFactorScaleSplit_implies_irrational
    (hcert :
      ∀ B : ℕ, ∃ m q : ℕ,
        4 ≤ m ∧
        B < m / 2 + 1 ∧
        q ∈ factorialGapLargePrefixPrivatePrimes m ∧
        factorialBlockBudget (m / 2 + 1) *
              factorialBlockEndpointLcm (m / 2 + 1) <
          factorialBlockScale (m / 2 + 1) *
            complementaryProjectedResidue
              (factorialBlockTailNumerator (m / 2 + 1))
              (factorialBlockPrivateModulus (m / 2 + 1)) ∧
        factorialBlockBudget (m / 2 + 1) *
              factorialBlockCollisionCore (m / 2 + 1) * q <
          factorialBlockScale (m / 2 + 1)) :
    Irrational factorialGapSeries := by
  sorry

theorem splitFactorNormalizedCollision_implies_irrational
    (hcert :
      ∀ B : ℕ, ∃ p a b : ℕ,
        p.Prime ∧
        B < p ∧
        a ∣ factorialBlockPrivateModulus p ∧
        b ∣ factorialBlockPrivateModulus p ∧
        1 < factorialBlockPrivateModulus p ∧
        complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockFactorProjectionModulus p a) ≠
          complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockFactorProjectionModulus p b) ∧
        factorialBlockBudget p *
              factorialBlockNormalizedCollisionCore p * max a b <
          2 * p ^ 2 * factorialBlockUpperDescFactorial p) :
    Irrational factorialGapSeries := by
  sorry

theorem fixedOwnerPair_eventually_absorbed
    {p i j : ℕ}
    (hi : 2 ≤ i)
    (hj : 2 ≤ j)
    (hlt :
      max (factorialGapDenominator i)
          (factorialGapDenominator j) < p) :
    factorialBlockPrivateQuotient p i = 1 ∧
      factorialBlockPrivateQuotient p j = 1 := by
  sorry

end PalomarCorpus.E68.MovingFactorScaleSplit

namespace PalomarCorpus.E68.MultiplicativeSuccessorRigidity
open scoped BigOperators
export PalomarCorpus.E68.Shared (factorialGapPrefix factorialGapSeries strictFacTopRat)
def gapSuccessor (m : ℕ) : ℤ :=
  strictFacTopRat (factorialGapPrefix m) m

theorem gapSuccessor_eq_mul_pred_of_dvd
    {m : ℕ} (hm : 3 ≤ m) (h : (m : ℤ) ∣ gapSuccessor m) :
    gapSuccessor m = (m : ℤ) * gapSuccessor (m - 1) := by
  sorry

theorem gapSuccessor_dvd_of_eventually_dvd
    {M : ℕ} (hM : 3 ≤ M)
    (h : ∀ k, M ≤ k → (k : ℤ) ∣ gapSuccessor k)
    {j : ℕ} (hj : M ≤ j + 1) :
    ∀ m, j ≤ m → gapSuccessor j ∣ gapSuccessor m := by
  sorry

theorem factorial_mul_gapSuccessor_eq_of_eventually_dvd
    {M : ℕ} (hM : 3 ≤ M)
    (h : ∀ k, M ≤ k → (k : ℤ) ∣ gapSuccessor k)
    {j : ℕ} (hj : M ≤ j + 1) :
    ∀ m, j ≤ m →
      (j.factorial : ℤ) * gapSuccessor m = (m.factorial : ℤ) * gapSuccessor j := by
  sorry

theorem eventually_dvd_gapSuccessor_of_not_irrational
    {d : ℕ} (hd : 0 < d)
    (hrat : ¬ Irrational factorialGapSeries) :
    ∃ B : ℕ, ∀ m : ℕ, B < m → (d : ℤ) ∣ gapSuccessor m := by
  sorry

theorem irrational_factorialGapSeries_of_cofinal_not_dvd_gapSuccessor
    {d : ℕ} (hd : 0 < d)
    (h : ∀ B : ℕ, ∃ m : ℕ, B < m ∧ ¬ (d : ℤ) ∣ gapSuccessor m) :
    Irrational factorialGapSeries := by
  sorry

theorem irrational_factorialGapSeries_of_cofinal_odd_gapSuccessor
    (h : ∀ B : ℕ, ∃ m : ℕ, B < m ∧ ¬ (2 : ℤ) ∣ gapSuccessor m) :
    Irrational factorialGapSeries := by
  sorry

theorem not_eventually_odd_gapSuccessor_of_not_irrational
    (hrat : ¬ Irrational factorialGapSeries) :
    ∃ B : ℕ, ∀ m : ℕ, B < m → (2 : ℤ) ∣ gapSuccessor m := by
  sorry

end PalomarCorpus.E68.MultiplicativeSuccessorRigidity

namespace PalomarCorpus.E68.PrimePole
open scoped BigOperators
def factorialGapPrefixLCM (M : ℕ) : ℕ :=
  (Finset.Icc 2 M).lcm fun n => n.factorial - 1
/-- The numerator obtained by writing the finite reciprocal sum over the
literal prefix LCM. -/

def factorialGapPrefixLCMNumerator (M : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 2 M,
    factorialGapPrefixLCM M / (n.factorial - 1)
/-- The indices whose factorial gaps have exact `q`-adic exponent `e`. -/

def factorialGapMaxHits (q M e : ℕ) : Finset ℕ :=
  (Finset.Icc 2 M).filter fun n =>
    q ^ e ∣ n.factorial - 1 ∧
      ¬q ^ (e + 1) ∣ n.factorial - 1
/-- The reciprocal sum, modulo `q`, of the maximal-hit cofactors. -/

def factorialGapPrincipalResidue (q M e : ℕ) : ZMod q :=
  ∑ n ∈ factorialGapMaxHits q M e,
    (((n.factorial - 1) / q ^ e : ℕ) : ZMod q)⁻¹
/-- The finite prime-pole numerator formula at a positive maximal `q`-adic
exponent. -/

theorem factorialGapPrefixLCMNumerator_mod_prime
    {q M e : ℕ}
    (hq : q.Prime)
    (he : 1 ≤ e)
    (hmax :
      ∀ n ∈ Finset.Icc 2 M,
        ¬q ^ (e + 1) ∣ n.factorial - 1)
    (hattain :
      ∃ n ∈ Finset.Icc 2 M,
        q ^ e ∣ n.factorial - 1) :
    (factorialGapPrefixLCMNumerator M : ZMod q) =
      ((factorialGapPrefixLCM M / q ^ e : ℕ) : ZMod q) *
        factorialGapPrincipalResidue q M e := by
  sorry

end PalomarCorpus.E68.PrimePole

namespace PalomarCorpus.E68.PrimeUnitTranslator
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
  sorry

theorem primeTranslator_channel_zero_of_lt_p
    {p d : ℕ} (hp : p.Prime) (hd2 : 2 ≤ d) (hdp : d < p) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by
  sorry

theorem primeTranslator_channel_at_prime
    {p : ℕ} (hp : p.Prime) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) p =
      (p.factorial : ℤ) - 1 := by
  sorry

theorem primeTranslator_channel_zero_of_p_lt
    {p d : ℕ} (hp : 0 < p) (hpd : p < d) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by
  sorry

theorem primeTranslator_channelResidual_eq_one
    {D p : ℕ} (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (primeTranslatorCoeff p) (primeTranslatorIndex p) = 1 := by
  sorry

theorem channelResidual_appendPrimeTranslator
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) {D p : ℕ} (z : ℤ)
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (appendPrimeTranslatorCoeff coeff p z)
        (appendPrimeTranslatorIndex index p) =
      channelResidual D coeff index + (z : ℝ) := by
  sorry

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
  sorry

end PalomarCorpus.E68.PrimeUnitTranslator

namespace PalomarCorpus.E68.ResidualIntegerClass
open scoped BigOperators
export PalomarCorpus.E68.Shared (adjacentDifference canonicalKernel channelBasisColumn channelLCM channelNumerator channelSynthesis channelWeight factorialGapSeries factorialMoment isolatedChannelUnit kernelCoordinates)
def TailCoordinates (D : ℕ) (z : ℕ →₀ ℤ) : Prop :=
  ∀ j, j < D → z j = 0

noncomputable def integerEvaluation (w : ℕ → ℤ) (z : ℕ →₀ ℤ) : ℤ :=
  z.sum (fun i c => c * w i)

noncomputable def coordinateMass (z : ℕ →₀ ℤ) : ℤ :=
  integerEvaluation (fun _ => 1) z

noncomputable def fullResidualTerm (f : ℕ →₀ ℤ) (d : ℕ) : ℝ :=
  if 1 < d then (channelNumerator f d : ℝ) /
    ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ) else 0

noncomputable def fullResidual (f : ℕ →₀ ℤ) : ℝ :=
  ∑' d : ℕ, fullResidualTerm f d

noncomputable def gapPrefixReal (D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 D, (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)

theorem residual_transparency {D : ℕ} (hD : 2 ≤ D) (t : ℤ)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    fullResidual (t • canonicalKernel D + channelSynthesis z) =
      (t : ℝ) * (channelLCM D : ℝ) *
        (factorialGapSeries - gapPrefixReal D) +
      (coordinateMass z : ℝ) := by
  sorry

theorem summable_fullResidual {f : ℕ →₀ ℤ} (h0 : f 0 = 0) :
    Summable (fullResidualTerm f) := by
  sorry

theorem zero_moment_residual_integral {f : ℕ →₀ ℤ}
    (h0 : f 0 = 0) (hm : factorialMoment f = 0) :
    ∃ k : ℤ, fullResidual f = (k : ℝ) := by
  sorry

theorem equal_moment_residual_integer_difference {f g : ℕ →₀ ℤ}
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hm : factorialMoment f = factorialMoment g) :
    ∃ k : ℤ, fullResidual f - fullResidual g = (k : ℝ) := by
  sorry

end PalomarCorpus.E68.ResidualIntegerClass

namespace PalomarCorpus.E68.StrictSuccessorCarry
export PalomarCorpus.E68.Shared (companionConstant facFloor factorialGapPredecessorGap factorialGapPrefix factorialGapStepCarry strictFacTop strictFacTopRat)
noncomputable def factorialGapSeries : ℝ :=
  ∑' d : ℕ, if 1 < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))
  else 0
/-- The fixed companion constant
`C = ∑_{n≥2} 1/(n!(n!-1))`. -/

theorem companionOrbit_completeCharacterization :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) = 0) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) ≠ 0) := by
  sorry

theorem strictSuccessorCarry_completeCharacterization :
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
  sorry

end PalomarCorpus.E68.StrictSuccessorCarry
