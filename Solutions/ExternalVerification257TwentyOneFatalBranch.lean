/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.TwentyOneQuotientGreedy

namespace Erdos249257.ExternalVerification257TwentyOneFatalBranch

noncomputable section

noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}

noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

noncomputable def GreedyMersenneFatalAt (x : ℝ) (n : ℕ) : Prop :=
  mersenneTail n < greedyMersenneRemainder x n

noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0

noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)

noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)

noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d

noncomputable def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card

noncomputable def localMersenneWeightsFrom (M R : ℕ) : ℕ → List ℕ
  | d =>
      if h : d ≤ R then
        localMersenneQuotient M d :: localMersenneWeightsFrom M R (d + 1)
      else
        []
termination_by d => R + 1 - d
decreasing_by omega

noncomputable def localMersenneWeights (M R : ℕ) : List ℕ :=
  localMersenneWeightsFrom M R 2

noncomputable def lowerSupportFromBits : ℕ → List Bool → Finset ℕ
  | _, [] => ∅
  | d, false :: bits => lowerSupportFromBits (d + 1) bits
  | d, true :: bits => insert d (lowerSupportFromBits (d + 1) bits)

noncomputable def twentyOneQuotientTarget (M : ℕ) : ℕ :=
  2 ^ M / 21

noncomputable def rationalMersenneGreedyBitsFrom : ℕ → ℕ → ℚ → List Bool
  | _, 0, _ => []
  | d, n + 1, x =>
      if mersenneWeightRat d ≤ x then
        true ::
          rationalMersenneGreedyBitsFrom (d + 1) n
            (x - mersenneWeightRat d)
      else
        false :: rationalMersenneGreedyBitsFrom (d + 1) n x

noncomputable def twentyOneEvenQuotientGreedySupport (R : ℕ) : Finset ℕ :=
  lowerSupportFromBits 2
    (integerGreedyBits
      (localMersenneWeights (2 * R) R)
      (twentyOneQuotientTarget (2 * R)))

noncomputable def twentyOneEvenQuotientGreedyRemainder (R : ℕ) : ℕ :=
  integerGreedyRemainder
    (localMersenneWeights (2 * R) R)
    (twentyOneQuotientTarget (2 * R))

noncomputable def localPrefixTwoStepPulse (D : Finset ℕ) (M : ℕ) : ℕ :=
  2 * endpointDivisorContribution D (M + 1) +
    endpointDivisorContribution D (M + 2)

noncomputable def twentyOneTargetTwoStepPulse (M : ℕ) : ℕ :=
  4 * (2 ^ M % 21) / 21

noncomputable def TwentyOneClosedLowerStateSupply : Prop :=
  ∀ R : ℕ, 2 ≤ R →
    ∃ D : Finset ℕ, ∃ s : ℕ,
      (∀ d ∈ D, 2 ≤ d ∧ d ≤ R) ∧
      localPrefixQuotient D (2 * R) + s =
        twentyOneQuotientTarget (2 * R) ∧
      s ≤ 2 ^ R

noncomputable def TwentyOneGreedyEventuallyHitsDoublingBlocks : Prop :=
  ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
    ∃ n : ℕ, K < n ∧ n ≤ 2 * K ∧
      n ∈ greedyMersenneSupport (1 / 21 : ℝ)

noncomputable def TwentyOneFatalAlignedBranch : Prop :=
  ∃ n R₀ : ℕ,
    GreedyMersenneFatalAt (1 / 21 : ℝ) n ∧
      (greedyMersenneSkippedSupport (1 / 21 : ℝ)).Finite ∧
      (∀ k : ℕ,
        n + k + 1 ∈ greedyMersenneSupport (1 / 21 : ℝ)) ∧
      (∀ R : ℕ, R₀ ≤ R →
        integerGreedyBits
            (localMersenneWeights (2 * R) (2 * R))
            (twentyOneQuotientTarget (2 * R)) =
          rationalMersenneGreedyBitsFrom 2 (2 * R - 1) (1 / 21 : ℚ)) ∧
      TwentyOneGreedyEventuallyHitsDoublingBlocks

private theorem integerGreedyBits_transport :
    integerGreedyBits =
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyBits := by
  funext weights C
  induction weights generalizing C with
  | nil =>
    simp [integerGreedyBits,
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyBits]
  | cons w ws ih =>
    simp [integerGreedyBits,
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyBits, ih]

private theorem weightedBoolSum_transport :
    weightedBoolSum =
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.weightedBoolSum := by
  funext weights bits
  induction weights generalizing bits with
  | nil =>
      cases bits <;>
        simp [weightedBoolSum,
          Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.weightedBoolSum]
  | cons w ws ih =>
      cases bits with
      | nil =>
          simp [weightedBoolSum,
            Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.weightedBoolSum]
      | cons b bs =>
          cases b <;>
            simp [weightedBoolSum,
              Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.weightedBoolSum, ih]

private theorem integerGreedyRemainder_transport :
    integerGreedyRemainder =
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyRemainder := by
  funext weights C
  simp only [integerGreedyRemainder,
    Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyRemainder,
    weightedBoolSum_transport, integerGreedyBits_transport]

private theorem localMersenneWeightsFrom_aux (M R : ℕ) : ∀ (k d : ℕ), R + 1 - d ≤ k →
    localMersenneWeightsFrom M R d =
      Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.localMersenneWeightsFrom
        M R d := by
  intro k
  induction k with
  | zero =>
      intro d hd
      have h : ¬ d ≤ R := by omega
      rw [localMersenneWeightsFrom,
        Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.localMersenneWeightsFrom]
      simp [h]
  | succ k ih =>
      intro d hd
      rw [localMersenneWeightsFrom,
        Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.localMersenneWeightsFrom]
      by_cases h : d ≤ R
      · rw [dif_pos h, dif_pos h, ih (d + 1) (by omega)]
        rfl
      · simp [h]

private theorem localMersenneWeightsFrom_transport :
    localMersenneWeightsFrom =
      Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.localMersenneWeightsFrom := by
  funext M R d
  exact localMersenneWeightsFrom_aux M R (R + 1 - d) d le_rfl

private theorem localMersenneWeights_transport :
    localMersenneWeights =
      Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.localMersenneWeights := by
  funext M R
  simp only [localMersenneWeights,
    Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.localMersenneWeights,
    localMersenneWeightsFrom_transport]

private theorem lowerSupportFromBits_transport :
    lowerSupportFromBits =
      Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.lowerSupportFromBits := by
  funext d bits
  induction bits generalizing d with
  | nil =>
      simp [lowerSupportFromBits,
        Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.lowerSupportFromBits]
  | cons b bs ih =>
      cases b <;>
        simp [lowerSupportFromBits,
          Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.lowerSupportFromBits, ih]

private theorem rationalMersenneGreedyBitsFrom_transport :
    rationalMersenneGreedyBitsFrom =
      Erdos257PeriodNoncollapse.rationalMersenneGreedyBitsFrom := by
  funext d n x
  induction n generalizing d x with
  | zero =>
      simp [rationalMersenneGreedyBitsFrom,
        Erdos257PeriodNoncollapse.rationalMersenneGreedyBitsFrom]
  | succ n ih =>
      simp only [rationalMersenneGreedyBitsFrom,
        Erdos257PeriodNoncollapse.rationalMersenneGreedyBitsFrom, ih,
        show mersenneWeightRat = Erdos257PeriodNoncollapse.mersenneWeightRat from rfl]

private theorem greedyMersenneRemainder_transport :
    greedyMersenneRemainder = Erdos257PeriodNoncollapse.greedyMersenneRemainder := by
  funext x n
  induction n with
  | zero =>
      simp only [greedyMersenneRemainder,
        Erdos257PeriodNoncollapse.greedyMersenneRemainder]
  | succ n ih =>
      simp only [greedyMersenneRemainder,
        Erdos257PeriodNoncollapse.greedyMersenneRemainder, ih,
        show mersenneWeight = Erdos257PeriodNoncollapse.mersenneWeight from rfl]

private theorem greedyMersenneSupport_transport :
    greedyMersenneSupport = Erdos257PeriodNoncollapse.greedyMersenneSupport := by
  funext x
  simp only [greedyMersenneSupport, Erdos257PeriodNoncollapse.greedyMersenneSupport,
    greedyMersenneRemainder_transport,
    show mersenneWeight = Erdos257PeriodNoncollapse.mersenneWeight from rfl]

private theorem greedyMersenneSkippedSupport_transport :
    greedyMersenneSkippedSupport =
      Erdos257PeriodNoncollapse.greedyMersenneSkippedSupport := by
  funext x
  simp only [greedyMersenneSkippedSupport,
    Erdos257PeriodNoncollapse.greedyMersenneSkippedSupport,
    greedyMersenneSupport_transport]

private theorem greedyMersenneFatalAt_transport :
    GreedyMersenneFatalAt = Erdos257PeriodNoncollapse.GreedyMersenneFatalAt := by
  funext x n
  simp only [GreedyMersenneFatalAt, Erdos257PeriodNoncollapse.GreedyMersenneFatalAt,
    greedyMersenneRemainder_transport,
    show mersenneTail = Erdos257PeriodNoncollapse.mersenneTail from rfl]

private theorem twentyOneEvenQuotientGreedySupport_transport :
    twentyOneEvenQuotientGreedySupport =
      Erdos257PeriodNoncollapse.twentyOneEvenQuotientGreedySupport := by
  funext R
  simp only [twentyOneEvenQuotientGreedySupport,
    Erdos257PeriodNoncollapse.twentyOneEvenQuotientGreedySupport,
    lowerSupportFromBits_transport, integerGreedyBits_transport,
    localMersenneWeights_transport,
    show twentyOneQuotientTarget =
      Erdos257PeriodNoncollapse.twentyOneQuotientTarget from rfl]

private theorem twentyOneEvenQuotientGreedyRemainder_transport :
    twentyOneEvenQuotientGreedyRemainder =
      Erdos257PeriodNoncollapse.twentyOneEvenQuotientGreedyRemainder := by
  funext R
  simp only [twentyOneEvenQuotientGreedyRemainder,
    Erdos257PeriodNoncollapse.twentyOneEvenQuotientGreedyRemainder,
    integerGreedyRemainder_transport, localMersenneWeights_transport,
    show twentyOneQuotientTarget =
      Erdos257PeriodNoncollapse.twentyOneQuotientTarget from rfl]

private theorem twentyOneGreedyEventuallyHitsDoublingBlocks_transport :
    TwentyOneGreedyEventuallyHitsDoublingBlocks =
      Erdos257PeriodNoncollapse.TwentyOneGreedyEventuallyHitsDoublingBlocks := by
  simp only [TwentyOneGreedyEventuallyHitsDoublingBlocks,
    Erdos257PeriodNoncollapse.TwentyOneGreedyEventuallyHitsDoublingBlocks,
    greedyMersenneSupport_transport]

private theorem twentyOneFatalAlignedBranch_transport :
    TwentyOneFatalAlignedBranch =
      Erdos257PeriodNoncollapse.TwentyOneFatalAlignedBranch := by
  simp only [TwentyOneFatalAlignedBranch,
    Erdos257PeriodNoncollapse.TwentyOneFatalAlignedBranch,
    greedyMersenneFatalAt_transport, greedyMersenneSkippedSupport_transport,
    greedyMersenneSupport_transport, integerGreedyBits_transport,
    localMersenneWeights_transport, rationalMersenneGreedyBitsFrom_transport,
    twentyOneGreedyEventuallyHitsDoublingBlocks_transport,
    show twentyOneQuotientTarget =
      Erdos257PeriodNoncollapse.twentyOneQuotientTarget from rfl]

private theorem mersenneAchievementSet_transport :
    mersenneAchievementSet = Erdos257PeriodNoncollapse.mersenneAchievementSet := rfl

private theorem twentyOneClosedLowerStateSupply_transport :
    TwentyOneClosedLowerStateSupply =
      Erdos257PeriodNoncollapse.TwentyOneClosedLowerStateSupply := rfl

private theorem twentyOneQuotientTarget_transport :
    twentyOneQuotientTarget = Erdos257PeriodNoncollapse.twentyOneQuotientTarget := rfl

private theorem localPrefixTwoStepPulse_transport :
    localPrefixTwoStepPulse = Erdos257PeriodNoncollapse.localPrefixTwoStepPulse := rfl

private theorem twentyOneTargetTwoStepPulse_transport :
    twentyOneTargetTwoStepPulse =
      Erdos257PeriodNoncollapse.twentyOneTargetTwoStepPulse := rfl

theorem twentyOneClosedRow_forces_quotientGreedy
    {R s : ℕ} {bits : List Bool}
    (hlen : bits.length = (localMersenneWeights (2 * R) R).length)
    (hrow :
      weightedBoolSum (localMersenneWeights (2 * R) R) bits + s =
        twentyOneQuotientTarget (2 * R))
    (hclosed : s ≤ 2 ^ R) :
    bits = integerGreedyBits
          (localMersenneWeights (2 * R) R)
          (twentyOneQuotientTarget (2 * R)) ∧
      s = twentyOneEvenQuotientGreedyRemainder R := by
  simp only [localMersenneWeights_transport, weightedBoolSum_transport,
    twentyOneQuotientTarget_transport] at hlen hrow
  simp only [localMersenneWeights_transport, integerGreedyBits_transport,
    twentyOneQuotientTarget_transport,
    twentyOneEvenQuotientGreedyRemainder_transport]
  exact Erdos257PeriodNoncollapse.twentyOneClosedRow_forces_quotientGreedy
    hlen hrow hclosed

theorem one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates
    (hsupply : TwentyOneClosedLowerStateSupply) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  rw [twentyOneClosedLowerStateSupply_transport] at hsupply
  rw [mersenneAchievementSet_transport]
  exact
    Erdos257PeriodNoncollapse.one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates
      hsupply

theorem one_div_twenty_one_mem_iff_not_fatalAlignedBranch :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ TwentyOneFatalAlignedBranch := by
  rw [mersenneAchievementSet_transport, twentyOneFatalAlignedBranch_transport]
  exact Erdos257PeriodNoncollapse.one_div_twenty_one_mem_iff_not_fatalAlignedBranch

theorem twentyOneFatalAlignedBranch_eventually_strict_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      2 ^ R < twentyOneEvenQuotientGreedyRemainder R := by
  rw [twentyOneFatalAlignedBranch_transport] at hbranch
  simp only [twentyOneEvenQuotientGreedyRemainder_transport]
  exact Erdos257PeriodNoncollapse.twentyOneFatalAlignedBranch_eventually_strict_supercapacity
    hbranch

theorem twentyOneFatalAlignedBranch_eventually_affine_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      twentyOneEvenQuotientGreedySupport (R + 1) =
          insert (R + 1) (twentyOneEvenQuotientGreedySupport R) ∧
        twentyOneEvenQuotientGreedyRemainder (R + 1) =
          (4 * twentyOneEvenQuotientGreedyRemainder R +
              twentyOneTargetTwoStepPulse (2 * R) -
                localPrefixTwoStepPulse
                  (twentyOneEvenQuotientGreedySupport R) (2 * R)) -
            (2 ^ (R + 1) + 1) := by
  rw [twentyOneFatalAlignedBranch_transport] at hbranch
  simp only [twentyOneEvenQuotientGreedySupport_transport,
    twentyOneEvenQuotientGreedyRemainder_transport,
    twentyOneTargetTwoStepPulse_transport, localPrefixTwoStepPulse_transport]
  exact Erdos257PeriodNoncollapse.twentyOneFatalAlignedBranch_eventually_affine_supercapacity
    hbranch

end

end Erdos249257.ExternalVerification257TwentyOneFatalBranch
