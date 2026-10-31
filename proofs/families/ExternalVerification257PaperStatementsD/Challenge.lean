/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.BooleanMobiusSkipRowCofinal`, `Erdos249257.CertificateKernel`,
`Erdos249257.CofinalStripReturn`, `Erdos249257.DyadicPrefixCompression`,
`Erdos249257.GenericTailOrbitRigidity`, `Erdos249257.GreedyAchievementSet`,
`Erdos249257.HalfCarryReachability`, `Erdos249257.HalfCylinderFixedTailSocket`,
`ErdosProblems.Erdos257.PaperCompleteR20.CofinalCarryCollapse`,
`ErdosProblems.Erdos257.PaperCompleteR20.GeneralTargetGap`.
-/

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory

namespace Erdos249257.ExternalVerification257PaperStatementsD

noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)

noncomputable def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n

noncomputable def CofinalPositiveHalfGreedySkips : Prop :=
  ∀ N : ℕ, ∃ c : ℕ,
    max N 4 ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
        mersenneWeightRat c

noncomputable def halfStripBound (n : ℕ) : ℕ :=
  2 * Nat.sqrt n + 4

noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1

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
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

noncomputable def GreedyHalfCarryCofinalStripReturn : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
    integerHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) M ≤
      (halfStripBound (M + 1) : ℤ)

noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def finiteErdosSum (F : Finset Nat) (b : Nat) : Rat :=
  ∑ n ∈ F, 1 / ((b : Rat) ^ n - 1)

noncomputable def greedyMersennePrefixRat (x : ℚ) (n : ℕ) : Finset ℕ :=
  (((Finset.range n).filter fun k =>
      mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k).image
    fun k => k + 1)

noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}

noncomputable def halfDyadicCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n

noncomputable def nextDyadicExcessIntNumerator (p : ℤ) (n L : ℕ) : ℤ :=
  ((2 ^ n : ℕ) : ℤ) * p - (L : ℤ)

noncomputable def halfGreedyPrefixRat (n : ℕ) : ℚ :=
  finiteErdosSum (greedyMersennePrefixRat (1 / 2 : ℚ) n) 2

noncomputable def halfGreedyPrefixDenominator (n : ℕ) : ℕ :=
  (halfGreedyPrefixRat n).den

noncomputable def halfGreedyResidualDisplayedNumerator (n : ℕ) : ℤ :=
  (halfGreedyPrefixDenominator n : ℤ) -
    2 * (halfGreedyPrefixRat n).num

noncomputable def halfGreedyNextDyadicExcessNumerator (n : ℕ) : ℤ :=
  nextDyadicExcessIntNumerator
    (halfGreedyResidualDisplayedNumerator n) n
    (halfGreedyPrefixDenominator n)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

noncomputable def InternalMersenneGap (x : ℝ) : Prop :=
  ∃ (D : Finset ℕ) (m : ℕ), 1 ≤ m ∧
    (∀ n ∈ D, 0 < n ∧ n < m) ∧
    positiveMersenneSupportValue (D : Set ℕ)+mersenneTail m < x ∧
    x < positiveMersenneSupportValue (D : Set ℕ)+mersenneWeight m

/-- States record:257rig-c18 from the long record for Erdős problem #257. Transported from
Erdos249257.HalfCarryReachability.greedy_half_infinite_of_cofinalStripReturn in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem greedy_half_infinite_of_cofinalStripReturn
    (hreturn : GreedyHalfCarryCofinalStripReturn) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := by
  sorry

/-- States thm:sqrt-bound-route from the long record for Erdős problem #257. Transported from
Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound
    (hnonneg : ∀ N : ℕ,
      0 ≤ mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N)
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) ≤
          2 * Real.sqrt (N : ℝ) + 4) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := by
  sorry

/-- States record:257rig-c16 from the long record for Erdős problem #257. Transported from
Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) ≤
          2 * Real.sqrt (N : ℝ) + 4) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := by
  sorry

/-- States record:257rig-c16, thm:sqrt-bound-route from the long record for Erdős problem #257.
Transported from Erdos249257.HalfCarryReachability.greedy_mobiusCenteredHalfCarry_nonneg in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem greedy_mobiusCenteredHalfCarry_nonneg (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N := by
  sorry

/-- States record:257bm-c2 from the long record for Erdős problem #257. Transported from
Erdos249257.cofinalPositiveHalfGreedySkips_iff_half_mem in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem cofinalPositiveHalfGreedySkips_iff_half_mem :
    CofinalPositiveHalfGreedySkips ↔
      (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry

/-- States lem:dyadic-excess-reformulation from the long record for Erdős problem #257.
Transported from Erdos249257.greedyHalf_mem_nextMersenneDyadicSliver_iff_excess in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem greedyHalf_mem_nextMersenneDyadicSliver_iff_excess (n : ℕ) :
    (halfDyadicCap (n + 1) <
          greedyMersenneRemainder (1 / 2 : ℝ) n ∧
        greedyMersenneRemainder (1 / 2 : ℝ) n <
          mersenneWeight (n + 1)) ↔
      (0 < halfGreedyNextDyadicExcessNumerator n ∧
        2 * halfGreedyNextDyadicExcessNumerator n <
          halfGreedyResidualDisplayedNumerator n) := by
  sorry

/-- States thm:last-skip-iff-fatal from the long record for Erdős problem #257. Transported from
Erdos249257.half_mem_iff_every_actual_skip_survives in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_iff_every_actual_skip_survives :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ M : ℕ,
        M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) →
          greedyMersenneRemainder (1 / 2 : ℝ) M ≤ mersenneTail M := by
  sorry

/-- States record:257bm-c2 from the long record for Erdős problem #257. Transported from
Erdos249257.half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips
    (hskips : CofinalPositiveHalfGreedySkips) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry

/-- States prop:collapse from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR20.greedy_half_of_cofinal_upper_carry in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem greedy_half_of_cofinal_upper_carry (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      (integerHalfCarry (greedyMersenneSupport (1/2 : ℝ)) N : ℝ) ≤
        C*Real.sqrt ((N : ℝ)+1)+D) :
    erdosSupportSeries 2 (greedyMersenneSupport (1/2 : ℝ)) = (1 : ℝ)/2 := by
  sorry

/-- States thm:greedy-survival from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR20.paper_greedy_survival in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedy_survival :
    (∀ x : ℝ, x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ erdosBorweinMersenneConstant →
      (x ∉ mersenneAchievementSet ↔ InternalMersenneGap x)) := by
  sorry

end Erdos249257.ExternalVerification257PaperStatementsD
