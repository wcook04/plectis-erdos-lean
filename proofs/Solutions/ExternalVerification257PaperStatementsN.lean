/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.BooleanMobiusSkipRowCofinal
import Erdos249257.CertificateKernel
import Erdos249257.DyadicPrefixCompression
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCarryReachability
import Erdos249257.HalfCylinderFiniteShadow
import Erdos249257.TerminalOnlyCofinal
import ErdosProblems.Erdos257.PaperCompleteR21.CentredCompletionAndDecisionBoundary
import ErdosProblems.Erdos257.PaperCompleteR21.EventualNonnegativeMargin
import ErdosProblems.Erdos257.PaperCompleteR21.GreedyGapCriteria
import ErdosProblems.Erdos257.PaperCompleteR21.GreedyOrbitNoTies
import ErdosProblems.Erdos257.PaperCompleteR21.SquareDepthAndHalfMembershipEquivalences

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.BooleanMobiusSkipRowCofinal`, `Erdos249257.CertificateKernel`,
`Erdos249257.DyadicPrefixCompression`, `Erdos249257.GenericTailOrbitRigidity`,
`Erdos249257.GreedyAchievementSet`, `Erdos249257.HalfCarryReachability`,
`Erdos249257.HalfCylinderFiniteShadow`, `Erdos249257.TerminalOnlyCofinal`,
`ErdosProblems.Erdos257.PaperCompleteR21.CentredCompletionAndDecisionBoundary`,
`ErdosProblems.Erdos257.PaperCompleteR21.EventualNonnegativeMargin`,
`ErdosProblems.Erdos257.PaperCompleteR21.GreedyGapCriteria`,
`ErdosProblems.Erdos257.PaperCompleteR21.GreedyOrbitNoTies`,
`ErdosProblems.Erdos257.PaperCompleteR21.SquareDepthAndHalfMembershipEquivalences`.
-/

open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

namespace Erdos249257.ExternalVerification257PaperStatementsN

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

noncomputable abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool

noncomputable def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}

noncomputable def HalfTerminalOnlyStripWitness (M : ℕ) : Prop :=
  ∃ a : HalfWord M,
    a ⟨0, Nat.zero_lt_succ M⟩ = false ∧
    (∀ h : 1 < M + 1, a ⟨1, h⟩ = false) ∧
    |(integerHalfCarry (wordSupport a) (M - 1) : ℝ)| ≤
      (halfStripBound M : ℝ)

noncomputable def HalfCarryCofinalTerminalOnlyStrip : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, max N 1 ≤ M ∧ HalfTerminalOnlyStripWitness M

noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1

noncomputable def finiteCoeffWindowNumerator
    (A : Set ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | J + 1 =>
      2 * finiteCoeffWindowNumerator A n J +
        supportCoeff A (n + J + 1)

noncomputable def HasRationalValue (x : ℝ) : Prop :=
  ∃ p : ℤ, ∃ v : ℕ, 0 < v ∧ x = (p : ℝ) / (v : ℝ)

noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

noncomputable def greedyMersennePrefixRat (x : ℚ) (n : ℕ) : Finset ℕ :=
  (((Finset.range n).filter fun k =>
      mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k).image
    fun k => k + 1)

noncomputable def halfGreedyPrefixSupport (n : ℕ) : Finset ℕ :=
  greedyMersennePrefixRat (1 / 2 : ℚ) n

noncomputable def greedyHalfFrozenMargin (k J : ℕ) : ℤ :=
  (finiteCoeffWindowNumerator
      (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J : ℤ) -
    (2 : ℤ) ^ J *
      mobiusCenteredHalfCarry
        (↑(halfGreedyPrefixSupport k) : Set ℕ) k

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

noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}

noncomputable def halfDyadicCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

noncomputable def tailGreedyRemainder (t : ℝ) (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => t
  | m + 1 =>
      if v (m + 1 + 1) ≤ tailGreedyRemainder t v m then
        tailGreedyRemainder t v m - v (m + 1 + 1)
      else tailGreedyRemainder t v m

theorem approx_orbit_induction
    (t : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (ht : Filter.Tendsto t Filter.atTop (nhds (1 / 2 : ℝ)))
    (hv : ∀ n : ℕ, 2 ≤ n →
      Filter.Tendsto (fun j => v j n) Filter.atTop (nhds (mersenneWeight n))) :
    ∀ r : ℕ,
      Filter.Tendsto (fun j => tailGreedyRemainder (t j) (v j) r) Filter.atTop
          (nhds (greedyMersenneRemainder (1 / 2 : ℝ) (r + 1))) ∧
        ∀ᶠ j in Filter.atTop, ∀ n : ℕ, 2 ≤ n → n ≤ r + 1 →
          ((v j n ≤ tailGreedyRemainder (t j) (v j) (n - 2)) ↔
            (mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.approx_orbit_induction t v ht hv

theorem fatal_absorbing {x : ℝ} (hx : 0 ≤ x) :
    (∀ n : ℕ, mersenneTail n < greedyMersenneRemainder x n →
        (∀ k : ℕ, n + k + 1 ∈ greedyMersenneSupport x) ∧
          ∀ k : ℕ, mersenneTail (n + k) < greedyMersenneRemainder x (n + k)) ∧
      ((greedyMersenneSkippedSupport x).Infinite → x ∈ mersenneAchievementSet) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.fatal_absorbing x hx

theorem paper_cpgs_equiv :
    ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
        0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
        greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
      ↔ CofinalPositiveHalfGreedySkips) ∧
      (∀ n : ℕ, 0 < greedyMersenneRemainderRat (1 / 2 : ℚ) n) ∧
      ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
        ↔ ∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
            greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c) ∧
      ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
        ↔ (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite) ∧
      ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
        ↔ (1 / 2 : ℝ) ∈ mersenneAchievementSet) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_cpgs_equiv

theorem paper_effective_horizon_test (k J : ℕ)
    (heta : 0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)
    (htest : ((k + J + 3 : ℕ) : ℝ) / (2 : ℝ) ^ J <
      1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) :
    0 < greedyHalfFrozenMargin k J := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_effective_horizon_test k J heta htest

theorem paper_eta_eq_coeffTail_sub_carry (k : ℕ) :
    1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k =
      binaryCoeffTail
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ)) (k + 1) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_eta_eq_coeffTail_sub_carry k

theorem paper_eta_hasRationalValue (k : ℕ) :
    HasRationalValue
      (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_eta_hasRationalValue k

theorem paper_eventual_nonnegative_margin_equivalence {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1) ↔
      ∃ J : ℕ, 0 ≤ greedyHalfFrozenMargin k J := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_eventual_nonnegative_margin_equivalence k hk

theorem paper_frozen_margin_limit_pos_iff (k : ℕ) :
    0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k ↔
      greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_limit_pos_iff k

theorem paper_frozen_margin_normalised_monotone (k : ℕ) :
    Monotone (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_monotone k

theorem paper_frozen_margin_normalised_tendsto (k : ℕ) :
    Tendsto (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J)
      atTop
      (nhds (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_tendsto k

theorem paper_frozen_margin_normalised_value (k J : ℕ) :
    (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J =
      (∑ i ∈ Finset.Icc 1 J,
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1 + i) : ℝ) /
            (2 : ℝ) ^ i) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_value k J

theorem paper_greedyHalfRemainder_ne_dyadicCap {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k ≠ halfDyadicCap (k + 1) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_greedyHalfRemainder_ne_dyadicCap k hk

theorem paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc (k : ℕ) :
    (↑(halfGreedyPrefixSupport k) : Set ℕ) =
      greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Icc 2 k := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc k

theorem paper_no_ties (k : ℕ) (hk : 2 ≤ k) :
    greedyMersenneRemainder (1 / 2 : ℝ) (k - 1) ≠ mersenneWeight k ∧
      greedyMersenneRemainder (1 / 2 : ℝ) (k - 1) ≠ mersenneTail k := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties k hk

theorem paper_no_ties_skip (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≠ mersenneTail (n + 1) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties_skip n

theorem paper_no_ties_take (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≠ mersenneWeight (n + 1) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties_take n

theorem paper_one_orbit_stability
    (t : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (dep : ℕ → ℕ)
    (ht : Filter.Tendsto t Filter.atTop (nhds (1 / 2 : ℝ)))
    (hv : ∀ n : ℕ, 2 ≤ n →
      Filter.Tendsto (fun j => v j n) Filter.atTop (nhds (mersenneWeight n)))
    (hvpos : ∀ j n : ℕ, 0 < v j n)
    (hdep : Filter.Tendsto dep Filter.atTop Filter.atTop)
    (K : ℕ) :
    ∀ᶠ j in Filter.atTop, K ≤ dep j ∧
      ∀ n : ℕ, 2 ≤ n → n ≤ K →
        ((v j n ≤ tailGreedyRemainder (t j) (v j) (n - 2)) ↔
          (mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_one_orbit_stability t v dep ht hv hvpos hdep K

theorem paper_one_sided_finite_decision_boundary :
    (∀ x : ℝ, x ∈ mersenneAchievementSet ↔
        0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
      (∀ x : ℝ, (∃ n : ℕ, mersenneTail n < greedyMersenneRemainder x n) →
        x ∉ mersenneAchievementSet) ∧
      (∀ x : ℝ, x ∈ mersenneAchievementSet →
        ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_one_sided_finite_decision_boundary

theorem paper_terminal_strip_equiv :
    ((∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ ∃ D : Finset ℕ,
        (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧
        |(integerHalfCarry (↑D : Set ℕ) (M - 1) : ℝ)| ≤ 2 * (Nat.sqrt M : ℝ) + 4)
      ↔ HalfCarryCofinalTerminalOnlyStrip) ∧
      ((∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ ∃ D : Finset ℕ,
          (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧
          |(integerHalfCarry (↑D : Set ℕ) (M - 1) : ℝ)| ≤ 2 * (Nat.sqrt M : ℝ) + 4)
        ↔ (1 / 2 : ℝ) ∈ mersenneAchievementSet) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_equiv

theorem tailGreedyRemainder_mersenne (m : ℕ) :
    tailGreedyRemainder (1 / 2 : ℝ) mersenneWeight m
      = greedyMersenneRemainder (1 / 2 : ℝ) (m + 1) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder_mersenne m

end Erdos249257.ExternalVerification257PaperStatementsN
