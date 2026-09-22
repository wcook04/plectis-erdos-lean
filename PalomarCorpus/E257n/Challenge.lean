/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band n

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

namespace PalomarCorpus.E257.PaperStatementsN
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
/-- The exact rational Mersenne weight `1 / (2^n - 1)`. Its meaningful support indices are positive; at index zero Lean's division convention gives zero. Local copy of Erdos249257.mersenneWeightRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
/-- Exact rational version of the greedy residual. Local copy of Erdos249257.greedyMersenneRemainderRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n
/-- Positive skipped ranks of the rational half-greedy support occur arbitrarily far out. Positivity separates the skipped-core construction from the already-terminal case in which a finite greedy prefix equals one half exactly. Local copy of Erdos249257.CofinalPositiveHalfGreedySkips, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CofinalPositiveHalfGreedySkips : Prop :=
  ∀ N : ℕ, ∃ c : ℕ,
    max N 4 ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
        mersenneWeightRat c
/-- The discrete square-root strip used by the half-carry search. Local copy of Erdos249257.HalfCarryReachability.halfStripBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfStripBound (n : ℕ) : ℕ :=
  2 * Nat.sqrt n + 4
/-- The exact binary affine orbit driven by the fresh coefficient word `a`. Local copy of Erdos249257.affineBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}` — the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- The integer carry whose state at time `N` is the packet's `K_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.integerHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1
/-- A Boolean support word through exponent `N`. Index zero is retained so restriction is literal; admissibility forces exponents zero and one off. Local copy of Erdos249257.HalfCarryReachability.HalfWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool
/-- The set represented by a finite Boolean word. Local copy of Erdos249257.HalfCarryReachability.wordSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}
/-- A normalized finite word whose *terminal* integer half-carry is in the discrete square-root strip. There is deliberately no all-prefix admissibility hypothesis here. Local copy of Erdos249257.HalfCarryReachability.HalfTerminalOnlyStripWitness, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfTerminalOnlyStripWitness (M : ℕ) : Prop :=
  ∃ a : HalfWord M,
    a ⟨0, Nat.zero_lt_succ M⟩ = false ∧
    (∀ h : 1 < M + 1, a ⟨1, h⟩ = false) ∧
    |(integerHalfCarry (wordSupport a) (M - 1) : ℝ)| ≤
      (halfStripBound M : ℝ)
/-- Terminal-only square-root-strip witnesses exist at cofinally many depths. The `max N 1` guard makes the terminal index `M - 1` line up with the scaled-residual identity at exponent `M`. Local copy of Erdos249257.HalfCarryReachability.HalfCarryCofinalTerminalOnlyStrip, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfCarryCofinalTerminalOnlyStrip : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, max N 1 ≤ M ∧ HalfTerminalOnlyStripWitness M
/-- The canonical integer half carry measured relative to the signed Möbius solution. Index `N` corresponds to the packet's state `e_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1
/-- Integer numerator of the frozen coefficient window. The recurrence uses the binary weights `2^(J-i)` without division. Local copy of Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteCoeffWindowNumerator
    (A : Set ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | J + 1 =>
      2 * finiteCoeffWindowNumerator A n J +
        supportCoeff A (n + J + 1)
/-- A real number represented by an integer numerator and a positive natural denominator. This is the explicit positive-denominator form of membership in `ℚ`; it keeps the carry multiplier visible in theorem statements. Local copy of Erdos249257.HasRationalValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HasRationalValue (x : ℝ) : Prop :=
  ∃ p : ℤ, ∃ v : ℕ, 0 < v ∧ x = (p : ℝ) / (v : ℝ)
/-- The scaled tail `T_c(N) = ∑_{j≥1} c(N+j)/2^j`. Local copy of Erdos249257.binaryCoeffTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
/-- Positive exponents selected through a finite exact-rational greedy run. Local copy of Erdos249257.greedyMersennePrefixRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersennePrefixRat (x : ℚ) (n : ℕ) : Finset ℕ :=
  (((Finset.range n).filter fun k =>
      mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k).image
    fun k => k + 1)
/-- Local copy of Erdos249257.halfGreedyPrefixSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfGreedyPrefixSupport (n : ℕ) : Finset ℕ :=
  greedyMersennePrefixRat (1 / 2 : ℚ) n
/-- Signed frozen-prefix margin. Its nonnegativity says that the first `J` future divisor-incidence rows cover the centered carry at depth `k`. Local copy of Erdos249257.greedyHalfFrozenMargin, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyHalfFrozenMargin (k J : ℕ) : ℤ :=
  (finiteCoeffWindowNumerator
      (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J : ℤ) -
    (2 : ℤ) ^ J *
      mobiusCenteredHalfCarry
        (↑(halfGreedyPrefixSupport k) : Set ℕ) k
/-- The real Mersenne weight `1 / (2^n - 1)`. Local copy of Erdos249257.mersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- Real greedy residual after processing exponents `1, ..., n`. Local copy of Erdos249257.greedyMersenneRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n
/-- The set of positive exponents selected by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}
/-- The positive exponents omitted by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSkippedSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}
/-- The first geometric channel of the Mersenne tail. Local copy of Erdos249257.halfDyadicCap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfDyadicCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n
/-- The value coded by a set of positive exponents. The sequence index is zero-based while the exponent supplied to the weight is `k+1`. Local copy of Erdos249257.positiveMersenneSupportValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- The remaining mass after processing exponents `1, ..., n`. Local copy of Erdos249257.mersenneTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- The greedy rule applied to an arbitrary target `t` and an arbitrary weight system `v`, in increasing order of rank, starting at rank `2`. `tailGreedyRemainder t v m` is the residual after the ranks `2, …, m + 1`, so the decision at rank `n ≥ 2` is `v n ≤ tailGreedyRemainder t v (n - 2)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailGreedyRemainder (t : ℝ) (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => t
  | m + 1 =>
      if v (m + 1 + 1) ≤ tailGreedyRemainder t v m then
        tailGreedyRemainder t v m - v (m + 1 + 1)
      else tailGreedyRemainder t v m
/-- States prop:one-orbit from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.approx_orbit_induction in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
  sorry
/-- States thm:fatal-absorbing from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.fatal_absorbing in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fatal_absorbing {x : ℝ} (hx : 0 ≤ x) :
    (∀ n : ℕ, mersenneTail n < greedyMersenneRemainder x n →
        (∀ k : ℕ, n + k + 1 ∈ greedyMersenneSupport x) ∧
          ∀ k : ℕ, mersenneTail (n + k) < greedyMersenneRemainder x (n + k)) ∧
      ((greedyMersenneSkippedSupport x).Infinite → x ∈ mersenneAchievementSet) := by
  sorry
/-- States prop:cpgs-equiv from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_cpgs_equiv in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_effective_horizon_test in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_effective_horizon_test (k J : ℕ)
    (heta : 0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)
    (htest : ((k + J + 3 : ℕ) : ℝ) / (2 : ℝ) ^ J <
      1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) :
    0 < greedyHalfFrozenMargin k J := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_eta_eq_coeffTail_sub_carry in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_eta_eq_coeffTail_sub_carry (k : ℕ) :
    1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k =
      binaryCoeffTail
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ)) (k + 1) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_eta_hasRationalValue in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_eta_hasRationalValue (k : ℕ) :
    HasRationalValue
      (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_eventual_nonnegative_margin_equivalence in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_eventual_nonnegative_margin_equivalence {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1) ↔
      ∃ J : ℕ, 0 ≤ greedyHalfFrozenMargin k J := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_limit_pos_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_frozen_margin_limit_pos_iff (k : ℕ) :
    0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k ↔
      greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_monotone in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_frozen_margin_normalised_monotone (k : ℕ) :
    Monotone (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_tendsto in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_frozen_margin_normalised_tendsto (k : ℕ) :
    Tendsto (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J)
      atTop
      (nhds (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_value in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_frozen_margin_normalised_value (k J : ℕ) :
    (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J =
      (∑ i ∈ Finset.Icc 1 J,
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1 + i) : ℝ) /
            (2 : ℝ) ^ i) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_greedyHalfRemainder_ne_dyadicCap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedyHalfRemainder_ne_dyadicCap {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k ≠ halfDyadicCap (k + 1) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc (k : ℕ) :
    (↑(halfGreedyPrefixSupport k) : Set ℕ) =
      greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Icc 2 k := by
  sorry
/-- States lem:no-ties from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_no_ties (k : ℕ) (hk : 2 ≤ k) :
    greedyMersenneRemainder (1 / 2 : ℝ) (k - 1) ≠ mersenneWeight k ∧
      greedyMersenneRemainder (1 / 2 : ℝ) (k - 1) ≠ mersenneTail k := by
  sorry
/-- States lem:no-ties from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties_skip in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_no_ties_skip (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≠ mersenneTail (n + 1) := by
  sorry
/-- States lem:no-ties from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties_take in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_no_ties_take (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≠ mersenneWeight (n + 1) := by
  sorry
/-- States prop:one-orbit from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_one_orbit_stability in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_one_sided_finite_decision_boundary in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_one_sided_finite_decision_boundary :
    (∀ x : ℝ, x ∈ mersenneAchievementSet ↔
        0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
      (∀ x : ℝ, (∃ n : ℕ, mersenneTail n < greedyMersenneRemainder x n) →
        x ∉ mersenneAchievementSet) ∧
      (∀ x : ℝ, x ∈ mersenneAchievementSet →
        ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) := by
  sorry
/-- States prop:strip-equiv from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_equiv in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_terminal_strip_equiv :
    ((∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ ∃ D : Finset ℕ,
        (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧
        |(integerHalfCarry (↑D : Set ℕ) (M - 1) : ℝ)| ≤ 2 * (Nat.sqrt M : ℝ) + 4)
      ↔ HalfCarryCofinalTerminalOnlyStrip) ∧
      ((∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ ∃ D : Finset ℕ,
          (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧
          |(integerHalfCarry (↑D : Set ℕ) (M - 1) : ℝ)| ≤ 2 * (Nat.sqrt M : ℝ) + 4)
        ↔ (1 / 2 : ℝ) ∈ mersenneAchievementSet) := by
  sorry
/-- States prop:one-orbit from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder_mersenne in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tailGreedyRemainder_mersenne (m : ℕ) :
    tailGreedyRemainder (1 / 2 : ℝ) mersenneWeight m
      = greedyMersenneRemainder (1 / 2 : ℝ) (m + 1) := by
  sorry
end PalomarCorpus.E257.PaperStatementsN
