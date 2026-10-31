/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_43

Every non-theorem declaration of `PalomarCorpus/E257_43/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
open Classical

namespace PalomarCorpus.E257_43.Shared
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The Mersenne tail beyond rank n, namely the sum over k at least 0 of the Mersenne weight at n+k+1. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- The manuscript's `T_{n+1}^{(J)} = ∑_{q=1}^{J} 2^{-qn}/(2^q-1)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungTail (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / (2 ^ (q * n) * (2 ^ q - 1))
/-- The manuscript's `w_n^{(J)} = ∑_{q=1}^{J} 2^{-qn}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungWeight (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / 2 ^ (q * n)
/-- The greedy residual just before rank `n` is examined; `rungRem J 0 = 1/2`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungRem, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungRem (J : ℕ) : ℕ → ℝ
  | 0 => 1 / 2
  | n + 1 => if rungWeight J n ≤ rungRem J n then rungRem J n - rungWeight J n else rungRem J n
/-- The greedy support: the ranks the greedy rule takes. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungGreedySupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungGreedySupport (J : ℕ) : Set ℕ := {n | rungWeight J n ≤ rungRem J n}
end PalomarCorpus.E257_43.Shared

namespace PalomarCorpus.E257.PaperStatementsN
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_43.Shared (mersenneTail mersenneWeight)
/-- Real greedy residual after processing exponents `1, ..., n`. Local copy of Erdos249257.greedyMersenneRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n
/-- The value coded by a set of positive exponents. The sequence index is zero-based while the exponent supplied to the weight is `k+1`. Local copy of Erdos249257.positiveMersenneSupportValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- The greedy rule applied to an arbitrary target `t` and an arbitrary weight system `v`, in increasing order of rank, starting at rank `2`. `tailGreedyRemainder t v m` is the residual after the ranks `2, …, m + 1`, so the decision at rank `n ≥ 2` is `v n ≤ tailGreedyRemainder t v (n - 2)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailGreedyRemainder (t : ℝ) (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => t
  | m + 1 =>
      if v (m + 1 + 1) ≤ tailGreedyRemainder t v m then
        tailGreedyRemainder t v m - v (m + 1 + 1)
      else tailGreedyRemainder t v m
end PalomarCorpus.E257.PaperStatementsN

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_43.Shared (mersenneTail mersenneWeight)
end PalomarCorpus.E257.PaperStatementsAM

namespace PalomarCorpus.E257.PaperStatementsAI
open Filter
open Topology
open Classical
export PalomarCorpus.E257_43.Shared (rungGreedySupport rungRem rungTail rungWeight)
end PalomarCorpus.E257.PaperStatementsAI

namespace PalomarCorpus.E257.PaperStatementsJ
open Filter
open Topology
open Classical
export PalomarCorpus.E257_43.Shared (rungGreedySupport rungRem rungTail rungWeight)
/-- The mass that the support `A` puts at rank `n`: this is `Set.indicator A (rungWeight J)`, so `∑' n, rungSupportWeight J A n` is the manuscript's `∑_{n ∈ A} w_n^{(J)}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungSupportWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungSupportWeight (J : ℕ) (A : Set ℕ) (n : ℕ) : ℝ :=
  if n ∈ A then rungWeight J n else 0
/-- The manuscript's `HalfRung(J)`: some `A ⊆ {2,3,…}` has `∑_{n ∈ A} w_n^{(J)} = 1/2`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.HalfRung, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfRung (J : ℕ) : Prop :=
  ∃ A : Set ℕ, (∀ n ∈ A, 2 ≤ n) ∧ ∑' n : ℕ, rungSupportWeight J A n = 1 / 2
/-- The manuscript's misalignment mass `μ_J(M) = ∑_{q=2}^{J} 2^{M mod q}/(2^q-1)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungMisalign, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungMisalign (J M : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 J, (2 : ℝ) ^ (M % q) / (2 ^ q - 1)
/-- A rank `n` is **bad** for `J` when no `M ∈ [n, 2n-2]` passes the witness test `μ_J(M) ≤ 11/15`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.RungBad, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RungBad (J n : ℕ) : Prop :=
  ∀ M : ℕ, n ≤ M → M + 2 ≤ 2 * n → ¬ (rungMisalign J M ≤ 11 / 15)
/-- Rank `n` is **fatal** when the residual sits strictly inside the gap `(T_{n+1}^{(J)}, w_n^{(J)})`, which no later tail can repair. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.RungFatal, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RungFatal (J n : ℕ) : Prop :=
  rungTail J n < rungRem J n ∧ rungRem J n < rungWeight J n
/-- The manuscript's `L_J = lcm(2,3,…,J)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungLcm (J : ℕ) : ℕ := (Finset.Icc 2 J).lcm id
/-- The bad ranks inside the manuscript's finite window `[4, L_J/2]`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungBadFinset, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungBadFinset (J : ℕ) : Finset ℕ :=
  (Finset.Icc 4 (rungLcm J / 2)).filter (fun n => RungBad J n)
/-- The manuscript's `B(J) = max(bad ∪ {3})`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungDecisionHorizon, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungDecisionHorizon (J : ℕ) : ℕ :=
  (insert 3 (rungBadFinset J)).max' ⟨3, Finset.mem_insert_self 3 _⟩
end PalomarCorpus.E257.PaperStatementsJ

namespace PalomarCorpus.E257.PaperStatementsAA
/-- The manuscript's misalignment mass `μ_J(M) = ∑_{q=2}^{J} 2^{M mod q}/(2^q-1)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.misalignMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def misalignMass (J M : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 J, (2 : ℝ) ^ (M % q) / (2 ^ q - 1)
/-- The manuscript's `B(r) = 2^⌊(r+4)/2⌋ + 2r + 3`: a division-free integer envelope for a reset which can feed a right branch at the two-thirds crossing of its largest false rank. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.resetCrossingBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def resetCrossingBound (r : ℕ) : ℕ :=
  2 ^ ((r + 4) / 2) + 2 * r + 3
/-- The manuscript's `L_J = lcm(2,3,…,J)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.truncLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def truncLcm (J : ℕ) : ℕ := (Finset.Icc 2 J).lcm id
/-- The manuscript's `T_{n+1}^{(J)} = ∑_{q=1}^{J} 2^{-qn}/(2^q-1)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.truncTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def truncTail (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / (2 ^ (q * n) * (2 ^ q - 1))
/-- The manuscript's `w_n^{(J)} = ∑_{q=1}^{J} 2^{-qn}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.truncWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def truncWeight (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / 2 ^ (q * n)
end PalomarCorpus.E257.PaperStatementsAA
