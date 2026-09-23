/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, record sections 12 to 13: what is open, stated exactly; logarithmic cost under arithmetic sampling

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
open Finset

namespace PalomarCorpus.E257_38.Shared
/-- The binary affine orbit driven by an integer sequence a from an initial value, defined by orbit 0 equal to the initial value and orbit (n+1) equal to twice orbit n minus a at n+1. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- Cost of a finitely supported nonnegative divisor majorant. Local copy of ErdosProblems.Erdos257.divisorMajorantCost, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def divisorMajorantCost (D : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, c d / d
/-- The paper's modulus `Q = lcm F`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.frameLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def frameLcm (F : Finset ℕ) : ℕ := F.lcm id
/-- The paper's divisor-incidence count `f_F(n) = #{a ∈ F : a ∣ n}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.incidenceCount, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def incidenceCount (F : Finset ℕ) (n : ℕ) : ℕ := (F.filter (fun a => a ∣ n)).card
/-- The literal modular atom requested in mandate 1a. Local copy of ErdosProblems.Erdos257.PaperCompleteR8.kernelWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def kernelWeight (B : ℝ) (d n : ℕ) : ℝ :=
  B ^ (n % d) / (B ^ d - 1)
/-- The finite positive frame potential. Local copy of ErdosProblems.Erdos257.PaperCompleteR8.framePotential, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def framePotential (F : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ a ∈ F, kernelWeight 2 a N
/-- The indicator of the paper's event `{U_F > 1}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.exceedInd, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exceedInd (F : Finset ℕ) (N : ℕ) : ℝ := if 1 < framePotential F N then 1 else 0
/-- The costs of the admissible positive logarithmic divisor majorants of `(F, t)`: the feasible set of the paper's programme (display 9.185). Local copy of ErdosProblems.Erdos257.PaperCompleteR21.logMajorantCosts, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def logMajorantCosts (F : Finset ℕ) (t : ℝ) : Set ℝ :=
  {K : ℝ | ∃ c : ℕ → ℝ, (∀ d, 0 ≤ c d) ∧
    (∀ s ∈ (frameLcm F).divisors,
        Real.log (1 + (incidenceCount F s : ℝ) / t) ≤ ∑ d ∈ s.divisors, c d) ∧
    K = divisorMajorantCost (frameLcm F).divisors c}
/-- The paper's `κ₁(F;t)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.kappaOne, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def kappaOne (F : Finset ℕ) (t : ℝ) : ℝ := sInf (logMajorantCosts F t)
/-- Average at the T positive multiples of L. Local copy of ErdosProblems.Erdos257.PaperCompleteR8.progressionMean, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def progressionMean (L T : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ m ∈ Finset.range T, f ((m + 1) * L)) / (T : ℝ)
/-- The paper's `ℙ_ℓ(U_F > 1)`: uniform sampling of `N = ℓ m` over one period `Q/ℓ` of `m ↦ U_F(ℓ m)`. For `ℓ ∣ Q` the sampled points `ℓ, 2ℓ, …, Q` are a complete set of representatives of the multiples of `ℓ` modulo `Q`, so this is `ℙ(U_F(N) > 1 | ℓ ∣ N)` for `N` uniform modulo `Q`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.condExceedProb, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def condExceedProb (F : Finset ℕ) (ℓ : ℕ) : ℝ :=
  progressionMean ℓ (F.lcm id / ℓ) (exceedInd F)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- The integer half carry attached to a support A, namely the binary affine orbit started at 1 and driven by the divisor incidence coefficients of A shifted by one, so that the orbit at n+1 is twice the orbit at n minus the number of divisors of n+2 lying in A; the shift and the recursion index compose, so the coefficient consumed at step n+1 is the one at n+2. -/
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1
end PalomarCorpus.E257_38.Shared

namespace PalomarCorpus.E257.PaperStatementsN
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_38.Shared (affineBinaryOrbit integerHalfCarry supportCoeff)
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
/-- The value coded by a set of positive exponents. The sequence index is zero-based while the exponent supplied to the weight is `k+1`. Local copy of Erdos249257.positiveMersenneSupportValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
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
end PalomarCorpus.E257.PaperStatementsN

namespace PalomarCorpus.E257.PaperStatementsL
open Filter
open Set
open Topology
export PalomarCorpus.E257_38.Shared (affineBinaryOrbit integerHalfCarry supportCoeff)
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- States prop:strip-equiv from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_relaxed_constant_six_every_depth in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_relaxed_constant_six_every_depth
    (A : Set ℕ) (hone : 1 ∉ A) (hvalue : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (M : ℕ) (hM : 1 ≤ M) :
    |(integerHalfCarry A (M - 1) : ℝ)| ≤ 2 * (Nat.sqrt M : ℝ) + 6 := by
  sorry
end PalomarCorpus.E257.PaperStatementsL

namespace PalomarCorpus.E257.PaperStatementsAC
open Finset
export PalomarCorpus.E257_38.Shared (condExceedProb divisorMajorantCost exceedInd frameLcm framePotential incidenceCount kappaOne kernelWeight logMajorantCosts progressionMean)
/-- Average the progression averages over R ≤ j < R+M, T=2^j. Local copy of ErdosProblems.Erdos257.PaperCompleteR8.dyadicMean, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicMean (L R M : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.Ico R (R + M), progressionMean L (2 ^ j) f) / (M : ℝ)
/-- States thm:257-logarithmic-counterexample from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.arithmetic_logarithmic_counterexample in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem arithmetic_logarithmic_counterexample (H : ℕ) (hH : 2 ≤ H) (A₀ : ℝ) (hA₀ : 0 ≤ A₀) :
    ∃ (L : ℕ) (F : Finset ℕ),
      0 < L ∧ Squarefree L ∧ F.Nonempty ∧ (0 : ℕ) ∉ F ∧
      (∀ a ∈ F, 0 < a ∧ Squarefree a) ∧
      (∀ a ∈ F, max (L : ℝ) A₀ < (a : ℝ)) ∧
      L ∣ F.lcm id ∧
      kappaOne F 1 ≤ 30 * Real.log 2 / (H : ℝ) ∧
      1 - Real.exp (-1) ≤ condExceedProb F L ∧
      ∃ R : ℕ, 1 / 2 < dyadicMean L R L (exceedInd F) := by
  sorry
/-- States prop:257-logarithmic-initial-interval from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.logarithmic_initial_interval in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem logarithmic_initial_interval (F : Finset ℕ) (hFne : F.Nonempty) (hF : 0 ∉ F)
    (X : ℕ) (hX : 1 ≤ X) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card : ℝ)) / (X : ℝ)
      ≤ 2 / Real.log (4 / 3 : ℝ) * kappaOne F t := by
  sorry
/-- States thm:257-logarithmic-counterexample from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.no_absolute_dyadic_kappaOne_constant in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_absolute_dyadic_kappaOne_constant :
    ¬ ∃ C : ℝ, ∀ (F : Finset ℕ), F.Nonempty → (0 : ℕ) ∉ F →
      ∀ (L M : ℕ), 0 < L → 0 < M → ∀ (R : ℕ) (t : ℝ), 0 < t → t ≤ 1 →
        dyadicMean L R M (fun N => if t < framePotential F N then (1 : ℝ) else 0)
          ≤ C * (1 + (L : ℝ) / (M : ℝ)) * kappaOne F t := by
  sorry
end PalomarCorpus.E257.PaperStatementsAC

namespace PalomarCorpus.E257.PaperStructuresBS
open Finset
export PalomarCorpus.E257_38.Shared (condExceedProb divisorMajorantCost exceedInd frameLcm framePotential incidenceCount kappaOne kernelWeight logMajorantCosts progressionMean)
/-- Local definition finiteCoverCost, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def finiteCoverCost (N : ℕ) (weight exponent : ℕ → ℝ) (coefficient : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    (∑' d : ℕ, coefficient j d / (d : ℝ)) / (weight j ^ exponent j)
      / ((2 : ℝ) ^ exponent j - 1)
/-- Local definition finiteLogCoverCosts, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def finiteLogCoverCosts (A : Set ℕ) : Set ℝ :=
  {K : ℝ | ∃ (N : ℕ) (frame : ℕ → Finset ℕ) (weight exponent : ℕ → ℝ)
      (coefficient : ℕ → ℕ → ℝ),
    (∀ j, 0 ∉ frame j) ∧
    (∀ j, j < N → 0 < weight j) ∧
    (∑ j ∈ Finset.range N, weight j = 1) ∧
    (∀ j, 0 < exponent j ∧ exponent j ≤ 1) ∧
    (∀ j d, 0 < d → 0 ≤ coefficient j d) ∧
    (∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))) ∧
    (∀ a ∈ A, ∃ j, j < N ∧ a ∈ frame j) ∧
    (∀ j n, 0 < n →
      (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j
        ≤ ∑ d ∈ n.divisors, coefficient j d) ∧
    K = finiteCoverCost N weight exponent coefficient}
/-- Arbitrary weight positive cover data on a prescribed support A: finite frames avoiding 0, strictly positive frame weights summing to 1, exponents alpha j with 0 < alpha j and alpha j at most 1, nonnegative coefficients with convergent columns, the requirement that every element of A lies in some frame, the divisor majorisation of the fractional frame incidence by the coefficient divisor sums, and convergence of the logarithmic budget whose j th term is the frame cost divided by the weight raised to alpha j and by 2 raised to alpha j minus 1. -/
structure LogBudgetCover (A : Set ℕ) where
  frame : ℕ → Finset ℕ
  weight : ℕ → ℝ
  exponent : ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  frame_positive : ∀ j, 0 ∉ frame j
  weight_positive : ∀ j, 0 < weight j
  weight_sum : HasSum weight 1
  exponent_bounds : ∀ j, 0 < exponent j ∧ exponent j ≤ 1
  coefficient_nonneg : ∀ j d, 0 < d → 0 ≤ coefficient j d
  column_summable : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))
  covers : ∀ a ∈ A, ∃ j, a ∈ frame j
  majorises : ∀ j n, 0 < n →
    (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j ≤
      ∑ d ∈ n.divisors, coefficient j d
  budget_summable : Summable (fun j =>
    (∑' d : ℕ, coefficient j d / (d : ℝ)) /
      (weight j ^ exponent j) / ((2 : ℝ) ^ exponent j - 1))
/-- The cost C j of frame j of a positive cover, namely the sum over d of c j d divided by d; the d = 0 summand is zero because division by zero is zero here. -/
noncomputable def LogBudgetCover.cost {A : Set ℕ} (C : LogBudgetCover A) : ℝ :=
  ∑' j, (∑' d : ℕ, C.coefficient j d / (d : ℝ)) /
    (C.weight j ^ C.exponent j) / ((2 : ℝ) ^ C.exponent j - 1)
/-- Local definition admissibleLogCoverCosts, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def admissibleLogCoverCosts (A : Set ℕ) : Set ℝ :=
  Set.range (fun C : LogBudgetCover A => C.cost)
/-- Local definition paperCoverCost, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def paperCoverCost (A : Set ℕ) : ℝ :=
  sInf (admissibleLogCoverCosts A ∪ finiteLogCoverCosts A)
/-- States cor:257-logarithmic-separation, eq:257-arithmetic-cover-lower from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.exists_support_paperCoverCost_ge in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_support_paperCoverCost_ge (H : ℕ) (hH : 2 ≤ H) :
    ∃ F : Finset ℕ, F.Nonempty ∧ (0 : ℕ) ∉ F ∧
      1 - Real.exp (-1) ≤ paperCoverCost (F : Set ℕ) ∧
      kappaOne F 1 ≤ 30 * Real.log 2 / (H : ℝ) := by
  sorry
/-- States cor:257-logarithmic-separation, eq:257-arithmetic-cover-lower from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.no_absolute_paperCoverCost_kappaOne_constant in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_absolute_paperCoverCost_kappaOne_constant :
    ¬ ∃ C : ℝ, ∀ F : Finset ℕ, F.Nonempty → (0 : ℕ) ∉ F →
      paperCoverCost (F : Set ℕ) ≤ C * kappaOne F 1 := by
  sorry
/-- States cor:257-logarithmic-separation, eq:257-arithmetic-cover-lower from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.sup_condExceedProb_le_paperCoverCost in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sup_condExceedProb_le_paperCoverCost (F : Finset ℕ) (hF : 0 ∉ F)
    (hne : (F.lcm id).divisors.Nonempty) :
    (F.lcm id).divisors.sup' hne (fun ℓ => condExceedProb F ℓ)
      ≤ paperCoverCost (F : Set ℕ) := by
  sorry
end PalomarCorpus.E257.PaperStructuresBS
