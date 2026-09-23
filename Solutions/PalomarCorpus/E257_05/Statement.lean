/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_05

Every non-theorem declaration of `PalomarCorpus/E257_05/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Topology
open Set
open scoped ENNReal
open MeasureTheory
open scoped BigOperators

namespace PalomarCorpus.E257_05.Shared
/-- The base b reciprocal power subseries supported on A, namely the sum over a in A of 1 divided by b to the power a minus 1, written as an unconditional sum of the indicator of A; the exponent a = 0 contributes 0 because division by zero is zero here, so membership of 0 in A does not change the value. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The Mersenne tail beyond rank n, namely the sum over k at least 0 of the Mersenne weight at n+k+1. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- The Erdős-Borwein constant, expressed in the positive Mersenne-tail coordinate already used throughout this file. Local copy of Erdos249257.erdosBorweinMersenneConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0
end PalomarCorpus.E257_05.Shared

namespace PalomarCorpus.E257.PaperStatementsAG
open Filter
open Topology
export PalomarCorpus.E257_05.Shared (erdosSupportSeries)
end PalomarCorpus.E257.PaperStatementsAG

namespace PalomarCorpus.E257.PaperStatementsBC
open Filter
open Topology
export PalomarCorpus.E257_05.Shared (erdosSupportSeries)
end PalomarCorpus.E257.PaperStatementsBC

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_05.Shared (erdosBorweinMersenneConstant mersenneTail mersenneWeight)
end PalomarCorpus.E257.PaperStatementsAM

namespace PalomarCorpus.E257.PaperStatementsB
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_05.Shared (mersenneTail mersenneWeight)
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
end PalomarCorpus.E257.PaperStatementsB

namespace PalomarCorpus.E257.PaperStatementsAA
end PalomarCorpus.E257.PaperStatementsAA

namespace PalomarCorpus.E257.PaperStatementsAR
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators
export PalomarCorpus.E257_05.Shared (erdosBorweinMersenneConstant mersenneTail mersenneWeight)
/-- The exact integer weight contributed at seam rank `s` by selecting a proper divisor rank `d < s`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.truncatedMersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
/-- Delta for a selected prefix. This applies in particular to the integer greedy take set; the identity itself needs no greediness hypothesis. Local copy of ErdosProblems.Erdos257.PaperCompleteR20.rowDeviation, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rowDeviation (n : ℕ) (D : Finset ℕ) : ℤ :=
  (2 : ℤ)^(2*n-1) - (2 : ℤ)^(n+1) - ∑ d ∈ D, (truncatedMersenneWeight n d : ℤ)
end PalomarCorpus.E257.PaperStatementsAR
