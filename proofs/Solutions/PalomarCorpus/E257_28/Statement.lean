/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_28

Every non-theorem declaration of `PalomarCorpus/E257_28/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Set
open scoped BigOperators
open Filter
open scoped ENNReal
open MeasureTheory
open Topology
open Finset

namespace PalomarCorpus.E257_28.Shared
/-- The local integer Mersenne quotient at binary scale M and rank d, namely the natural number quotient of 2 to the power M by 2 to the power d minus 1; at d = 0 the divisor is 0 and the value is 0. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- The total local quotient carried by a finite set D of ranks at binary scale M, namely the sum over d in D of the local Mersenne quotient at M and d. -/
noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d
/-- The carry left after reading the nonterminating binary expansion of `2⁻ᵏ` through place `M` and subtracting the quotient contributions of `D`. The theorem below proves that the truncating natural subtraction is honest in the endpoint situation where it is used. Local copy of Erdos249257.localBinarySuffix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localBinarySuffix (D : Finset ℕ) (k M : ℕ) : ℕ :=
  2 ^ (M - k) - localPrefixQuotient D M - 1
/-- The rational Mersenne weight 1 divided by 2 to the power n minus 1, taken in the rationals; at n = 0 the value is 0. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
end PalomarCorpus.E257_28.Shared

namespace PalomarCorpus.E257.PaperStatementsF
open Set
open scoped BigOperators
open Filter
open scoped ENNReal
open MeasureTheory
open Topology
export PalomarCorpus.E257_28.Shared (localBinarySuffix localMersenneQuotient localPrefixQuotient mersenneWeightRat)
/-- Exact rational version of the greedy residual. Local copy of Erdos249257.greedyMersenneRemainderRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n
/-- Positive exponents selected through a finite exact-rational greedy run. Local copy of Erdos249257.greedyMersennePrefixRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersennePrefixRat (x : ℚ) (n : ℕ) : Finset ℕ :=
  (((Finset.range n).filter fun k =>
      mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k).image
    fun k => k + 1)
/-- Local copy of Erdos249257.halfGreedyPrefixSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfGreedyPrefixSupport (n : ℕ) : Finset ℕ :=
  greedyMersennePrefixRat (1 / 2 : ℚ) n
/-- The genuinely residual part of the predecessor supply: only a skipped rank immediately before an actual take is exposed. Consecutive skipped ranks have a uniform finite-lookahead proof below. Local copy of Erdos249257.HalfGreedyPreTakePrecriticalSuffixSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfGreedyPreTakePrecriticalSuffixSupply : Prop :=
  ∀ c : ℕ,
    6 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    mersenneWeightRat (c + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) c →
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3)
/-- The minimal actual-orbit form of the socket: the quotient lower bound is required only when rank `c` is genuinely skipped by the rational half-greedy orbit. Local copy of Erdos249257.HalfGreedySkippedCriticalQuotientSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfGreedySkippedCriticalQuotientSupply : Prop :=
  ∀ c : ℕ,
    4 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    2 ^ ((2 * c - 2) - 1) ≤
      localPrefixQuotient
        (insert c (halfGreedyPrefixSupport (c - 1))) (2 * c - 2)
/-- A one-row-earlier form of the actual skipped-rank socket. At endpoint `2c-3` the relevant binary suffix has half the critical capacity. Local copy of Erdos249257.HalfGreedySkippedPrecriticalSuffixSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfGreedySkippedPrecriticalSuffixSupply : Prop :=
  ∀ c : ℕ,
    4 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3)
end PalomarCorpus.E257.PaperStatementsF

namespace PalomarCorpus.E257.PaperStatementsAA
end PalomarCorpus.E257.PaperStatementsAA

namespace PalomarCorpus.E257.PaperStatementsAR
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators
export PalomarCorpus.E257_28.Shared (localBinarySuffix localMersenneQuotient localPrefixQuotient mersenneWeightRat)
/-- An exact finite Boolean quotient row at endpoint `n`. Local copy of Erdos249257.ExactLocalMersenneHalfRow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ExactLocalMersenneHalfRow (n : ℕ) : Prop :=
  ∃ D : Finset ℕ,
    (∀ d ∈ D, 2 ≤ d ∧ d ≤ n) ∧
      localPrefixQuotient D n = 2 ^ (n - 1) - 1
/-- The exact finite Mersenne value of a Boolean lower support. Local copy of Erdos249257.localMersennePrefixValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d
/-- The source-current fractional part of `2^M / (2^d - 1)` for `d ≥ 2`. The exponent is reduced modulo `d` before the division. Local copy of Erdos249257.localMersenneFraction, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneFraction (M d : ℕ) : ℚ :=
  ((2 ^ (M % d) : ℕ) : ℚ) / ((2 ^ d - 1 : ℕ) : ℚ)
/-- Sum of the corresponding fractional contributions. Local copy of Erdos249257.localFractionMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localFractionMass (D : Finset ℕ) (M : ℕ) : ℚ :=
  ∑ d ∈ D, localMersenneFraction M d
end PalomarCorpus.E257.PaperStatementsAR

namespace PalomarCorpus.E257.PaperStatementsAD
open scoped BigOperators
export PalomarCorpus.E257_28.Shared (localMersenneQuotient)
end PalomarCorpus.E257.PaperStatementsAD

namespace PalomarCorpus.E257.PaperStatementsBE
open Finset
/-- `j` indexes the smallest power `2^(d-j+1)` that is still at least `E`. The final disjunction handles the last index, where there is no next power in the band family. Local copy of Erdos249257.HalfUpperResetCriticalBand.CriticalDyadicBandIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CriticalDyadicBandIndex (d E j : ℕ) : Prop :=
  j ≤ d ∧
    E ≤ 2 ^ (d - j + 1) ∧
      (j = d ∨ 2 ^ (d - (j + 1) + 1) < E)
/-- Avoidance of every width-`2(d+j)` interval immediately below the dyadic power indexed by `j`. Local copy of Erdos249257.HalfUpperResetCriticalBand.DyadicBandEscape, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicBandEscape (d E : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ d →
    2 ^ (d - j + 1) < E ∨ E + 2 * (d + j) ≤ 2 ^ (d - j + 1)
end PalomarCorpus.E257.PaperStatementsBE
