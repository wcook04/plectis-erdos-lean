/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_20

Every non-theorem declaration of `PalomarCorpus/E257_20/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset
open Set
open scoped BigOperators
open Filter
open Topology
open Matrix
open scoped ENNReal
open MeasureTheory

namespace PalomarCorpus.E257_20.Shared
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The Mersenne tail beyond rank n, namely the sum over k at least 0 of the Mersenne weight at n+k+1. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- The positive gap between one Mersenne weight and the tail after it. Local copy of Erdos249257.mersenneGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneGap (n : ℕ) : ℝ :=
  mersenneWeight n - mersenneTail n
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
end PalomarCorpus.E257_20.Shared

namespace PalomarCorpus.E257.PaperStatementsAC
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
end PalomarCorpus.E257.PaperStatementsAC

namespace PalomarCorpus.E257.PaperStatementsI
open Set
open scoped BigOperators
open Filter
open Topology
export PalomarCorpus.E257_20.Shared (supportCoeff)
/-- The exact binary affine orbit driven by the fresh coefficient word `a`. Local copy of Erdos249257.affineBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- The integer carry whose state at time `N` is the packet's `K_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.integerHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1
/-- The canonical integer half carry measured relative to the signed Möbius solution. Index `N` corresponds to the packet's state `e_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1
/-- The two fresh coefficient rows, measured relative to the three units contributed by the centred recurrence itself. Local copy of Erdos249257.pairedCenteredForcing, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def pairedCenteredForcing (A : Set ℕ) (N : ℕ) : ℤ :=
  2 * (supportCoeff A (N + 2) : ℤ) +
    (supportCoeff A (N + 3) : ℤ) - 3
end PalomarCorpus.E257.PaperStatementsI

namespace PalomarCorpus.E257.PaperStatementsAA
end PalomarCorpus.E257.PaperStatementsAA

namespace PalomarCorpus.E257.PaperStatementsAB
open Matrix
end PalomarCorpus.E257.PaperStatementsAB

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_20.Shared (mersenneGap mersenneTail mersenneWeight)
end PalomarCorpus.E257.PaperStatementsAM

namespace PalomarCorpus.E257.PaperStatementsAH
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_20.Shared (mersenneGap mersenneTail mersenneWeight)
end PalomarCorpus.E257.PaperStatementsAH

namespace PalomarCorpus.E257.PaperStatementsAL
open Filter
open Set
open Topology
export PalomarCorpus.E257_20.Shared (supportCoeff)
/-- A Boolean support word through exponent `N`. Index zero is retained so restriction is literal; admissibility forces exponents zero and one off. Local copy of Erdos249257.HalfCarryReachability.HalfWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool
/-- The set represented by a finite Boolean word. Local copy of Erdos249257.HalfCarryReachability.wordSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}
/-- Append one Boolean bit to a finite half word. Local copy of Erdos249257.HalfCarrySelectedWindow.extendHalfWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def extendHalfWord {N : ℕ} (a : HalfWord N) (β : Bool) : HalfWord (N + 1) :=
  Fin.lastCases β a
end PalomarCorpus.E257.PaperStatementsAL

namespace PalomarCorpus.E257.PaperStatementsAN
open scoped BigOperators
open Filter
open Topology
export PalomarCorpus.E257_20.Shared (supportCoeff)
end PalomarCorpus.E257.PaperStatementsAN
