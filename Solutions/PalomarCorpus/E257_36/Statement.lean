/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_36

Every non-theorem declaration of `PalomarCorpus/E257_36/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Set
open ArithmeticFunction
open scoped ENNReal
open MeasureTheory
open Topology
open Finset

namespace PalomarCorpus.E257_36.Shared
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
end PalomarCorpus.E257_36.Shared

namespace PalomarCorpus.E257.PaperStatementsBD
open Filter
open Set
/-- The radius of the balanced-pulse family at location `m`. Local copy of Erdos249257.balancedPulseRadius, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def balancedPulseRadius (m : ℕ) : ℕ := (m + 1) / 2
/-- A two-site pulse whose mass can be moved from position `m` to `m+1` without changing its binary-series value. Local copy of Erdos249257.balancedPulseCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def balancedPulseCoeff (m r : ℕ) : ℕ → ℕ := fun n ↦
  if n = m then balancedPulseRadius m - r
  else if n = m + 1 then 2 * r
  else 0
/-- The displayed balanced-pulse family at location `m`: the coefficient sequences `balancedPulseCoeff m r` for the admissible parameters `0 ≤ r ≤ balancedPulseRadius m`. These are exactly the parameters for which the pulse is mass preserving and stays in the linear-growth class (`balancedPulseCoeff_le_self`). Local copy of ErdosProblems.Erdos257.PaperCompleteR21.balancedPulseFamily, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def balancedPulseFamily (m : ℕ) : Set (ℕ → ℕ) :=
  balancedPulseCoeff m '' Set.Iic (balancedPulseRadius m)
end PalomarCorpus.E257.PaperStatementsBD

namespace PalomarCorpus.E257.PaperStatementsAQ
open ArithmeticFunction
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_36.Shared (mersenneWeight)
/-- The Boolean support term selected by the negative Möbius sign. Local copy of Erdos249257.MobiusSignSupportNoGo.negativeMobiusTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def negativeMobiusTerm (d : ℕ+) : ℝ :=
  if moebius (d : ℕ) = -1 then mersenneWeight (d : ℕ) else 0
/-- The positive Möbius tail, with the exceptional `d = 1` term removed. Local copy of Erdos249257.MobiusSignSupportNoGo.positiveMobiusTailTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMobiusTailTerm (d : ℕ+) : ℝ :=
  if moebius (d : ℕ) = 1 ∧ (d : ℕ) ≠ 1 then mersenneWeight (d : ℕ) else 0
end PalomarCorpus.E257.PaperStatementsAQ

namespace PalomarCorpus.E257.PaperStatementsR
open ArithmeticFunction
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_36.Shared (mersenneWeight)
/-- The exact rational Mersenne weight `1 / (2^n - 1)`. Its meaningful support indices are positive; at index zero Lean's division convention gives zero. Local copy of Erdos249257.mersenneWeightRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
/-- A finite rational upper enclosure for `mersenneTail n`. The lookahead parameter exposes a family of exact rational bounds without comparing an infinite real tail numerically. Local copy of Erdos249257.mersenneTailUpperRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTailUpperRat (n lookahead : ℕ) : ℚ :=
  (∑ k ∈ Finset.range lookahead, mersenneWeightRat (n + k + 1))
    + 2 * mersenneWeightRat (n + lookahead + 1)
/-- Exact rational version of the greedy residual. Local copy of Erdos249257.greedyMersenneRemainderRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n
/-- A decidable finite certificate: an exact rational upper enclosure is no larger than the exact rational greedy residual. Local copy of Erdos249257.CertifiedGreedyMersenneDeath, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CertifiedGreedyMersenneDeath
    (x : ℚ) (level lookahead : ℕ) : Prop :=
  mersenneTailUpperRat level lookahead
    ≤ greedyMersenneRemainderRat x level
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- The finite Erdős partial sum `∑_{n ∈ F} 1 / (b ^ n - 1)` as a rational number, stated with subtraction in `ℚ` so the statement reads exactly like the mathematical series. Local copy of Erdos249257.finiteErdosSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteErdosSum (F : Finset Nat) (b : Nat) : Rat :=
  ∑ n ∈ F, 1 / ((b : Rat) ^ n - 1)
/-- The value coded by a set of positive exponents. The sequence index is zero-based while the exponent supplied to the weight is `k+1`. Local copy of Erdos249257.positiveMersenneSupportValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
end PalomarCorpus.E257.PaperStatementsR

namespace PalomarCorpus.E257.PaperStatementsP
open Finset
/-- The window step `a_n = φ(n+h) - φ(n)` driving the carry recurrence. Local copy of Erdos249257.TotientTailPeriodKiller.deltaTotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- The integer carry orbit launched from candidate `d` at position `N`: `orbit 0 = d`, `orbit (i+1) = 2·orbit i - a_{N+i+1}`. If `D_h(N)` is the integer `d`, this orbit equals `D_h(N+i)` forever. Local copy of Erdos249257.TotientTailPeriodKiller.carryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)
/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`: the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
/-- `periodLcm t = lcm(1, …, t)`: the universal period at scale `t`. Every primitive period `h₀ ≤ t` divides it. Local copy of Erdos249257.TotientTailPeriodKiller.periodLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
/-- The **carry-survivor certificate**: every integer candidate in the initial box `|d| ≤ N+h+1`, enumerated as `d = j - (N+h+1)` for `j < 2·(N+h+1)+1`, provably escapes the strip `|·| ≤ N+i+h+1` within `K` steps (escape stated as a two-sided disjunction). Finitely many candidates, finitely many steps: decidable. Local copy of Erdos249257.TotientTailPeriodKiller.survivorKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def survivorKill (h N K : ℕ) : Prop :=
  ∀ j ∈ Finset.range (2 * (N + h + 1) + 1),
    ∃ i ∈ Finset.range (K + 1),
      carryOrbit h N ((j : ℤ) - (N + h + 1)) i ≤ -(N + i + h + 2 : ℤ)
        ∨ (N + i + h + 2 : ℤ) ≤ carryOrbit h N ((j : ℤ) - (N + h + 1)) i
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
end PalomarCorpus.E257.PaperStatementsP

namespace PalomarCorpus.E257.PaperStatementsAA
end PalomarCorpus.E257.PaperStatementsAA
