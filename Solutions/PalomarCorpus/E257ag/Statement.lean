/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257ag

Every non-theorem declaration of `PalomarCorpus/E257ag/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Topology

namespace PalomarCorpus.E257.PaperStatementsAG
open Filter
open Topology
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- The finite Erdős partial sum `∑_{n ∈ F} 1 / (b ^ n - 1)` as a rational number, stated with subtraction in `ℚ` so the statement reads exactly like the mathematical series. Local copy of Erdos249257.finiteErdosSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteErdosSum (F : Finset Nat) (b : Nat) : Rat :=
  ∑ n ∈ F, 1 / ((b : Rat) ^ n - 1)
/-- **The signed weighted divisor coefficient** `∑_{d ∣ n} w d` for an integer weight `w : ℕ → ℤ` — the Dirichlet incidence `w * 1` with signs. At a Nat weight (cast) this is `weightedCoeff`. Local copy of Erdos249257.intWeightedCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def intWeightedCoeff (w : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, w d
/-- **The signed weighted Erdős series** `∑_a w(a)/(b^a - 1)` for an integer weight. The `a = 0` term is junk-safe (`w(0)/0 = 0`). At a cast Nat weight this is `weightedErdosSeries`; mixed-sign rational coefficient series reduce to it by clearing denominators. Local copy of Erdos249257.intWeightedErdosSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def intWeightedErdosSeries (b : ℕ) (w : ℕ → ℤ) : ℝ :=
  ∑' a : ℕ, ((w a : ℤ) : ℝ) / ((b : ℝ) ^ a - 1)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}` — the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
end PalomarCorpus.E257.PaperStatementsAG
