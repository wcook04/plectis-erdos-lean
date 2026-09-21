/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257ac

Every non-theorem declaration of `PalomarCorpus/E257ac/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset

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
/-- Average at the T positive multiples of L. Local copy of ErdosProblems.Erdos257.PaperCompleteR8.progressionMean, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def progressionMean (L T : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ m ∈ Finset.range T, f ((m + 1) * L)) / (T : ℝ)
/-- The literal modular atom requested in mandate 1a. Local copy of ErdosProblems.Erdos257.PaperCompleteR8.kernelWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def kernelWeight (B : ℝ) (d n : ℕ) : ℝ :=
  B ^ (n % d) / (B ^ d - 1)
/-- The finite positive frame potential. Local copy of ErdosProblems.Erdos257.PaperCompleteR8.framePotential, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def framePotential (F : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ a ∈ F, kernelWeight 2 a N
/-- The indicator of the paper's event `{U_F > 1}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.exceedInd, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exceedInd (F : Finset ℕ) (N : ℕ) : ℝ := if 1 < framePotential F N then 1 else 0
/-- The paper's `ℙ_ℓ(U_F > 1)`: uniform sampling of `N = ℓ m` over one period `Q/ℓ` of `m ↦ U_F(ℓ m)`. For `ℓ ∣ Q` the sampled points `ℓ, 2ℓ, …, Q` are a complete set of representatives of the multiples of `ℓ` modulo `Q`, so this is `ℙ(U_F(N) > 1 | ℓ ∣ N)` for `N` uniform modulo `Q`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.condExceedProb, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def condExceedProb (F : Finset ℕ) (ℓ : ℕ) : ℝ :=
  progressionMean ℓ (F.lcm id / ℓ) (exceedInd F)
/-- The paper's modulus `Q = lcm F`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.frameLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def frameLcm (F : Finset ℕ) : ℕ := F.lcm id
/-- The paper's divisor-incidence count `f_F(n) = #{a ∈ F : a ∣ n}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.incidenceCount, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def incidenceCount (F : Finset ℕ) (n : ℕ) : ℕ := (F.filter (fun a => a ∣ n)).card
/-- Cost of a finitely supported nonnegative divisor majorant. Local copy of ErdosProblems.Erdos257.divisorMajorantCost, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def divisorMajorantCost (D : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, c d / d
/-- The costs of the admissible positive logarithmic divisor majorants of `(F, t)`: the feasible set of the paper's programme (display 9.185). Local copy of ErdosProblems.Erdos257.PaperCompleteR21.logMajorantCosts, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def logMajorantCosts (F : Finset ℕ) (t : ℝ) : Set ℝ :=
  {K : ℝ | ∃ c : ℕ → ℝ, (∀ d, 0 ≤ c d) ∧
    (∀ s ∈ (frameLcm F).divisors,
        Real.log (1 + (incidenceCount F s : ℝ) / t) ≤ ∑ d ∈ s.divisors, c d) ∧
    K = divisorMajorantCost (frameLcm F).divisors c}
/-- The paper's `κ₁(F;t)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.kappaOne, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def kappaOne (F : Finset ℕ) (t : ℝ) : ℝ := sInf (logMajorantCosts F t)
/-- Average the progression averages over R ≤ j < R+M, T=2^j. Local copy of ErdosProblems.Erdos257.PaperCompleteR8.dyadicMean, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicMean (L R M : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.Ico R (R + M), progressionMean L (2 ^ j) f) / (M : ℝ)
end PalomarCorpus.E257.PaperStatementsAC
