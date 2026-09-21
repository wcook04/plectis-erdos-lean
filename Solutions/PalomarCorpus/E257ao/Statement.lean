/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257ao

Every non-theorem declaration of `PalomarCorpus/E257ao/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Topology
open scoped ArithmeticFunction.Omega

namespace PalomarCorpus.E257.PaperStatementsAO
open Filter
open Topology
open scoped ArithmeticFunction.Omega
/-- The signed coefficient layer between exact `p`-adic levels `e-1` and `e`. Local copy of Erdos249257.MaximalOmegaLayer.primePowerLayer, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primePowerLayer (p e : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  g (p ^ e * n) - g (p ^ (e - 1) * n)
/-- The two-signature mixed layer. Further list-level iteration can use this as its checked algebraic step without committing to a factorization API. Local copy of Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mixedPrimePowerLayerTwo
    (p e q f : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  primePowerLayer q f (primePowerLayer p e g) n
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}` — the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- Integer-valued packaging of the support divisor-count coefficient. Local copy of Erdos249257.SupportDilationDifferences.supportCoeffInt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeffInt (A : Set ℕ) (n : ℕ) : ℤ :=
  supportCoeff A n
/-- Support elements with exact `p`-adic exponent `e`, after removing the prime-power layer. Local copy of Erdos249257.SupportSunflowerDichotomy.exactPrimePowerPullback, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exactPrimePowerPullback (p e : ℕ) (A : Set ℕ) : Set ℕ :=
  {d | d.Coprime p ∧ p ^ e * d ∈ A}
end PalomarCorpus.E257.PaperStatementsAO
