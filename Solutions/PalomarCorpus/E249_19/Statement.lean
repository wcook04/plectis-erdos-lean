/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_19

Every non-theorem declaration of `PalomarCorpus/E249_19/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset
open scoped BigOperators
open Matrix
open ArithmeticFunction

namespace PalomarCorpus.E249_19.Shared
/-- Large prime-ray layers escape every prescribed finite prime support. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.FinitePrimeSupportEscape, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FinitePrimeSupportEscape (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ,
    q.Prime → Q₀ ≤ q →
      ∀ p ∈ S, p.Prime → ¬ p ∣ C (m * q)
/-- The atom of index `n` at rung `r` of the Möbius-Mersenne ladder, namely `μ(n + 1) / (2 ^ (n + 1) - 1) ^ r` with `μ` the Möbius function; the index is shifted so that `n = 0` carries the divisor `d = 1`. -/
noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)
/-- The rung `Θ_r = ∑_{d ≥ 1} μ(d) / (2 ^ d - 1) ^ r` of the Möbius-Mersenne ladder, defined as the real sum of the atoms above. The divisor convolution `φ = μ * id` gives `Θ_2 = S - 1/2` for the binary totient series `S = ∑_{n ≥ 1} φ(n) / 2 ^ n`. At `r = 0` the family is not summable and the Lean sum takes its default value `0`; every compared theorem uses the ladder only at `r ≥ 1`. -/
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n
/-- The universal period `lcm(1, 2, ..., t)`, given recursively by `periodLcm 0 = 1` and `periodLcm (t + 1) = lcm (periodLcm t) (t + 1)`. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
end PalomarCorpus.E249_19.Shared

namespace PalomarCorpus.E249.PaperStatementsAJ
export PalomarCorpus.E249_19.Shared (FinitePrimeSupportEscape)
/-- The unsigned binary cyclotomic layer `|Φ_n(2)|`. Local copy of ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCyclotomicLayer (n : ℕ) : ℕ :=
  ((Polynomial.cyclotomic n ℤ).eval (2 : ℤ)).natAbs
/-- Every rational prime divisor of a layer supplies an exact-order witness in extension degree at most `d`. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.BoundedDegreeOrderConsumer, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def BoundedDegreeOrderConsumer
    (C : ℕ → ℕ) (m d : ℕ) : Prop :=
  ∀ q p : ℕ,
    q.Prime → p.Prime → p ∣ C (m * q) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1
/-- Bounded-degree order witnesses beyond a prime-index cutoff. Unlike `BoundedDegreeOrderConsumer`, this permits the finitely many characteristic primes that occur naturally in cyclotomic layers. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.EventualBoundedDegreeOrderConsumer, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def EventualBoundedDegreeOrderConsumer
    (C : ℕ → ℕ) (m d : ℕ) : Prop :=
  ∃ Q₀ : ℕ, ∀ q p : ℕ,
    q.Prime → Q₀ ≤ q → p.Prime → p ∣ C (m * q) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1
/-- Eventual nontrivial, clean cyclotomic layers on the prime ray `m*q`. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.PrimeRayLayerSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PrimeRayLayerSupply (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∃ Q₀ : ℕ, ∀ q : ℕ,
    q.Prime → Q₀ ≤ q →
      1 < C (m * q) ∧ Nat.Coprime (C (m * q)) (m * q)
/-- The prime divisors appearing on the ray `m*q` are unbounded, even after imposing an arbitrary lower bound on the prime index `q`. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.UnboundedPrimeDivisorSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def UnboundedPrimeDivisorSupply (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ B N₀ : ℕ, ∃ q p : ℕ,
    q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsA
open Finset
export PalomarCorpus.E249_19.Shared (periodLcm)
end PalomarCorpus.E249.PaperStatementsA

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_19.Shared (periodLcm)
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAK
export PalomarCorpus.E249_19.Shared (FinitePrimeSupportEscape)
end PalomarCorpus.E249.PaperStatementsAK

namespace PalomarCorpus.E249.PaperStatementsAF
open scoped BigOperators
open Matrix
open ArithmeticFunction
export PalomarCorpus.E249_19.Shared (mobiusMersenneTerm mobiusMersenneTheta)
end PalomarCorpus.E249.PaperStatementsAF

namespace PalomarCorpus.E249.PaperStatementsBG
open scoped BigOperators
open Matrix
open ArithmeticFunction
export PalomarCorpus.E249_19.Shared (mobiusMersenneTerm mobiusMersenneTheta)
/-- The first `Y` atoms of the Möbius--Mersenne rung `r`. Local copy of ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n
/-- The rank-one strict-subrank quotient from the first `Y` atoms. Local copy of ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ :=
  mobiusMersennePrefix Y (e + 2) ^ 2 /
    mobiusMersennePrefix Y (2 * e + 2)
end PalomarCorpus.E249.PaperStatementsBG
