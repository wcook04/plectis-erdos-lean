/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249ae

Every non-theorem declaration of `PalomarCorpus/E249ae/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
/-- Explicit three-way phase form of one foreign channel. Local copy of Erdos249257.DiagonalFreshLossBridge.foreignChannelPhaseTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def foreignChannelPhaseTerm (d H s : ℕ) : ℤ :=
  if d ∣ 2 * H + s then
    ArithmeticFunction.moebius d * ((((2 * H + s) / d : ℕ) : ℤ))
  else if d ∣ H + s then
    -(ArithmeticFunction.moebius d * ((((H + s) / d : ℕ) : ℤ)))
  else 0
/-- The Mersenne denominator at exponent `n`. Local copy of Erdos249257.RadicalMobiusShadow.mersenne, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenne (n : ℕ) : ℕ := 2 ^ n - 1
/-- The integral numerator, written as its squarefree-divisor expansion. For `s ⊆ primeFactors(r)`, put `d = ∏ p ∈ s, p`. Then the summand is `(-1)^|s| (r/d) ((2^r-1)/(2^d-1))`. This is exactly the nonzero part of `Σ_{d ∣ r} μ(d) (r/d) ((2^r-1)/(2^d-1))`: nonsquarefree divisors have Möbius coefficient zero. The subset form makes that finite support explicit and keeps the definition executable without factoring irrelevant divisors. Local copy of Erdos249257.RadicalMobiusShadow.mobiusNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusNumerator (r : ℕ) : ℤ :=
  ∑ s ∈ r.primeFactors.powerset,
    (-1 : ℤ) ^ s.card *
      ((r / s.prod id : ℕ) : ℤ) *
        (((mersenne r) / (mersenne (s.prod id)) : ℕ) : ℤ)
/-- The unscaled radical shadow `B(r) = M_r / (2^r - 1)`. Local copy of Erdos249257.RadicalMobiusShadow.baseMobiusShadow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def baseMobiusShadow (r : ℕ) : ℚ :=
  Rat.divInt (mobiusNumerator r) (mersenne r : ℤ)
/-- The squarefree kernel used by the numeric shadow: the product of the distinct prime factors of `n`. For `n = 0` this convention gives `1`; all development-facing scaling theorems assume `0 < n`. Local copy of Erdos249257.RadicalMobiusShadow.squarefreeKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def squarefreeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p
/-- The numeric shadow at an arbitrary scale. By construction it only sees the distinct prime factors of `H`. Local copy of Erdos249257.RadicalMobiusShadow.numericMobiusShadow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def numericMobiusShadow (H : ℕ) : ℚ :=
  baseMobiusShadow (squarefreeKernel H) / (squarefreeKernel H : ℚ)
/-- The exact rational explicit shadow at an arbitrary scale. Local copy of Erdos249257.FullTargetPrimeAdjunctionNoGo.scaleExplicitShadowRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def scaleExplicitShadowRat (H : ℕ) : ℚ :=
  (H : ℚ) * numericMobiusShadow H
/-- Local copy of Erdos249257.FullTargetPrimeAdjunctionNoGo.scaleExplicitShadow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def scaleExplicitShadow (H : ℕ) : ℝ :=
  (scaleExplicitShadowRat H : ℝ)
/-- `Hₜ = lcm(1, ..., t)`. The interval avoids inserting zero into the finite LCM. Local copy of Erdos249257.MersenneShadowCyclotomicNoncollapse.lcmHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmHeight (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).lcm (fun n ↦ n)
/-- Prime indices in the development's upper half `(t/2, t]`. Local copy of Erdos249257.MersenneShadowCyclotomicNoncollapse.upperHalfPrimes, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def upperHalfPrimes (t : ℕ) : Finset ℕ :=
  (Finset.Ioc (t / 2) t).filter Nat.Prime
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.dyadicBase, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicBase (B : ℕ) : ℚ :=
  2 - ∑ n ∈ Finset.range (B + 1), ((n - Nat.totient n : ℕ) : ℚ) / 2 ^ n
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def gamma (B P n : ℕ) : ℕ :=
  if n ≤ B then Nat.totient n else if P ∣ n then n - 1 else n
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.discrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def discrepancy (c : ℕ → ℕ) (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((c (N + h + j + 1) : ℤ) - c (N + j + 1)) * 2 ^ (L - 1 - j)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.certificate, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certificate (c : ℕ → ℕ) (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < discrepancy c h N L % 2 ^ L ∧
  discrepancy c h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.separation, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def separation (c : ℕ → ℕ) : Prop :=
  ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, certificate c h N L
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.value, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def value (B P : ℕ) : ℚ := dyadicBase B - 1 / ((2 ^ P - 1 : ℕ) : ℚ)
/-- The natural argument of an integer-intercept affine form. Its values before the form becomes nonnegative are irrelevant to an eventual relation. Local copy of ErdosProblems.Erdos249.PaperCompleteR20.integerAffineValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerAffineValue {ι : Type*} (a : ι → ℕ) (b : ι → ℤ)
    (i : ι) (n : ℕ) : ℕ :=
  Int.toNat ((a i : ℤ) * (n : ℤ) + b i)
/-- The paper's `d`-summand of the complementary sum at height `H`, offset `s`: `μ(d)((2H+s)/d · 1_{d ∣ 2H+s} - (H+s)/d · 1_{d ∣ H+s})`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.complementSummand, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def complementSummand (d H s : ℕ) : ℚ :=
  (ArithmeticFunction.moebius d : ℚ) *
    (((2 * H + s : ℕ) : ℚ) / (d : ℚ) * (if d ∣ 2 * H + s then 1 else 0) -
      ((H + s : ℕ) : ℚ) / (d : ℚ) * (if d ∣ H + s then 1 else 0))
/-- The manuscript's Lambert value `L(f) = ∑_{n≥1} f(n)/(2ⁿ-1)`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.lambertValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lambertValue (f : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ+, f (n : ℕ) / ((2 : ℝ) ^ (n : ℕ) - 1)
/-- The manuscript's `K_d(N) = N/(d(2ᵈ-1)) + 2ᵈ/(2ᵈ-1)²`, the `d`th term of the Möbius expansion of `R_N` with its sign `μ(d)` removed. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusTermKernel (d N : ℕ) : ℝ :=
  (N : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ d - 1)) + (2 : ℝ) ^ d / (((2 : ℝ) ^ d - 1) ^ 2)
/-- Pillai's gcd-sum function, transcribed from the manuscript's defining divisor sum `P(n) = ∑_{e ∣ n} φ(e)·(n/e)`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.pillaiP, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def pillaiP (n : ℕ) : ℕ := ∑ e ∈ n.divisors, Nat.totient e * (n / e)
/-- `φ` as an `ArithmeticFunction` (`Nat.totient 0 = 0` already holds), so that the manuscript's `φ * Id` is the Dirichlet convolution it names. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.totientArith, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientArith : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩
end PalomarCorpus.E249.PaperStatementsAE
