/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_05

Every non-theorem declaration of `PalomarCorpus/E249_05/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Finset
open Filter Topology
open scoped ArithmeticFunction.Moebius
open scoped Polynomial

namespace PalomarCorpus.E249_05.Shared
/-- `Hₜ = lcm(1, ..., t)`. The interval avoids inserting zero into the finite LCM. Local copy of Erdos249257.MersenneShadowCyclotomicNoncollapse.lcmHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmHeight (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).lcm (fun n ↦ n)
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
/-- The binary totient tail `R_N = ∑_{j ≥ 1} φ(N + j) / 2 ^ j`, a real number satisfying `2 ^ N S = Φ_N + R_N`, where `S = ∑_{n ≥ 1} φ(n) / 2 ^ n` and `Φ_N = ∑_{n ≤ N} φ(n) 2 ^ (N - n)` is an integer. It obeys `0 < R_N ≤ N + 1` for `N ≥ 1`. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
end PalomarCorpus.E249_05.Shared

namespace PalomarCorpus.E249.PaperStatementsAK
end PalomarCorpus.E249.PaperStatementsAK

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
export PalomarCorpus.E249_05.Shared (baseMobiusShadow lcmHeight mersenne mobiusNumerator numericMobiusShadow squarefreeKernel)
/-- Prime indices in the development's upper half `(t/2, t]`. Local copy of Erdos249257.MersenneShadowCyclotomicNoncollapse.upperHalfPrimes, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def upperHalfPrimes (t : ℕ) : Finset ℕ :=
  (Finset.Ioc (t / 2) t).filter Nat.Prime
/-- Pillai's gcd-sum function, transcribed from the manuscript's defining divisor sum `P(n) = ∑_{e ∣ n} φ(e)·(n/e)`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.pillaiP, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def pillaiP (n : ℕ) : ℕ := ∑ e ∈ n.divisors, Nat.totient e * (n / e)
/-- `φ` as an `ArithmeticFunction` (`Nat.totient 0 = 0` already holds), so that the manuscript's `φ * Id` is the Dirichlet convolution it names. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.totientArith, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientArith : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩
end PalomarCorpus.E249.PaperStatementsAE

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
open Finset
export PalomarCorpus.E249_05.Shared (totientTail)
end PalomarCorpus.E249.PaperStatementsAX

namespace PalomarCorpus.E249.CompleteKernelBases
open Filter Topology
open scoped BigOperators
/-- The rational-valued sequence n ↦ φ(k^j n + r). -/
noncomputable def allBaseTotientKernelSeq (k j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (k ^ j * n + r)
/-- All base-k kernel indices at levels zero through e, inclusive. -/
noncomputable abbrev AllBaseThroughLevelIndex (k e : ℕ) := Σ j : Fin (e + 1), Fin (k ^ j.val)
/-- All rational-valued base-k totient subsequences through level e. -/
noncomputable def allBaseThroughLevelFamily (k e : ℕ) : AllBaseThroughLevelIndex k e → ℕ → ℚ
  | ⟨j, r⟩ => allBaseTotientKernelSeq k j.val r.val
/-- The dyadic section `n ↦ φ(2 ^ j n + r)` of Euler's totient at level `j` and residue `r`, with values in `ℚ` through the cast from `ℕ`. -/
noncomputable def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)
/-- Index type for the canonical duplicate-free family of dyadic totient sections through level `e`: a left index `i ∈ Fin 2` names the zero-residue channel `n ↦ φ(2 ^ i n)`, and a right index `⟨j, r⟩` with `j < e` and `r < 2 ^ j` names the odd residue `2 r + 1` at level `j + 1`, so the type has `2 ^ e + 1` elements. -/
noncomputable abbrev TotientCanonicalIndex (e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)
/-- The canonical duplicate-free family of dyadic totient sections through level `e`: a left index `i ∈ Fin 2` gives `n ↦ φ(2 ^ i n)`, and a right index `⟨j, r⟩` gives the odd-residue channel `n ↦ φ(2 ^ (j + 1) n + 2 r + 1)`. -/
noncomputable def canonicalTotientKernelFamily (e : ℕ) :
    TotientCanonicalIndex e → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j.val + 1) (2 * r.val + 1)
/-- The dyadic kernel indices at levels zero through e, inclusive. -/
noncomputable abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)
/-- The family of rational-valued totient subsequences through dyadic level e. -/
noncomputable def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val
/-- All pairs of a dyadic level j and a residue below 2^j. -/
noncomputable abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)
/-- Every dyadic subsequence n ↦ φ(2^j n + r), viewed as a rational-valued sequence. -/
noncomputable def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val
/-- Two initial channels together with every odd-residue channel at a positive dyadic level. -/
noncomputable abbrev TotientOddCoreIndex := Fin 2 ⊕ Σ j : ℕ, Fin (2 ^ j)
/-- The two initial zero-residue channels and all odd-residue dyadic channels, as rational-valued sequences. -/
noncomputable def oddCoreTotientKernelFamily : TotientOddCoreIndex → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j + 1) (2 * r.val + 1)
end PalomarCorpus.E249.CompleteKernelBases

namespace PalomarCorpus.E249.PaperStatementsAD
open Finset
export PalomarCorpus.E249_05.Shared (totientTail)
end PalomarCorpus.E249.PaperStatementsAD

namespace PalomarCorpus.E249.PaperStatementsAQ
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial
export PalomarCorpus.E249_05.Shared (baseMobiusShadow mersenne mobiusNumerator)
/-- Integer evaluation `Φ_m(2)`. Local copy of Erdos249257.CyclotomicProjectionOfShadow.cyclotomicEval, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cyclotomicEval (m : ℕ) : ℤ :=
  (Polynomial.cyclotomic m ℤ).eval 2
/-- The unsigned cyclotomic channel modulus `|Φ_m(2)|`. Local copy of Erdos249257.CyclotomicProjectionOfShadow.cyclotomicValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cyclotomicValue (m : ℕ) : ℕ :=
  (cyclotomicEval m).natAbs
/-- `1 + X^d + ... + X^((q - 1)d)`. Local copy of Erdos249257.RepunitMobiusNumerator.spacedRepunit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def spacedRepunit (d q : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range q, Polynomial.monomial (d * j) 1
/-- The divisor-signed polynomial numerator. For positive `r`, evaluation at `X = 2` is the common-denominator Möbius numerator; the public bridge below is stated only on the formal development.s squarefree boundary. Local copy of Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusNumeratorPolynomial (r : ℕ) : ℤ[X] :=
  ∑ d ∈ r.divisors,
    Polynomial.C (ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))) *
      spacedRepunit d (r / d)
end PalomarCorpus.E249.PaperStatementsAQ

namespace PalomarCorpus.E249.PaperStatementsAR
open scoped BigOperators
open scoped Polynomial
export PalomarCorpus.E249_05.Shared (baseMobiusShadow lcmHeight mersenne mobiusNumerator numericMobiusShadow squarefreeKernel)
/-- The scalar contributed by the odd prime factors of `r`. Local copy of Erdos249257.CyclicTensorMobiusShadow.oddJordanScalar, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def oddJordanScalar (r : ℕ) : ℤ :=
  ∏ q ∈ r.primeFactors.filter (fun q => q ≠ 2), ((q : ℤ) ^ 2 - 1)
/-- `rₜ = rad(Hₜ)` using the canonical T6 squarefree kernel. Local copy of Erdos249257.MersenneShadowCyclotomicNoncollapse.lcmRadical, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmRadical (t : ℕ) : ℕ :=
  squarefreeKernel (lcmHeight t)
/-- `hₜ = Hₜ / rₜ`, the scale multiplying the radical shadow. Local copy of Erdos249257.MersenneShadowCyclotomicNoncollapse.lcmScale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmScale (t : ℕ) : ℕ :=
  lcmHeight t / lcmRadical t
end PalomarCorpus.E249.PaperStatementsAR
