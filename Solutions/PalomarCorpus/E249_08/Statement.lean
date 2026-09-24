/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_08

Every non-theorem declaration of `PalomarCorpus/E249_08/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial
open scoped Pointwise
open ArithmeticFunction

namespace PalomarCorpus.E249_08.Shared
/-- The closed-form cylinder mass at the coprime node `(a,b)`: `M(a,b) = 1/((2ᵃ-1)(2ᵇ-1)) = P(a ∣ X)·P(b ∣ Y)`. Local copy of GcdMomentCalculus.cylinderMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cylinderMass (a b : ℕ+) : ℝ :=
  1 / (((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1))
/-- The second Jordan totient, as the integer-valued Dirichlet convolution `μ * id²`. Local copy of Erdos249257.CyclotomicProjectionOfShadow.jordanTotientTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def jordanTotientTwo : ArithmeticFunction ℤ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℤ) *
    (ArithmeticFunction.pow 2 : ArithmeticFunction ℤ)
/-- The manuscript's Lambert value `L(f) = ∑_{n≥1} f(n)/(2ⁿ-1)`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.lambertValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lambertValue (f : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ+, f (n : ℕ) / ((2 : ℝ) ^ (n : ℕ) - 1)
/-- `1 + X^d + ... + X^((q - 1)d)`. Local copy of Erdos249257.RepunitMobiusNumerator.spacedRepunit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def spacedRepunit (d q : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range q, Polynomial.monomial (d * j) 1
/-- The divisor-signed polynomial numerator. For positive `r`, evaluation at `X = 2` is the common-denominator Möbius numerator; the public bridge below is stated only on the formal development.s squarefree boundary. Local copy of Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusNumeratorPolynomial (r : ℕ) : ℤ[X] :=
  ∑ d ∈ r.divisors,
    Polynomial.C (ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))) *
      spacedRepunit d (r / d)
end PalomarCorpus.E249_08.Shared

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
export PalomarCorpus.E249_08.Shared (lambertValue)
/-- The manuscript's `K_d(N) = N/(d(2ᵈ-1)) + 2ᵈ/(2ᵈ-1)²`, the `d`th term of the Möbius expansion of `R_N` with its sign `μ(d)` removed. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusTermKernel (d N : ℕ) : ℝ :=
  (N : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ d - 1)) + (2 : ℝ) ^ d / (((2 : ℝ) ^ d - 1) ^ 2)
end PalomarCorpus.E249.PaperStatementsAE

namespace PalomarCorpus.E249.PaperStatementsAY
open scoped BigOperators
export PalomarCorpus.E249_08.Shared (cylinderMass)
end PalomarCorpus.E249.PaperStatementsAY

namespace PalomarCorpus.E249.PaperStatementsAK
export PalomarCorpus.E249_08.Shared (cylinderMass)
end PalomarCorpus.E249.PaperStatementsAK

namespace PalomarCorpus.E249.PaperStatementsB
export PalomarCorpus.E249_08.Shared (cylinderMass)
/-- The depth-`d` finite unfolding of the mediant recursion: sum the stop mass `1/(2^{a+b}-1)` at every node of the first `d` generations of the subtree rooted at `(a,b)`, under the children `(a+b, b)` and `(a, a+b)`. Local copy of GcdMomentCalculus.sternBrocotDepthMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sternBrocotDepthMass : ℕ → ℕ+ → ℕ+ → ℝ
  | 0, _, _ => 0
  | (dp + 1), a, b =>
      1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
        + sternBrocotDepthMass dp (a + b) b + sternBrocotDepthMass dp a (a + b)
end PalomarCorpus.E249.PaperStatementsB

namespace PalomarCorpus.E249.PaperStatementsAC
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial
export PalomarCorpus.E249_08.Shared (jordanTotientTwo mobiusNumeratorPolynomial spacedRepunit)
/-- The natural coefficient in the gcd-word presentation. Local copy of Erdos249257.RepunitMobiusNumerator.gcdWordCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def gcdWordCoeff (r k : ℕ) : ℕ :=
  (r / r.gcd k) * (r.gcd k).totient
end PalomarCorpus.E249.PaperStatementsAC

namespace PalomarCorpus.E249.PaperStatementsAQ
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial
export PalomarCorpus.E249_08.Shared (jordanTotientTwo mobiusNumeratorPolynomial spacedRepunit)
/-- Integer evaluation `Φ_m(2)`. Local copy of Erdos249257.CyclotomicProjectionOfShadow.cyclotomicEval, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cyclotomicEval (m : ℕ) : ℤ :=
  (Polynomial.cyclotomic m ℤ).eval 2
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
end PalomarCorpus.E249.PaperStatementsAQ

namespace PalomarCorpus.E249.PaperStatementsAS
open scoped ArithmeticFunction.Moebius
open scoped BigOperators
open scoped Pointwise
open scoped Polynomial
export PalomarCorpus.E249_08.Shared (mobiusNumeratorPolynomial spacedRepunit)
end PalomarCorpus.E249.PaperStatementsAS

namespace PalomarCorpus.E249.PaperStatementsBA
open scoped BigOperators
open ArithmeticFunction
export PalomarCorpus.E249_08.Shared (lambertValue)
/-- The Euler totient as an integer-valued arithmetic function. Local copy of MersenneLambertLadder.totientZ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientZ : ArithmeticFunction ℤ :=
  ⟨fun n => (Nat.totient n : ℤ), by simp⟩
/-- **The primitive-conductor weight** `A = φ * μ` (Dirichlet convolution). `A(n)` counts the primitive Dirichlet characters of conductor `n` (OEIS A007431); it is multiplicative, nonnegative, vanishes exactly on `n ≡ 2 (mod 4)`, and satisfies `A(p) = p - 2`, `A(p^e) = (p-1)²·p^(e-2)`. Local copy of MersenneLambertLadder.primWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primWeight : ArithmeticFunction ℤ := totientZ * moebius
end PalomarCorpus.E249.PaperStatementsBA
