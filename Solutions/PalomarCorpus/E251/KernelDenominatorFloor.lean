/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.KernelDenominatorFloor
import Solutions.PalomarCorpus.E251.Shared

open scoped BigOperators

namespace PalomarCorpus.E251.KernelDenominatorFloor
export PalomarCorpus.E251.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)

noncomputable abbrev noSmallDivisor := ErdosProblems.Erdos251.noSmallDivisor
noncomputable abbrev isPrimeTD := ErdosProblems.Erdos251.isPrimeTD
noncomputable abbrev primeSumLoop := ErdosProblems.Erdos251.primeSumLoop
noncomputable abbrev certCheck := ErdosProblems.Erdos251.certCheck
noncomputable abbrev certX := ErdosProblems.Erdos251.certX
noncomputable abbrev certC := ErdosProblems.Erdos251.certC
noncomputable abbrev certU := ErdosProblems.Erdos251.certU
noncomputable abbrev certV := ErdosProblems.Erdos251.certV
noncomputable abbrev certU' := ErdosProblems.Erdos251.certU'
noncomputable abbrev certV' := ErdosProblems.Erdos251.certV'

/-- The kernel re-runs the `10^4` trial-division sieve and decides the six
conditions on the certificate literals. -/
theorem cert_10000 : certCheck certC certU certV certU' certV' certX = true :=
  ErdosProblems.Erdos251.cert_10000

/-- A passing certificate at any truncation index `c ≥ 9` forces every rational
`a / b` equal to the prime series to satisfy `v + v' ≤ b`. -/
theorem den_bound_of_certCheck (c u v u' v' X : ℕ) (hc : 9 ≤ c)
    (h : certCheck c u v u' v' X = true) :
    ∀ (a : ℤ) (b : ℕ), 0 < b → (∑' n, primeDyadicTerm n) = a / b → v + v' ≤ b :=
  ErdosProblems.Erdos251.den_bound_of_certCheck c u v u' v' X hc h

/-- Every rational `a / b` equal to `S` has `b ≥ 2^589 > 10^177`. -/
theorem kernel_denominator_floor (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b :=
  ErdosProblems.Erdos251.kernel_denominator_floor a b hb hS

/-- The same floor for the prime-gap series `S - 2` of Erdős #251. -/
theorem kernel_denominator_floor_primeGap (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeGapDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b :=
  ErdosProblems.Erdos251.kernel_denominator_floor_primeGap a b hb hS

end PalomarCorpus.E251.KernelDenominatorFloor
