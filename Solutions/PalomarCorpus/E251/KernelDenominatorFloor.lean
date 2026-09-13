/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.KernelDenominatorFloor
import Solutions.PalomarCorpus.E251.Statement

open scoped BigOperators

namespace PalomarCorpus.E251.KernelDenominatorFloor
export PalomarCorpus.E251.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)

private theorem noSmallDivisor_eq_source (m : ℕ) :
    ∀ fuel k : ℕ,
      noSmallDivisor m fuel k = ErdosProblems.Erdos251.noSmallDivisor m fuel k := by
  intro fuel
  induction fuel with
  | zero => intro k; rfl
  | succ fuel ih =>
      intro k
      simp only [noSmallDivisor, ErdosProblems.Erdos251.noSmallDivisor, ih]

private theorem isPrimeTD_eq_source (m : ℕ) :
    isPrimeTD m = ErdosProblems.Erdos251.isPrimeTD m := by
  simp only [isPrimeTD, ErdosProblems.Erdos251.isPrimeTD, noSmallDivisor_eq_source]

private theorem primeSumLoop_eq_source (B : ℕ) :
    ∀ X : ℕ, primeSumLoop B X = ErdosProblems.Erdos251.primeSumLoop B X := by
  intro X
  induction X with
  | zero => rfl
  | succ X ih =>
      simp only [primeSumLoop, ErdosProblems.Erdos251.primeSumLoop, ih,
        isPrimeTD_eq_source]

private theorem certCheck_eq_source (c u v u' v' X : ℕ) :
    certCheck c u v u' v' X = ErdosProblems.Erdos251.certCheck c u v u' v' X := by
  simp only [certCheck, ErdosProblems.Erdos251.certCheck, primeSumLoop_eq_source]

private theorem certX_eq_source : certX = ErdosProblems.Erdos251.certX := rfl

private theorem certC_eq_source : certC = ErdosProblems.Erdos251.certC := rfl

private theorem certU_eq_source : certU = ErdosProblems.Erdos251.certU := rfl

private theorem certV_eq_source : certV = ErdosProblems.Erdos251.certV := rfl

private theorem certU'_eq_source : certU' = ErdosProblems.Erdos251.certU' := rfl

private theorem certV'_eq_source : certV' = ErdosProblems.Erdos251.certV' := rfl

/-- The kernel re-runs the `10^4` trial-division sieve and decides the six
conditions on the certificate literals. -/
theorem cert_10000 : certCheck certC certU certV certU' certV' certX = true := by
  rw [certCheck_eq_source, certC_eq_source, certU_eq_source, certV_eq_source,
    certU'_eq_source, certV'_eq_source, certX_eq_source]
  exact ErdosProblems.Erdos251.cert_10000

/-- A passing certificate at any truncation index `c ≥ 9` forces every rational
`a / b` equal to the prime series to satisfy `v + v' ≤ b`. -/
theorem den_bound_of_certCheck (c u v u' v' X : ℕ) (hc : 9 ≤ c)
    (h : certCheck c u v u' v' X = true) :
    ∀ (a : ℤ) (b : ℕ), 0 < b → (∑' n, primeDyadicTerm n) = a / b → v + v' ≤ b := by
  rw [certCheck_eq_source] at h
  exact ErdosProblems.Erdos251.den_bound_of_certCheck c u v u' v' X hc h

/-- Every rational `a / b` equal to `S` has `b ≥ 2^589 > 10^177`. -/
theorem kernel_denominator_floor (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b :=
  ErdosProblems.Erdos251.kernel_denominator_floor a b hb hS

/-- The same floor for the prime-gap series `S - 2` of Erdős #251. -/
theorem kernel_denominator_floor_primeGap (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeGapDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b :=
  ErdosProblems.Erdos251.kernel_denominator_floor_primeGap a b hb hS

end PalomarCorpus.E251.KernelDenominatorFloor
