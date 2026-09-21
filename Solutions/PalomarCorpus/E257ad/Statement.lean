/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257ad

Every non-theorem declaration of `PalomarCorpus/E257ad/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E257.PaperStatementsAD
open scoped BigOperators
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def toNatWord {s : ℕ} (b : SeamRowWord s) : ℕ → Bool :=
  fun d => if h : 2 ≤ d ∧ d < s then b ⟨d - 2, by omega⟩ else false
/-- Descending greedy subset for an integer capacity. Local copy of Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C
/-- The exact quotient digit created when the row is multiplied by four. Local copy of Erdos249257.HalfCylinderIntegerGreedy.rowPulse, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rowPulse (s d : ℕ) : ℕ :=
  (if d ∣ 2 * s + 2 then 1 else 0) +
    2 * (if d ∣ 2 * s + 1 then 1 else 0)
/-- The binary-boundary target before any selected divisor weights are removed. Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamSubsetTarget, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s
/-- The exact integer weight contributed at seam rank `s` by selecting a proper divisor rank `d < s`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.truncatedMersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
/-- The weights with indices `d,d+1,…,s-1`, in descending size order. Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega
/-- The actual proper-divisor weight word, indexed by `2,…,s-1`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamWeights, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])
/-- `Hₜ = lcm(1, ..., t)`. The interval avoids inserting zero into the finite LCM. Local copy of Erdos249257.MersenneShadowCyclotomicNoncollapse.lcmHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmHeight (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).lcm (fun n ↦ n)
/-- Prime indices in the development's upper half `(t/2, t]`. Local copy of Erdos249257.MersenneShadowCyclotomicNoncollapse.upperHalfPrimes, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def upperHalfPrimes (t : ℕ) : Finset ℕ :=
  (Finset.Ioc (t / 2) t).filter Nat.Prime
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
/-- Number of selected lower ranks which divide the next endpoint. Local copy of Erdos249257.endpointDivisorContribution, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card
/-- The quotient of one scaled Mersenne weight written without division: a shift by the Euclidean remainder times a finite geometric word. Local copy of Erdos249257.localMersenneGeometricQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneGeometricQuotient (M d : ℕ) : ℕ :=
  2 ^ (M % d) * ∑ j ∈ Finset.range (M / d), (2 ^ d) ^ j
/-- The integral part of `2^M / (2^d - 1)`. Local copy of Erdos249257.localMersenneQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- Sum of the integral quotient contributions of a finite Boolean support. Local copy of Erdos249257.localPrefixQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d
/-- `D` is the paper's `D_n`: among the quotient sums over subsets of `{2,…,n-1}` it gives the largest sum at most `T_n`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.IsRowLower, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsRowLower (n : ℕ) (D : Finset ℕ) : Prop :=
  D ⊆ Finset.Ico 2 n ∧
    localPrefixQuotient D (2 * n) ≤ seamSubsetTarget n ∧
      ∀ S, S ⊆ Finset.Ico 2 n →
        localPrefixQuotient S (2 * n) ≤ seamSubsetTarget n →
          localPrefixQuotient S (2 * n) ≤ localPrefixQuotient D (2 * n)
/-- `B` is the paper's `B_n`: among the quotient sums over subsets of `{2,…,n-1}` it gives the smallest sum strictly greater than `T_n`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.IsRowUpper, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsRowUpper (n : ℕ) (B : Finset ℕ) : Prop :=
  B ⊆ Finset.Ico 2 n ∧
    seamSubsetTarget n < localPrefixQuotient B (2 * n) ∧
      ∀ S, S ⊆ Finset.Ico 2 n →
        seamSubsetTarget n < localPrefixQuotient S (2 * n) →
          localPrefixQuotient B (2 * n) ≤ localPrefixQuotient S (2 * n)
/-- The subset of `{2,…,n-1}` selected by a Boolean row word. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rowSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rowSupport (n : ℕ) (b : SeamRowWord n) : Finset ℕ :=
  (Finset.Ico 2 n).filter (fun d => b.toNatWord d = true)
/-- The take set of the integer greedy process of §`ssec:seam-model`: the ranks `d = 2,…,n-1` are visited in ascending order against `T_n`, and `d` is taken exactly when its weight does not exceed the current residual. The process is `integerGreedyBits` run on the weight list `seamWeights n = [w(n,2),…,w(n,n-1)]` with capacity `T_n`; see `paper_greedy_step`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedySupport (n : ℕ) : Finset ℕ := rowSupport n (seamGreedyWord n)
/-- The paper's integral Möbius numerator `A_r = ∑_{d ∣ r} μ(d) (r/d) (M_r / M_d)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.paperA, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperA (r : ℕ) : ℤ :=
  ∑ d ∈ r.divisors,
    ArithmeticFunction.moebius d * (((r / d : ℕ)) : ℤ) *
      (((mersenne r /
        mersenne d : ℕ)) : ℤ)
/-- The paper's finite rational sum `B(r) = ∑_{d ∣ r} μ(d)(r/d) / (2^d - 1)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.paperB, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperB (r : ℕ) : ℚ :=
  ∑ d ∈ r.divisors,
    ((ArithmeticFunction.moebius d : ℤ) : ℚ) * ((r : ℚ) / (d : ℚ)) /
      ((2 : ℚ) ^ d - 1)
end PalomarCorpus.E257.PaperStatementsAD
