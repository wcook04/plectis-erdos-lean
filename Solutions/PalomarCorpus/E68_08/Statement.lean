/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E68_08

Every non-theorem declaration of `PalomarCorpus/E68_08/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E68.MovingFactorScaleSplit
open scoped BigOperators
/-- The Erdős 68 series `S = ∑_{d ≥ 2} 1/(d! - 1)`, restated in this namespace with the terms at `d ≤ 1` set to zero. -/
noncomputable def factorialGapSeries : ℝ :=
  ∑' d : ℕ, if 1 < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))
  else 0
/-- The finite set of primes `q` dividing `m! - 1` with `m + 1 < q` that are coprime to `k! - 1` for every `k` with `2 ≤ k < m`; these are the large primes whose first appearance among the denominators is at index `m`. -/
noncomputable def factorialGapLargePrefixPrivatePrimes (m : ℕ) : Finset ℕ :=
  (m.factorial - 1).primeFactors.filter fun q =>
    m + 1 < q ∧
      ∀ k ∈ Finset.Ico 2 m,
        Nat.Coprime q (k.factorial - 1)
/-- The block of denominator indices `2 ≤ i ≤ 2 * p - 1` used at block parameter `p`, with the subtraction taken in the natural numbers. -/
noncomputable def factorialBlockIndices (p : ℕ) : Finset ℕ :=
  Finset.Icc 2 (2 * p - 1)
/-- The `n`-th denominator `n! - 1` of the series. -/
noncomputable def factorialGapDenominator (n : ℕ) : ℕ :=
  n.factorial - 1
/-- The factorial base `(p - 1)!` of the block at parameter `p`, the factor that absorbs every fixed denominator once `p` is large. -/
noncomputable def factorialBlockBase (p : ℕ) : ℕ :=
  (p - 1).factorial
/-- The pairwise collision core of a family of moduli `d` indexed by a finite set `s`, the least common multiple over `i` in `s` of the least common multiple over the other `j` in `s` of `gcd (d i) (d j)`; it records every prime power carried by at least two distinct members. -/
noncomputable def pairwiseCollisionCore
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.lcm fun i =>
    (s.erase i).lcm fun j => Nat.gcd (d i) (d j)
/-- The collision core `lcm (base) (pairwiseCollisionCore s d)`, the shared part of the family taken together with the given base. -/
noncomputable def collisionCore
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  Nat.lcm base (pairwiseCollisionCore s d)
/-- The block denominator `lcm (base) (lcm over s of d)`, the common denominator that clears the base and every modulus of the family. -/
noncomputable def endpointDenominatorLcm
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  Nat.lcm base (s.lcm d)
/-- The numerator obtained by writing the finite reciprocal sum of the family over that common denominator, namely the sum over `i` in `s` of `endpointDenominatorLcm base s d / d i`. -/
noncomputable def endpointTailNumerator
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.sum fun i => endpointDenominatorLcm base s d / d i
/-- The private part `d i / gcd (d i, collisionCore base s d)` of the modulus at `i`, the factor of `d i` carried neither by the base nor by any other member of the family. -/
noncomputable def privateQuotient
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) (i : ι) : ℕ :=
  d i / Nat.gcd (d i) (collisionCore base s d)
/-- The product over `i` in `s` of the private quotients, the modulus that remains once the shared collision core has been divided out of each member. -/
noncomputable def privateModulus
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.prod (privateQuotient base s d)
/-- The least nonnegative residue `T % Q` of `T` modulo `Q`. -/
noncomputable def projectedResidue (T Q : ℕ) : ℕ :=
  T % Q
/-- The complementary residue of `T` modulo `Q`, computed as `(Q - (T % Q)) % Q` with natural subtraction; for positive `Q` it is the distance from `T` up to the next multiple of `Q`, and it is `0` exactly when `Q` divides `T`. -/
noncomputable def complementaryProjectedResidue (T Q : ℕ) : ℕ :=
  projectedResidue (Q - projectedResidue T Q) Q
/-- The leave one out modulus `R / r`, the natural division of a modulus `R` by one of its factors `r`. -/
noncomputable def leaveOneOutModulus (R r : ℕ) : ℕ :=
  R / r
/-- The block common denominator at parameter `p`, the least common multiple of the base `(p - 1)!` with the denominators `i! - 1` for `2 ≤ i ≤ 2 * p - 1`. -/
noncomputable def factorialBlockEndpointLcm (p : ℕ) : ℕ :=
  endpointDenominatorLcm
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator
/-- The collision core of the block at parameter `p`, the least common multiple of `(p - 1)!` with every pairwise greatest common divisor of the denominators `i! - 1` in the block. -/
noncomputable def factorialBlockCollisionCore (p : ℕ) : ℕ :=
  collisionCore
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator
/-- The normalised collision core of the block at `p`, the collision core divided by the factorial base `(p - 1)!`. -/
noncomputable def factorialBlockNormalizedCollisionCore (p : ℕ) : ℕ :=
  factorialBlockCollisionCore p / factorialBlockBase p
/-- The descending factorial `(2 * p - 1) (2 * p - 2) ⋯ p`, equal to `(2 * p - 1)! / (p - 1)!`, the factorial scale of the block after the base has been removed. -/
noncomputable def factorialBlockUpperDescFactorial (p : ℕ) : ℕ :=
  (2 * p - 1).descFactorial p
/-- The private modulus of the block at `p`, the product of the private quotients of the denominators `i! - 1` over `2 ≤ i ≤ 2 * p - 1`. -/
noncomputable def factorialBlockPrivateModulus (p : ℕ) : ℕ :=
  privateModulus
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator
/-- The tail numerator of the block at `p`, the finite sum of the block common denominator divided by each denominator `i! - 1` of the block. -/
noncomputable def factorialBlockTailNumerator (p : ℕ) : ℕ :=
  endpointTailNumerator
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator
/-- The private quotient of the single denominator `n! - 1` inside the block at parameter `p`. -/
noncomputable def factorialBlockPrivateQuotient (p n : ℕ) : ℕ :=
  privateQuotient
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator n
/-- The leave one out modulus obtained by dividing the private modulus of the block at `p` by a factor `a`. -/
noncomputable def factorialBlockFactorProjectionModulus (p a : ℕ) : ℕ :=
  leaveOneOutModulus (factorialBlockPrivateModulus p) a
/-- The tail scale `2 * p^2 * (2 * p - 1)!`, the denominator of the explicit estimate `S - H (2 * p - 1) < (2 * p + 1) / (2 * p^2 * (2 * p - 1)!)` for the positive tail beyond the block. -/
noncomputable def factorialBlockScale (p : ℕ) : ℕ :=
  2 * p ^ 2 * (2 * p - 1).factorial
/-- The tail budget `2 * p + 1`, the numerator of that same explicit estimate for the positive tail beyond the block. -/
noncomputable def factorialBlockBudget (p : ℕ) : ℕ :=
  2 * p + 1
end PalomarCorpus.E68.MovingFactorScaleSplit

namespace PalomarCorpus.E68.MultiplicativeSuccessorRigidity
open scoped BigOperators
/-- The exact rational partial sum `H n = ∑_{2 ≤ k ≤ n} 1/(k! - 1)`, computed in `ℚ` with no real approximation; it is `0` for `n < 2`. -/
noncomputable def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)
/-- Computable rational form of `strictFacTop`, used for exact finite certificates while retaining the real-valued statement needed for the series. Local copy of ErdosProblems.Erdos68.strictFacTopRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1
/-- The strict successor `Z m = ⌊m! * H m⌋ + 1` of the exact rational prefix, the least integer strictly above the factorially scaled prefix at index `m`. -/
noncomputable def gapSuccessor (m : ℕ) : ℤ :=
  strictFacTopRat (factorialGapPrefix m) m
end PalomarCorpus.E68.MultiplicativeSuccessorRigidity
