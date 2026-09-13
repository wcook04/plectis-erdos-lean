/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E68

Every non-theorem declaration of `PalomarCorpus/E68/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open scoped BigOperators
open Finsupp

namespace PalomarCorpus.E68.Shared
/-- The adjacent factorial difference `T n = n * e (n - 1) - e n`, the finitely supported integer vector with coefficient `n` at index `n - 1` and coefficient `-1` at index `n`, the subtraction `n - 1` taken in the natural numbers; for `n ≥ 1` its factorial moment vanishes because `n * (n - 1)! = n!`. -/
noncomputable def adjacentDifference (n : ℕ) : ℕ →₀ ℤ :=
  single (n - 1) (n : ℤ) - single n 1
/-- The common denominator `L D = lcm (d! - 1)` taken over the channel indices `2 ≤ d ≤ D`, the least common multiple of the denominators of the partial sum through `D`; the index set is empty and the value is `1` when `D < 2`. -/
noncomputable def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)
/-- The channel weight `W d i = i! / (d!)^(i / d)`, computed with natural division and an exact integer because `(d!)^(i / d)` divides `i!`; the value is `i!` whenever `d ≤ 1` or `d > i`. -/
noncomputable def channelWeight (i d : ℕ) : ℕ :=
  i.factorial / (d.factorial ^ (i / d))
/-- The `d`-th divisor channel numerator `V d (lam)`, the finite sum of `lam i * channelWeight i d` over the support of `lam`; because `d!` is congruent to `1` modulo `d! - 1`, this integer agrees with the factorial moment of `lam` modulo `d! - 1`. -/
noncomputable def channelNumerator (lam : ℕ →₀ ℤ) (d : ℕ) : ℤ :=
  lam.sum fun i z => z * (channelWeight i d : ℤ)
/-- The companion constant `C = ∑_{n ≥ 2} 1/(n! (n! - 1))`, a convergent real series whose terms are set to zero for `n ≤ 1` and which satisfies `C + (e - 2) = S` for the Erdős 68 series `S`. -/
noncomputable def companionConstant : ℝ :=
  ∑' n : ℕ, if 2 ≤ n then
    (1 : ℝ) /
      ((n.factorial : ℝ) * ((((n.factorial : ℤ) - 1 : ℤ) : ℝ)))
  else 0
/-- The integer `⌊m! * x⌋`, the `m`-th point of the factorial orbit of a real number `x`. -/
noncomputable def facFloor (x : ℝ) (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℝ) * x⌋
/-- The exact rational partial sum `H n = ∑_{2 ≤ k ≤ n} 1/(k! - 1)`, computed in `ℚ` with no real approximation; it is `0` for `n < 2`. -/
noncomputable def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)
/-- The Erdős 68 series `S = ∑_{n ≥ 2} 1/(n! - 1)` as a real infinite sum, with the terms at `n ≤ 1` set to zero so that the vanishing modulus `1! - 1` never occurs. -/
noncomputable def factorialGapSeries : ℝ :=
  ∑' n : ℕ, if 1 < n then (1 : ℝ) / (((n.factorial : ℤ) - 1 : ℤ) : ℝ) else 0
/-- The factorial moment `M (lam) = ∑ lam i * i!` of a finitely supported integer vector. -/
noncomputable def factorialMoment (lam : ℕ →₀ ℤ) : ℤ :=
  lam.sum fun i z => z * (i.factorial : ℤ)
/-- The isolated channel unit `U n`, defined by strong recursion as `T n` minus the sum of `channelWeight n d * U d` over the divisors `d` of `n` with `2 ≤ d < n`, and as the zero vector for `n ≤ 1`; the recursion cancels every proper divisor channel, so `U n` has zero factorial moment and acts only on the channel at `n`. -/
noncomputable def isolatedChannelUnit (n : ℕ) : ℕ →₀ ℤ :=
  n.strongRecOn' fun n rec =>
    if n ≤ 1 then 0
    else
      adjacentDifference n -
        ∑ d ∈ (Finset.Ico 2 n).attach,
          if d.1 ∣ n then
            (channelWeight n d.1 : ℤ) • rec d.1 (Finset.mem_Ico.mp d.2).2
          else 0
/-- The `j`-th column of the divisor channel basis: the unit vector at index `1` when `j = 0`, and the isolated channel unit `U (j + 1)` when `j ≥ 1`. -/
noncomputable def channelBasisColumn (j : ℕ) : ℕ →₀ ℤ :=
  if j = 0 then single 1 1 else isolatedChannelUnit (j + 1)
/-- The finitely supported integer vector assembled from coordinates `a` in the divisor channel basis, namely the finite sum of `a j` scaled copies of `channelBasisColumn j`. -/
noncomputable def channelSynthesis (a : ℕ →₀ ℤ) : ℕ →₀ ℤ :=
  a.sum (fun j z => z • channelBasisColumn j)
/-- The divisor channel coordinates of the canonical low channel kernel at depth `D`: the value `L D` in coordinate `0`, which carries the unit vector at index `1`, and the value `-(L D / (d! - 1))` in coordinate `d - 1`, which carries `U d`, for each `d` with `2 ≤ d ≤ D`. -/
noncomputable def kernelCoordinates (D : ℕ) : ℕ →₀ ℤ :=
  single 0 (channelLCM D : ℤ) -
    ∑ d ∈ Finset.Icc 2 D,
      single (d - 1) ((channelLCM D : ℤ) / ((d.factorial : ℤ) - 1))
/-- The canonical low channel kernel `K D = L D * e 1 - ∑_{2 ≤ d ≤ D} (L D / (d! - 1)) * U d`, the vector of factorial moment `L D` whose channel numerators vanish at every `d` with `2 ≤ d ≤ D`. -/
noncomputable def canonicalKernel (D : ℕ) : ℕ →₀ ℤ :=
  channelSynthesis (kernelCoordinates D)
/-- The least integer strictly greater than `n! * x` for a real number `x`, namely `⌊n! * x⌋ + 1`. -/
noncomputable def strictFacTop (x : ℝ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℝ) * x⌋ + 1
/-- The predecessor gap `Δ m = Z (m - 1) - (m - 1)! * H (m - 1)`, the distance from the factorially scaled exact prefix at index `m - 1` up to the least integer strictly above it; it lies in the interval `(0, 1]`. -/
noncomputable def factorialGapPredecessorGap (m : ℕ) : ℝ :=
  (strictFacTop
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℝ) -
    ((m - 1).factorial : ℝ) *
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ)
/-- The exact integer carry `b m` of the strict successor recurrence `Z m = m * Z (m - 1) + 1 - b m`, given here by `b m = -⌊1 + 1/(m! - 1) - m * Δ m⌋`; the value `1` is the unit carry. -/
noncomputable def factorialGapStepCarry (m : ℕ) : ℤ :=
  -⌊1 + 1 / ((m.factorial : ℝ) - 1) -
      (m : ℝ) * factorialGapPredecessorGap m⌋
/-- The least integer strictly greater than `n! * x` for a rational number `x`, namely `⌊n! * x⌋ + 1`, computed by exact rational arithmetic. -/
noncomputable def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ := ⌊(n.factorial : ℚ) * x⌋ + 1
end PalomarCorpus.E68.Shared

namespace PalomarCorpus.E68.AdjacentUnitCarryWindow
export PalomarCorpus.E68.Shared (factorialGapPrefix strictFacTopRat)
/-- The exact rational number `(m - 1)! * H (m - 1)`, the factorially scaled exact prefix one index below `m`. -/
noncomputable def predecessorScaled (m : ℕ) : ℚ :=
  ((m - 1).factorial : ℚ) * factorialGapPrefix (m - 1)
/-- The numerator of the reduced predecessor gap: for `q = (m - 1)! * H (m - 1)` it is `(⌊q⌋ + 1) * q.den - q.num`, so that the gap `Δ m` equals this integer divided by `q.den`. -/
noncomputable def predecessorNumerator (m : ℕ) : ℤ :=
  let q := predecessorScaled m; (⌊q⌋ + 1) * q.den - q.num
/-- The exact transition normaliser `G m = (predecessorScaled m).den * (m! - 1) / (predecessorScaled (m + 1)).den`, computed with natural division; it is the factor by which the product `(predecessorScaled m).den * (m! - 1)` exceeds the reduced denominator at `m + 1`. -/
noncomputable def transitionNormalizer (m : ℕ) : ℕ :=
  (predecessorScaled m).den * (m.factorial - 1) / (predecessorScaled (m + 1)).den
/-- The predecessor gap `Δ m = Z (m - 1) - (m - 1)! * H (m - 1)` as a real number built from the exact rational prefix; it lies in the interval `(0, 1]`. -/
noncomputable def predecessorGap (m : ℕ) : ℝ :=
  (strictFacTopRat (factorialGapPrefix (m - 1)) (m - 1) : ℝ) -
    ((m - 1).factorial : ℝ) * (factorialGapPrefix (m - 1) : ℝ)
/-- The exact integer carry `b m = -⌊1 + 1/(m! - 1) - m * Δ m⌋` of the strict successor recurrence, restated in this namespace. -/
noncomputable def stepCarry (m : ℕ) : ℤ :=
  -⌊1 + 1 / ((m.factorial : ℝ) - 1) - (m : ℝ) * predecessorGap m⌋
/-- The cleared two step window denominator `D m = (predecessorScaled m).den * (m! - 1) * ((m + 1)! - 1)`, the common denominator of the two carry conditions at `m` and at `m + 1`. -/
noncomputable def windowDen (m : ℕ) : ℤ :=
  ((predecessorScaled m).den : ℤ) * ((m.factorial : ℤ) - 1) *
    (((m + 1).factorial : ℤ) - 1)
/-- The cleared lower endpoint of the two step window, the integer `(m + 2) * D m + (m + 1) * (predecessorScaled m).den * ((m + 1)! - 1) + (predecessorScaled m).den * (m! - 1)`, which is `D m` times `(m + 2) + (m + 1)/(m! - 1) + 1/((m + 1)! - 1)`. -/
noncomputable def windowLower (m : ℕ) : ℤ :=
  (m + 2 : ℤ) * windowDen m + (m + 1 : ℤ) *
    ((predecessorScaled m).den : ℤ) * (((m + 1).factorial : ℤ) - 1) +
    ((predecessorScaled m).den : ℤ) * ((m.factorial : ℤ) - 1)
/-- The cleared two step state, the integer `m * (m + 1) * predecessorNumerator m * (m! - 1) * ((m + 1)! - 1)`, which is `D m` times `m * (m + 1) * Δ m`. -/
noncomputable def windowState (m : ℕ) : ℤ :=
  (m : ℤ) * (m + 1 : ℤ) * predecessorNumerator m *
    ((m.factorial : ℤ) - 1) * (((m + 1).factorial : ℤ) - 1)
/-- The integer displacement `Ω m = windowState m - windowLower m` of the cleared two step state above the lower endpoint of its window. -/
noncomputable def windowOffset (m : ℕ) : ℤ := windowState m - windowLower m
end PalomarCorpus.E68.AdjacentUnitCarryWindow

namespace PalomarCorpus.E68.ChannelRadius
export PalomarCorpus.E68.Shared (channelLCM)
end PalomarCorpus.E68.ChannelRadius

namespace PalomarCorpus.E68.CommonDenominatorGrowth
open Filter
export PalomarCorpus.E68.Shared (channelLCM)
/-- The predicate that the lower limit of a real sequence `f` is at least `c`, written out as: for every real `a < c`, the inequality `a < f n` holds for all sufficiently large `n`. -/
noncomputable def LowerLimitAtLeast (f : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ a : ℝ, a < c → ∀ᶠ n : ℕ in atTop, a < f n
end PalomarCorpus.E68.CommonDenominatorGrowth

namespace PalomarCorpus.E68.CompanionOrbitBoundary
export PalomarCorpus.E68.Shared (companionConstant facFloor factorialGapPredecessorGap factorialGapPrefix factorialGapStepCarry strictFacTop strictFacTopRat)
/-- The Erdős 68 series `S = ∑_{d ≥ 2} 1/(d! - 1)`, restated in this namespace with the terms at `d ≤ 1` set to zero. -/
noncomputable def factorialGapSeries : ℝ :=
  ∑' d : ℕ, if 1 < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))
  else 0
/-- The anchored unit factorial term, equal to `1/n!` for `n ≥ 2` and to `0` otherwise. -/
noncomputable def unitFactTerm (n : ℕ) : ℝ :=
  if 2 ≤ n then (1 : ℝ) / ((n.factorial : ℝ)) else 0
/-- The canonical factorial base digit `d m (x) = ⌊m! * x⌋ - m * ⌊(m - 1)! * x⌋` of a real number `x` at radix `m`; for `m ≥ 2` it satisfies `0 ≤ d m (x) < m`. -/
noncomputable def canonicalDigit (x : ℝ) (m : ℕ) : ℤ :=
  facFloor x m - (m : ℤ) * facFloor x (m - 1)
end PalomarCorpus.E68.CompanionOrbitBoundary

namespace PalomarCorpus.E68.FiniteDenominator
export PalomarCorpus.E68.Shared (factorialGapSeries)
end PalomarCorpus.E68.FiniteDenominator

namespace PalomarCorpus.E68.KempnerIndex
open scoped BigOperators
export PalomarCorpus.E68.Shared (factorialGapPredecessorGap factorialGapPrefix factorialGapSeries factorialGapStepCarry strictFacTop)
end PalomarCorpus.E68.KempnerIndex

namespace PalomarCorpus.E68.MomentIdeal
open scoped BigOperators
open Finsupp
export PalomarCorpus.E68.Shared (adjacentDifference canonicalKernel channelBasisColumn channelLCM channelNumerator channelSynthesis channelWeight factorialMoment isolatedChannelUnit kernelCoordinates)
/-- The auxiliary coordinate `u n = (U n) 1` of the isolated channel unit, the integer weight that `U n` places on index `1`. -/
noncomputable def channelScalar (n : ℕ) : ℤ := isolatedChannelUnit n 1
/-- The greatest common divisor of the absolute values `|u n|` over the finite range `D + 1 ≤ n ≤ N`, as a natural number; the empty range gives `0`. -/
noncomputable def finiteScalarGcd (D N : ℕ) : ℕ :=
  (Finset.Icc (D + 1) N).gcd (fun n => (channelScalar n).natAbs)
/-- The auxiliary coordinate `a D = (K D) 1` of the canonical low channel kernel at depth `D`. -/
noncomputable def kernelOne (D : ℕ) : ℤ := canonicalKernel D 1
/-- The support restriction of the problem: every index in the support of `f` is at least `2`, so `f` has no coefficient at index `0` and none at the auxiliary index `1`. -/
noncomputable def Admissible (f : ℕ →₀ ℤ) : Prop :=
  ∀ n ∈ f.support, 2 ≤ n
/-- The low channel condition at depth `D`: the channel numerator of `f` vanishes at every channel `d` with `2 ≤ d ≤ D`. -/
noncomputable def LowChannels (D : ℕ) (f : ℕ →₀ ℤ) : Prop :=
  ∀ d ∈ Finset.Icc 2 D, channelNumerator f d = 0
/-- The property that the integer `m` is the factorial moment of some admissible finitely supported integer vector whose channel numerators vanish at every `d` with `2 ≤ d ≤ D`. -/
noncomputable def AttainsMoment (D : ℕ) (m : ℤ) : Prop :=
  ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧ factorialMoment f = m
/-- The candidate generator `L D * (G / gcd (G, a D))` of the attainable moments at depth `D`, where `G` is the greatest common divisor of the auxiliary coordinates `u n` over the finite horizon `D + 1 ≤ n ≤ D * (2 * p - 1)` cut at the parameter `p`, on which this definition imposes no primality, and the outer division is exact integer division. -/
noncomputable def minimumMoment (D p : ℕ) : ℤ :=
  let G : ℤ := finiteScalarGcd D (D * (2 * p - 1))
  (channelLCM D : ℤ) * (G / (Int.gcd G (kernelOne D) : ℤ))
/-- The primitivity condition on `f`: for no natural `k ≥ 2` is `f` equal to `k` times another finitely supported integer vector. -/
noncomputable def PrimitiveVector (f : ℕ →₀ ℤ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ¬ ∃ g : ℕ →₀ ℤ, f = (k : ℤ) • g
/-- The content of `f`, the greatest common divisor of the absolute values of its coefficients over its support; the zero vector has content `0`. -/
noncomputable def coefficientContent (f : ℕ →₀ ℤ) : ℕ :=
  f.support.gcd (fun n => (f n).natAbs)
end PalomarCorpus.E68.MomentIdeal

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
export PalomarCorpus.E68.Shared (factorialGapPrefix factorialGapSeries strictFacTopRat)
/-- The strict successor `Z m = ⌊m! * H m⌋ + 1` of the exact rational prefix, the least integer strictly above the factorially scaled prefix at index `m`. -/
noncomputable def gapSuccessor (m : ℕ) : ℤ :=
  strictFacTopRat (factorialGapPrefix m) m
end PalomarCorpus.E68.MultiplicativeSuccessorRigidity

namespace PalomarCorpus.E68.PrimePole
open scoped BigOperators
/-- The prefix common denominator, the least common multiple of `n! - 1` over `2 ≤ n ≤ M`. -/
noncomputable def factorialGapPrefixLCM (M : ℕ) : ℕ :=
  (Finset.Icc 2 M).lcm fun n => n.factorial - 1
/-- The numerator obtained by writing the finite prefix sum over the literal prefix common denominator, namely the sum over `2 ≤ n ≤ M` of `factorialGapPrefixLCM M / (n! - 1)`. -/
noncomputable def factorialGapPrefixLCMNumerator (M : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 2 M,
    factorialGapPrefixLCM M / (n.factorial - 1)
/-- The set of indices `n` with `2 ≤ n ≤ M` whose denominator `n! - 1` has exact `q`-adic exponent `e`, that is `q^e` divides `n! - 1` and `q^(e + 1)` does not. -/
noncomputable def factorialGapMaxHits (q M e : ℕ) : Finset ℕ :=
  (Finset.Icc 2 M).filter fun n =>
    q ^ e ∣ n.factorial - 1 ∧
      ¬q ^ (e + 1) ∣ n.factorial - 1
/-- The reciprocal residue of the maximal valuation layer, the sum in `ZMod q` over those indices of the inverses of the cofactors `(n! - 1) / q^e`. -/
noncomputable def factorialGapPrincipalResidue (q M e : ℕ) : ZMod q :=
  ∑ n ∈ factorialGapMaxHits q M e,
    (((n.factorial - 1) / q ^ e : ℕ) : ZMod q)⁻¹
end PalomarCorpus.E68.PrimePole

namespace PalomarCorpus.E68.PrimeUnitTranslator
/-- The factorial moment of a finite family of integer coefficients placed at natural indices, the sum over the index type of `coeff j * (index j)!`. -/
noncomputable def factorialMoment {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) : ℤ :=
  ∑ j, coeff j * (index j).factorial
/-- The `d`-th channel numerator of such a family, the sum over the index type of `coeff j * ((index j)! / (d!)^(index j / d))`, the inner weight being an exact natural division. -/
noncomputable def channelNumerator {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℤ :=
  ∑ j, coeff j * ((index j).factorial /
    d.factorial ^ (index j / d) : ℕ)
/-- The coefficient pair `(p, -1)` of the prime translator, as a function on `Fin 2`. -/
noncomputable def primeTranslatorCoeff (p : ℕ) : Fin 2 → ℤ := ![(p : ℤ), -1]
/-- The index pair `(p - 1, p)` carrying the prime translator coefficients, with the subtraction taken in the natural numbers. -/
noncomputable def primeTranslatorIndex (p : ℕ) : Fin 2 → ℕ := ![p - 1, p]
/-- The contribution of the channel `d` to the residual beyond a cutoff `D`, equal to the channel numerator at `d` divided by `d! - 1` when `D < d`, and `0` otherwise. -/
noncomputable def channelResidualTerm {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℝ :=
  if D < d then
    (channelNumerator coeff index d : ℝ) /
      (((d.factorial : ℤ) - 1 : ℤ) : ℝ)
  else 0
/-- The residual of a finite coefficient family beyond the cutoff `D`, the infinite sum over `d` of the contributions `channelResidualTerm D coeff index d`. -/
noncomputable def channelResidual {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) : ℝ :=
  ∑' d : ℕ, channelResidualTerm D coeff index d
/-- The coefficients of the family enlarged by `z` copies of the prime translator at `p`, defined on the disjoint union of the original index type with `Fin 2`. -/
noncomputable def appendPrimeTranslatorCoeff {ι : Type*}
    (coeff : ι → ℤ) (p : ℕ) (z : ℤ) : Sum ι (Fin 2) → ℤ :=
  Sum.elim coeff (fun j => z * primeTranslatorCoeff p j)
/-- The indices of that enlarged family, the original indices together with `p - 1` and `p`. -/
noncomputable def appendPrimeTranslatorIndex {ι : Type*}
    (index : ι → ℕ) (p : ℕ) : Sum ι (Fin 2) → ℕ :=
  Sum.elim index (primeTranslatorIndex p)
/-- For a family of `n + 1` indices, the square integer matrix whose first row holds the factorial values `(index j)!` and whose row `d + 1` holds the channel weight of `index j` at the channel `d + 2`. -/
noncomputable def augmentedChannelMomentMatrix {n : ℕ}
    (index : Fin (n + 1) → ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun r j =>
    Fin.cases ((index j).factorial : ℤ)
      (fun d : Fin n =>
        ((index j).factorial /
          (d.val + 2).factorial ^ (index j / (d.val + 2)) : ℕ)) r
/-- The integer coefficient vector obtained by Cramer's rule from the augmented matrix and the first standard basis vector; applying the matrix to it returns the determinant times that basis vector, so the channel numerators at `2` through `n + 1` vanish and the factorial moment equals the determinant. -/
noncomputable def cramerChannelKernelCoeff {n : ℕ}
    (index : Fin (n + 1) → ℕ) : Fin (n + 1) → ℤ :=
  (augmentedChannelMomentMatrix index).cramer (Pi.single 0 1)
/-- The common grid scale `(D!)^2` at cutoff `D`, a step divisible by every `d` with `2 ≤ d ≤ D`. -/
noncomputable def factorialGridScale (D : ℕ) : ℕ := D.factorial ^ 2
/-- The arithmetic grid of `n + 2` indices `(t + j) * ((n + 2)!)^2` for `j < n + 2`, an equally spaced block of support indices starting at `t * ((n + 2)!)^2`. -/
noncomputable def factorialGridIndex (n t : ℕ) (j : Fin (n + 2)) : ℕ :=
  (t + j.val) * factorialGridScale (n + 2)
end PalomarCorpus.E68.PrimeUnitTranslator

namespace PalomarCorpus.E68.ResidualIntegerClass
open scoped BigOperators
open Finsupp
export PalomarCorpus.E68.Shared (adjacentDifference canonicalKernel channelBasisColumn channelLCM channelNumerator channelSynthesis channelWeight factorialGapSeries factorialMoment isolatedChannelUnit kernelCoordinates)
/-- The condition that the divisor channel coordinates `z` vanish below index `D`, so for `D ≥ 1` the vector they synthesise uses only the isolated channel units `U n` with `n > D`. -/
noncomputable def TailCoordinates (D : ℕ) (z : ℕ →₀ ℤ) : Prop :=
  ∀ j, j < D → z j = 0
/-- The pairing `∑ z i * w i` of finitely supported integer coordinates `z` against an integer weight function `w`. -/
noncomputable def integerEvaluation (w : ℕ → ℤ) (z : ℕ →₀ ℤ) : ℤ :=
  z.sum (fun i c => c * w i)
/-- The coordinate mass of `z`, the sum of its coordinates, obtained by pairing `z` with the constant weight `1`. -/
noncomputable def coordinateMass (z : ℕ →₀ ℤ) : ℤ :=
  integerEvaluation (fun _ => 1) z
/-- The contribution of the channel `d` to the full residual, equal to the channel numerator `V d (f)` divided by `d! - 1` for `d > 1` and `0` for `d ≤ 1`, the guard excluding the vanishing moduli at `d = 0` and `d = 1`. -/
noncomputable def fullResidualTerm (f : ℕ →₀ ℤ) (d : ℕ) : ℝ :=
  if 1 < d then (channelNumerator f d : ℝ) /
    ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ) else 0
/-- The full residual of a finitely supported integer vector, the infinite sum over all `d` of the contributions `fullResidualTerm f d`. -/
noncomputable def fullResidual (f : ℕ →₀ ℤ) : ℝ :=
  ∑' d : ℕ, fullResidualTerm f d
/-- The real value of the exact prefix `H D = ∑_{2 ≤ d ≤ D} 1/(d! - 1)`. -/
noncomputable def gapPrefixReal (D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 D, (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)
end PalomarCorpus.E68.ResidualIntegerClass

namespace PalomarCorpus.E68.StrictSuccessorCarry
export PalomarCorpus.E68.Shared (companionConstant facFloor factorialGapPredecessorGap factorialGapPrefix factorialGapStepCarry strictFacTop strictFacTopRat)
/-- The Erdős 68 series `S = ∑_{d ≥ 2} 1/(d! - 1)`, restated in this namespace with the terms at `d ≤ 1` set to zero. -/
noncomputable def factorialGapSeries : ℝ :=
  ∑' d : ℕ, if 1 < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))
  else 0
end PalomarCorpus.E68.StrictSuccessorCarry
