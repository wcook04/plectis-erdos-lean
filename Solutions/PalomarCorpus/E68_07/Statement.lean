/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E68_07

Every non-theorem declaration of `PalomarCorpus/E68_07/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Finsupp

namespace PalomarCorpus.E68_07.Shared
/-- The Erdős 68 series `S = ∑_{n ≥ 2} 1/(n! - 1)` as a real infinite sum, with the terms at `n ≤ 1` set to zero so that the vanishing modulus `1! - 1` never occurs. -/
noncomputable def factorialGapSeries : ℝ :=
  ∑' n : ℕ, if 1 < n then (1 : ℝ) / (((n.factorial : ℤ) - 1 : ℤ) : ℝ) else 0
end PalomarCorpus.E68_07.Shared

namespace PalomarCorpus.E68.FiniteDenominator
export PalomarCorpus.E68_07.Shared (factorialGapSeries)
end PalomarCorpus.E68.FiniteDenominator

namespace PalomarCorpus.E68.KempnerIndex
open scoped BigOperators
export PalomarCorpus.E68_07.Shared (factorialGapSeries)
/-- The exact rational partial sum `H n = ∑_{2 ≤ k ≤ n} 1/(k! - 1)`, computed in `ℚ` with no real approximation; it is `0` for `n < 2`. -/
noncomputable def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)
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
end PalomarCorpus.E68.KempnerIndex

namespace PalomarCorpus.E68.MomentIdeal
open scoped BigOperators
open Finsupp
/-- The channel weight `W d i = i! / (d!)^(i / d)`, computed with natural division and an exact integer because `(d!)^(i / d)` divides `i!`; the value is `i!` whenever `d ≤ 1` or `d > i`. -/
noncomputable def channelWeight (i d : ℕ) : ℕ :=
  i.factorial / (d.factorial ^ (i / d))
/-- The `d`-th divisor channel numerator `V d (lam)`, the finite sum of `lam i * channelWeight i d` over the support of `lam`; because `d!` is congruent to `1` modulo `d! - 1`, this integer agrees with the factorial moment of `lam` modulo `d! - 1`. -/
noncomputable def channelNumerator (lam : ℕ →₀ ℤ) (d : ℕ) : ℤ :=
  lam.sum fun i z => z * (channelWeight i d : ℤ)
/-- The factorial moment `M (lam) = ∑ lam i * i!` of a finitely supported integer vector. -/
noncomputable def factorialMoment (lam : ℕ →₀ ℤ) : ℤ :=
  lam.sum fun i z => z * (i.factorial : ℤ)
/-- The common denominator `L D = lcm (d! - 1)` taken over the channel indices `2 ≤ d ≤ D`, the least common multiple of the denominators of the partial sum through `D`; the index set is empty and the value is `1` when `D < 2`. -/
noncomputable def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)
/-- The adjacent factorial difference `T n = n * e (n - 1) - e n`, the finitely supported integer vector with coefficient `n` at index `n - 1` and coefficient `-1` at index `n`, the subtraction `n - 1` taken in the natural numbers; for `n ≥ 1` its factorial moment vanishes because `n * (n - 1)! = n!`. -/
noncomputable def adjacentDifference (n : ℕ) : ℕ →₀ ℤ :=
  single (n - 1) (n : ℤ) - single n 1
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
/-- The auxiliary coordinate `u n = (U n) 1` of the isolated channel unit, the integer weight that `U n` places on index `1`. -/
noncomputable def channelScalar (n : ℕ) : ℤ := isolatedChannelUnit n 1
/-- The greatest common divisor of the absolute values `|u n|` over the finite range `D + 1 ≤ n ≤ N`, as a natural number; the empty range gives `0`. -/
noncomputable def finiteScalarGcd (D N : ℕ) : ℕ :=
  (Finset.Icc (D + 1) N).gcd (fun n => (channelScalar n).natAbs)
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
/-- The content of `f`, the greatest common divisor of the absolute values of its coefficients over its support; the zero vector has content `0`. -/
noncomputable def coefficientContent (f : ℕ →₀ ℤ) : ℕ :=
  f.support.gcd (fun n => (f n).natAbs)
end PalomarCorpus.E68.MomentIdeal
