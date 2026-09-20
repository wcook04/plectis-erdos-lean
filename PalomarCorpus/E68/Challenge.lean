/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős Problem 68

Erdős asked whether `S = ∑_{n ≥ 2} 1/(n! - 1)` is irrational. That question is
open and no theorem here decides it.

The principal result is the common denominator growth bound. For
`L N = lcm_{2 ≤ n ≤ N} (n! - 1)`, the lower limit of
`log (L N) / (N^(3/2) · log N)` is at least `2√2/3`, stated both as an
eventual lower bound and as a literal `EReal` liminf. `L N` is a common
denominator of the partial sums. It is not the reduced denominator of a
rational representation of `S`, so the bound closes the clearing route that
multiplies a prefix by its full least common multiple and proves nothing
about irrationality.

The strongest reduction is multiplicative successor rigidity. Write `H m` for
the exact rational prefix, `Z m = ⌊m! · H m⌋ + 1`, and `b m` for the carry in
`Z m = m · Z (m - 1) + 1 - b m`. If `S` is rational then `Z m = m · Z (m - 1)`
eventually and every fixed positive modulus eventually divides `Z m`, so
cofinal failure of one congruence fixed in advance implies irrationality. No
such failure is produced here.

Exact reformulations: rationality is equivalent to eventual unit carries, to
eventual `m ∣ Z m`, and, through the companion constant
`C = ∑_{n ≥ 2} 1/(n!(n! - 1)) = S - e + 2`, to `⌊m! · C⌋ ≡ -2 (mod m)`
eventually. Each is an equivalence in both directions and produces no cofinal
event.

Channel calculus: the divisor channel basis and its isolated units, the exact
attainable moment ideal at each depth `D ≥ 2`, the residual transparency
identity, the finite prime pole residue formula, and the prime unit
translator with its remote factorial grid reduction.

Route closures: the square subsequence channel radius bounds, the adjacent
unit carry window, and fixed owner absorption. Finite exclusions: a non unit
carry at `m ≥ 3` forces `q ∤ (m - 1)!` for every displayed denominator `q`,
and the explicit floors `2^39990 ≤ q`, `10^12040 < q`.
-/

open Filter
open scoped BigOperators
open Finsupp
open Filter Topology

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
/-- For `m ≥ 3`, the carries at `m` and at `m + 1` are both equal to `1` if and only if `0 < Ω m` and `Ω m ≤ D m`; a pair of consecutive unit carries is therefore exactly the membership of one integer in a half open window of width `D m`. -/
theorem consecutive_unit_carries_iff_positive_offset_le_den {m : ℕ} (hm : 3 ≤ m) :
    (stepCarry m = 1 ∧ stepCarry (m + 1) = 1) ↔
      0 < windowOffset m ∧ windowOffset m ≤ windowDen m := by
  sorry
/-- For `m ≥ 3`, the natural number identity `(predecessorScaled (m + 2)).den * G (m + 1) * G m = (predecessorScaled m).den * (m! - 1) * ((m + 1)! - 1)` holds, so the reduced predecessor denominator telescopes across two steps independently of the carry values. -/
theorem twoStep_den_mul_transitionNormalizers {m : ℕ} (hm : 3 ≤ m) :
    (predecessorScaled (m + 2)).den * transitionNormalizer (m + 1) *
      transitionNormalizer m = (predecessorScaled m).den *
        (m.factorial - 1) * ((m + 1).factorial - 1) := by
  sorry
/-- For `m ≥ 3`, the window denominator satisfies `D m = (predecessorScaled (m + 2)).den * G (m + 1) * G m` as an integer, the integer form of the preceding telescope. -/
theorem adjacentUnitCarryWindowDen_eq_twoStep_den {m : ℕ} (hm : 3 ≤ m) :
    windowDen m = ((predecessorScaled (m + 2)).den : ℤ) *
      transitionNormalizer (m + 1) * transitionNormalizer m := by
  sorry
/-- For `m ≥ 3`, the offset factors exactly as `Ω m = predecessorNumerator (m + 2) * G (m + 1) * G m + D m * ((m + 1) * b m + b (m + 1) - (m + 2))`; when both carries equal `1` the bracket vanishes, the common normaliser cancels against the telescoped denominator, and the whole window reduces to `0 < predecessorNumerator (m + 2) ≤ (predecessorScaled (m + 2)).den`, an inequality that every reduced gap in `(0, 1]` already satisfies, so this window by itself excludes no pair of consecutive unit carries. -/
theorem adjacentUnitCarryWindowOffset_eq_twoStep_factorization {m : ℕ} (hm : 3 ≤ m) :
    windowOffset m = predecessorNumerator (m + 2) * transitionNormalizer (m + 1) *
      transitionNormalizer m + windowDen m *
        (((m + 1 : ℕ) : ℤ) * stepCarry m + stepCarry (m + 1) - (m + 2 : ℤ)) := by
  sorry
end PalomarCorpus.E68.AdjacentUnitCarryWindow

namespace PalomarCorpus.E68.ChannelRadius
export PalomarCorpus.E68.Shared (channelLCM)
/-- If `t ≥ 2^32`, the natural number `M` is positive and divisible by `channelLCM (2 * t^2)`, and `M < (R + 1)! - 1`, then `3 * t^3 < 2 * (R + 1)`; in the intended reading `M` is a positive factorial moment clearing every channel modulus through `2 * t^2` and staying below `(R + 1)! - 1`, and `R + 1` is a support radius, which the conclusion places above `(3/2) * t^3`. -/
theorem square_subsequence_radius_three_halves_lower
    {t M R : ℕ} (ht : 2 ^ 32 ≤ t)
    (hMpos : 0 < M)
    (hdiv : channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    3 * t ^ 3 < 2 * (R + 1) := by
  sorry
/-- For natural number sequences `M` and `R` satisfying, at every `t ≥ 2^32`, positivity of `M t`, divisibility of `M t` by `channelLCM (2 * t^2)` and `M t < (R t + 1)! - 1`, there is no threshold `T` beyond which `2 * (R t + 1) ≤ 3 * t^3`; the reverse of the sharper cubic bound cannot hold from some point on. -/
theorem no_eventual_square_subsequence_three_halves_upper
    (M R : ℕ → ℕ)
    (hMpos : ∀ t, 2 ^ 32 ≤ t → 0 < M t)
    (hdiv : ∀ t, 2 ^ 32 ≤ t → channelLCM (2 * t ^ 2) ∣ M t)
    (hsmall : ∀ t, 2 ^ 32 ≤ t →
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T, ∀ t, T ≤ t → 2 * (R t + 1) ≤ 3 * t ^ 3 := by
  sorry
/-- Under the same hypotheses imposed at every `t ≥ 4096`, the real valued sequence `R t + 1` is not little o of `t^3` along the filter at infinity, both sides being natural number values cast to the reals. -/
theorem not_isLittleO_square_subsequence_radius
    (M R : ℕ → ℕ)
    (hMpos : ∀ t, 4096 ≤ t → 0 < M t)
    (hdiv : ∀ t, 4096 ≤ t → channelLCM (2 * t ^ 2) ∣ M t)
    (hsmall : ∀ t, 4096 ≤ t →
      M t < (R t + 1).factorial - 1) :
    ¬ (fun t : ℕ => ((R t + 1 : ℕ) : ℝ)) =o[Filter.atTop]
        (fun t : ℕ => (t : ℝ) ^ 3) := by
  sorry
/-- If `t ≥ 4096`, `M` is positive and divisible by `channelLCM (2 * t^2)`, and `M < (R + 1)! - 1`, then `t^3 < 8 * (R + 1)`; this is the coarser explicit constant, available on the range `4096 ≤ t < 2^32`, which lies below the threshold of the stronger bound. -/
theorem square_subsequence_radius_cubic_lower
    {t M R : ℕ} (ht : 4096 ≤ t)
    (hMpos : 0 < M)
    (hdiv : channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    t ^ 3 < 8 * (R + 1) := by
  sorry
/-- For natural number sequences satisfying the same hypotheses at every `t ≥ 4096`, there is no threshold `T` beyond which `8 * (R t + 1) ≤ t^3`. -/
theorem no_eventual_square_subsequence_cubic_upper
    (M R : ℕ → ℕ)
    (hMpos : ∀ t, 4096 ≤ t → 0 < M t)
    (hdiv : ∀ t, 4096 ≤ t → channelLCM (2 * t ^ 2) ∣ M t)
    (hsmall : ∀ t, 4096 ≤ t →
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T, ∀ t, T ≤ t → 8 * (R t + 1) ≤ t ^ 3 := by
  sorry
/-- Boundary statement about the finite logarithmic constraint itself: for `t ≥ 4` and `R` with `9 * (R + 1) = 16 * t^3`, one has `2 * t * (u * log u - u - log 2) < (R + 1) * log (R + 1) + (2 * t + 1).choose 3 * log (2 * t^2)`, where `u = 2 * t^2 + 1 - 2 * t` is formed in the natural numbers and then cast to the reals; the constraint is satisfied at radius `(16/9) * t^3`, so it forces no lower bound at that constant by itself, and it bounds no support radius. -/
theorem sharp_radius_satisfies_square_log_constraint
    {t R : ℕ} (ht : 4 ≤ t) (hsharp : 9 * (R + 1) = 16 * t ^ 3) :
    (2 * t : ℝ) *
          (((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) *
              Real.log ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) -
            (2 * t ^ 2 + 1 - 2 * t : ℕ) - Real.log 2) <
        ((R + 1 : ℕ) : ℝ) * Real.log (R + 1 : ℝ) +
          (((2 * t + 1).choose 3 : ℕ) : ℝ) *
            Real.log ((2 * t ^ 2 : ℕ) : ℝ) := by
  sorry
end PalomarCorpus.E68.ChannelRadius

namespace PalomarCorpus.E68.CommonDenominatorGrowth
open Filter
export PalomarCorpus.E68.Shared (channelLCM)
/-- The predicate that the lower limit of a real sequence `f` is at least `c`, written out as: for every real `a < c`, the inequality `a < f n` holds for all sufficiently large `n`. -/
noncomputable def LowerLimitAtLeast (f : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ a : ℝ, a < c → ∀ᶠ n : ℕ in atTop, a < f n
/-- The lower limit of `log (channelLCM N) / (N * √N * log N)` is at least `2√2/3`, where `channelLCM N` is the least common multiple of `n! - 1` over `2 ≤ n ≤ N` and `N * √N` is the real form of `N^(3/2)`; this bounds the growth of a common denominator of the partial sums, and it bounds no reduced denominator of a rational representation of the series. -/
theorem common_denominator_growth :
    LowerLimitAtLeast
      (fun N : ℕ => Real.log (channelLCM N : ℝ) /
        ((N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)))
      (2 * Real.sqrt 2 / 3) := by
  sorry
/-- The same bound in literal extended real form: the coercion of `2√2/3` is at most the `liminf` at infinity of the extended real values of `log (channelLCM N) / (N^(3/2) * log N)`, the exponent taken as a real power; the extended real codomain allows an infinite lower limit with no boundedness hypothesis; as at the preceding declaration, this bounds a common denominator of the partial sums and bounds no reduced denominator of a rational representation of the series. -/
theorem common_denominator_growth_liminf :
    ((2 * Real.sqrt 2 / 3 : ℝ) : EReal) ≤
      Filter.liminf (fun N : ℕ =>
        ((Real.log (channelLCM N : ℝ) /
          ((N : ℝ) ^ ((3 : ℝ) / 2) * Real.log (N : ℝ)) : ℝ) : EReal)) atTop := by
  sorry
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
/-- The strict successor carry boundary, in four exact conjuncts: `S` fails to be irrational if and only if the carry equals `1` for all sufficiently large `m`; `S` is irrational if and only if the carry differs from `1` for cofinally many `m`; at every `m ≥ 3` the carry equals `1` if and only if `m` divides `strictFacTopRat (H m) m`; and `S` is irrational if and only if that divisibility fails cofinally. These are reformulations over exact rational prefixes, with no real approximation and no prime restriction, and they supply no cofinal failure. -/
theorem companionOrbitBoundary_strictSuccessorCarry :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → factorialGapStepCarry m = 1) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧ factorialGapStepCarry m ≠ 1) ∧
    (∀ m : ℕ, 3 ≤ m →
      (factorialGapStepCarry m = 1 ↔
        (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m)) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬((m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m)) := by
  sorry
/-- At an arbitrary real base point `x`, two exact criteria for the shifted number `x + ∑_{n ≥ 2} 1/n!`: it fails to be irrational if and only if the canonical factorial digits of `x` are eventually equal to the integer `m - 2`, and equally if and only if `⌊m! * x⌋ + 2` has integer remainder `0` modulo `m` for all sufficiently large `m`. -/
theorem companionOrbitBoundary_genericShift (x : ℝ) :
    (¬Irrational (x + ∑' n : ℕ, unitFactTerm n) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → canonicalDigit x m = (m : ℤ) - 2) ∧
    (¬Irrational (x + ∑' n : ℕ, unitFactTerm n) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((facFloor x m + 2 : ℤ) % (m : ℤ)) = 0) := by
  sorry
/-- The companion orbit boundary for the series itself: `S` fails to be irrational if and only if `⌊m! * C⌋ + 2` has integer remainder `0` modulo `m` for all sufficiently large `m`, and `S` is irrational if and only if that residue is missed for cofinally many `m`, with `C` the fixed companion constant; the statement identifies the required event and does not produce it. -/
theorem companionOrbitBoundary_factorialGapSeries :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) = 0) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) ≠ 0) := by
  sorry
/-- Supporting evaluation for the companion decomposition: the sum of the anchored unit factorial terms equals `exp 1 - 2`, which is the identity making `C + (e - 2) = S`. -/
theorem tsum_unitFactTerm_eq_exp_one_sub_two :
    (∑' n : ℕ, unitFactTerm n) = Real.exp 1 - 2 := by
  sorry
end PalomarCorpus.E68.CompanionOrbitBoundary

namespace PalomarCorpus.E68.FactorialGapBounds
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E68.Shared (channelLCM)
/-- For 2 ≤ m < n, the gcd of m! − 1 and n! − 1 divides and is at most the descending-factorial product minus one, which is strictly less than n^(n − m). -/
theorem factorial_gap_gcd_exact
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) :
    let g := Nat.gcd (m.factorial - 1) (n.factorial - 1)
    let Q := n.descFactorial (n - m)
    g ∣ Q - 1 ∧ g ≤ Q - 1 ∧ Q - 1 < n ^ (n - m) := by
  sorry
/-- The sum of log(n! − 1) over the final k indices through D is at most log(channelLCM D) plus binomial(k + 1, 3) log D, for k < D. -/
theorem factorialGapSegment_log_sum_le_channelLCM_add_choose
    {D k : ℕ} (hkD : k < D) :
    (∑ n ∈ Finset.Ico (D + 1 - k) (D + 1),
      Real.log ((n.factorial - 1 : ℕ) : ℝ)) ≤
      Real.log (channelLCM D : ℝ) +
        (((k + 1).choose 3 : ℕ) : ℝ) * Real.log (D : ℝ) := by
  sorry
end PalomarCorpus.E68.FactorialGapBounds

namespace PalomarCorpus.E68.FiniteDenominator
export PalomarCorpus.E68.Shared (factorialGapSeries)
/-- If `q` is a positive natural number, `a` is an integer and `S = a / q`, then `2^39990 ≤ q` and `10^12040 < q`; no reducedness or certificate validity hypothesis is imposed, so every displayed rational representation of the series has denominator above both explicit floors. This is one finite exclusion and it does not decide irrationality. -/
theorem finite_denominator_exclusion (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hS : factorialGapSeries = (a : ℝ) / q) :
    (2 : ℕ) ^ 39990 ≤ q ∧ (10 : ℕ) ^ 12040 < q := by
  sorry
end PalomarCorpus.E68.FiniteDenominator

namespace PalomarCorpus.E68.KempnerIndex
open scoped BigOperators
export PalomarCorpus.E68.Shared (factorialGapPredecessorGap factorialGapPrefix factorialGapSeries factorialGapStepCarry strictFacTop)
/-- If `m ≥ 3`, the carry at `m` differs from `1`, `q` is a positive natural number and `S = a / q` for an integer `a`, then `q` does not divide `(m - 1)!`; equivalently one non unit carry at `m` forces the Kempner index of every displayed denominator, the least `k` with `q ∣ k!`, to be at least `m`. -/
theorem rational_denominator_not_dvd_pred_factorial_of_nonunit_carry
    {m q : ℕ} {a : ℤ}
    (hm : 3 ≤ m)
    (hmiss : factorialGapStepCarry m ≠ 1)
    (hq : 0 < q)
    (hseries :
      factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    ¬ (q ∣ (m - 1).factorial) := by
  sorry
/-- The instance of the preceding exclusion at the exact carry certificate of index `60`: if `q` is a positive natural number and `S = a / q` for an integer `a`, then `q` does not divide `59!`. -/
theorem rational_denominator_not_dvd_fiftynine_factorial
    {q : ℕ} {a : ℤ}
    (hq : 0 < q)
    (hseries :
      factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    ¬ (q ∣ Nat.factorial 59) := by
  sorry
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
/-- For `D ≥ 2` and a prime `p` with `D / 2 < p ≤ D`, where `D / 2` is natural division, an integer `m` is the factorial moment of some admissible vector annihilating the channels `2` through `D` if and only if `minimumMoment D p` divides `m`; the attainable moments are exactly that ideal. -/
theorem attainable_moment_ideal {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) (m : ℤ) :
    AttainsMoment D m ↔ minimumMoment D p ∣ m := by
  sorry
/-- For `D ≥ 2` and a prime `p` with `D / 2 < p ≤ D`: the generator `minimumMoment D p` is positive, it generates exactly the attainable moments, and it is realised by an admissible vector that annihilates the channels `2` through `D` and is primitive. -/
theorem exact_moment_ideal_with_primitive_attainment {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    0 < minimumMoment D p ∧
    (∀ m : ℤ, AttainsMoment D m ↔ minimumMoment D p ∣ m) ∧
    ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧
      factorialMoment f = minimumMoment D p ∧ PrimitiveVector f := by
  sorry
/-- Under the same hypotheses, some admissible vector annihilating the channels `2` through `D` has factorial moment exactly `minimumMoment D p` and coefficient content `1`. -/
theorem minimum_moment_content_one {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧
      factorialMoment f = minimumMoment D p ∧ coefficientContent f = 1 := by
  sorry
/-- Under the same hypotheses on two eligible primes `p` and `q`, both satisfying `D / 2 < p ≤ D` and `D / 2 < q ≤ D`, the values `minimumMoment D p` and `minimumMoment D q` coincide, so the generator does not depend on the prime used to cut the finite horizon. -/
theorem minimumMoment_independent_prime {D p q : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D)
    (hq : q.Prime) (hDq : D / 2 < q) (hqD : q ≤ D) :
    minimumMoment D p = minimumMoment D q := by
  sorry
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
/-- Conditional criterion: if for every bound `B` there are naturals `m ≥ 4` and a prime `q` with `B < m / 2 + 1`, with `q` a large prefix private prime of `m! - 1`, and with the block parameter `p = m / 2 + 1`, the division taken in the natural numbers, satisfying both `(2 * p + 1) * (block common denominator) < (tail scale) * (complementary residue of the block tail numerator modulo the private modulus)` and `(2 * p + 1) * (collision core) * q < (tail scale)`, then `S` is irrational. The hypothesis is a cofinal certificate and this entry does not supply it. -/
theorem movingPrivateFactorScaleSplit_implies_irrational
    (hcert :
      ∀ B : ℕ, ∃ m q : ℕ,
        4 ≤ m ∧
        B < m / 2 + 1 ∧
        q ∈ factorialGapLargePrefixPrivatePrimes m ∧
        factorialBlockBudget (m / 2 + 1) *
              factorialBlockEndpointLcm (m / 2 + 1) <
          factorialBlockScale (m / 2 + 1) *
            complementaryProjectedResidue
              (factorialBlockTailNumerator (m / 2 + 1))
              (factorialBlockPrivateModulus (m / 2 + 1)) ∧
        factorialBlockBudget (m / 2 + 1) *
              factorialBlockCollisionCore (m / 2 + 1) * q <
          factorialBlockScale (m / 2 + 1)) :
    Irrational factorialGapSeries := by
  sorry
/-- Conditional criterion with arbitrary split factors: if for every bound `B` there are a prime `p > B` and naturals `a` and `b` dividing the private modulus of the block at `p`, with that modulus greater than `1`, with the complementary residues of the block tail numerator modulo the two leave one out moduli different, and with `(2 * p + 1) * (normalised collision core) * max a b < 2 * p^2 * (2 * p - 1)! / (p - 1)!`, then `S` is irrational. The two factors need not come from distinct denominator owners, and the cofinal certificate is not supplied here. -/
theorem splitFactorNormalizedCollision_implies_irrational
    (hcert :
      ∀ B : ℕ, ∃ p a b : ℕ,
        p.Prime ∧
        B < p ∧
        a ∣ factorialBlockPrivateModulus p ∧
        b ∣ factorialBlockPrivateModulus p ∧
        1 < factorialBlockPrivateModulus p ∧
        complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockFactorProjectionModulus p a) ≠
          complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockFactorProjectionModulus p b) ∧
        factorialBlockBudget p *
              factorialBlockNormalizedCollisionCore p * max a b <
          2 * p ^ 2 * factorialBlockUpperDescFactorial p) :
    Irrational factorialGapSeries := by
  sorry
/-- Route closure: if `i ≥ 2`, `j ≥ 2` and the larger of `i! - 1` and `j! - 1` is smaller than `p`, then both private quotients in the block at `p` are exactly `1`; a fixed pair of denominator owners is absorbed by the factorial base `(p - 1)!` once `p` passes it, so no fixed pair can feed the preceding criteria cofinally. -/
theorem fixedOwnerPair_eventually_absorbed
    {p i j : ℕ}
    (hi : 2 ≤ i)
    (hj : 2 ≤ j)
    (hlt :
      max (factorialGapDenominator i)
          (factorialGapDenominator j) < p) :
    factorialBlockPrivateQuotient p i = 1 ∧
      factorialBlockPrivateQuotient p j = 1 := by
  sorry
end PalomarCorpus.E68.MovingFactorScaleSplit

namespace PalomarCorpus.E68.MultiplicativeSuccessorRigidity
open scoped BigOperators
export PalomarCorpus.E68.Shared (factorialGapPrefix factorialGapSeries strictFacTopRat)
/-- The strict successor `Z m = ⌊m! * H m⌋ + 1` of the exact rational prefix, the least integer strictly above the factorially scaled prefix at index `m`. -/
noncomputable def gapSuccessor (m : ℕ) : ℤ :=
  strictFacTopRat (factorialGapPrefix m) m
/-- If `m ≥ 3` and `m` divides `Z m`, then `Z m = m * Z (m - 1)`; a unit carry removes the additive term from the strict successor recurrence. -/
theorem gapSuccessor_eq_mul_pred_of_dvd
    {m : ℕ} (hm : 3 ≤ m) (h : (m : ℤ) ∣ gapSuccessor m) :
    gapSuccessor m = (m : ℤ) * gapSuccessor (m - 1) := by
  sorry
/-- If `M ≥ 3`, every `k ≥ M` satisfies `k ∣ Z k`, and `M ≤ j + 1`, then `Z j` divides `Z m` for every `m ≥ j`; on the branch that rationality would force the strict successors form a divisibility chain. -/
theorem gapSuccessor_dvd_of_eventually_dvd
    {M : ℕ} (hM : 3 ≤ M)
    (h : ∀ k, M ≤ k → (k : ℤ) ∣ gapSuccessor k)
    {j : ℕ} (hj : M ≤ j + 1) :
    ∀ m, j ≤ m → gapSuccessor j ∣ gapSuccessor m := by
  sorry
/-- Under the same hypotheses, `j! * Z m = m! * Z j` for every `m ≥ j`, so the quotient `Z m / m!` is constant from index `j` onward. -/
theorem factorial_mul_gapSuccessor_eq_of_eventually_dvd
    {M : ℕ} (hM : 3 ≤ M)
    (h : ∀ k, M ≤ k → (k : ℤ) ∣ gapSuccessor k)
    {j : ℕ} (hj : M ≤ j + 1) :
    ∀ m, j ≤ m →
      (j.factorial : ℤ) * gapSuccessor m = (m.factorial : ℤ) * gapSuccessor j := by
  sorry
/-- If `d` is a positive natural number and `S` fails to be irrational, then there is a bound `B` with `d ∣ Z m` for every `m > B`; on the rational branch every fixed modulus eventually divides the strict successor. -/
theorem eventually_dvd_gapSuccessor_of_not_irrational
    {d : ℕ} (hd : 0 < d)
    (hrat : ¬ Irrational factorialGapSeries) :
    ∃ B : ℕ, ∀ m : ℕ, B < m → (d : ℤ) ∣ gapSuccessor m := by
  sorry
/-- The contrapositive producer: if `d` is a positive natural number and for every bound `B` there is `m > B` with `d` not dividing `Z m`, then `S` is irrational. The hypothesis is cofinal failure of one congruence fixed in advance, and this entry does not establish it for any `d`. -/
theorem irrational_factorialGapSeries_of_cofinal_not_dvd_gapSuccessor
    {d : ℕ} (hd : 0 < d)
    (h : ∀ B : ℕ, ∃ m : ℕ, B < m ∧ ¬ (d : ℤ) ∣ gapSuccessor m) :
    Irrational factorialGapSeries := by
  sorry
/-- The case `d = 2` of the preceding criterion: if for every bound `B` there is `m > B` with `Z m` odd, then `S` is irrational. -/
theorem irrational_factorialGapSeries_of_cofinal_odd_gapSuccessor
    (h : ∀ B : ℕ, ∃ m : ℕ, B < m ∧ ¬ (2 : ℤ) ∣ gapSuccessor m) :
    Irrational factorialGapSeries := by
  sorry
/-- If `S` fails to be irrational, then there is a bound `B` beyond which `Z m` is even, so the strict successors cannot be odd cofinally on the rational branch. -/
theorem not_eventually_odd_gapSuccessor_of_not_irrational
    (hrat : ¬ Irrational factorialGapSeries) :
    ∃ B : ℕ, ∀ m : ℕ, B < m → (2 : ℤ) ∣ gapSuccessor m := by
  sorry
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
/-- If `q` is prime, `e ≥ 1`, no index `n` with `2 ≤ n ≤ M` has `q^(e + 1)` dividing `n! - 1`, and some index has `q^e` dividing `n! - 1`, then in `ZMod q` the prefix numerator equals the image of the cofactor `factorialGapPrefixLCM M / q^e` times the reciprocal residue of the maximal layer; since that cofactor is a unit modulo `q`, the prime power `q^e` survives reduction of the prefix exactly when the reciprocal residue is nonzero. The statement assigns no valuation to the infinite series. -/
theorem factorialGapPrefixLCMNumerator_mod_prime
    {q M e : ℕ}
    (hq : q.Prime)
    (he : 1 ≤ e)
    (hmax :
      ∀ n ∈ Finset.Icc 2 M,
        ¬q ^ (e + 1) ∣ n.factorial - 1)
    (hattain :
      ∃ n ∈ Finset.Icc 2 M,
        q ^ e ∣ n.factorial - 1) :
    (factorialGapPrefixLCMNumerator M : ZMod q) =
      ((factorialGapPrefixLCM M / q ^ e : ℕ) : ZMod q) *
        factorialGapPrincipalResidue q M e := by
  sorry
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
/-- Component fact: for `p > 0` the prime translator has factorial moment zero, since `p * (p - 1)! = p!`. -/
theorem primeTranslator_moment_zero
    {p : ℕ} (hp : 0 < p) :
    factorialMoment (primeTranslatorCoeff p) (primeTranslatorIndex p) = 0 := by
  sorry
/-- Component fact: for a prime `p` and a channel `d` with `2 ≤ d < p`, the channel numerator of the prime translator vanishes. -/
theorem primeTranslator_channel_zero_of_lt_p
    {p d : ℕ} (hp : p.Prime) (hd2 : 2 ≤ d) (hdp : d < p) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by
  sorry
/-- Component fact: for a prime `p` the channel numerator of the prime translator at the channel `p` equals `p! - 1`, exactly the modulus of that channel. -/
theorem primeTranslator_channel_at_prime
    {p : ℕ} (hp : p.Prime) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) p =
      (p.factorial : ℤ) - 1 := by
  sorry
/-- Component fact: for `p > 0` and any channel `d > p`, the channel numerator of the prime translator vanishes. -/
theorem primeTranslator_channel_zero_of_p_lt
    {p d : ℕ} (hp : 0 < p) (hpd : p < d) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by
  sorry
/-- For `2 ≤ D` and a prime `p > D`, the residual of the prime translator beyond the cutoff `D` equals exactly `1`, so the translator is an exact unit direction for the residual. -/
theorem primeTranslator_channelResidual_eq_one
    {D p : ℕ} (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (primeTranslatorCoeff p) (primeTranslatorIndex p) = 1 := by
  sorry
/-- For any finite coefficient family, any `2 ≤ D` and any prime `p > D`, enlarging the family by `z` copies of the prime translator changes the residual beyond `D` by exactly the integer `z` and leaves the rest of the residual unchanged. -/
theorem channelResidual_appendPrimeTranslator
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) {D p : ℕ} (z : ℤ)
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (appendPrimeTranslatorCoeff coeff p z)
        (appendPrimeTranslatorIndex index p) =
      channelResidual D coeff index + (z : ℝ) := by
  sorry
/-- For every cutoff parameter `n` and every support threshold `B` there exist a prime `p` and an integer `z` such that the Cramer coefficient vector on the factorial grid starting at `B + 1`, enlarged by `z` copies of the prime translator at `p`, has every support index above `B`, has vanishing channel numerator at every `d` with `2 ≤ d ≤ n + 2`, has nonzero factorial moment, and has residual beyond `n + 2` of absolute value at most `1/2`. The bound is not strict, so the reduced residual may be an integer, and no nonintegrality is asserted. -/
theorem exists_remote_factorialGrid_primeTranslator_reduction
    (n B : ℕ) :
    ∃ p : ℕ, ∃ z : ℤ,
      p.Prime ∧
      (∀ j : Sum (Fin (n + 2)) (Fin 2),
        B < appendPrimeTranslatorIndex
          (factorialGridIndex n (B + 1)) p j) ∧
      (∀ d ∈ Finset.Icc 2 (n + 2),
        channelNumerator
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p) d = 0) ∧
      factorialMoment
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p) ≠ 0 ∧
      |channelResidual (n + 2)
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p)| ≤ (1 : ℝ) / 2 := by
  sorry
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
/-- The transparency identity: for `D ≥ 2`, an integer `t` and coordinates `z` vanishing below `D`, the full residual of `t • K D + channelSynthesis z` equals `t * L D * (S - H D) + coordinateMass z`; the residual of every vector written in the low channel normal form of the statement is therefore the scaled factorial gap tail plus an integer, so an integral channel correction can move it only by an integer. -/
theorem residual_transparency {D : ℕ} (hD : 2 ≤ D) (t : ℤ)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    fullResidual (t • canonicalKernel D + channelSynthesis z) =
      (t : ℝ) * (channelLCM D : ℝ) *
        (factorialGapSeries - gapPrefixReal D) +
      (coordinateMass z : ℝ) := by
  sorry
/-- Supporting convergence lemma: for a finitely supported integer vector `f` with `f 0 = 0`, the family of channel contributions `fullResidualTerm f` is summable. The hypothesis `f 0 = 0` excludes the index 0 coefficient, whose channel weight is 1 in every channel; the statement assumes it and this entry does not establish whether it can be dropped. -/
theorem summable_fullResidual {f : ℕ →₀ ℤ} (h0 : f 0 = 0) :
    Summable (fullResidualTerm f) := by
  sorry
/-- If `f 0 = 0` and the factorial moment of `f` vanishes, then the full residual of `f` is an integer. The hypothesis `f 0 = 0` excludes the index 0 coefficient, whose channel weight is 1 in every channel; the statement assumes it and this entry does not establish whether it can be dropped. -/
theorem zero_moment_residual_integral {f : ℕ →₀ ℤ}
    (h0 : f 0 = 0) (hm : factorialMoment f = 0) :
    ∃ k : ℤ, fullResidual f = (k : ℝ) := by
  sorry
/-- If `f 0 = 0`, `g 0 = 0` and `f` and `g` have the same factorial moment, then their full residuals differ by an integer, so on vectors vanishing at index `0` the factorial moment fixes the residual class modulo the integers. The hypothesis `f 0 = 0` excludes the index 0 coefficient, whose channel weight is 1 in every channel; the statement assumes it and this entry does not establish whether it can be dropped. -/
theorem equal_moment_residual_integer_difference {f g : ℕ →₀ ℤ}
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hm : factorialMoment f = factorialMoment g) :
    ∃ k : ℤ, fullResidual f - fullResidual g = (k : ℝ) := by
  sorry
end PalomarCorpus.E68.ResidualIntegerClass

namespace PalomarCorpus.E68.StrictSuccessorCarry
export PalomarCorpus.E68.Shared (companionConstant facFloor factorialGapPredecessorGap factorialGapPrefix factorialGapStepCarry strictFacTop strictFacTopRat)
/-- The Erdős 68 series `S = ∑_{d ≥ 2} 1/(d! - 1)`, restated in this namespace with the terms at `d ≤ 1` set to zero. -/
noncomputable def factorialGapSeries : ℝ :=
  ∑' d : ℕ, if 1 < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))
  else 0
/-- The fixed companion orbit characterisation in both directions: `S` fails to be irrational if and only if `⌊m! * C⌋ + 2` has integer remainder `0` modulo `m` for all sufficiently large `m`, and `S` is irrational if and only if that residue is missed for cofinally many `m`. Neither direction produces the cofinal miss. -/
theorem companionOrbit_completeCharacterization :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) = 0) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) ≠ 0) := by
  sorry
/-- The complete strict successor characterisation in four conjuncts: eventual unit carries characterise failure of irrationality, cofinally many non unit carries characterise irrationality, at every `m ≥ 3` a unit carry is equivalent to `m` dividing `strictFacTopRat (H m) m`, and cofinal failure of that divisibility again characterises irrationality. The equivalences transfer the question to exact rational prefixes and supply no cofinal failure. -/
theorem strictSuccessorCarry_completeCharacterization :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → factorialGapStepCarry m = 1) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧ factorialGapStepCarry m ≠ 1) ∧
    (∀ m : ℕ, 3 ≤ m →
      (factorialGapStepCarry m = 1 ↔
        (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m)) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬((m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m)) := by
  sorry
end PalomarCorpus.E68.StrictSuccessorCarry
