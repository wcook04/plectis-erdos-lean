/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #68, the adjacent unit carry window, channel radius and common denominator growth families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #68, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #68 remains open, and no theorem in
this entry decides it.
-/

open Filter

namespace PalomarCorpus.E68_06.Shared
/-- The common denominator `L D = lcm (d! - 1)` taken over the channel indices `2 ≤ d ≤ D`, the least common multiple of the denominators of the partial sum through `D`; the index set is empty and the value is `1` when `D < 2`. -/
noncomputable def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)
/-- The exact rational partial sum `H n = ∑_{2 ≤ k ≤ n} 1/(k! - 1)`, computed in `ℚ` with no real approximation; it is `0` for `n < 2`. -/
noncomputable def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)
/-- Computable rational form of `strictFacTop`, used for exact finite certificates while retaining the real-valued statement needed for the series. Local copy of ErdosProblems.Erdos68.strictFacTopRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ := ⌊(n.factorial : ℚ) * x⌋ + 1
end PalomarCorpus.E68_06.Shared

namespace PalomarCorpus.E68.AdjacentUnitCarryWindow
export PalomarCorpus.E68_06.Shared (factorialGapPrefix strictFacTopRat)
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
export PalomarCorpus.E68_06.Shared (channelLCM)
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
export PalomarCorpus.E68_06.Shared (channelLCM)
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
/-- The companion radius-constant bound in the same literal extended real form: if a channel multiple sequence `M` and a radius sequence `R` eventually satisfy `0 < M t`, `channelLCM (2 * t^2) ∣ M t` and `M t < (R t + 1)! - 1`, then the coercion of `16/9` is at most the `liminf` at infinity of the extended real values of `(R t + 1) / t^3`; the hypotheses are the paper's, carried in the signature rather than assumed, and the extended real codomain allows an infinite lower limit with no boundedness hypothesis. -/
theorem asymptotic_radius_constant_liminf (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    (((16 : ℝ) / 9) : EReal) ≤
      Filter.liminf (fun t : ℕ =>
        ((((R t + 1 : ℕ) : ℝ) / (t : ℝ) ^ 3 : ℝ) : EReal)) atTop := by
  sorry
end PalomarCorpus.E68.CommonDenominatorGrowth

namespace PalomarCorpus.E68.CompanionOrbitBoundary
export PalomarCorpus.E68_06.Shared (factorialGapPrefix strictFacTopRat)
/-- The Erdős 68 series `S = ∑_{d ≥ 2} 1/(d! - 1)`, restated in this namespace with the terms at `d ≤ 1` set to zero. -/
noncomputable def factorialGapSeries : ℝ :=
  ∑' d : ℕ, if 1 < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))
  else 0
/-- The companion constant `C = ∑_{n ≥ 2} 1/(n! (n! - 1))`, a convergent real series whose terms are set to zero for `n ≤ 1` and which satisfies `C + (e - 2) = S` for the Erdős 68 series `S`. -/
noncomputable def companionConstant : ℝ :=
  ∑' n : ℕ, if 2 ≤ n then
    (1 : ℝ) /
      ((n.factorial : ℝ) * ((((n.factorial : ℤ) - 1 : ℤ) : ℝ)))
  else 0
/-- The anchored unit factorial term, equal to `1/n!` for `n ≥ 2` and to `0` otherwise. -/
noncomputable def unitFactTerm (n : ℕ) : ℝ :=
  if 2 ≤ n then (1 : ℝ) / ((n.factorial : ℝ)) else 0
/-- The integer `⌊m! * x⌋`, the `m`-th point of the factorial orbit of a real number `x`. -/
noncomputable def facFloor (x : ℝ) (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℝ) * x⌋
/-- The canonical factorial base digit `d m (x) = ⌊m! * x⌋ - m * ⌊(m - 1)! * x⌋` of a real number `x` at radix `m`; for `m ≥ 2` it satisfies `0 ≤ d m (x) < m`. -/
noncomputable def canonicalDigit (x : ℝ) (m : ℕ) : ℤ :=
  facFloor x m - (m : ℤ) * facFloor x (m - 1)
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
