/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E68_06

Every non-theorem declaration of `PalomarCorpus/E68_06/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E68.AdjacentUnitCarryWindow

namespace PalomarCorpus.E68.ChannelRadius
export PalomarCorpus.E68_06.Shared (channelLCM)
end PalomarCorpus.E68.ChannelRadius

namespace PalomarCorpus.E68.CommonDenominatorGrowth
open Filter
export PalomarCorpus.E68_06.Shared (channelLCM)
/-- The predicate that the lower limit of a real sequence `f` is at least `c`, written out as: for every real `a < c`, the inequality `a < f n` holds for all sufficiently large `n`. -/
noncomputable def LowerLimitAtLeast (f : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ a : ℝ, a < c → ∀ᶠ n : ℕ in atTop, a < f n
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
end PalomarCorpus.E68.CompanionOrbitBoundary
