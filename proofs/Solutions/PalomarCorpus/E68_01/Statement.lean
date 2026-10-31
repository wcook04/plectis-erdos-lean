/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E68_01

Every non-theorem declaration of `PalomarCorpus/E68_01/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Finsupp
open Filter Topology
open Filter

namespace PalomarCorpus.E68_01.Shared
/-- The common denominator `L D = lcm (d! - 1)` taken over the channel indices `2 ≤ d ≤ D`, the least common multiple of the denominators of the partial sum through `D`; the index set is empty and the value is `1` when `D < 2`. -/
noncomputable def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)
/-- The exact rational partial sum `H n = ∑_{2 ≤ k ≤ n} 1/(k! - 1)`, computed in `ℚ` with no real approximation; it is `0` for `n < 2`. -/
noncomputable def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)
/-- One summand of the universal factorial-gap tail beyond `D`. Local copy of Erdos68.factorialGapTailTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapTailTerm (D d : ℕ) : ℝ :=
  if D < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)
  else 0
/-- The universal factorial-gap tail beyond `D`. Local copy of Erdos68.factorialGapTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapTail (D : ℕ) : ℝ :=
  ∑' d : ℕ, factorialGapTailTerm D d
/-- The original Erdős #68 series, expressed through the universal factorial-gap tail beginning after `1`. Local copy of Erdos68.factorialGapSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapSeries : ℝ :=
  factorialGapTail 1
/-- The least integer strictly greater than `n! * x` for a real number `x`, namely `⌊n! * x⌋ + 1`. -/
noncomputable def strictFacTop (x : ℝ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℝ) * x⌋ + 1
/-- The predecessor gap `Δ m = Z (m - 1) - (m - 1)! * H (m - 1)`, the distance from the factorially scaled exact prefix at index `m - 1` up to the least integer strictly above it; it lies in the interval `(0, 1]`. -/
noncomputable def factorialGapPredecessorGap (m : ℕ) : ℝ :=
  (strictFacTop
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℝ) -
    ((m - 1).factorial : ℝ) *
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ)
end PalomarCorpus.E68_01.Shared

namespace PalomarCorpus.E68.PaperStatementsA
open scoped BigOperators
open Finsupp
export PalomarCorpus.E68_01.Shared (factorialGapPredecessorGap factorialGapPrefix factorialGapSeries factorialGapTail factorialGapTailTerm strictFacTop)
/-- Floor of the `m!`-scaled real number. Local copy of ErdosProblems.Erdos68.facFloor, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def facFloor (x : ℝ) (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℝ) * x⌋
/-- Fractional remainder after truncation at factorial scale `m!`. Local copy of ErdosProblems.Erdos68.canonicalRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalRemainder (x : ℝ) (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * x - (facFloor x m : ℝ)
/-- Companion-constant term, anchored at `n ≥ 2`. Local copy of ErdosProblems.Erdos68.compConstTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def compConstTerm (n : ℕ) : ℝ :=
  if 2 ≤ n then
    (1 : ℝ) /
      ((((n.factorial : ℕ) : ℝ)) *
        ((((n.factorial : ℤ) - 1 : ℤ) : ℝ)))
  else 0
/-- The fixed companion constant whose factorial orbit controls the carry congruence. Local copy of ErdosProblems.Erdos68.companionConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def companionConstant : ℝ :=
  ∑' n : ℕ, compConstTerm n
/-- The least common multiple of the literal factorial-gap denominators through one prefix endpoint. Local copy of ErdosProblems.Erdos68.factorialGapPrefixLCM, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapPrefixLCM (n : ℕ) : ℕ :=
  (Finset.Icc 2 n).lcm fun k => k.factorial - 1
/-- The exact tail after `m`, scaled by `m!`. Local copy of ErdosProblems.Erdos68.factorialGapScaledTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapScaledTail (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * factorialGapTail m
end PalomarCorpus.E68.PaperStatementsA

namespace PalomarCorpus.E68.PaperStatementsE
open scoped BigOperators
/-- Recursive lcm of a list, normalized to `1` on the empty list. Local copy of Erdos68.listLCM, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def listLCM : List ℕ → ℕ
  | [] => 1
  | a :: tail => Nat.lcm a (listLCM tail)
/-- Product of all pairwise gcd collision terms in a list, with each unordered pair counted once. Local copy of Erdos68.pairwiseGCDProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def pairwiseGCDProduct : List ℕ → ℕ
  | [] => 1
  | a :: tail =>
      (tail.map (Nat.gcd a)).prod * pairwiseGCDProduct tail
end PalomarCorpus.E68.PaperStatementsE

namespace PalomarCorpus.E68.FactorialGapBounds
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E68_01.Shared (channelLCM)
end PalomarCorpus.E68.FactorialGapBounds

namespace PalomarCorpus.E68.CommonDenominatorGrowth
open Filter
export PalomarCorpus.E68_01.Shared (channelLCM)
end PalomarCorpus.E68.CommonDenominatorGrowth

namespace PalomarCorpus.E68.PaperStatementsB
open scoped BigOperators
export PalomarCorpus.E68_01.Shared (factorialGapPredecessorGap factorialGapPrefix factorialGapSeries factorialGapTail factorialGapTailTerm strictFacTop)
/-- The exact rounding carry in the strict-successor recurrence for the Erdős #68 prefixes. Local copy of ErdosProblems.Erdos68.factorialGapStepCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapStepCarry (m : ℕ) : ℤ :=
  -⌊1 + 1 / ((m.factorial : ℝ) - 1) -
      (m : ℝ) * factorialGapPredecessorGap m⌋
/-- Computable rational form of `strictFacTop`, used for exact finite certificates while retaining the real-valued statement needed for the series. Local copy of ErdosProblems.Erdos68.strictFacTopRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1
end PalomarCorpus.E68.PaperStatementsB
