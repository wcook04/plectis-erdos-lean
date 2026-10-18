/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243_11

Every non-theorem declaration of `PalomarCorpus/E243_11/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Finset

namespace PalomarCorpus.E243_11.Shared
/-- The running maximum `max_{k ≤ n} u k` of a natural-valued sequence, given by `runningMax u 0 = u 0` and `runningMax u (n+1) = max (runningMax u n) (u (n+1))`. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
end PalomarCorpus.E243_11.Shared

namespace PalomarCorpus.E243.ProtectedEpochEnergy
export PalomarCorpus.E243_11.Shared (runningMax)
end PalomarCorpus.E243.ProtectedEpochEnergy

namespace PalomarCorpus.E243.RecordAmplifiedCancellationVisibility
export PalomarCorpus.E243_11.Shared (runningMax)
end PalomarCorpus.E243.RecordAmplifiedCancellationVisibility

namespace PalomarCorpus.E243.RecordIncrementBarrier
export PalomarCorpus.E243_11.Shared (runningMax sylvesterNext)
end PalomarCorpus.E243.RecordIncrementBarrier

namespace PalomarCorpus.E243.RepairEntropy
open scoped BigOperators
/-- The deletion product `∏_{s ≤ n < t} c n` of the deletion factors over the half-open window of indices from `s` to `t`, with the empty product `1` when `t ≤ s`. -/
noncomputable def deletionProduct (c : ℕ → ℕ) (s t : ℕ) : ℕ :=
  ∏ n ∈ Finset.Ico s t, c n
/-- The proposition that the modulus `m` is repaired over the window from `s` to `t`, meaning that `m` divides the deletion product `∏_{s ≤ n < t} c n`. -/
noncomputable def repairedAt (c : ℕ → ℕ) (s t m : ℕ) : Prop :=
  m ∣ deletionProduct c s t
end PalomarCorpus.E243.RepairEntropy

namespace PalomarCorpus.E243.SaturatedSquareTransport
end PalomarCorpus.E243.SaturatedSquareTransport

namespace PalomarCorpus.E243.SlowRiseBarrier
end PalomarCorpus.E243.SlowRiseBarrier

namespace PalomarCorpus.E243.SummableNegativeMassRigidity
open scoped BigOperators
open Finset
export PalomarCorpus.E243_11.Shared (sylvesterNext)
/-- The product-cleared denominator update `D ↦ a * D` on the integers, one step of the recurrence `D (n+1) = a n * D n`. -/
noncomputable def nextDenState (a D : ℤ) : ℤ :=
  a * D
/-- The product-cleared tail-numerator update `C ↦ a * C - D` on the integers, obtained by clearing denominators in the tail relation `x n = 1 / a n + x (n+1)`. -/
noncomputable def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D
/-- The centred reciprocal-tail error `D - (a - 1) * C` of an integer state, the integer measuring the failure of the identity `D = (a - 1) * C` that holds exactly on a Sylvester tail. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- The normalised negative mass at index `n`, the real number obtained by dividing the magnitude of the negative part of the integer error `E n`, namely `|min (E n) 0|`, by the natural number `C n` cast to the reals; the definition imposes no positivity on `C n`, and division by zero returns `0` in the reals. -/
noncomputable def negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  (Int.natAbs (min (E n) 0) : ℝ) / C n
/-- The prefix product `a 0 * a 1 * ... * a (n-1)` of the first `n` terms of a natural sequence, with the empty product `1` at `n = 0`. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- The cleared integer numerator `p * P n - ∑_{j < n} q * (P n / a j)` with `P n = ∏_{j < n} a j`, which is `q * P n` times the reciprocal tail `p / q - ∑_{j < n} 1 / a j`; the inner quotient is natural division and is exact for `j < n`. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- The canonical numerator state as a natural number, `Int.toNat` of the cleared integer numerator, hence equal to that integer when it is nonnegative and `0` otherwise. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
/-- The canonical cleared denominator `q * P n` with `P n = ∏_{j < n} a j`, the factor that clears the rational reciprocal sum `p / q` and every term of the preceding finite prefix. -/
noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n
end PalomarCorpus.E243.SummableNegativeMassRigidity
