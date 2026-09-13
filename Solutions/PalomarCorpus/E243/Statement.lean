/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243

Every non-theorem declaration of `PalomarCorpus/E243/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open scoped BigOperators
open Finset
open scoped Topology

namespace PalomarCorpus.E243.Shared
/-- The centred reciprocal-tail error `D - (a - 1) * C` of an integer state, the integer measuring the failure of the identity `D = (a - 1) * C` that holds exactly on a Sylvester tail. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- The prefix product `a 0 * a 1 * ... * a (n-1)` of the first `n` terms of a natural sequence, with the empty product `1` at `n = 0`. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- The running maximum `max_{k ≤ n} u k` of a natural-valued sequence, given by `runningMax u 0 = u 0` and `runningMax u (n+1) = max (runningMax u n) (u (n+1))`. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- The Sylvester successor map `a ↦ a ^ 2 - a + 1` on the integers, the multiplier map for which the telescope `1 / (a - 1) = 1 / a + 1 / (sylvesterNext a - 1)` holds, so that a tail with this recurrence has reciprocal sum exactly `1 / (a - 1)`. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
end PalomarCorpus.E243.Shared

namespace PalomarCorpus.E243.BoundedNegativePartRigidity
export PalomarCorpus.E243.Shared (centeredState sylvesterNext)
end PalomarCorpus.E243.BoundedNegativePartRigidity

namespace PalomarCorpus.E243.BoundedRiseReducedTail
end PalomarCorpus.E243.BoundedRiseReducedTail

namespace PalomarCorpus.E243.OriginalCoordinateBoundedDefect
open Filter
export PalomarCorpus.E243.Shared (prefixProduct)
/-- The original-coordinate product defect at index `n`, the real number `(P n / a n) * (a n ^ 2 / a (n+1) - 1)` where `P n = ∏_{j < n} a j`, which weighs the departure from the Sylvester growth relation by the prefix product; the naturals `P n`, `a n` and `a (n+1)` are cast to the reals. -/
noncomputable def productDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)
end PalomarCorpus.E243.OriginalCoordinateBoundedDefect

namespace PalomarCorpus.E243.PeriodicNegativeOrbit
end PalomarCorpus.E243.PeriodicNegativeOrbit

namespace PalomarCorpus.E243.PrimitiveRecordRigidity
export PalomarCorpus.E243.Shared (runningMax sylvesterNext)
end PalomarCorpus.E243.PrimitiveRecordRigidity

namespace PalomarCorpus.E243.ProtectedEpochEnergy
export PalomarCorpus.E243.Shared (runningMax)
end PalomarCorpus.E243.ProtectedEpochEnergy

namespace PalomarCorpus.E243.RecordAmplifiedCancellationVisibility
export PalomarCorpus.E243.Shared (runningMax)
end PalomarCorpus.E243.RecordAmplifiedCancellationVisibility

namespace PalomarCorpus.E243.RecordIncrementBarrier
export PalomarCorpus.E243.Shared (runningMax sylvesterNext)
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
export PalomarCorpus.E243.Shared (centeredState prefixProduct sylvesterNext)
/-- The product-cleared denominator update `D ↦ a * D` on the integers, one step of the recurrence `D (n+1) = a n * D n`. -/
noncomputable def nextDenState (a D : ℤ) : ℤ :=
  a * D
/-- The product-cleared tail-numerator update `C ↦ a * C - D` on the integers, obtained by clearing denominators in the tail relation `x n = 1 / a n + x (n+1)`. -/
noncomputable def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D
/-- The normalised negative mass at index `n`, the real number obtained by dividing the magnitude of the negative part of the integer error `E n`, namely `|min (E n) 0|`, by the natural number `C n` cast to the reals; the definition imposes no positivity on `C n`, and division by zero returns `0` in the reals. -/
noncomputable def negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  (Int.natAbs (min (E n) 0) : ℝ) / C n
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

namespace PalomarCorpus.E243.WeightedRecordExcess
open Filter
open scoped Topology
/-- The cumulative least common multiple `L n = lcm(q, a 0, ..., a (n-1))` of the denominator `q` of the reciprocal sum and the first `n` multipliers, defined by `L 0 = q` and `L (n+1) = lcm (L n) (a n)`. -/
noncomputable def L (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n+1 => Nat.lcm (L q a n) (a n)
/-- The overlap debt `M n`, the accumulated product of the overlaps `gcd (L j) (a j)` for `j < n`, defined by `M 0 = 1` and `M (n+1) = M n * gcd (L n) (a n)`; it records the multiplicity lost when the full cleared scale `q * ∏_{j < n} a j` is compressed to the least common multiple `L n`. -/
noncomputable def M (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => M q a n * Nat.gcd (L q a n) (a n)
/-- The canonical cleared tail numerator as a natural number: `Int.toNat` of `p * P n - ∑_{j < n} q * (P n / a j)` with `P n = ∏_{j < n} a j`, hence `q * P n` times the reciprocal tail `p / q - ∑_{j < n} 1 / a j` whenever that integer is nonnegative, and `0` otherwise. -/
noncomputable def C (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (p * ((∏ j ∈ Finset.range n, a j : ℕ) : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * ((∏ k ∈ Finset.range n, a k : ℕ) / a j : ℕ)).toNat
/-- The numerator in the least common multiple coordinates, `U n = C n / M n`, the natural division of the canonical cleared numerator by the overlap debt, which truncates whenever `M n` fails to divide `C n`. Exactness of that division on the canonical orbit is context and is not imposed by this definition. -/
noncomputable def U (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ := C a p q n / M q a n
/-- The centred error in the least common multiple coordinates, defined as the integer `L n - (a n - 1) * U n`. That it equals the cleared centred error divided by the overlap debt `M n` is a fact about the canonical orbit and is not imposed by this definition. -/
noncomputable def V (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  (L q a n : ℤ) - ((a n : ℤ)-1) * (U a p q n : ℤ)
/-- The weighted record-excess summand: at an index `n` where `U (n+1)` strictly exceeds `U j` for every `j ≤ n`, so that `n + 1` sets a strict record, the real value `(-V n - B)_+ * f (U n)` with the positive part taken by `Int.toNat`, and the value `0` at every other index. -/
noncomputable def weight (a : ℕ → ℕ) (p : ℤ) (q B : ℕ) (f : ℝ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if (∀ j ≤ n, U a p q j < U a p q (n+1)) then
    (((-V a p q n - B).toNat : ℕ) : ℝ) * f (U a p q n) else 0
/-- The growth-defect form of the weighted record-excess summand: at an index `n` where `U (n+1)` strictly exceeds `U j` for every `j ≤ n`, the real value `U n * f (U n) * max (a n ^ 2 / a (n+1) - 1 - B / U n) 0` written in the original growth coordinates, and the value `0` at every other index. -/
noncomputable def growthWeight (a : ℕ → ℕ) (p : ℤ) (q B : ℕ)
    (f : ℝ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if (∀ j ≤ n, U a p q j < U a p q (n+1)) then
    (U a p q n : ℝ) * f (U a p q n) *
      max ((a n : ℝ)^2 / (a (n+1) : ℝ) - 1 - (B : ℝ) / U a p q n) 0
  else 0
end PalomarCorpus.E243.WeightedRecordExcess
