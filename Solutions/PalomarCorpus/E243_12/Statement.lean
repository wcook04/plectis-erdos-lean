/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243_12

Every non-theorem declaration of `PalomarCorpus/E243_12/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open scoped Topology

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
