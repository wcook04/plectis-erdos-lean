/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #243, the weighted record excess family

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #243, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #243 remains open, and no theorem in
this entry decides it.
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
/-- Exact reformulation in the record coordinates: for `a` strictly increasing positive integers with reciprocal sum the rational `p / q`, `q > 0`, and `a (n+1) / a n ^ 2 → 1`, and for a weight `f` that is nonnegative and antitone on `[1, ∞)` with `∫_1^x f → ∞`, the sequence satisfies `a (n+1) = a n ^ 2 - a n + 1` from some index onward if and only if the weighted record-excess series `∑ (-V n - B)_+ f (U n)` over strict record indices is summable for some natural baseline `B`. The hypotheses of the problem do not supply that summability, so this is an equivalent restatement of the question rather than a resolution of it. -/
theorem weighted_record_excess (a : ℕ → ℕ) (ha : StrictMono a)
    (hapos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hg : Tendsto (fun n => (a (n+1) : ℝ) / (a n : ℝ)^2) atTop (𝓝 1))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : Tendsto (fun x : ℝ => ∫ t in (1 : ℝ)..x, f t) atTop atTop) :
    (∃ N, ∀ n, N ≤ n → (a (n+1) : ℤ) = (a n : ℤ)^2 - a n + 1) ↔
      ∃ B : ℕ, Summable (weight a p q B f) := by
  sorry
/-- The growth-defect form of the weighted record-excess summand: at an index `n` where `U (n+1)` strictly exceeds `U j` for every `j ≤ n`, the real value `U n * f (U n) * max (a n ^ 2 / a (n+1) - 1 - B / U n) 0` written in the original growth coordinates, and the value `0` at every other index. -/
noncomputable def growthWeight (a : ℕ → ℕ) (p : ℤ) (q B : ℕ)
    (f : ℝ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if (∀ j ≤ n, U a p q j < U a p q (n+1)) then
    (U a p q n : ℝ) * f (U a p q n) *
      max ((a n : ℝ)^2 / (a (n+1) : ℝ) - 1 - (B : ℝ) / U a p q n) 0
  else 0
/-- The same exact reformulation with the summand expressed in the original growth coordinates: under the same hypotheses on `a` and on the weight `f`, the sequence satisfies `a (n+1) = a n ^ 2 - a n + 1` from some index onward if and only if `∑ U n f (U n) (a n ^ 2 / a (n+1) - 1 - B / U n)_+` over strict record indices is summable for some natural baseline `B`. This is an equivalent restatement of the question in the problem's own growth quantity, and it establishes nothing about the value. -/
theorem weighted_growth_record_excess (a : ℕ → ℕ) (ha : StrictMono a)
    (hapos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hg : Tendsto (fun n => (a (n+1) : ℝ) / (a n : ℝ)^2) atTop (𝓝 1))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : Tendsto (fun x : ℝ => ∫ t in (1 : ℝ)..x, f t) atTop atTop) :
    (∃ N, ∀ n, N ≤ n → (a (n+1) : ℤ) = (a n : ℤ)^2 - a n + 1) ↔
      ∃ B : ℕ, Summable (growthWeight a p q B f) := by
  sorry
end PalomarCorpus.E243.WeightedRecordExcess
