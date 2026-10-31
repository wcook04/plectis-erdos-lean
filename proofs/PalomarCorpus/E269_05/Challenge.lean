/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #269, record sections 6 to 7: bounding the tails and clearing a rational denominator; a residue criterion and the bounds it allows

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #269, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #269 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Filter
open scoped Topology BigOperators

namespace PalomarCorpus.E269_05.Shared
/-- The predicate that the power `p ^ e` lies strictly inside the dyadic block from `2 ^ a` to `2 ^ (a + 1)`, that is `2 ^ a < p ^ e` and `p ^ e < 2 ^ (a + 1)`; for an odd prime `p` it records that a new pure `p`-power is crossed strictly between two consecutive powers of two, so that the running least common multiple gains one further factor `p` inside that block. -/
noncomputable def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)
/-- The radix of the `a`th dyadic block for the primes 2, 3 and 5: the product of 2 with 3 when some power of 3 lies strictly inside the block from `2 ^ a` to `2 ^ (a + 1)` and with 5 when some power of 5 does, so its value is 2, 6, 10 or 30. It equals the ratio `H (2 ^ (a + 1)) / H (2 ^ a)` of consecutive three-prime running heights. -/
noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 *
        (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
        (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)
/-- The representative of the integer `x` modulo `C` in the range 1 to `C`, equal to `C` when `C` divides `x` and to the ordinary nonnegative remainder otherwise, so a zero residue class is recorded as `C` rather than as 0; for `C = 0` the value is `Int.natAbs x`. -/
noncomputable def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ :=
  if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))
/-- The smooth lattice value `p ^ i * q ^ j * r ^ k` attached to the exponent triple `(i, j, k)`. -/
noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k
/-- The finite set of exponent triples `(i, j, k)`, each entry smaller than `x`, whose smooth value `p ^ i * q ^ j * r ^ k` is strictly less than `x`; for generators at least 2 the entrywise cap is never binding, so the set is exactly the triples whose smooth value is below `x`, and for pairwise distinct primes those values are exactly the `{p, q, r}`-smooth numbers below `x`. -/
noncomputable def strictSmoothExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range x).product ((Finset.range x).product (Finset.range x))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 < x
/-- The exponent triples counted by `strictSmoothExponents` at `y` and not at `x`; for generators at least 2 and `x ≤ y` these are exactly the triples whose smooth value lies in the half open interval from `x` to `y`. -/
noncomputable def strictSmoothShell (p q r x y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothExponents p q r y \ strictSmoothExponents p q r x
/-- The `a`th dyadic shell for the primes 2, 3 and 5: the exponent triples `(i, j, k)` with `2 ^ a ≤ 2 ^ i * 3 ^ j * 5 ^ k < 2 ^ (a + 1)`. -/
noncomputable def dyadicSmoothShell235 (a : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothShell 2 3 5 (2 ^ a) (2 ^ (a + 1))
/-- The number of points of the `a`th dyadic shell whose smooth value is strictly below `p ^ Nat.log p (2 ^ (a + 1))`, the largest power of `p` not exceeding `2 ^ (a + 1)`; for odd `p`, when no power of `p` lies strictly inside the shell that threshold is at most `2 ^ a` and the count is 0, while at `p = 2` the threshold is `2 ^ (a + 1)` and the count is the whole shell. -/
noncomputable def dyadicBeforeThresholdCount235 (p a : ℕ) : ℕ :=
  ((dyadicSmoothShell235 a).filter fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      p ^ Nat.log p (2 ^ (a + 1))).card
/-- The forcing digit of the `a`th dyadic block for the primes 2, 3 and 5: the shell cardinality corrected by the two threshold counts, with coefficients 10 and 4 when the largest power of 3 below `2 ^ (a + 1)` does not exceed the largest power of 5 below it and with coefficients 2 and 12 otherwise. Its ordinary meaning is the sum over the shell of `H (2 ^ (a + 1)) / (2 * H x)`, a positive integer, and the two coefficient patterns record which of the two odd prime thresholds is the smaller. -/
noncomputable def dyadicOrderedBlockDigit235 (a : ℕ) : ℕ :=
  if 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤ 5 ^ Nat.log 5 (2 ^ (a + 1)) then
    (dyadicSmoothShell235 a).card +
      10 * dyadicBeforeThresholdCount235 3 a +
      4 * dyadicBeforeThresholdCount235 5 a
  else
    (dyadicSmoothShell235 a).card +
      2 * dyadicBeforeThresholdCount235 3 a +
      12 * dyadicBeforeThresholdCount235 5 a
/-- The three-prime height `H x = p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x`, the product of the largest powers of `p`, `q` and `r` not exceeding `x`; the `Nat.log` convention makes `H 0 = H 1 = 1`, and for pairwise distinct primes and `x` at least 1 this is the least common multiple of the smooth numbers at most `x`. -/
noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x
/-- The normalized state at scale `a` of an arbitrary real tail function `tail`, namely `(H (2 ^ a) / 2) * tail a` with the three-prime height for 2, 3 and 5 cast to the reals and the division taken in the reals. -/
noncomputable def dyadicNormalizedTailStateR235 (tail : ℕ → ℝ) (a : ℕ) : ℝ :=
  ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a
/-- The rational mass of the `a`th dyadic shell, the sum over that shell of the reciprocal of the three-prime height of the corresponding smooth value. -/
noncomputable def dyadicShellMassQ235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    ((threePrimeHeight 2 3 5
      (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹)
/-- The real cast of the rational shell mass `dyadicShellMassQ235`. -/
noncomputable def dyadicShellMassR235 (a : ℕ) : ℝ :=
  dyadicShellMassQ235 a
/-- The tail of the shell masses from scale `a` onward, taken as the Mathlib unconditional sum of `dyadicShellMassR235 (a + n)` over `n`; summability is proved in `actual_dyadicShellOrbit_recurrence_and_escape`, so this is the genuine infinite sum, and the value at `a = 0` is the reciprocal running least common multiple sum of Erdős problem 269 for the prime set `{2, 3, 5}`. -/
noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ :=
  ∑' n : ℕ, dyadicShellMassR235 (a + n)
/-- The genuine normalized state `(H (2 ^ a) / 2) * T a` of the literal `{2,3,5}` shell tail, that is `dyadicNormalizedTailStateR235` applied to the actual tail `dyadicShellTsumTailR235`. -/
noncomputable def trueNormalizedState (a : ℕ) : ℝ :=
  dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a
end PalomarCorpus.E269_05.Shared

namespace PalomarCorpus.E269.PaperStatementsG
open scoped BigOperators
export PalomarCorpus.E269_05.Shared (dyadicNormalizedTailStateR235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight trueNormalizedState)
/-- The integer-power condition defining the paper's first clearing index. Local copy of ErdosProblems.Erdos269.PaperR13.ClearingCondition, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ClearingCondition (u v w a : ℕ) : Prop :=
  1 ≤ a ∧ 2 ^ (u + 1) ≤ 2 ^ a ∧ 3 ^ v ≤ 2 ^ a ∧ 5 ^ w ≤ 2 ^ a
/-- The paper's elementary bound `a_D = u+1+2v+3w` satisfies all three integer-power thresholds. Local copy of ErdosProblems.Erdos269.PaperR13.clearingCondition_sufficient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def clearingCondition_sufficient (u v w : ℕ) :
    ClearingCondition u v w (u + 1 + 2 * v + 3 * w) := by
  let aD := u + 1 + 2 * v + 3 * w
  have h2 : 2 ^ (u + 1) ≤ 2 ^ aD :=
    Nat.pow_le_pow_right (by norm_num) (by dsimp [aD]; omega)
  have h3four : 3 ^ v ≤ 4 ^ v := Nat.pow_le_pow_left (by norm_num) v
  have h4two : 4 ^ v = 2 ^ (2 * v) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have h3 : 3 ^ v ≤ 2 ^ aD := by
    rw [h4two] at h3four
    exact h3four.trans (Nat.pow_le_pow_right (by norm_num) (by dsimp [aD]; omega))
  have h5eight : 5 ^ w ≤ 8 ^ w := Nat.pow_le_pow_left (by norm_num) w
  have h8two : 8 ^ w = 2 ^ (3 * w) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
  have h5 : 5 ^ w ≤ 2 ^ aD := by
    rw [h8two] at h5eight
    exact h5eight.trans (Nat.pow_le_pow_right (by norm_num) (by dsimp [aD]; omega))
  exact ⟨by omega, h2, h3, h5⟩
/-- The first positive scale satisfying the three integer-power comparisons. Local copy of ErdosProblems.Erdos269.PaperR13.firstClearingIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def firstClearingIndex (u v w : ℕ) : ℕ := by
  classical
  exact Nat.find ⟨u + 1 + 2 * v + 3 * w, clearingCondition_sufficient u v w⟩
/-- Rational mass of the smooth window `[start, start + count)` of shells. Local copy of ErdosProblems.Erdos269.dyadicSmoothWindowMassQ235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicSmoothWindowMassQ235 (start count : ℕ) : ℚ :=
  ∑ i ∈ Finset.range count, dyadicShellMassQ235 (start + i)
/-- Half-height normalizer at scale `a`: the coefficient of the normalized tail state and the clearing denominator of the smooth prefix. Local copy of ErdosProblems.Erdos269.heightNormalizer235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def heightNormalizer235 (a : ℕ) : ℕ :=
  threePrimeHeight 2 3 5 (2 ^ a) / 2
/-- The rational representative of the paper state `X_a`, written from the value `N / D` and the finite rational prefix below scale `a`. Local copy of ErdosProblems.Erdos269.PaperR13.rationalTailState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalTailState (N : ℤ) (D a : ℕ) : ℚ :=
  (heightNormalizer235 a : ℚ) *
    ((N : ℚ) / (D : ℚ) - 1 - dyadicSmoothWindowMassQ235 1 (a - 1))
/-- Local copy of ErdosProblems.Erdos269.PaperR7.Exponent235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev Exponent235 := ℕ × ℕ × ℕ
/-- Local copy of ErdosProblems.Erdos269.PaperR7.exponentValue235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exponentValue235 (e : Exponent235) : ℕ :=
  smooth3Val 2 3 5 e.1 e.2.1 e.2.2
/-- Positive smooth integers, counted once as numbers rather than as exponents. Local copy of ErdosProblems.Erdos269.PaperR7.Smooth235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Smooth235 := {x : ℕ // x ∈ Set.range exponentValue235}
/-- Exponent vectors of the actual `{p,q,r}`-smooth prefix up to `x`. The logarithmic box makes the prefix finite; the final filter keeps only products which really lie below `x`. Local copy of ErdosProblems.Erdos269.smoothPrefixExponents, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def smoothPrefixExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (Nat.log p x + 1)).product
      ((Finset.range (Nat.log q x + 1)).product
        (Finset.range (Nat.log r x + 1)))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 ≤ x
/-- The literal running LCM of the finite smooth prefix. Local copy of ErdosProblems.Erdos269.smoothPrefixLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def smoothPrefixLcm (p q r x : ℕ) : ℕ :=
  (smoothPrefixExponents p q r x).lcm
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2
/-- The original running-LCM summand at a smooth integer. Local copy of ErdosProblems.Erdos269.PaperR7.smoothReciprocal235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def smoothReciprocal235 (x : Smooth235) : ℝ :=
  (smoothPrefixLcm 2 3 5 x.val : ℝ)⁻¹
/-- The scalar `S` as a sum over actual distinct smooth integers and actual LCMs. Local copy of ErdosProblems.Erdos269.PaperR7.paperSeries235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperSeries235 : ℝ := ∑' x : Smooth235, smoothReciprocal235 x
/-- States long269:res:exact-denominator, res:exact-onset from the long record and the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR13.exact_denominators_and_minimal_clearing in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exact_denominators_and_minimal_clearing
    {N : ℤ} {u v w B a : ℕ}
    (hB : 0 < B) (hB30 : Nat.Coprime B 30)
    (hcop : Nat.Coprime N.natAbs (2 ^ u * 3 ^ v * 5 ^ w * B))
    (ha : 1 ≤ a)
    (hval : paperSeries235 =
      (N : ℝ) / ((2 ^ u * 3 ^ v * 5 ^ w * B : ℕ) : ℝ)) :
    ((rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a : ℚ) : ℝ) =
        trueNormalizedState a ∧
      (rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w * B) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      ((B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      (((B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den = 1 ↔
        firstClearingIndex u v w ≤ a) := by
  sorry
end PalomarCorpus.E269.PaperStatementsG

namespace PalomarCorpus.E269.PaperStatementsC
open scoped BigOperators
export PalomarCorpus.E269_05.Shared (DyadicInternalPower dyadicBeforeThresholdCount235 dyadicBlockBase235 dyadicNormalizedTailStateR235 dyadicOrderedBlockDigit235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight trueNormalizedState)
/-- Geometric (unconstrained) quadratic majorant. Local copy of ErdosProblems.Erdos269.carryMajorantQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryMajorantQ (n : ℕ) : ℚ :=
  ((n : ℚ) ^ 2 + 8 * n + 18) / 9
/-- The long record's actual jump index. Local copy of ErdosProblems.Erdos269.PaperR7.paperJumpIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperJumpIndex (a : ℕ) : ℕ := a + Nat.log 3 (2 ^ a) + Nat.log 5 (2 ^ a)
/-- Jump-constrained quadratic majorant. Local copy of ErdosProblems.Erdos269.carryMajorantQtilde, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryMajorantQtilde (n : ℕ) : ℚ :=
  (1210 * (n : ℚ) ^ 2 + 9130 * n + 18847) / 11979
/-- States long269:res:pinning from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.paper_pinning_and_eight_scale_rigidity in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_pinning_and_eight_scale_rigidity :
    (∀ a : ℕ, trueNormalizedState a =
      ((dyadicOrderedBlockDigit235 a : ℝ) + trueNormalizedState (a + 1)) /
        (dyadicBlockBase235 a : ℝ) ∧ 0 < trueNormalizedState a) ∧
    (∀ a : ℕ, ∀ z : ℤ, trueNormalizedState a = (z : ℝ) →
      ∀ n, a ≤ n → ∃ w : ℤ, trueNormalizedState n = (w : ℝ)) ∧
    (∀ (width : ℕ → ℝ) (A : ℕ) (y : ℕ → ℝ),
      (∀ n, 0 < width n) →
      (∀ n, A ≤ n → y (n + 1) =
        (dyadicBlockBase235 n : ℝ) * y n - (dyadicOrderedBlockDigit235 n : ℝ)) →
      (∀ n, A ≤ n →
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < y n ∧
        y n ≤ (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) →
      (∀ n, A ≤ n →
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < trueNormalizedState n ∧
        trueNormalizedState n ≤
          (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) →
      (∀ ε > 0, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → width (A + k) / 8 ^ k < ε) →
      y A = trueNormalizedState A) := by
  sorry
/-- States long269:res:jump-constrained-bound from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR10.actual_sharp_tail_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem actual_sharp_tail_bound (a : ℕ) :
    0 < trueNormalizedState a ∧
    trueNormalizedState a ≤ (carryMajorantQtilde (paperJumpIndex a) : ℝ) ∧
    (carryMajorantQtilde (paperJumpIndex a) : ℝ) <
      (carryMajorantQ (paperJumpIndex a) : ℝ) := by
  sorry
end PalomarCorpus.E269.PaperStatementsC

namespace PalomarCorpus.E269.PaperStatementsB
export PalomarCorpus.E269_05.Shared (leastPositiveResidue)
/-- States long269:res:consumer from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.no_bounded_positive_int_state_of_leastPositiveResidue in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_bounded_positive_int_state_of_leastPositiveResidue
    {C bound : ℕ} {x c : ℤ}
    (hC : 0 < C)
    (hcpos : 0 < c)
    (hcbound : Int.natAbs c ≤ bound)
    (hescape : bound < leastPositiveResidue C x)
    (hmod : Int.ModEq C c x) :
    False := by
  sorry
end PalomarCorpus.E269.PaperStatementsB

namespace PalomarCorpus.E269.FixedStartResidue
open Filter
open scoped Topology BigOperators
export PalomarCorpus.E269_05.Shared (DyadicInternalPower dyadicBeforeThresholdCount235 dyadicBlockBase235 dyadicNormalizedTailStateR235 dyadicOrderedBlockDigit235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 leastPositiveResidue smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight trueNormalizedState)
/-- The accumulated forcing of the digit sequence `e` along the radix sequence `b` from index `lo`, defined by value 0 at length 0 and by `b (lo + len) * F + e (lo + len)` at length `len + 1`, where `F` is the value at length `len`. -/
noncomputable def windowForcing (b e : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 0
  | len + 1 => b (lo + len) * windowForcing b e lo len + e (lo + len)
/-- The product of the actual dyadic radices over the window from lo through lo+len-1; it is 1 for the empty window. -/
noncomputable def actualWindowProduct (lo len : ℕ) : ℕ :=
  ∏ j ∈ Finset.range len, dyadicBlockBase235 (lo + j)
/-- The accumulated integer forcing of the actual dyadic shell digits over a window, using the same affine recurrence as the normalized tail. -/
noncomputable abbrev actualWindowForcing (lo len : ℕ) : ℤ :=
  windowForcing (fun a => (dyadicBlockBase235 a : ℤ))
    (fun a => (dyadicOrderedBlockDigit235 a : ℤ)) lo len
/-- For every fixed positive multiplier B and starting scale lo, the least positive residue of minus B times the window forcing eventually equals (ceil(B X_lo)-B X_lo) times the window product plus B X_(lo+h), including the integral case. -/
theorem eventually_fixedStartResidue_formula (B lo : ℕ) (hB : 0 < B) :
    ∀ᶠ h in atTop,
      (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) =
        ((⌈(B : ℝ) * trueNormalizedState lo⌉ : ℤ) : ℝ) *
            (actualWindowProduct lo h : ℝ) -
          (B : ℝ) * trueNormalizedState lo *
            (actualWindowProduct lo h : ℝ) +
          (B : ℝ) * trueNormalizedState (lo + h) := by
  sorry
/-- At each fixed starting scale and positive multiplier, the least positive residue divided by the window product converges to ceil(B X_lo)-B X_lo. The limit is zero exactly when B X_lo is integral. -/
theorem fixedStartResidue_ratio_tendsto (B lo : ℕ) (hB : 0 < B) :
    Tendsto
      (fun h : ℕ =>
        (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) /
            (actualWindowProduct lo h : ℝ))
      atTop
      (nhds (((⌈(B : ℝ) * trueNormalizedState lo⌉ : ℤ) : ℝ) -
        (B : ℝ) * trueNormalizedState lo)) := by
  sorry
/-- If B X_lo is an integer with B positive, the least positive window residue eventually equals the positive final tail B X_(lo+h), so the integral case is explicitly retained. -/
theorem eventually_fixedStartResidue_eq_tail_of_integral
    (B lo : ℕ) (hB : 0 < B) (hInt : ∃ z : ℤ, (B : ℝ) * trueNormalizedState lo = z) :
    ∀ᶠ h in atTop,
      (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) =
        (B : ℝ) * trueNormalizedState (lo + h) := by
  sorry
end PalomarCorpus.E269.FixedStartResidue
