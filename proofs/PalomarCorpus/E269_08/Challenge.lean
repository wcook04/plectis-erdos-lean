/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #269, note sections 2 to 5: nonsingular minors of every order; the recurrence for the repeated sum; a window test and the remaining arithmetic

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #269, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #269 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators

namespace PalomarCorpus.E269_08.Shared
/-- The predicate that the power `p ^ e` lies strictly inside the dyadic block from `2 ^ a` to `2 ^ (a + 1)`, that is `2 ^ a < p ^ e` and `p ^ e < 2 ^ (a + 1)`; for an odd prime `p` it records that a new pure `p`-power is crossed strictly between two consecutive powers of two, so that the running least common multiple gains one further factor `p` inside that block. -/
noncomputable def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)
/-- Local copy of ErdosProblems.Erdos269.PaperR7.Exponent235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev Exponent235 := ℕ × ℕ × ℕ
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
/-- Local copy of ErdosProblems.Erdos269.PaperR7.exponentValue235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exponentValue235 (e : Exponent235) : ℕ :=
  smooth3Val 2 3 5 e.1 e.2.1 e.2.2
/-- Positive smooth integers, counted once as numbers rather than as exponents. Local copy of ErdosProblems.Erdos269.PaperR7.Smooth235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Smooth235 := {x : ℕ // x ∈ Set.range exponentValue235}
/-- The finite index set of exponent triples `(i, j, k)` with `i ≤ Nat.log p x`, `j ≤ Nat.log q x`, `k ≤ Nat.log r x` and smooth value at most `x`; for pairwise distinct primes these are the exponent coordinates of the `{p, q, r}`-smooth numbers not exceeding `x`. -/
noncomputable def smoothPrefixExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (Nat.log p x + 1)).product
      ((Finset.range (Nat.log q x + 1)).product
        (Finset.range (Nat.log r x + 1)))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 ≤ x
/-- The least common multiple of the smooth values `p ^ i * q ^ j * r ^ k` over the index set `smoothPrefixExponents p q r x`, that is the running least common multiple of all `{p, q, r}`-smooth numbers at most `x`. -/
noncomputable def smoothPrefixLcm (p q r x : ℕ) : ℕ :=
  (smoothPrefixExponents p q r x).lcm
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2
/-- The original running-LCM summand at a smooth integer. Local copy of ErdosProblems.Erdos269.PaperR7.smoothReciprocal235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def smoothReciprocal235 (x : Smooth235) : ℝ :=
  (smoothPrefixLcm 2 3 5 x.val : ℝ)⁻¹
/-- The scalar `S` as a sum over actual distinct smooth integers and actual LCMs. Local copy of ErdosProblems.Erdos269.PaperR7.paperSeries235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperSeries235 : ℝ := ∑' x : Smooth235, smoothReciprocal235 x
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
end PalomarCorpus.E269_08.Shared

namespace PalomarCorpus.E269.PaperStatementsA
open scoped BigOperators
export PalomarCorpus.E269_08.Shared (smooth3Val threePrimeHeight)
/-- The literal reduction: invert the natural running-LCM height modulo B. Local copy of ErdosProblems.Erdos269.PaperR7.kernelMod235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def kernelMod235 (B i j k : ℕ) : ZMod B :=
  (threePrimeHeight 2 3 5 (smooth3Val 2 3 5 i j k) : ZMod B)⁻¹
/-- The exact rational lattice kernel attached to the running-LCM height. Local copy of ErdosProblems.Erdos269.threePrimeKernelQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹
/-- States res:admissible-modular-minors from the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.admissible_modular_minors in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem admissible_modular_minors (n : ℕ) :
    ∃ I J : Fin n → ℕ, Function.Injective I ∧ Function.Injective J ∧
      (∀ k : ℕ,
        (Matrix.det fun i j : Fin n => threePrimeKernelQ 2 3 5 (I i) (J j) k) ≠ 0) ∧
      (∀ B : ℕ, 2 ≤ B → Nat.Coprime B 30 → ∀ k : ℕ,
        IsUnit (Matrix.det fun i j : Fin n => kernelMod235 B (I i) (J j) k) ∧
        IsUnit (Matrix.of fun i j : Fin n => kernelMod235 B (I i) (J j) k)) := by
  sorry
end PalomarCorpus.E269.PaperStatementsA

namespace PalomarCorpus.E269.PaperStatementsC
open scoped BigOperators
export PalomarCorpus.E269_08.Shared (DyadicInternalPower Exponent235 Smooth235 dyadicBeforeThresholdCount235 dyadicBlockBase235 dyadicOrderedBlockDigit235 dyadicSmoothShell235 exponentValue235 leastPositiveResidue paperSeries235 smooth3Val smoothPrefixExponents smoothPrefixLcm smoothReciprocal235 strictSmoothExponents strictSmoothShell threePrimeHeight)
/-- A real number is at least `δ` from every integer. Local copy of ErdosProblems.Erdos269.FarFromIntegers, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FarFromIntegers (x δ : ℝ) : Prop :=
  ∀ z : ℤ, δ ≤ |x - (z : ℝ)|
/-- Normalize a real source tail by half of the current endpoint height. Local copy of ErdosProblems.Erdos269.dyadicNormalizedTailStateR235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicNormalizedTailStateR235 (tail : ℕ → ℝ) (a : ℕ) : ℝ :=
  ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a
/-- Literal reciprocal running-height mass of one half-open dyadic shell. Local copy of ErdosProblems.Erdos269.dyadicShellMassQ235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicShellMassQ235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    ((threePrimeHeight 2 3 5
      (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹)
/-- Real-valued shell mass used by the actual infinite analytic tail. Local copy of ErdosProblems.Erdos269.dyadicShellMassR235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicShellMassR235 (a : ℕ) : ℝ :=
  dyadicShellMassQ235 a
/-- The literal infinite tail beginning at dyadic shell `a`. Local copy of ErdosProblems.Erdos269.dyadicShellTsumTailR235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ :=
  ∑' n : ℕ, dyadicShellMassR235 (a + n)
/-- The genuine infinite normalized tail state. Local copy of ErdosProblems.Erdos269.trueNormalizedState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def trueNormalizedState (a : ℕ) : ℝ :=
  dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a
/-- The forcing digit as printed in the short note, before any regrouping. Local copy of ErdosProblems.Erdos269.PaperR7.literalForcing235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def literalForcing235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) /
      (2 * (threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ))
/-- A canonical integer-valued representative; equality to the scaled state is proved below. Local copy of ErdosProblems.Erdos269.PaperR7.paperReducedCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperReducedCarry (B a : ℕ) : ℤ :=
  ⌊(B : ℝ) * trueNormalizedState a⌋
/-- States res:dyadic-alphabet from the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.dyadic_alphabet_whole in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadic_alphabet_whole :
    (∀ a : ℕ,
      (∃ m : ℕ, 0 < m ∧ literalForcing235 a = (m : ℚ)) ∧
      (dyadicBlockBase235 a = 2 ∨ dyadicBlockBase235 a = 6 ∨
        dyadicBlockBase235 a = 10 ∨ dyadicBlockBase235 a = 30)) ∧
    literalForcing235 4 = 65 ∧ dyadicBlockBase235 4 = 30 ∧
    (∃ a : ℕ, dyadicBlockBase235 a < dyadicOrderedBlockDigit235 a) := by
  sorry
/-- States res:consumer from the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.paper_finite_endpoint_obstruction in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_finite_endpoint_obstruction {W K : ℕ} {d B F : ℤ}
    (hW : 0 < W) (hd : 0 < d) (hbound : d ≤ (K : ℤ))
    (hmod : Int.ModEq (W : ℤ) d (-B * F)) :
    leastPositiveResidue W (-B * F) ≤ K := by
  sorry
/-- States res:actual-orbit from the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.short_actual_orbit in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem short_actual_orbit :
    Summable smoothReciprocal235 ∧
    (∀ a : ℕ, Summable (fun n : ℕ => dyadicShellMassR235 (a + n))) ∧
    (∀ a : ℕ,
      trueNormalizedState (a + 1) =
        (dyadicBlockBase235 a : ℝ) * trueNormalizedState a -
          (dyadicOrderedBlockDigit235 a : ℝ)) ∧
    (∀ a : ℕ, 0 < trueNormalizedState a ∧
      trueNormalizedState a ≤ (8640 / 343 : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 ∧
      (8640 / 343 : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 <
        90 * ((a + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ B : ℤ,
      (∃ a : ℕ, ∀ n, a ≤ n → ∃ z : ℤ,
        (B : ℝ) * trueNormalizedState n = (z : ℝ)) ∨
      (∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
        FarFromIntegers ((B : ℝ) * trueNormalizedState a) ((1 : ℝ) / 31))) := by
  sorry
/-- States res:denominator-reduction from the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.short_fixed_split_bridge in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem short_fixed_split_bridge {N : ℤ} {D u v w B : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    ∀ a : ℕ, u + 1 + 2 * v + 3 * w ≤ a →
      (paperReducedCarry B a : ℝ) = (B : ℝ) * trueNormalizedState a ∧
      0 < paperReducedCarry B a ∧
      paperReducedCarry B (a + 1) =
        (dyadicBlockBase235 a : ℤ) * paperReducedCarry B a -
          (B : ℤ) * (dyadicOrderedBlockDigit235 a : ℤ) ∧
      paperReducedCarry B a ≤ ((90 * B * (a + 1) ^ 2 : ℕ) : ℤ) := by
  sorry
end PalomarCorpus.E269.PaperStatementsC

namespace PalomarCorpus.E269.PaperStatementsG
open scoped BigOperators
export PalomarCorpus.E269_08.Shared (DyadicInternalPower Exponent235 Smooth235 dyadicBeforeThresholdCount235 dyadicBlockBase235 dyadicOrderedBlockDigit235 dyadicSmoothShell235 exponentValue235 leastPositiveResidue paperSeries235 smooth3Val smoothPrefixExponents smoothPrefixLcm smoothReciprocal235 strictSmoothExponents strictSmoothShell)
/-- Affine forcing accumulated across the same local window. Local copy of ErdosProblems.Erdos269.windowForcing, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowForcing (b e : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 0
  | len + 1 => b (lo + len) * windowForcing b e lo len + e (lo + len)
/-- Local copy of ErdosProblems.Erdos269.PaperR7.actualWindowForcing, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev actualWindowForcing (lo len : ℕ) : ℤ :=
  windowForcing (fun a => (dyadicBlockBase235 a : ℤ))
    (fun a => (dyadicOrderedBlockDigit235 a : ℤ)) lo len
/-- Multiplicative base accumulated across a local window. Local copy of ErdosProblems.Erdos269.windowBase, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowBase (b : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 1
  | len + 1 => b (lo + len) * windowBase b lo len
/-- Local copy of ErdosProblems.Erdos269.PaperR7.actualWindowBase, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev actualWindowBase (lo len : ℕ) : ℤ :=
  windowBase (fun a => (dyadicBlockBase235 a : ℤ)) lo len
/-- The criterion as printed: positive starting thresholds and the literal cap. Local copy of ErdosProblems.Erdos269.PaperR7.ShortPaperEscape, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ShortPaperEscape : Prop :=
  ∀ B : ℕ, 0 < B → Nat.Coprime B 30 → ∀ a₀ : ℕ, 1 ≤ a₀ →
    ∃ lo len : ℕ, a₀ ≤ lo ∧ 0 < len ∧
      90 * B * (lo + len + 1) ^ 2 <
        leastPositiveResidue (Int.natAbs (actualWindowBase lo len))
          (-((B : ℤ) * actualWindowForcing lo len))
/-- States eq:escape, res:windowconsumer from the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.short_window_equivalence in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem short_window_equivalence :
    Irrational paperSeries235 ↔ ShortPaperEscape := by
  sorry
end PalomarCorpus.E269.PaperStatementsG
