/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #269, record sections 9 to 10: the remaining arithmetic questions; further examples, conditional lemmas and source references

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #269, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #269 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators

namespace PalomarCorpus.E269_07.Shared
/-- Local copy of ErdosProblems.Erdos269.PaperR7.Exponent235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev Exponent235 := ℕ × ℕ × ℕ
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
/-- The three-prime height `H x = p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x`, the product of the largest powers of `p`, `q` and `r` not exceeding `x`; the `Nat.log` convention makes `H 0 = H 1 = 1`, and for pairwise distinct primes and `x` at least 1 this is the least common multiple of the smooth numbers at most `x`. -/
noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x
/-- The window base of the sequence `b` from index `lo` over `len` steps, the product `b lo * b (lo + 1) * ... * b (lo + len - 1)` defined by recursion on `len` with the empty product equal to 1. -/
noncomputable def windowBase (b : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 1
  | len + 1 => b (lo + len) * windowBase b lo len
/-- The accumulated forcing of the digit sequence `e` along the radix sequence `b` from index `lo`, defined by value 0 at length 0 and by `b (lo + len) * F + e (lo + len)` at length `len + 1`, where `F` is the value at length `len`. -/
noncomputable def windowForcing (b e : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 0
  | len + 1 => b (lo + len) * windowForcing b e lo len + e (lo + len)
end PalomarCorpus.E269_07.Shared

namespace PalomarCorpus.E269.PaperStatementsA
open scoped BigOperators
export PalomarCorpus.E269_07.Shared (Exponent235 Smooth235 dyadicSmoothShell235 exponentValue235 paperSeries235 smooth3Val smoothPrefixExponents smoothPrefixLcm smoothReciprocal235 strictSmoothExponents strictSmoothShell threePrimeHeight)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.cubicShiftCoefficient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cubicShiftCoefficient : ℕ → ℤ
  | 0 => 1
  | 1 => -3
  | 2 => 3
  | _ => -1
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.entryStrip, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def entryStrip {α : Type*} [DecidableEq α] (T : ℕ → Finset α) : ℕ → Finset α
  | 0 => T 0
  | n + 1 => T (n + 1) \ T n
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.triangleLogPoint, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def triangleLogPoint (v : ℕ × ℕ) : ℝ :=
  (v.1 : ℝ) * Real.logb 2 3 + (v.2 : ℝ) * Real.logb 2 5
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.triangleTheta, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def triangleTheta (p : ℕ) : ℝ := 1 / Real.logb 2 p
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.triangleOddPart, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def triangleOddPart (v : ℕ × ℕ) : ℕ := 3 ^ v.1 * 5 ^ v.2
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.literalTriangle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def literalTriangle (a : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (a + 1)).product (Finset.range (a + 1))).filter
    (fun v => triangleOddPart v < 2 ^ (a + 1))
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.phaseFloor, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def phaseFloor (p a : ℕ) (t : ℝ) : ℤ :=
  ⌊((a : ℝ) + t) * triangleTheta p⌋
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.phaseCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def phaseCarry (p a : ℕ) (t : ℝ) (u : ℕ) : ℤ :=
  phaseFloor p (a + u) t - phaseFloor p a t - phaseFloor p u 0
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.phaseChi, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def phaseChi (a : ℕ) (t : ℝ) (u : ℕ) : ℝ :=
  (3 : ℝ) ^ (-phaseCarry 3 a t u) * (5 : ℝ) ^ (-phaseCarry 5 a t u)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.phaseOmega, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def phaseOmega (a : ℕ) (t : ℝ) : ℝ :=
  (3 : ℝ) ^ (phaseFloor 3 a 1 - phaseFloor 3 a t) *
    (5 : ℝ) ^ (phaseFloor 5 a 1 - phaseFloor 5 a t)
/-- Number of shell points before the new `p`-power threshold. Local copy of ErdosProblems.Erdos269.dyadicBeforeThresholdCount235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicBeforeThresholdCount235 (p a : ℕ) : ℕ :=
  ((dyadicSmoothShell235 a).filter fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      p ^ Nat.log p (2 ^ (a + 1))).card
/-- The source-faithful ordered block digit. Its coefficients are the suffix products from processing the later odd jump first: `10,4` when the `3`-jump precedes the `5`-jump, and `2,12` in the reverse order. Local copy of ErdosProblems.Erdos269.dyadicOrderedBlockDigit235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicOrderedBlockDigit235 (a : ℕ) : ℕ :=
  if 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤ 5 ^ Nat.log 5 (2 ^ (a + 1)) then
    (dyadicSmoothShell235 a).card +
      10 * dyadicBeforeThresholdCount235 3 a +
      4 * dyadicBeforeThresholdCount235 5 a
  else
    (dyadicSmoothShell235 a).card +
      2 * dyadicBeforeThresholdCount235 3 a +
      12 * dyadicBeforeThresholdCount235 5 a
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.recodedCoefficient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def recodedCoefficient (q a : ℕ) : ℝ :=
  (dyadicOrderedBlockDigit235 a : ℝ) * (q : ℝ) ^ (a + 1) /
    (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.shiftHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev shiftHeight (n : ℕ) : ℕ := threePrimeHeight 2 3 5 (2 ^ n)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.shiftGamma, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftGamma (a t : ℕ) : ℝ :=
  (shiftHeight t : ℝ) * (shiftHeight (a + 1) : ℝ) / (shiftHeight (a + t + 1) : ℝ)
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.shiftedNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftedNumerator (c : ℕ → ℤ) (σ r a : ℕ) : ℝ :=
  15 * ∑ j ∈ Finset.range (σ + 1), (c j : ℝ) * shiftGamma a (j * r) *
    (dyadicOrderedBlockDigit235 (a + j * r) : ℝ)
/-- States long269:res:strip-decomposition from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.actual_cubic_no_crossing_strips in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem actual_cubic_no_crossing_strips (a r : ℕ)
    (hcross : ∀ ν : ℕ, ν ≤ 3 → ∀ v ∈ literalTriangle (a + ν * r),
      phaseCarry 3 a (Int.fract (triangleLogPoint v)) (ν * r) = 0 ∧
      phaseCarry 5 a (Int.fract (triangleLogPoint v)) (ν * r) = 0) :
    shiftedNumerator cubicShiftCoefficient 3 r a / 15 =
      -(∑ v ∈ literalTriangle (a + r) \ literalTriangle a,
          phaseOmega a (Int.fract (triangleLogPoint v))) +
        2 * (∑ v ∈ literalTriangle (a + 2 * r) \ literalTriangle (a + r),
          phaseOmega a (Int.fract (triangleLogPoint v))) -
        (∑ v ∈ literalTriangle (a + 3 * r) \ literalTriangle (a + 2 * r),
          phaseOmega a (Int.fract (triangleLogPoint v))) := by
  sorry
/-- States long269:res:strip-decomposition from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.actual_weighted_strip_decomposition in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem actual_weighted_strip_decomposition (c : ℕ → ℤ) (σ r a : ℕ) :
    shiftedNumerator c σ r a / 15 =
      ∑ s ∈ Finset.range (σ + 1),
        ∑ v ∈ entryStrip (fun n => literalTriangle (a + n * r)) s,
          phaseOmega a (Int.fract (triangleLogPoint v)) *
            ∑ ν ∈ Finset.Icc s σ, (c ν : ℝ) *
              phaseChi a (Int.fract (triangleLogPoint v)) (ν * r) := by
  sorry
/-- States long269:res:fixed-base-recoding from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.fixed_base_recoding_whole in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fixed_base_recoding_whole :
    (HasSum (fun a : ℕ => recodedCoefficient 30 a / (30 : ℝ) ^ (a + 1)) (paperSeries235 / 2)) ∧
    (Summable (fun a : ℕ => |recodedCoefficient 30 a / (30 : ℝ) ^ (a + 1)|)) ∧
    (HasSum (fun a : ℕ => recodedCoefficient 8 a / (8 : ℝ) ^ (a + 1)) (paperSeries235 / 2)) ∧
    (Summable (fun a : ℕ => |recodedCoefficient 8 a / (8 : ℝ) ^ (a + 1)|)) ∧
    (∀ a : ℕ, (∃ z : ℕ, 0 < z ∧ recodedCoefficient 30 a = (z : ℝ)) ∧
      (15 / 4 : ℝ) ^ (a + 1) ≤ recodedCoefficient 30 a) ∧
    (∀ a : ℕ, (∃ z : ℕ, recodedCoefficient 8 a = (z : ℝ) / (15 : ℝ) ^ (a + 1)) ∧
      0 < recodedCoefficient 8 a ∧ recodedCoefficient 8 a < 225 * ((a + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ q : ℕ, 2 ≤ q →
      ((∀ n : ℕ, 1 ≤ n → threePrimeHeight 2 3 5 (2 ^ n) ∣ q ^ n) ↔ 30 ∣ q) ∧
      ∀ a : ℕ, ((q : ℝ) / 8) ^ (a + 1) ≤ recodedCoefficient q a) := by
  sorry
end PalomarCorpus.E269.PaperStatementsA

namespace PalomarCorpus.E269.PaperStatementsC
open scoped BigOperators
export PalomarCorpus.E269_07.Shared (Exponent235 Smooth235 dyadicSmoothShell235 exponentValue235 paperSeries235 smooth3Val smoothPrefixExponents smoothPrefixLcm smoothReciprocal235 strictSmoothExponents strictSmoothShell threePrimeHeight)
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
/-- The exact all-denominator, all-start nonintegrality statement of the long record. Local copy of ErdosProblems.Erdos269.PaperR7.AllReducedTailsNonintegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def AllReducedTailsNonintegral : Prop :=
  ∀ B : ℕ, 0 < B → Nat.Coprime B 30 → ∀ a : ℕ, 1 ≤ a →
    ∀ z : ℤ, (B : ℝ) * trueNormalizedState a ≠ (z : ℝ)
/-- States long269:res:tails-equivalence from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.allReducedTailsNonintegral_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem allReducedTailsNonintegral_iff :
    AllReducedTailsNonintegral ↔ Irrational paperSeries235 := by
  sorry
end PalomarCorpus.E269.PaperStatementsC

namespace PalomarCorpus.E269.PaperStatementsG
open scoped BigOperators
export PalomarCorpus.E269_07.Shared (windowBase windowForcing)
/-- States long269:long:denominator-reduction from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.conditional_denominator_reduction_real_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem conditional_denominator_reduction_real_bound
    (c d b m : ℕ → ℤ) (s B : ℤ) (hs : 0 < s)
    (hfactor : ∀ n, c n = s * d n)
    (hrec : ∀ n, c (n + 1) = b n * c n - (s * B) * m n) :
    (∀ n, d (n + 1) = b n * d n - B * m n) ∧
    (∀ lo len, d (lo + len) = windowBase b lo len * d lo -
      B * windowForcing b m lo len) ∧
    (∀ n (t : ℝ),
      (0 < c n ∧ (c n : ℝ) ≤ ((s * B : ℤ) : ℝ) * t) ↔
        (0 < d n ∧ (d n : ℝ) ≤ (B : ℝ) * t)) := by
  sorry
end PalomarCorpus.E269.PaperStatementsG

namespace PalomarCorpus.E269.CarryMechanism
open scoped BigOperators
export PalomarCorpus.E269_07.Shared (windowBase windowForcing)
/-- The representative of the integer `x` modulo `C` in the range 1 to `C`, equal to `C` when `C` divides `x` and to the ordinary nonnegative remainder otherwise, so a zero residue class is recorded as `C` rather than as 0; for `C = 0` the value is `Int.natAbs x`. -/
noncomputable def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ :=
  if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))
/-- The escape proposition at a radix sequence `b`, a digit sequence `m` and a short bound: for every positive `B` coprime to 30 and every starting index there are a later index `lo` and a positive length `len` with nonzero window base such that the least positive residue of `-B` times the window forcing, modulo the absolute window base, exceeds the short bound evaluated at `B` and `lo + len`. It is named as a proposition and is not asserted. -/
noncomputable def CofinalLocalWindowEscape
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ) : Prop :=
  ∀ B : ℕ, 0 < B → Nat.Coprime B 30 →
    ∀ lo₀ : ℕ, ∃ lo len : ℕ,
      lo₀ ≤ lo ∧ 0 < len ∧
      0 < Int.natAbs (windowBase (fun n => b n) lo len) ∧
      shortBound B (lo + len) <
        leastPositiveResidue
          (Int.natAbs (windowBase (fun n => b n) lo len))
          (-((B : ℤ) *
            windowForcing (fun n => b n) (fun n => m n) lo len))
/-- If the cofinal local-window escape holds for a radix sequence `b`, a digit sequence `m` and a short bound, then for every positive `B` coprime to 30 there is no integer sequence `d` that satisfies `d (n + 1) = b n * d n - B * m n` at every index, is positive at every index, and has absolute value at most the short bound at `B` and `n` at every index. The escape proposition is a hypothesis here rather than a theorem. -/
theorem no_positive_reducedCarry_of_cofinalLocalWindowEscape
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ)
    (hescape : CofinalLocalWindowEscape b m shortBound)
    (B : ℕ) (hBpos : 0 < B) (hBcoprime : Nat.Coprime B 30)
    (d : ℕ → ℤ)
    (hrec : ∀ n,
      d (n + 1) = (b n : ℤ) * d n - (B : ℤ) * (m n : ℤ))
    (hpos : ∀ n, 0 < d n)
    (hbound : ∀ n, Int.natAbs (d n) ≤ shortBound B n) :
    False := by
  sorry
end PalomarCorpus.E269.CarryMechanism
