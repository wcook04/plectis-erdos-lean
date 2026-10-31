/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E269_01

Every non-theorem declaration of `PalomarCorpus/E269_01/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Polynomial
open scoped BigOperators
open Finset

namespace PalomarCorpus.E269_01.Shared
/-- The Hecke--Mahler series `F_θ(β,α) = ∑_{n≥1} ∑_{k=1}^{⌊nθ⌋} β^n α^k`. The outer index runs over all `n ≥ 0`; the inner sum is empty at `n = 0`. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.heckeMahlerSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def heckeMahlerSeries (θ β α : ℝ) : ℝ :=
  ∑' n : ℕ, ∑ k ∈ Finset.Icc 1 ⌊(n : ℝ) * θ⌋₊, β ^ n * α ^ k
/-- Bugeaud and Laurent, Theorem 1.1, in the case `ρ = 0` due to Loxton and van der Poorten, Theorem 8, p. 40: the Hecke--Mahler series takes transcendental values at nonzero algebraic arguments inside the stated region. This is the one external input of the two-prime theorem. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.BugeaudLaurentTranscendence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def BugeaudLaurentTranscendence : Prop :=
  ∀ θ β α : ℝ, Irrational θ → 0 < θ → θ < 1 →
    IsAlgebraic ℚ β → IsAlgebraic ℚ α → β ≠ 0 → α ≠ 0 →
    |β| < 1 → |β| * |α| ^ θ < 1 →
    Transcendental ℚ (heckeMahlerSeries θ β α)
/-- The smooth lattice value `p ^ i * q ^ j * r ^ k` attached to the exponent triple `(i, j, k)`. -/
noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k
/-- The three-prime height `H x = p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x`, the product of the largest powers of `p`, `q` and `r` not exceeding `x`; the `Nat.log` convention makes `H 0 = H 1 = 1`, and for pairwise distinct primes and `x` at least 1 this is the least common multiple of the smooth numbers at most `x`. -/
noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x
/-- The rational running-LCM kernel at the exponent triple `(i, j, k)`, the inverse in the rationals of the natural-number three-prime height of `p ^ i * q ^ j * r ^ k`. -/
noncomputable def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹
end PalomarCorpus.E269_01.Shared

namespace PalomarCorpus.E269.PaperStatementsX
open Polynomial
open scoped BigOperators
export PalomarCorpus.E269_01.Shared (BugeaudLaurentTranscendence heckeMahlerSeries)
/-- The positive `{p,q}`-smooth integers. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.SmoothSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SmoothSet (p q : ℕ) : Set ℕ := {n : ℕ | 0 < n ∧ ∃ i j : ℕ, n = p ^ i * q ^ j}
/-- The exponent pairs of the actual `{p,q}`-smooth prefix up to `x`. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.smoothPrefixPairs, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def smoothPrefixPairs (p q x : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.range (Nat.log p x + 1)) ×ˢ (Finset.range (Nat.log q x + 1))).filter
    fun e => p ^ e.1 * q ^ e.2 ≤ x)
/-- The literal running least common multiple of the `{p,q}`-smooth numbers `≤ x`. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.runningLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def runningLcm (p q x : ℕ) : ℕ :=
  (smoothPrefixPairs p q x).lcm fun e => p ^ e.1 * q ^ e.2
/-- The distinct values taken by the running LCM on the positive smooth integers. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.runningLcmValues, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def runningLcmValues (p q : ℕ) : Set ℕ := (runningLcm p q) '' SmoothSet p q
/-- `D_{p,q}`: each distinct running LCM counted once. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.distinctSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def distinctSum (p q : ℕ) : ℝ :=
  ∑' H : runningLcmValues p q, (((H : ℕ) : ℝ))⁻¹
/-- `R_{p,q}`: the reciprocal running LCM summed at every positive `{p,q}`-smooth integer. Local copy of ErdosProblems.Erdos269.PaperCompleteR21.repeatedSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def repeatedSum (p q : ℕ) : ℝ :=
  ∑' n : SmoothSet p q, ((runningLcm p q (n : ℕ) : ℝ))⁻¹
end PalomarCorpus.E269.PaperStatementsX

namespace PalomarCorpus.E269.PaperStatementsY
open Polynomial
open scoped BigOperators
export PalomarCorpus.E269_01.Shared (BugeaudLaurentTranscendence heckeMahlerSeries)
/-- Exact value named `A` on the page; this definition makes no arithmetic assertion. Local copy of ErdosProblems.Erdos269.PaperR7.twoPrimeHeckeValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def twoPrimeHeckeValue (p q : ℕ) : ℝ :=
  ∑' n : ℕ, ((p : ℝ)⁻¹) ^ n *
    ((q : ℝ)⁻¹) ^ ⌊(n : ℝ) * Real.logb q p⌋₊
end PalomarCorpus.E269.PaperStatementsY

namespace PalomarCorpus.E269.PaperStatementsD
open Finset
open scoped BigOperators
export PalomarCorpus.E269_01.Shared (smooth3Val threePrimeHeight threePrimeKernelQ)
/-- Literal real logarithmic-cell relation from the paper. Local copy of ErdosProblems.Erdos269.PaperCompleteR20.SameThreePrimeRealLogCell, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SameThreePrimeRealLogCell (p q r : ℕ) (x y : ℝ) : Prop :=
  ⌊Real.logb p x⌋₊ = ⌊Real.logb p y⌋₊ ∧
    ⌊Real.logb q x⌋₊ = ⌊Real.logb q y⌋₊ ∧
      ⌊Real.logb r x⌋₊ = ⌊Real.logb r y⌋₊
/-- Exponent triples in the paper's real half-open shell. Local copy of ErdosProblems.Erdos269.PaperCompleteR20.realSmoothExponentShell, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realSmoothExponentShell
    (p q r : ℕ) (lo hi : ℝ) (hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (hp + 1)).product
      ((range (hq + 1)).product (range (hr + 1)))).filter
    fun e => lo ≤ (smooth3Val p q r e.1 e.2.1 e.2.2 : ℝ) ∧
      (smooth3Val p q r e.1 e.2.1 e.2.2 : ℝ) < hi
/-- Local copy of ErdosProblems.Erdos269.PaperR10.realPrefixExponents, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realPrefixExponents (p q r : ℕ) (x : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (⌊Real.logb p x⌋₊ + 1)).product
    ((Finset.range (⌊Real.logb q x⌋₊ + 1)).product
      (Finset.range (⌊Real.logb r x⌋₊ + 1)))).filter
        (fun e => (smooth3Val p q r e.1 e.2.1 e.2.2 : ℝ) ≤ x)
/-- Local copy of ErdosProblems.Erdos269.PaperR10.realPrefixLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realPrefixLcm (p q r : ℕ) (x : ℝ) : ℕ :=
  (realPrefixExponents p q r x).lcm
    (fun e => smooth3Val p q r e.1 e.2.1 e.2.2)
/-- Local copy of ErdosProblems.Erdos269.PaperR10.realThreePrimeHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realThreePrimeHeight (p q r : ℕ) (x : ℝ) : ℕ :=
  p ^ ⌊Real.logb p x⌋₊ * q ^ ⌊Real.logb q x⌋₊ * r ^ ⌊Real.logb r x⌋₊
end PalomarCorpus.E269.PaperStatementsD

namespace PalomarCorpus.E269.PaperStatementsA
open scoped BigOperators
/-- The first `count` positive powers of one prime base. Exponent zero is omitted because it is the common initial value `1` in every channel. Local copy of ErdosProblems.Erdos269.positivePrimePowers, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positivePrimePowers (p count : ℕ) : Finset ℕ :=
  (Finset.range count).image fun e => p ^ (e + 1)
/-- The finite union of the first `count` positive powers in each of the three prime channels. Local copy of ErdosProblems.Erdos269.threePrimePositiveJumpSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def threePrimePositiveJumpSet (p q r count : ℕ) : Finset ℕ :=
  (positivePrimePowers p count ∪ positivePrimePowers q count) ∪
    positivePrimePowers r count
/-- The finite jump set including the unique common origin `1`. Local copy of ErdosProblems.Erdos269.threePrimeJumpSetWithOrigin, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def threePrimeJumpSetWithOrigin (p q r count : ℕ) : Finset ℕ :=
  insert 1 (threePrimePositiveJumpSet p q r count)
end PalomarCorpus.E269.PaperStatementsA

namespace PalomarCorpus.E269.ThreePrimeStructure
export PalomarCorpus.E269_01.Shared (smooth3Val threePrimeHeight threePrimeKernelQ)
/-- The rectangular index set of exponent triples `(i, j, k)` with `i ≤ hp`, `j ≤ hq` and `k ≤ hr`. -/
noncomputable def smoothExponentBox (hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (hp + 1)).product
    ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))
/-- The three-prime height of the smooth value of the exponent triple `e`, that is `H (p ^ e.1 * q ^ e.2.1 * r ^ e.2.2)`. -/
noncomputable def smoothPointHeight (p q r : ℕ) (e : ℕ × ℕ × ℕ) : ℕ :=
  threePrimeHeight p q r (smooth3Val p q r e.1 e.2.1 e.2.2)
/-- The subset of the exponent box with bounds `hp`, `hq`, `hr` on which the point height equals `H`, that is one fibre of the height map over that box. -/
noncomputable def smoothHeightFiber
    (p q r hp hq hr H : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (smoothExponentBox hp hq hr).filter fun e => smoothPointHeight p q r e = H
end PalomarCorpus.E269.ThreePrimeStructure

namespace PalomarCorpus.E269.PaperStatementsB
end PalomarCorpus.E269.PaperStatementsB
