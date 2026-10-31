/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #269, record sections 1 to 2: the problem, and what is settled; the finite geometry of the running value

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #269, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #269 remains open, and no theorem in
this entry decides it.
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
/-- States long269:res:lead-two-prime, res:two-prime-transcendence from the long record and the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR21.two_prime_sums_transcendental in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_prime_sums_transcendental (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Transcendental ℚ (distinctSum p q) ∧ Transcendental ℚ (repeatedSum p q) := by
  sorry
/-- States long269:res:lead-two-prime from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR21.two_prime_transcendence in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_prime_transcendence (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Transcendental ℚ (repeatedSum p q) ∧ Transcendental ℚ (distinctSum p q) := by
  sorry
end PalomarCorpus.E269.PaperStatementsX

namespace PalomarCorpus.E269.PaperStatementsY
open Polynomial
open scoped BigOperators
export PalomarCorpus.E269_01.Shared (BugeaudLaurentTranscendence heckeMahlerSeries)
/-- Exact value named `A` on the page; this definition makes no arithmetic assertion. Local copy of ErdosProblems.Erdos269.PaperR7.twoPrimeHeckeValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def twoPrimeHeckeValue (p q : ℕ) : ℝ :=
  ∑' n : ℕ, ((p : ℝ)⁻¹) ^ n *
    ((q : ℝ)⁻¹) ^ ⌊(n : ℝ) * Real.logb q p⌋₊
/-- States long269:res:lead-two-prime, res:two-prime-transcendence from the long record and the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR21.transcendental_heckeValue in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem transcendental_heckeValue (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Transcendental ℚ (twoPrimeHeckeValue p q) := by
  sorry
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
/-- States long269:res:cell, res:cell from the long record and the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_eq_of_sameLogCell in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem realPrefixLcm_eq_of_sameLogCell
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hcell : SameThreePrimeRealLogCell p q r x y) :
    realPrefixLcm p q r x = realPrefixLcm p q r y := by
  sorry
/-- States long269:res:cell, res:cell from the long record and the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_jump_first in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem realPrefixLcm_jump_first
    {p q r : ℕ} (pPrime : p.Prime) (qPrime : q.Prime) (rPrime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊ + 1)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊) :
    realPrefixLcm p q r y = p * realPrefixLcm p q r x := by
  sorry
/-- States long269:res:cell, res:cell from the long record and the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_jump_second in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem realPrefixLcm_jump_second
    {p q r : ℕ} (pPrime : p.Prime) (qPrime : q.Prime) (rPrime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊ + 1)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊) :
    realPrefixLcm p q r y = q * realPrefixLcm p q r x := by
  sorry
/-- States long269:res:cell, res:cell from the long record and the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_jump_third in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem realPrefixLcm_jump_third
    {p q r : ℕ} (pPrime : p.Prime) (qPrime : q.Prime) (rPrime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊ + 1) :
    realPrefixLcm p q r y = r * realPrefixLcm p q r x := by
  sorry
/-- States long269:res:drop, long269:res:shell from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.realSmoothExponentShell_bounds in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem realSmoothExponentShell_bounds
    {p q r hp hq hr j : ℕ} {lo hi : ℝ}
    (hpPos : 0 < p) (hrPos : 0 < r) :
    (hi ≤ (r : ℝ) * lo →
      (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
        (hp + 1) * (hq + 1)) ∧
    (hi ≤ (p : ℝ) * lo →
      (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
        (hq + 1) * (hr + 1)) ∧
    (hi ≤ (r : ℝ) * lo → hp ≤ hq → hq ≤ hr → hp + hq + hr = j →
      9 * (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
        (j + 3) ^ 2) := by
  sorry
/-- States long269:res:lcm, res:lcm from the long record and the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.running_lcm_real_cutoff_exact in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem running_lcm_real_cutoff_exact {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x : ℝ} (hx : 1 ≤ x) :
    realPrefixLcm p q r x = realThreePrimeHeight p q r x := by
  sorry
/-- States long269:res:cell from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.threePrimeKernelQ_eq_of_sameRealLogCell in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem threePrimeKernelQ_eq_of_sameRealLogCell
    {p q r i j k i' j' k' : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hcell : SameThreePrimeRealLogCell p q r
      (smooth3Val p q r i j k : ℝ) (smooth3Val p q r i' j' k' : ℝ)) :
    threePrimeKernelQ p q r i j k =
      threePrimeKernelQ p q r i' j' k' := by
  sorry
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
/-- States long269:res:count, res:cell from the long record and the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.paper_jump_count in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_jump_count {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (n : ℕ) :
    (threePrimePositiveJumpSet p q r n).card = 3 * n ∧
    (threePrimeJumpSetWithOrigin p q r n).card = 3 * n + 1 := by
  sorry
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
/-- With no hypothesis on the generators, the sum of the kernel over a finite exponent box equals the sum, over the heights attained on that box, of the cardinality of the corresponding height fibre scaled by the reciprocal of that height. The multiplicities of the running least common multiple values are exposed rather than cancelled. -/
theorem finiteSmoothKernelSum_groupedByHeight
    (p q r hp hq hr : ℕ) :
    (∑ e ∈ smoothExponentBox hp hq hr,
      threePrimeKernelQ p q r e.1 e.2.1 e.2.2) =
      ∑ H ∈ (smoothExponentBox hp hq hr).image (smoothPointHeight p q r),
        (smoothHeightFiber p q r hp hq hr H).card • ((H : ℚ)⁻¹) := by
  sorry
end PalomarCorpus.E269.ThreePrimeStructure

namespace PalomarCorpus.E269.PaperStatementsB
/-- States long269:res:short from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.exponent_unique_real_base_short_interval in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exponent_unique_real_base_short_interval
    {base lo hi weight : ℝ} {a b : ℕ}
    (hbase : 1 ≤ base) (hweight : 0 ≤ weight)
    (hwidth : hi ≤ base * lo)
    (haLo : lo ≤ base ^ a * weight) (haHi : base ^ a * weight < hi)
    (hbLo : lo ≤ base ^ b * weight) (hbHi : base ^ b * weight < hi) :
    a = b := by
  sorry
end PalomarCorpus.E269.PaperStatementsB
