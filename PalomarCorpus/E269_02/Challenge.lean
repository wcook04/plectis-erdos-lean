/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #269, record sections 4 to 5: why the third prime prevents finite separation; the recurrence for tails between powers of two

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #269, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #269 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Module
open Submodule
open Set
open Metric
open scoped Topology
open scoped BoundedContinuousFunction
open scoped ENNReal
open Polynomial

namespace PalomarCorpus.E269_02.Shared
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
/-- The smooth lattice value `p ^ i * q ^ j * r ^ k` attached to the exponent triple `(i, j, k)`. -/
noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k
/-- The three-prime height `H x = p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x`, the product of the largest powers of `p`, `q` and `r` not exceeding `x`; the `Nat.log` convention makes `H 0 = H 1 = 1`, and for pairwise distinct primes and `x` at least 1 this is the least common multiple of the smooth numbers at most `x`. -/
noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x
end PalomarCorpus.E269_02.Shared

namespace PalomarCorpus.E269.PaperStatementsB
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.realTwoPrimeHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realTwoPrimeHeight (p q t : ℝ) : ℝ :=
  p ^ ⌊Real.logb p t⌋ * q ^ ⌊Real.logb q t⌋
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.realTwoPrimeKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realTwoPrimeKernel (p q : ℝ) (i j : ℕ) : ℝ :=
  (realTwoPrimeHeight p q (p ^ i * q ^ j))⁻¹
/-- States long269:res:two-prime-rank from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.real_two_prime_separation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_two_prime_separation {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    (∀ i j : ℕ, realTwoPrimeKernel p q i j =
      (p ^ i * q ^ ⌊Real.logb q (p ^ i)⌋)⁻¹ *
        (p ^ ⌊Real.logb p (q ^ j)⌋ * q ^ j)⁻¹) ∧
    (∀ i i' j j' : ℕ,
      realTwoPrimeKernel p q i j * realTwoPrimeKernel p q i' j' -
        realTwoPrimeKernel p q i j' * realTwoPrimeKernel p q i' j = 0) := by
  sorry
end PalomarCorpus.E269.PaperStatementsB

namespace PalomarCorpus.E269.PaperStatementsA
open scoped BigOperators
export PalomarCorpus.E269_02.Shared (DyadicInternalPower dyadicBlockBase235 smooth3Val threePrimeHeight)
/-- The exact rational lattice kernel attached to the running-LCM height. Local copy of ErdosProblems.Erdos269.threePrimeKernelQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹
/-- States long269:res:rank from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.paper_two_by_two_fixture in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_two_by_two_fixture :
    threePrimeKernelQ 2 3 5 0 0 0 = 1 ∧
    threePrimeKernelQ 2 3 5 0 1 0 = 1 / 6 ∧
    threePrimeKernelQ 2 3 5 1 0 0 = 1 / 2 ∧
    threePrimeKernelQ 2 3 5 1 1 0 = 1 / 60 ∧
    (Matrix.det (fun i j : Fin 2 => threePrimeKernelQ 2 3 5 i j 0)) = -(1 / 15 : ℚ) ∧
    (Matrix.det (fun i j : Fin 2 => threePrimeKernelQ 2 3 5 i j 0)) ≠ 0 := by
  sorry
/-- States long269:res:infinite-rank, long269:res:lead-infinite-rank, res:infinite-rank from the long record and the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.paper_uniform_rank_and_nonseparation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_uniform_rank_and_nonseparation {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (_hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (∀ n : ℕ, ∃ I J : Fin n → ℕ,
      Function.Injective I ∧ Function.Injective J ∧
      ∀ k : ℕ, (Matrix.det fun a b : Fin n =>
        threePrimeKernelQ p q r (I a) (J b) k) ≠ 0) ∧
    (∀ d : ℕ, ¬ ∃ (f : Fin d → ℕ → ℚ) (G : Fin d → ℕ → ℕ → ℚ),
      ∀ i j k, threePrimeKernelQ p q r i j k = ∑ l : Fin d, f l i * G l j k) := by
  sorry
/-- States long269:eq:dyadic-alphabet, long269:res:dyadic-alphabet from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.radix_eq_height_ratio in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem radix_eq_height_ratio (a : ℕ) :
    (dyadicBlockBase235 a : ℚ) =
      (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) /
        (threePrimeHeight 2 3 5 (2 ^ a) : ℚ) := by
  sorry
/-- States long269:eq:dyadic-alphabet, long269:res:dyadic-alphabet from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.dyadicBlockBase235_cases in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadicBlockBase235_cases (a : ℕ) :
    dyadicBlockBase235 a = 2 ∨
      dyadicBlockBase235 a = 6 ∨
      dyadicBlockBase235 a = 10 ∨
      dyadicBlockBase235 a = 30 := by
  sorry
/-- States long269:eq:dyadic-alphabet, long269:res:dyadic-alphabet from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.dyadicBlockBase235_mem_interval in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadicBlockBase235_mem_interval (a : ℕ) :
    2 ≤ dyadicBlockBase235 a ∧ dyadicBlockBase235 a ≤ 30 := by
  sorry
/-- States long269:eq:dyadic-alphabet, long269:res:dyadic-alphabet from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.dyadicInternalPower_exponent_unique in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadicInternalPower_exponent_unique
    {p a e f : ℕ} (hp : 2 ≤ p)
    (he : DyadicInternalPower p a e)
    (hf : DyadicInternalPower p a f) :
    e = f := by
  sorry
/-- States long269:eq:dyadic-alphabet, long269:res:dyadic-alphabet from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.exists_dyadicInternalPower_iff_log_succ in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_dyadicInternalPower_iff_log_succ
    {p a : ℕ} (hp : 2 < p) (hpOdd : Odd p) :
    (∃ e, DyadicInternalPower p a e) ↔
      Nat.log p (2 ^ (a + 1)) = Nat.log p (2 ^ a) + 1 := by
  sorry
/-- States long269:eq:dyadic-alphabet, long269:res:dyadic-alphabet from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.log_dyadic_succ_eq_of_no_internalPower in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem log_dyadic_succ_eq_of_no_internalPower
    {p a : ℕ} (hp : 2 < p) (hpOdd : Odd p)
    (hNo : ¬ ∃ e, DyadicInternalPower p a e) :
    Nat.log p (2 ^ (a + 1)) = Nat.log p (2 ^ a) := by
  sorry
/-- States long269:eq:dyadic-alphabet, long269:res:dyadic-alphabet from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.threePrimeHeight_dyadicBlock_succ in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem threePrimeHeight_dyadicBlock_succ (a : ℕ) :
    threePrimeHeight 2 3 5 (2 ^ (a + 1)) =
      dyadicBlockBase235 a * threePrimeHeight 2 3 5 (2 ^ a) := by
  sorry
end PalomarCorpus.E269.PaperStatementsA

namespace PalomarCorpus.E269.PaperStructuresH
open scoped BigOperators
open Module
open Submodule
/-- A cut at `k`, with `m` rows. Local copy of ErdosProblems.Erdos269.PaperR7.cutVector, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cutVector {F : Type*} [Field F] (c : F) (m k : ℕ) : Fin m → F :=
  fun i => if (i : ℕ) < k then 1 else c
/-- States long269:res:finite-cut-rank, res:finite-cut-rank from the long record and the short record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.rank_cutMatrix in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rank_cutMatrix {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) {m : ℕ} (hm : 0 < m)
    (E : Finset ℕ) (hbound : ∀ k ∈ E, k ≤ m)
    (A : Matrix (Fin m) ι F)
    (hcols : Set.range A.col = Set.range (fun k : E => cutVector c m k)) :
    A.rank = E.card - if 0 ∈ E ∧ m ∈ E then 1 else 0 := by
  sorry
end PalomarCorpus.E269.PaperStructuresH

namespace PalomarCorpus.E269.PaperStatementsE
open Set
open Metric
open scoped BigOperators
open scoped Topology
open scoped BoundedContinuousFunction
open scoped ENNReal
open Polynomial
/-- The binary carry of `Nat.log` across a product. Local copy of ErdosProblems.Erdos269.logCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def logCarry (b x y : ℕ) : ℕ :=
  Nat.log b (x * y) - Nat.log b x - Nat.log b y
/-- The normalised real-valued carry matrix, using the actual integer-log carry. Local copy of ErdosProblems.Erdos269.PaperR7.realCarryMatrix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realCarryMatrix (p q r i j : ℕ) : ℝ :=
  ((r : ℝ)⁻¹) ^ logCarry r (p ^ i) (q ^ j)
/-- Local copy of ErdosProblems.Erdos269.PaperR8.FiniteSeparatedRank, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FiniteSeparatedRank (A : ℕ → ℕ → ℝ) : Prop :=
  ∃ d : ℕ, ∃ f g : Fin d → ℕ → ℝ,
    ∀ i j, A i j = ∑ k : Fin d, f k i * g k j
/-- All finite-separated-rank matrices, with no bounded-factor restriction. Local copy of ErdosProblems.Erdos269.PaperR8.FiniteRankMatrix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev FiniteRankMatrix := {A : ℕ → ℕ → ℝ // FiniteSeparatedRank A}
/-- An extended supremum is essential: the real supremum convention at an unbounded set must not turn infinite error into zero. Local copy of ErdosProblems.Erdos269.PaperR8.uniformError, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def uniformError (C A : ℕ → ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ i : ℕ, ⨆ j : ℕ, ENNReal.ofReal |C i j - A i j|
/-- States long269:res:uniform-rank from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR8.uniform_rank_complete in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem uniform_rank_complete {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    (⨅ A : FiniteRankMatrix, uniformError (realCarryMatrix p q r) A.val) =
        ENNReal.ofReal ((1 - (r : ℝ)⁻¹) / 2) ∧
    (⨅ A : FiniteRankMatrix, uniformError (realCarryMatrix p q r) A.val) =
        ENNReal.ofReal (((r : ℝ) - 1) / (2 * (r : ℝ))) ∧
    ∃ A : FiniteRankMatrix,
      (∀ i j, A.val i j = (1 + (r : ℝ)⁻¹) / 2) ∧
      uniformError (realCarryMatrix p q r) A.val =
        (⨅ F : FiniteRankMatrix, uniformError (realCarryMatrix p q r) F.val) := by
  sorry
end PalomarCorpus.E269.PaperStatementsE

namespace PalomarCorpus.E269.PaperStatementsC
open scoped BigOperators
export PalomarCorpus.E269_02.Shared (DyadicInternalPower dyadicBlockBase235 smooth3Val threePrimeHeight)
/-- Normalize a real source tail by half of the current endpoint height. Local copy of ErdosProblems.Erdos269.dyadicNormalizedTailStateR235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicNormalizedTailStateR235 (tail : ℕ → ℝ) (a : ℕ) : ℝ :=
  ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a
/-- Strict `{p,q,r}`-smooth exponent prefix. The ambient exponent box of side `x` is deliberately redundant; it gives a finite, integer-only carrier for the strict inequality used by the returned floor-sum formula. Local copy of ErdosProblems.Erdos269.strictSmoothExponents, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictSmoothExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range x).product ((Finset.range x).product (Finset.range x))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 < x
/-- Exact shell between two strict cutoffs. Local copy of ErdosProblems.Erdos269.strictSmoothShell, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictSmoothShell (p q r x y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothExponents p q r y \ strictSmoothExponents p q r x
/-- The actual `{2,3,5}`-smooth exponent points in the half-open dyadic shell `[2^a,2^(a+1))`. Local copy of ErdosProblems.Erdos269.dyadicSmoothShell235, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicSmoothShell235 (a : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothShell 2 3 5 (2 ^ a) (2 ^ (a + 1))
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
/-- States long269:eq:shell-digit-identity, long269:res:actual-orbit from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.long_actual_orbit in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem long_actual_orbit :
    Summable dyadicShellMassR235 ∧
    paperSeries235 = (∑' a : ℕ, dyadicShellMassR235 a) ∧
    (∀ a : ℕ,
      0 < dyadicOrderedBlockDigit235 a ∧
      (dyadicOrderedBlockDigit235 a : ℝ) =
        (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) / 2 * dyadicShellMassR235 a ∧
      trueNormalizedState (a + 1) =
        (dyadicBlockBase235 a : ℝ) * trueNormalizedState a -
          (dyadicOrderedBlockDigit235 a : ℝ) ∧
      trueNormalizedState a =
        ∑' n : ℕ, (dyadicOrderedBlockDigit235 (a + n) : ℝ) /
          ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (a + j) : ℝ)) := by
  sorry
end PalomarCorpus.E269.PaperStatementsC
