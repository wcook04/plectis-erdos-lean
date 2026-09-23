/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #68, record sections 1 to 3: which prime powers survive reduction; the growth of the common denominator; rationality and the next integer above a scaled partial sum

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #68, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #68 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Finsupp
open Filter Topology
open Filter

namespace PalomarCorpus.E68_01.Shared
/-- The common denominator `L D = lcm (d! - 1)` taken over the channel indices `2 ≤ d ≤ D`, the least common multiple of the denominators of the partial sum through `D`; the index set is empty and the value is `1` when `D < 2`. -/
noncomputable def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)
/-- The exact rational partial sum `H n = ∑_{2 ≤ k ≤ n} 1/(k! - 1)`, computed in `ℚ` with no real approximation; it is `0` for `n < 2`. -/
noncomputable def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)
/-- One summand of the universal factorial-gap tail beyond `D`. Local copy of Erdos68.factorialGapTailTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapTailTerm (D d : ℕ) : ℝ :=
  if D < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)
  else 0
/-- The universal factorial-gap tail beyond `D`. Local copy of Erdos68.factorialGapTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapTail (D : ℕ) : ℝ :=
  ∑' d : ℕ, factorialGapTailTerm D d
/-- The original Erdős #68 series, expressed through the universal factorial-gap tail beginning after `1`. Local copy of Erdos68.factorialGapSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapSeries : ℝ :=
  factorialGapTail 1
/-- The least integer strictly greater than `n! * x` for a real number `x`, namely `⌊n! * x⌋ + 1`. -/
noncomputable def strictFacTop (x : ℝ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℝ) * x⌋ + 1
/-- The predecessor gap `Δ m = Z (m - 1) - (m - 1)! * H (m - 1)`, the distance from the factorially scaled exact prefix at index `m - 1` up to the least integer strictly above it; it lies in the interval `(0, 1]`. -/
noncomputable def factorialGapPredecessorGap (m : ℕ) : ℝ :=
  (strictFacTop
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℝ) -
    ((m - 1).factorial : ℝ) *
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ)
end PalomarCorpus.E68_01.Shared

namespace PalomarCorpus.E68.PaperStatementsA
open scoped BigOperators
open Finsupp
export PalomarCorpus.E68_01.Shared (factorialGapPredecessorGap factorialGapPrefix factorialGapSeries factorialGapTail factorialGapTailTerm strictFacTop)
/-- Floor of the `m!`-scaled real number. Local copy of ErdosProblems.Erdos68.facFloor, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def facFloor (x : ℝ) (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℝ) * x⌋
/-- Fractional remainder after truncation at factorial scale `m!`. Local copy of ErdosProblems.Erdos68.canonicalRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalRemainder (x : ℝ) (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * x - (facFloor x m : ℝ)
/-- Companion-constant term, anchored at `n ≥ 2`. Local copy of ErdosProblems.Erdos68.compConstTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def compConstTerm (n : ℕ) : ℝ :=
  if 2 ≤ n then
    (1 : ℝ) /
      ((((n.factorial : ℕ) : ℝ)) *
        ((((n.factorial : ℤ) - 1 : ℤ) : ℝ)))
  else 0
/-- The fixed companion constant whose factorial orbit controls the carry congruence. Local copy of ErdosProblems.Erdos68.companionConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def companionConstant : ℝ :=
  ∑' n : ℕ, compConstTerm n
/-- The least common multiple of the literal factorial-gap denominators through one prefix endpoint. Local copy of ErdosProblems.Erdos68.factorialGapPrefixLCM, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapPrefixLCM (n : ℕ) : ℕ :=
  (Finset.Icc 2 n).lcm fun k => k.factorial - 1
/-- The exact tail after `m`, scaled by `m!`. Local copy of ErdosProblems.Erdos68.factorialGapScaledTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapScaledTail (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * factorialGapTail m
/-- States long68:res:wilson-cofinality from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.cofinal_first_prime_occurrences in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cofinal_first_prime_occurrences :
    ∀ B : ℕ, ∃ q m : ℕ, B < m ∧ q.Prime ∧ m < q ∧
      q ∣ m.factorial - 1 ∧
      ∀ k : ℕ, 2 ≤ k → k < m → Nat.Coprime q (k.factorial - 1) := by
  sorry
/-- States long68:res:companion-orbit from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.companion_orbit in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem companion_orbit :
    ¬ Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (facFloor companionConstant m + 2) % (m : ℤ) = 0 := by
  sorry
/-- States long68:eq:finite-escape, long68:eq:lower-escape, long68:res:lower-escape from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.lower_interval_criterion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lower_interval_criterion :
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        factorialGapScaledTail m ≤
          (m : ℝ) * canonicalRemainder factorialGapSeries (m - 1)) ∧
    (∀ m : ℕ, 3 ≤ m →
      ((m : ℝ) * factorialGapPredecessorGap m ≤ 1 + 1 / ((m.factorial : ℝ) - 1) ∨
        1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
          (m : ℝ) * factorialGapPredecessorGap m) →
      factorialGapScaledTail m ≤
        (m : ℝ) * canonicalRemainder factorialGapSeries (m - 1)) ∧
    ((∀ B : ℕ, ∃ m : ℕ, 3 ≤ m ∧ B < m ∧
      ((m : ℝ) * factorialGapPredecessorGap m ≤ 1 + 1 / ((m.factorial : ℝ) - 1) ∨
        1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
          (m : ℝ) * factorialGapPredecessorGap m)) →
      Irrational factorialGapSeries) := by
  sorry
/-- States long68:eq:prime-pole-survival, long68:res:prime-pole from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.maximal_prime_power_survival in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem maximal_prime_power_survival {M p : ℕ} (_hM : 2 ≤ M)
    (hp : p.Prime) (hpL : p ∣ factorialGapPrefixLCM M) :
    (factorialGapPrefix M).den.factorization p =
        (factorialGapPrefixLCM M).factorization p ↔
      (∑ n ∈ (Finset.Icc 2 M).filter
          (fun n => (n.factorial - 1).factorization p =
            (factorialGapPrefixLCM M).factorization p),
        (((n.factorial - 1) /
          p ^ (factorialGapPrefixLCM M).factorization p : ℕ) : ZMod p)⁻¹) ≠ 0 := by
  sorry
end PalomarCorpus.E68.PaperStatementsA

namespace PalomarCorpus.E68.PaperStatementsE
open scoped BigOperators
/-- Recursive lcm of a list, normalized to `1` on the empty list. Local copy of Erdos68.listLCM, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def listLCM : List ℕ → ℕ
  | [] => 1
  | a :: tail => Nat.lcm a (listLCM tail)
/-- Product of all pairwise gcd collision terms in a list, with each unordered pair counted once. Local copy of Erdos68.pairwiseGCDProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def pairwiseGCDProduct : List ℕ → ℕ
  | [] => 1
  | a :: tail =>
      (tail.map (Nat.gcd a)).prod * pairwiseGCDProduct tail
/-- States long68:res:product-lcm from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.product_lcm_pairwise_gcd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem product_lcm_pairwise_gcd (xs : List ℕ) :
    xs.prod ∣ listLCM xs * pairwiseGCDProduct xs := by
  sorry
end PalomarCorpus.E68.PaperStatementsE

namespace PalomarCorpus.E68.FactorialGapBounds
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E68_01.Shared (channelLCM)
/-- For 2 ≤ m < n, the gcd of m! − 1 and n! − 1 divides and is at most the descending-factorial product minus one, which is strictly less than n^(n − m). -/
theorem factorial_gap_gcd_exact
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) :
    let g := Nat.gcd (m.factorial - 1) (n.factorial - 1)
    let Q := n.descFactorial (n - m)
    g ∣ Q - 1 ∧ g ≤ Q - 1 ∧ Q - 1 < n ^ (n - m) := by
  sorry
/-- The sum of log(n! − 1) over the final k indices through D is at most log(channelLCM D) plus binomial(k + 1, 3) log D, for k < D. -/
theorem factorialGapSegment_log_sum_le_channelLCM_add_choose
    {D k : ℕ} (hkD : k < D) :
    (∑ n ∈ Finset.Ico (D + 1 - k) (D + 1),
      Real.log ((n.factorial - 1 : ℕ) : ℝ)) ≤
      Real.log (channelLCM D : ℝ) +
        (((k + 1).choose 3 : ℕ) : ℝ) * Real.log (D : ℝ) := by
  sorry
end PalomarCorpus.E68.FactorialGapBounds

namespace PalomarCorpus.E68.CommonDenominatorGrowth
open Filter
export PalomarCorpus.E68_01.Shared (channelLCM)
/-- The same bound in literal extended real form: the coercion of `2√2/3` is at most the `liminf` at infinity of the extended real values of `log (channelLCM N) / (N^(3/2) * log N)`, the exponent taken as a real power; the extended real codomain allows an infinite lower limit with no boundedness hypothesis; as at the preceding declaration, this bounds a common denominator of the partial sums and bounds no reduced denominator of a rational representation of the series. -/
theorem common_denominator_growth_liminf :
    ((2 * Real.sqrt 2 / 3 : ℝ) : EReal) ≤
      Filter.liminf (fun N : ℕ =>
        ((Real.log (channelLCM N : ℝ) /
          ((N : ℝ) ^ ((3 : ℝ) / 2) * Real.log (N : ℝ)) : ℝ) : EReal)) atTop := by
  sorry
end PalomarCorpus.E68.CommonDenominatorGrowth

namespace PalomarCorpus.E68.PaperStatementsB
open scoped BigOperators
export PalomarCorpus.E68_01.Shared (factorialGapPredecessorGap factorialGapPrefix factorialGapSeries factorialGapTail factorialGapTailTerm strictFacTop)
/-- The exact rounding carry in the strict-successor recurrence for the Erdős #68 prefixes. Local copy of ErdosProblems.Erdos68.factorialGapStepCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialGapStepCarry (m : ℕ) : ℤ :=
  -⌊1 + 1 / ((m.factorial : ℝ) - 1) -
      (m : ℝ) * factorialGapPredecessorGap m⌋
/-- Computable rational form of `strictFacTop`, used for exact finite certificates while retaining the real-valued statement needed for the series. Local copy of ErdosProblems.Erdos68.strictFacTopRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1
/-- States long68:eq:carry-rationality, long68:eq:strict-misses, long68:eq:unit-window from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.strict_successor_characterisation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem strict_successor_characterisation :
    (∀ m : ℕ, 3 ≤ m →
      (factorialGapStepCarry m = 1 ↔
        (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) ∧
      ((m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m ↔
        1 + 1 / ((m.factorial : ℝ) - 1) <
            (m : ℝ) * factorialGapPredecessorGap m ∧
        (m : ℝ) * factorialGapPredecessorGap m ≤
            2 + 1 / ((m.factorial : ℝ) - 1))) ∧
    (¬ Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → factorialGapStepCarry m = 1) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) ∧
    (∀ (m q : ℕ) (a : ℤ), 3 ≤ m → 0 < q →
      factorialGapSeries = (a : ℝ) / (q : ℝ) →
      factorialGapStepCarry m ≠ 1 →
      (¬ q ∣ (m - 1).factorial) ∧ m ≤ q) := by
  sorry
end PalomarCorpus.E68.PaperStatementsB
