/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #243, record sections 4 to 7: integer numerators, denominators and errors; when a zero error forces the Sylvester recurrence; a criterion using new maxima of an LCM numerator

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #243, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #243 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Filter Topology

namespace PalomarCorpus.E243.PaperStatementsA
/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. Local copy of ErdosProblems.Erdos243.centeredState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- Product-cleared denominator update `Dₙ₊₁ = aₙ Dₙ`. Local copy of ErdosProblems.Erdos243.nextDenState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def nextDenState (a D : ℤ) : ℤ :=
  a * D
/-- Product-cleared reciprocal-tail update `Cₙ₊₁ = aₙ Cₙ - Dₙ`. Local copy of ErdosProblems.Erdos243.nextTailState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
/-- The next denominator defect from the Sylvester step. Local copy of ErdosProblems.Erdos243.sylvesterDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterDefect (a aNext : ℤ) : ℤ :=
  aNext - sylvesterNext a
/-- States long243:res:powerpersistence from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR20.primePower_persists in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem primePower_persists
    (a u v w hc : ℕ → ℕ) {p k s t : ℕ}
    (hp : p.Prime)
    (hst : s ≤ t)
    (hcop : ∀ n, Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, 0 < v n)
    (hq : ∀ n, w n + v n = a n * u n)
    (hwpos : ∀ n, 0 < w n)
    (hnum : ∀ n, w n = hc n * u (n + 1))
    (hden : ∀ n, a n * v n = hc n * v (n + 1))
    (hstart : p ^ k ∣ v s)
    (hsmall : ∀ n, s ≤ n → n < t → w n < p ^ (k + 1)) :
    p ^ k ∣ v t := by
  sorry
/-- States long243:res:valuationtransition from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.reduced_denominator_valuation_le_max in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem reduced_denominator_valuation_le_max
    {u v a w h v' p : ℕ} (hp : p.Prime)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hcop : Nat.Coprime u v)
    (hw : w + v = a * u) (hwpos : 0 < w)
    (hh : h = Nat.gcd w (a * v))
    (hv'def : v' = a * v / h) :
    v'.factorization p ≤ max (a.factorization p) (v.factorization p) := by
  sorry
/-- States long243:res:valuationtransition from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.reduced_denominator_valuation_strict_loss in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem reduced_denominator_valuation_strict_loss
    {u v a w h v' p : ℕ} (hp : p.Prime)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hcop : Nat.Coprime u v)
    (hw : w + v = a * u) (hwpos : 0 < w)
    (hh : h = Nat.gcd w (a * v))
    (hv'def : v' = a * v / h)
    (hloss : v'.factorization p < v.factorization p) :
    a.factorization p = v.factorization p ∧ 1 ≤ v.factorization p ∧
      v.factorization p < w.factorization p := by
  sorry
/-- States long243:res:valuationtransition from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.reduced_denominator_valuation_transition in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem reduced_denominator_valuation_transition
    {u v a w h v' p : ℕ} (hp : p.Prime)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hcop : Nat.Coprime u v)
    (hw : w + v = a * u) (hwpos : 0 < w)
    (hh : h = Nat.gcd w (a * v))
    (hv'def : v' = a * v / h) :
    (a.factorization p ≠ v.factorization p →
        v'.factorization p = max (a.factorization p) (v.factorization p))
    ∧ (a.factorization p = v.factorization p →
        v'.factorization p
          = max 0 (2 * v.factorization p - w.factorization p)) := by
  sorry
/-- States long243:res:oldmodulussaturation from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.unit_word_saturates_old_modulus in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem unit_word_saturates_old_modulus
    (M : ℕ) (hM : 2 ≤ M) (k : ℕ) (r : ℕ → ZMod M)
    (hr : ∀ i, i ≤ k → IsUnit (r i)) :
    ∃ a v : ℕ → ZMod M,
      (∀ i, i ≤ k → v i = 0) ∧
      (∀ i, i < k → r (i + 1) + v i = a i * r i) ∧
      (∀ i, i < k → v (i + 1) = a i * v i) ∧
      (∀ i, i + 2 ≤ k →
        r (i + 2) = (a i + a (i + 1)) * r (i + 1) - a i ^ 2 * r i) := by
  sorry
/-- States long243:res:secondorder from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.reduced_second_order_int in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem reduced_second_order_int
    (a aNext u uNext uNextNext v vNext h hNext : ℤ)
    (hu : h * uNext + v = a * u)
    (hv : h * vNext = a * v)
    (huNext : hNext * uNextNext + vNext = aNext * uNext) :
    a ^ 2 * u + h * hNext * uNextNext =
      h * (a + aNext) * uNext := by
  sorry
/-- States long243:res:scale from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.state_scale in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem state_scale (s a D C : ℤ) :
    nextDenState a (s * D) = s * nextDenState a D ∧
    nextTailState a (s * D) (s * C) = s * nextTailState a D C ∧
    centeredState a (s * D) (s * C) = s * centeredState a D C := by
  sorry
/-- States long243:res:absorb from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.centeredState_zero_absorbing in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem centeredState_zero_absorbing
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hcentered : ∀ n, Int.natAbs (E n) < C n)
    (n : ℕ) (hzero : E n = 0) :
    E (n + 1) = 0 := by
  sorry
/-- States long243:res:update from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.nextTailState_eq_sub_centered in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem nextTailState_eq_sub_centered (a D C : ℤ) :
    nextTailState a D C = C - centeredState a D C := by
  sorry
/-- States long243:res:defect from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.sylvesterDefect_mul_nextTailState in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sylvesterDefect_mul_nextTailState
    (a aNext D C : ℤ) :
    sylvesterDefect a aNext * nextTailState a D C =
      a ^ 2 * centeredState a D C -
        centeredState aNext (nextDenState a D) (nextTailState a D C) := by
  sorry
/-- States long243:res:step, res:eventual, res:step from the long record and the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.sylvesterNext_eq_of_centered_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sylvesterNext_eq_of_centered_zero
    (a aNext D C : ℤ)
    (hCnext : nextTailState a D C ≠ 0)
    (hE : centeredState a D C = 0)
    (hEnext :
      centeredState aNext (nextDenState a D) (nextTailState a D C) = 0) :
    aNext = sylvesterNext a := by
  sorry
/-- States long243:res:eventual from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.sylvesterNext_eventually_of_centered_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sylvesterNext_eventually_of_centered_zero
    (a D C : ℕ → ℤ)
    (hD : ∀ n, D (n + 1) = nextDenState (a n) (D n))
    (hC : ∀ n, C (n + 1) = nextTailState (a n) (D n) (C n))
    (hE : ∃ N, ∀ n, N ≤ n → centeredState (a n) (D n) (C n) = 0)
    (hCne : ∃ N, ∀ n, N ≤ n → C (n + 1) ≠ 0) :
    ∃ N, ∀ n, N ≤ n → a (n + 1) = sylvesterNext (a n) := by
  sorry
end PalomarCorpus.E243.PaperStatementsA

namespace PalomarCorpus.E243.PaperStatementsH
open scoped BigOperators
/-- States long243:res:curvature from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.cancellationFree_curvature_square in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cancellationFree_curvature_square
    {a aNext p pNext pNextNext q : ℤ}
    (hq : q = a * p - pNext)
    (hrec : pNextNext + a ^ 2 * p = (a + aNext) * pNext) :
    q ^ 2 + (p * pNextNext - pNext ^ 2) =
      (aNext - a) * p * pNext := by
  sorry
end PalomarCorpus.E243.PaperStatementsH

namespace PalomarCorpus.E243.CompletePaperRecords
open Filter Topology
open scoped BigOperators
/-- The prefix product `a 0 * a 1 * ... * a (n-1)` of the first `n` terms of a natural sequence, with the empty product `1` at `n = 0`. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- The integer numerator obtained by clearing q times the prefix product from the first n terms of the reciprocal-series remainder. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- The natural-number projection of the cleared integer remainder numerator. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
/-- The least common multiple of q and the first n digits of a, defined recursively. -/
noncomputable def cumulativeDigitLcm (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => Nat.lcm (cumulativeDigitLcm q a n) (a n)
/-- The product of the successive gcd overlaps between each digit and the preceding cumulative least common multiple. -/
noncomputable def cumulativeOverlapDebt (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      cumulativeOverlapDebt q a n *
        Nat.gcd (cumulativeDigitLcm q a n) (a n)
/-- The numerator C n divided in the natural numbers by its cumulative overlap debt. -/
noncomputable def lcmLiftedNumerator (q : ℕ) (a C : ℕ → ℕ) (n : ℕ) : ℕ :=
  C n / cumulativeOverlapDebt q a n
/-- The signed discrepancy between the cumulative least common multiple and (a n − 1) times the lifted numerator. -/
noncomputable def lcmLiftedDigit (q : ℕ) (a C : ℕ → ℕ) (n : ℕ) : ℤ :=
  (cumulativeDigitLcm q a n : ℤ) -
    ((a n : ℤ) - 1) * (lcmLiftedNumerator q a C n : ℤ)
/-- The value at n + 1 strictly exceeds every value at an index at most n. -/
noncomputable def IsStrictRecord (U : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ j, j ≤ n → U j < U (n + 1)
/-- The integrals from 1 to R exceed every real bound as R ranges over values at least 1. -/
noncomputable def IntegralUnbounded (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, 1 ≤ R ∧ M < ∫ t in (1 : ℝ)..R, f t
/-- The overlap-corrected natural numerator of the rational reciprocal-series remainder. -/
noncomputable def canonicalLcmNumerator (a : ℕ → ℕ) (p : ℤ) (q : ℕ) : ℕ → ℕ :=
  lcmLiftedNumerator q a (canonicalNaturalNumerator a p q)
/-- The signed discrepancy associated with the canonical overlap-corrected numerator. -/
noncomputable def canonicalLcmDigit (a : ℕ → ℕ) (p : ℤ) (q : ℕ) : ℕ → ℤ :=
  lcmLiftedDigit q a (canonicalNaturalNumerator a p q)
/-- At a strict record, the negative digit excess beyond B, weighted by f at the preceding numerator; zero at other indices. -/
noncomputable def paperRecordCharge (U : ℕ → ℕ) (V : ℕ → ℤ)
    (B : ℕ) (f : ℝ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if IsStrictRecord U n then
    ((max (-V n - (B : ℤ)) 0 : ℤ) : ℝ) * f (U n : ℝ)
  else 0
/-- Under the rational-sum and asymptotically quadratic growth hypotheses, eventual Sylvester recurrence is equivalent to summability of the canonical weighted record excess for some finite cutoff B. -/
theorem canonical_weighted_record_excess
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) (hdiv : IntegralUnbounded f) :
    (∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1) ↔
      ∃ B : ℕ, Summable (paperRecordCharge (canonicalLcmNumerator a p q)
        (canonicalLcmDigit a p q) B f) := by
  sorry
/-- For a positive least-common-multiple numerator recurrence with the displayed centering inequality, boundedness of U is equivalent to summability of its weighted record excess, for every specified finite cutoff B and admissible weight. -/
theorem arithmetic_weighted_record_dichotomy
    (a L U : ℕ → ℕ) (V : ℕ → ℤ)
    (ha : ∀ n, 0 < a n) (hLpos : ∀ n, 0 < L n) (hU : ∀ n, 0 < U n)
    (hL : ∀ n, L (n + 1) = Nat.lcm (L n) (a n))
    (hstate : ∀ n, (Nat.gcd (L n) (a n) : ℤ) * U (n + 1) =
      (U n : ℤ) - V n)
    (herror : ∀ n, V n = (L n : ℤ) - ((a n : ℤ) - 1) * U n)
    (hcenter : ∀ n, -(U n : ℤ) ≤ 2 * V n)
    (B : ℕ) (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) (hdiv : IntegralUnbounded f) :
    (∃ H : ℕ, ∀ n, U n ≤ H) ↔ Summable (paperRecordCharge U V B f) := by
  sorry
end PalomarCorpus.E243.CompletePaperRecords
