/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #243, band a

Erdős problem #243 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E243` under the Challenge size ceiling; it does not replace it.
-/

namespace PalomarCorpus.E243.PaperStatementsA
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR9.exceptionFinset, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exceptionFinset (E : Set ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter (fun n ↦ n ∈ E)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR9.exceptionCount, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exceptionCount (E : Set ℕ) (X : ℕ) : ℕ :=
  (exceptionFinset E X).card
/-- Arbitrarily late prefixes have arbitrarily small exceptional proportion. The strict inequality automatically excludes the zero-length prefix. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.ZeroLowerDensity, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ZeroLowerDensity (E : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ X : ℕ,
    N ≤ X ∧ (exceptionCount E X : ℝ) < ε * (X : ℝ)
/-- The literal unshifted polynomial printed as Q_{m,c} in the paper. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.rationalBinomialCubic, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalBinomialCubic (m c : ℚ) : Polynomial ℚ :=
  Polynomial.C (m / 6) * Polynomial.X * (Polynomial.X + 1) *
    (Polynomial.X + 2) + Polynomial.C c
/-- Integer-valued binomial basis for a rising cubic. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.risingBinomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def risingBinomial (n : ℕ) : ℤ := ((n + 2).choose 3 : ℤ)
/-- Index set of the barrier family: `k` indexes the barrier `(2 * k + 1) * p` lying in the window `(p * Q / 4, p * Q / 2]`. Local copy of ErdosProblems.Erdos243.barrierIdx, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def barrierIdx (Q : ℕ) : Finset ℕ := Finset.Icc ((Q + 4) / 8) ((Q - 2) / 4)
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
/-- States long243:res:reduciblecase from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR11.primitive_zero_density_paper_multiplier_lemma in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem primitive_zero_density_paper_multiplier_lemma
    (a u v : ℕ → ℕ) (m c : ℤ) (T : ℕ) (hm : 0 < m)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hzero : ZeroLowerDensity {n : ℕ | (u n : ℤ) ≠ m * risingBinomial n + c}) :
    (c = 1 ∨ c = -1) ∧
    (∀ n, T ≤ n → Nat.Coprime (a n) (v n)) ∧
    (∀ i j, T ≤ i → T ≤ j → i ≠ j → Nat.Coprime (a i) (a j)) ∧
    (∀ N, ∃ n, max T N ≤ n ∧ 1 < a n) ∧
    (∀ B N, ∃ p j : ℕ, Nat.Prime p ∧ B < p ∧ max T N ≤ j ∧ p ∣ a j) ∧
    Irreducible (rationalBinomialCubic (m : ℚ) (c : ℚ)) := by
  sorry
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
/-- States long243:eq:Qmc, long243:eq:primitivetail, long243:res:gcdshape from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.cubic_profile_gcd_stabilisation_and_primitive_shape in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cubic_profile_gcd_stabilisation_and_primitive_shape
    (a C D : ℕ → ℕ) (A B : ℚ) (hA : 0 < A)
    (hCpos : ∀ n, 0 < C n) (hDpos : ∀ n, 0 < D n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hzero : ZeroLowerDensity
      {n : ℕ | (C n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B}) :
    ∃ M : ℤ, 0 < M ∧ (M : ℚ) = 6 * A ∧
      (∀ n : ℕ, (Nat.gcd (C n) (D n) : ℤ) ∣ M) ∧
      ∃ g N : ℕ, 0 < g ∧
        (∀ n, N ≤ n → Nat.gcd (C n) (D n) = g) ∧
        ∃ m c : ℤ, 0 < m ∧ (c = 1 ∨ c = -1) ∧
          (∀ n : ℕ,
            (A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B) / (g : ℚ)
              = (m : ℚ) / 6 * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + (c : ℚ)) ∧
          (∀ n, N ≤ n →
            C (n + 1) / g + D n / g = a n * (C n / g) ∧
            D (n + 1) / g = a n * (D n / g) ∧
            Nat.Coprime (C n / g) (D n / g) ∧
            Nat.Coprime (C n / g) (C (n + 1) / g) ∧
            0 < C n / g ∧ 0 < D n / g) := by
  sorry
/-- States long243:res:crt from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.exists_shiftedBlock_consecutiveMultiples in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_shiftedBlock_consecutiveMultiples
    (B : ℕ) (m : ℕ → ℕ)
    (hm : ∀ i, i < B → 2 ≤ m i)
    (hpair : ∀ i, i < B → ∀ j, j < B → i ≠ j → Nat.Coprime (m i) (m j))
    (L : ℕ) :
    ∃ t, L < t ∧ ∀ i, i < B → m i ∣ t + i := by
  sorry
/-- States long243:res:epochenergy from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.mem_barrierIdx_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mem_barrierIdx_iff {Q : ℕ} (hQ : 16 ≤ Q) (k : ℕ) :
    k ∈ barrierIdx Q ↔ Q < 4 * (2 * k + 1) ∧ 2 * (2 * k + 1) ≤ Q := by
  sorry
/-- States long243:res:barrier from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.no_boundedRise_coprimeToEarlierModuli in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_boundedRise_coprimeToEarlierModuli
    (u : ℕ → ℕ) (B : ℕ) (hB : 1 ≤ B)
    (hrise : ∀ n, u (n + 1) ≤ u n + B)
    (hTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    ¬ ∃ m : ℕ → ℕ,
      (∀ i, 2 ≤ m i) ∧
      (∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) ∧
      (∀ i t, i < t → Nat.gcd (m i) (u t) = 1) := by
  sorry
/-- States long243:res:constant from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.no_constantNegative_shapeEquation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_constantNegative_shapeEquation
    (m c : ℕ) (hm : 0 < m) :
    ¬ ∃ a D : ℕ → ℕ,
      (∀ n, 2 ≤ a n) ∧
      (∀ n, D (n + 1) = a n * D n) ∧
      (∀ n, D n + m = (a n - 1) * (c + n * m)) := by
  sorry
/-- States long243:res:constant from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.no_eventuallyConstantNegative_shapeEquation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_eventuallyConstantNegative_shapeEquation
    (m c N : ℕ) (hm : 0 < m) :
    ¬ ∃ a D : ℕ → ℕ,
      (∀ n, 2 ≤ a n) ∧
      (∀ n, D (n + 1) = a n * D n) ∧
      (∀ n, D (N + n) + m = (a (N + n) - 1) * (c + n * m)) := by
  sorry
/-- States long243:res:periodic from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.no_periodicNegative_shapeEquation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_periodicNegative_shapeEquation
    (h M : ℕ) (hh : 0 < h) (hM : 0 < M) :
    ¬ ∃ a D C e : ℕ → ℕ,
      (∀ n, 2 ≤ a n) ∧
      (∀ n, 0 < e n) ∧
      (∀ n, e n < a n) ∧
      (∀ n, D (n + 1) = a n * D n) ∧
      (∀ n, C (n + 1) = C n + e n) ∧
      (∀ n, D n + e n = (a n - 1) * C n) ∧
      (∀ n, e (n + h) = e n) ∧
      (∀ n, C (n + h) = C n + M) := by
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
/-- States res:absorb, res:descent from the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.absorption_and_descent in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem absorption_and_descent :
    (∀ (a C D : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, C (n + 1) + D n = a n * C n) →
      (∀ n, D (n + 1) = a n * D n) →
      (∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)) →
      (∀ n, Int.natAbs (E n) < C n) →
      ∀ n, E n = 0 → E (n + 1) = 0) ∧
    (∀ (C : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n) →
      (∃ N, ∀ n, N ≤ n → 0 ≤ E n) →
      ∃ N, ∀ n, N ≤ n → E n = 0) := by
  sorry
/-- States res:cor from the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.bounded_negative_endpoint_eventual_multiplier in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem bounded_negative_endpoint_eventual_multiplier
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∃ N, ∀ n, N ≤ n → 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n)
    (hvanish : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry
/-- States res:defect, res:update from the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.error_identities in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem error_identities (a aNext D C : ℤ) :
    nextTailState a D C = C - centeredState a D C ∧
    sylvesterDefect a aNext * nextTailState a D C =
      a ^ 2 * centeredState a D C -
        centeredState aNext (nextDenState a D) (nextTailState a D C) := by
  sorry
/-- States long243:res:gcdstab, res:gcdstab from the long record and the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.gcd_stabilises_and_reduces in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem gcd_stabilises_and_reduces
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hnegative : ∃ B : ℕ, ∀ N, ∃ t,
      N ≤ t ∧ E t < 0 ∧ -(B : ℤ) ≤ E t) :
    ∃ N g : ℕ, 0 < g ∧
      (∀ n, N ≤ n → Nat.gcd (C n) (D n) = g) ∧
      (∀ n, N ≤ n → 0 < C n / g) ∧
      (∀ n, N ≤ n → Nat.Coprime (C n / g) (D n / g)) ∧
      (∀ n, N ≤ n → C (n + 1) / g + D n / g = a n * (C n / g)) ∧
      (∀ n, N ≤ n → D (n + 1) / g = a n * (D n / g)) := by
  sorry
/-- States res:eventual, res:step from the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.natural_sylvester_of_eventual_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem natural_sylvester_of_eventual_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hzero : ∃ N, ∀ n, N ≤ n → E n = 0) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry
/-- States long243:res:reduced, res:reduced from the long record and the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.persistent_coprimality in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem persistent_coprimality
    (a u v : ℕ → ℕ)
    (hred : ∀ n, Nat.Coprime (u n) (v n))
    (hu : ∀ n, u (n + 1) + v n = a n * u n)
    (hv : ∀ n, v (n + 1) = a n * v n) :
    (∀ n, Nat.Coprime (a n) (v n)) ∧
    (∀ i j, i ≠ j → Nat.Coprime (a i) (a j)) ∧
    (∀ i t, i < t → Nat.Coprime (a i) (u t)) := by
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
/-- States long243:res:cor from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.boundedNegativePart_sylvesterNext_eventually in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem boundedNegativePart_sylvesterNext_eventually
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry
/-- States long243:res:descent from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.centeredState_eventually_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem centeredState_eventually_zero
    (C E : ℕ → ℕ) (hrec : ∀ n, C (n + 1) + E n = C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
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
/-- States long243:res:bounded, res:bounded from the long record and the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.eventuallyBoundedNegativePart_eventually_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem eventuallyBoundedNegativePart_eventually_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  sorry
/-- States res:crt from the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.exists_shifted_consecutiveMultiples in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_shifted_consecutiveMultiples
    {k : ℕ}
    (m : Fin k → ℕ)
    (hm : ∀ i, 1 < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (L : ℕ) :
    ∃ x, L < x ∧ ∀ i : Fin k, m i ∣ x + i.1 := by
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
