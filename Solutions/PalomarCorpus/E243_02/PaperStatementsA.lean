/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR11.CubicIntegralNormalisation
import ErdosProblems.Erdos243.PaperCompleteR11.CubicRationalRoots
import ErdosProblems.Erdos243.PaperCompleteR11.CubicZeroDensityShape
import ErdosProblems.Erdos243.PaperCompleteR11.PrimitiveMultiplierSupply
import ErdosProblems.Erdos243.PaperCompleteR20.PowerPersistence
import ErdosProblems.Erdos243.PaperCompleteR21.CubicProfileGcdShape
import ErdosProblems.Erdos243.PaperCompleteR21.ForbiddenBlockCrossing
import ErdosProblems.Erdos243.PaperCompleteR21.NegativeMagnitudeExclusions
import ErdosProblems.Erdos243.PaperCompleteR21.ProtectedEpochBarrierCount
import ErdosProblems.Erdos243.PaperCompleteR21.ReducedStepLocalArithmetic
import ErdosProblems.Erdos243.PaperCompleteR7.Arithmetic
import ErdosProblems.Erdos243.PaperCompleteR7.Reduction
import ErdosProblems.Erdos243.PaperCompleteR9.PolynomialCorrections
import ErdosProblems.Erdos243.ProtectedEpochEnergy
import ErdosProblems.Erdos243.ReciprocalTailRigidity
import Solutions.PalomarCorpus.E243_02.Statement

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E243.PaperStatementsA

noncomputable def exceptionFinset (E : Set ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter (fun n ↦ n ∈ E)

noncomputable def exceptionCount (E : Set ℕ) (X : ℕ) : ℕ :=
  (exceptionFinset E X).card

noncomputable def ZeroLowerDensity (E : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ X : ℕ,
    N ≤ X ∧ (exceptionCount E X : ℝ) < ε * (X : ℝ)

noncomputable def rationalBinomialCubic (m c : ℚ) : Polynomial ℚ :=
  Polynomial.C (m / 6) * Polynomial.X * (Polynomial.X + 1) *
    (Polynomial.X + 2) + Polynomial.C c

noncomputable def risingBinomial (n : ℕ) : ℤ := ((n + 2).choose 3 : ℤ)

noncomputable def barrierIdx (Q : ℕ) : Finset ℕ := Finset.Icc ((Q + 4) / 8) ((Q - 2) / 4)

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
    Irreducible (rationalBinomialCubic (m : ℚ) (c : ℚ)) := @ErdosProblems.Erdos243.PaperCompleteR11.primitive_zero_density_paper_multiplier_lemma a u v m c T hm hv hnum hden hcop hzero

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
    p ^ k ∣ v t := @ErdosProblems.Erdos243.PaperCompleteR20.primePower_persists a u v w hc p k s t hp hst hcop hvpos hq hwpos hnum hden hstart hsmall

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
            0 < C n / g ∧ 0 < D n / g) := @ErdosProblems.Erdos243.PaperCompleteR21.cubic_profile_gcd_stabilisation_and_primitive_shape a C D A B hA hCpos hDpos hC hD hzero

theorem exists_shiftedBlock_consecutiveMultiples
    (B : ℕ) (m : ℕ → ℕ)
    (hm : ∀ i, i < B → 2 ≤ m i)
    (hpair : ∀ i, i < B → ∀ j, j < B → i ≠ j → Nat.Coprime (m i) (m j))
    (L : ℕ) :
    ∃ t, L < t ∧ ∀ i, i < B → m i ∣ t + i := @ErdosProblems.Erdos243.PaperCompleteR21.exists_shiftedBlock_consecutiveMultiples B m hm hpair L

theorem mem_barrierIdx_iff {Q : ℕ} (hQ : 16 ≤ Q) (k : ℕ) :
    k ∈ barrierIdx Q ↔ Q < 4 * (2 * k + 1) ∧ 2 * (2 * k + 1) ≤ Q := @ErdosProblems.Erdos243.PaperCompleteR21.mem_barrierIdx_iff Q hQ k

theorem no_boundedRise_coprimeToEarlierModuli
    (u : ℕ → ℕ) (B : ℕ) (hB : 1 ≤ B)
    (hrise : ∀ n, u (n + 1) ≤ u n + B)
    (hTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    ¬ ∃ m : ℕ → ℕ,
      (∀ i, 2 ≤ m i) ∧
      (∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) ∧
      (∀ i t, i < t → Nat.gcd (m i) (u t) = 1) := @ErdosProblems.Erdos243.PaperCompleteR21.no_boundedRise_coprimeToEarlierModuli u B hB hrise hTop

theorem no_constantNegative_shapeEquation
    (m c : ℕ) (hm : 0 < m) :
    ¬ ∃ a D : ℕ → ℕ,
      (∀ n, 2 ≤ a n) ∧
      (∀ n, D (n + 1) = a n * D n) ∧
      (∀ n, D n + m = (a n - 1) * (c + n * m)) := @ErdosProblems.Erdos243.PaperCompleteR21.no_constantNegative_shapeEquation m c hm

theorem no_eventuallyConstantNegative_shapeEquation
    (m c N : ℕ) (hm : 0 < m) :
    ¬ ∃ a D : ℕ → ℕ,
      (∀ n, 2 ≤ a n) ∧
      (∀ n, D (n + 1) = a n * D n) ∧
      (∀ n, D (N + n) + m = (a (N + n) - 1) * (c + n * m)) := @ErdosProblems.Erdos243.PaperCompleteR21.no_eventuallyConstantNegative_shapeEquation m c N hm

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
      (∀ n, C (n + h) = C n + M) := @ErdosProblems.Erdos243.PaperCompleteR21.no_periodicNegative_shapeEquation h M hh hM

theorem reduced_denominator_valuation_le_max
    {u v a w h v' p : ℕ} (hp : p.Prime)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hcop : Nat.Coprime u v)
    (hw : w + v = a * u) (hwpos : 0 < w)
    (hh : h = Nat.gcd w (a * v))
    (hv'def : v' = a * v / h) :
    v'.factorization p ≤ max (a.factorization p) (v.factorization p) := @ErdosProblems.Erdos243.PaperCompleteR21.reduced_denominator_valuation_le_max u v a w h v' p hp hu hv ha hcop hw hwpos hh hv'def

theorem reduced_denominator_valuation_strict_loss
    {u v a w h v' p : ℕ} (hp : p.Prime)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hcop : Nat.Coprime u v)
    (hw : w + v = a * u) (hwpos : 0 < w)
    (hh : h = Nat.gcd w (a * v))
    (hv'def : v' = a * v / h)
    (hloss : v'.factorization p < v.factorization p) :
    a.factorization p = v.factorization p ∧ 1 ≤ v.factorization p ∧
      v.factorization p < w.factorization p := @ErdosProblems.Erdos243.PaperCompleteR21.reduced_denominator_valuation_strict_loss u v a w h v' p hp hu hv ha hcop hw hwpos hh hv'def hloss

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
          = max 0 (2 * v.factorization p - w.factorization p)) := @ErdosProblems.Erdos243.PaperCompleteR21.reduced_denominator_valuation_transition u v a w h v' p hp hu hv ha hcop hw hwpos hh hv'def

theorem unit_word_saturates_old_modulus
    (M : ℕ) (hM : 2 ≤ M) (k : ℕ) (r : ℕ → ZMod M)
    (hr : ∀ i, i ≤ k → IsUnit (r i)) :
    ∃ a v : ℕ → ZMod M,
      (∀ i, i ≤ k → v i = 0) ∧
      (∀ i, i < k → r (i + 1) + v i = a i * r i) ∧
      (∀ i, i < k → v (i + 1) = a i * v i) ∧
      (∀ i, i + 2 ≤ k →
        r (i + 2) = (a i + a (i + 1)) * r (i + 1) - a i ^ 2 * r i) := @ErdosProblems.Erdos243.PaperCompleteR21.unit_word_saturates_old_modulus M hM k r hr

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
      ∃ N, ∀ n, N ≤ n → E n = 0) := @ErdosProblems.Erdos243.PaperCompleteR7.absorption_and_descent

theorem bounded_negative_endpoint_eventual_multiplier
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∃ N, ∀ n, N ≤ n → 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n)
    (hvanish : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := @ErdosProblems.Erdos243.PaperCompleteR7.bounded_negative_endpoint_eventual_multiplier a C D E ha hCpos hC hD hE hbound hvanish

theorem error_identities (a aNext D C : ℤ) :
    nextTailState a D C = C - centeredState a D C ∧
    sylvesterDefect a aNext * nextTailState a D C =
      a ^ 2 * centeredState a D C -
        centeredState aNext (nextDenState a D) (nextTailState a D C) := @ErdosProblems.Erdos243.PaperCompleteR7.error_identities a aNext D C

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
      (∀ n, N ≤ n → D (n + 1) / g = a n * (D n / g)) := @ErdosProblems.Erdos243.PaperCompleteR7.gcd_stabilises_and_reduces a C D E hC hD hE hnegative

theorem natural_sylvester_of_eventual_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hzero : ∃ N, ∀ n, N ≤ n → E n = 0) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := @ErdosProblems.Erdos243.PaperCompleteR7.natural_sylvester_of_eventual_zero a C D E hCpos hC hD hE hzero

theorem persistent_coprimality
    (a u v : ℕ → ℕ)
    (hred : ∀ n, Nat.Coprime (u n) (v n))
    (hu : ∀ n, u (n + 1) + v n = a n * u n)
    (hv : ∀ n, v (n + 1) = a n * v n) :
    (∀ n, Nat.Coprime (a n) (v n)) ∧
    (∀ i j, i ≠ j → Nat.Coprime (a i) (a j)) ∧
    (∀ i t, i < t → Nat.Coprime (a i) (u t)) := @ErdosProblems.Erdos243.PaperCompleteR7.persistent_coprimality a u v hred hu hv

theorem reduced_second_order_int
    (a aNext u uNext uNextNext v vNext h hNext : ℤ)
    (hu : h * uNext + v = a * u)
    (hv : h * vNext = a * v)
    (huNext : hNext * uNextNext + vNext = aNext * uNext) :
    a ^ 2 * u + h * hNext * uNextNext =
      h * (a + aNext) * uNext := @ErdosProblems.Erdos243.PaperCompleteR7.reduced_second_order_int a aNext u uNext uNextNext v vNext h hNext hu hv huNext

theorem state_scale (s a D C : ℤ) :
    nextDenState a (s * D) = s * nextDenState a D ∧
    nextTailState a (s * D) (s * C) = s * nextTailState a D C ∧
    centeredState a (s * D) (s * C) = s * centeredState a D C := @ErdosProblems.Erdos243.PaperCompleteR7.state_scale s a D C

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
      (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := @ErdosProblems.Erdos243.boundedNegativePart_sylvesterNext_eventually a C D E ha hCpos hC hD hE hbound hvanish

theorem centeredState_eventually_zero
    (C E : ℕ → ℕ) (hrec : ∀ n, C (n + 1) + E n = C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := @ErdosProblems.Erdos243.centeredState_eventually_zero C E hrec

theorem centeredState_zero_absorbing
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hcentered : ∀ n, Int.natAbs (E n) < C n)
    (n : ℕ) (hzero : E n = 0) :
    E (n + 1) = 0 := @ErdosProblems.Erdos243.centeredState_zero_absorbing a C D E hC hD hE hcentered n hzero

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
    ∃ N, ∀ n, N ≤ n → E n = 0 := @ErdosProblems.Erdos243.eventuallyBoundedNegativePart_eventually_zero a C D E ha hCpos hC hD hE hbound hvanish

theorem exists_shifted_consecutiveMultiples
    {k : ℕ}
    (m : Fin k → ℕ)
    (hm : ∀ i, 1 < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (L : ℕ) :
    ∃ x, L < x ∧ ∀ i : Fin k, m i ∣ x + i.1 := @ErdosProblems.Erdos243.exists_shifted_consecutiveMultiples k m hm hpair L

theorem nextTailState_eq_sub_centered (a D C : ℤ) :
    nextTailState a D C = C - centeredState a D C := @ErdosProblems.Erdos243.nextTailState_eq_sub_centered a D C

theorem sylvesterDefect_mul_nextTailState
    (a aNext D C : ℤ) :
    sylvesterDefect a aNext * nextTailState a D C =
      a ^ 2 * centeredState a D C -
        centeredState aNext (nextDenState a D) (nextTailState a D C) := @ErdosProblems.Erdos243.sylvesterDefect_mul_nextTailState a aNext D C

theorem sylvesterNext_eq_of_centered_zero
    (a aNext D C : ℤ)
    (hCnext : nextTailState a D C ≠ 0)
    (hE : centeredState a D C = 0)
    (hEnext :
      centeredState aNext (nextDenState a D) (nextTailState a D C) = 0) :
    aNext = sylvesterNext a := @ErdosProblems.Erdos243.sylvesterNext_eq_of_centered_zero a aNext D C hCnext hE hEnext

theorem sylvesterNext_eventually_of_centered_zero
    (a D C : ℕ → ℤ)
    (hD : ∀ n, D (n + 1) = nextDenState (a n) (D n))
    (hC : ∀ n, C (n + 1) = nextTailState (a n) (D n) (C n))
    (hE : ∃ N, ∀ n, N ≤ n → centeredState (a n) (D n) (C n) = 0)
    (hCne : ∃ N, ∀ n, N ≤ n → C (n + 1) ≠ 0) :
    ∃ N, ∀ n, N ≤ n → a (n + 1) = sylvesterNext (a n) := @ErdosProblems.Erdos243.sylvesterNext_eventually_of_centered_zero a D C hD hC hE hCne

end PalomarCorpus.E243.PaperStatementsA
