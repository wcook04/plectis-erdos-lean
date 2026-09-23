/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #243, the bounded negative part rigidity, bounded rise reduced tail and periodic negative orbit families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #243, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #243 remains open, and no theorem in
this entry decides it.
-/

namespace PalomarCorpus.E243_10.Shared
/-- The running maximum `max_{k ≤ n} u k` of a natural-valued sequence, given by `runningMax u 0 = u 0` and `runningMax u (n+1) = max (runningMax u n) (u (n+1))`. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
end PalomarCorpus.E243_10.Shared

namespace PalomarCorpus.E243.BoundedNegativePartRigidity
export PalomarCorpus.E243_10.Shared (sylvesterNext)
/-- The centred reciprocal-tail error `D - (a - 1) * C` of an integer state, the integer measuring the failure of the identity `D = (a - 1) * C` that holds exactly on a Sylvester tail. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- Principal integer-state theorem: for natural sequences with `a n > 1` and `C n > 0` obeying the exact cleared dynamics `C (n+1) + D n = a n * C n` and `D (n+1) = a n * D n`, with centred error `E n = D n - (a n - 1) * C n` taken in the integers, if `E` has an eventually bounded negative part, meaning `-B ≤ E n` for all `n` past some index, and satisfies division-free normalised vanishing, meaning that for every scale `K` one eventually has `K * |E n| < C n` in the naturals, then `E n = 0` from some index onward and `a (n+1) = a n ^ 2 - a n + 1` in the integers from some index onward. No periodicity and no sign condition is assumed, so the error may change sign infinitely often. -/
theorem boundedNegativePart_completeRigidity
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E n) < C n) :
    (∃ N, ∀ n, N ≤ n → E n = 0) ∧
      ∃ N, ∀ n, N ≤ n →
        (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry
end PalomarCorpus.E243.BoundedNegativePartRigidity

namespace PalomarCorpus.E243.BoundedRiseReducedTail
/-- An unbounded natural sequence cannot have bounded upward increments while avoiding every earlier modulus in a pairwise coprime tail of moduli greater than one. -/
theorem no_boundedRise_of_tailAvoidance
    (u m : ℕ → ℕ) (N B : ℕ)
    (hB : 0 < B)
    (hm : ∀ n, N ≤ n → 1 < m n)
    (hpair : ∀ {i j : ℕ}, N ≤ i → N ≤ j → i ≠ j →
      Nat.Coprime (m i) (m j))
    (havoid : ∀ {i t : ℕ}, N ≤ i → i < t →
      Nat.Coprime (m i) (u t))
    (hrise : ∀ n, N ≤ n → u (n + 1) ≤ u n + B)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False := by
  sorry
/-- Unconditional exclusion: there is no reduced exact tail of naturals with `a n > 1` for every `n`, `u n` coprime to `v n` for every `n`, `u (n+1) + v n = a n * u n`, `v (n+1) = a n * v n`, a fixed `B > 0` with `u (n+1) ≤ u n + B` at every index, and `u n → ∞`. Reduced exactness makes distinct multipliers pairwise coprime and keeps every earlier multiplier coprime to every later numerator, and a Chinese remainder block of consecutive forbidden heights cannot be crossed by steps of size at most `B`. -/
theorem no_boundedRise_reducedTail
    (a u v : ℕ → ℕ) (B : ℕ)
    (hB : 0 < B)
    (ha : ∀ n, 1 < a n)
    (hred : ∀ n, Nat.Coprime (u n) (v n))
    (hu : ∀ n, u (n + 1) + v n = a n * u n)
    (hv : ∀ n, v (n + 1) = a n * v n)
    (hrise : ∀ n, u (n + 1) ≤ u n + B)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False := by
  sorry
/-- The reduced numerator of a reciprocal-tail recurrence cannot tend to infinity while having eventually bounded upward increments. -/
theorem no_eventuallyBoundedRise_reducedTail
    (a u v : ℕ → ℕ) (N B : ℕ)
    (hB : 0 < B)
    (ha : ∀ n, N ≤ n → 1 < a n)
    (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n))
    (hu : ∀ n, N ≤ n → u (n + 1) + v n = a n * u n)
    (hv : ∀ n, N ≤ n → v (n + 1) = a n * v n)
    (hrise : ∀ n, N ≤ n → u (n + 1) ≤ u n + B)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False := by
  sorry
end PalomarCorpus.E243.BoundedRiseReducedTail

namespace PalomarCorpus.E243.PeriodicNegativeOrbit
/-- Unconditional exclusion of a phase-primitive periodic negative-error orbit: for natural sequences with `a n ≥ 2`, `0 < e n < a n`, `D (n+1) = a n * D n`, `C (n+1) = C n + e n`, the shape equation `D n + e n = (a n - 1) * C n`, a period `h > 0` with `e (n+h) = e n`, a positive drift `C (n+h) = C n + M` with `M > 0`, and the primitivity condition that no prime dividing `M` divides both `C 0` and every value of `e`, the hypotheses are contradictory. Here `e n` is the magnitude of a negative centred error, and `a n - 1` is natural subtraction, which is harmless because `a n ≥ 2`. -/
theorem no_phasePrimitivePeriodicNegative_orbit
    (a D C e : ℕ → ℕ) (h M : ℕ)
    (hh : 0 < h)
    (hM : 0 < M)
    (ha : ∀ n, 2 ≤ a n)
    (hepos : ∀ n, 0 < e n)
    (helt : ∀ n, e n < a n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hC : ∀ n, C (n + 1) = C n + e n)
    (hshape : ∀ n, D n + e n = (a n - 1) * C n)
    (hperiod : ∀ n, e (n + h) = e n)
    (hphase : ∀ n, C (n + h) = C n + M)
    (hprimitive : ∀ p, p.Prime → p ∣ M →
      ¬ (p ∣ C 0 ∧ ∀ n, p ∣ e n)) :
    False := by
  sorry
/-- The same exclusion at an arbitrary common scale, with the primitivity condition removed: for natural sequences with `a n ≥ 2`, `0 < e n < a n`, `D (n+1) = a n * D n`, `C (n+1) = C n + e n`, `D n + e n = (a n - 1) * C n`, period `h > 0` and positive drift `C (n+h) = C n + M` with `M > 0`, the hypotheses are contradictory. A shared prime divides the whole orbit, dividing it out strictly decreases the positive drift, and a descent returns to the phase-primitive case. -/
theorem no_periodicNegative_orbit
    (a D C e : ℕ → ℕ) (h M : ℕ)
    (hh : 0 < h)
    (hM : 0 < M)
    (ha : ∀ n, 2 ≤ a n)
    (hepos : ∀ n, 0 < e n)
    (helt : ∀ n, e n < a n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hC : ∀ n, C (n + 1) = C n + e n)
    (hshape : ∀ n, D n + e n = (a n - 1) * C n)
    (hperiod : ∀ n, e (n + h) = e n)
    (hphase : ∀ n, C (n + h) = C n + M) :
    False := by
  sorry
/-- Eventual form of the periodic exclusion, with every hypothesis imposed only from an offset `N`: `a n ≥ 2` for `n ≥ N`, `0 < e (N+n) < a (N+n)` for every `n`, `D (n+1) = a n * D n`, `C (n+1) = C n + e n` and `D n + e n = (a n - 1) * C n` for `n ≥ N`, `e (N+n+h) = e (N+n)` with `h > 0`, and `C (N+n+h) = C (N+n) + M` with `M > 0`. These hypotheses are contradictory, so no tail of an orbit can be periodic in the negative-error regime with positive drift. -/
theorem no_eventuallyPeriodicNegative_orbit
    (a D C e : ℕ → ℕ) (N h M : ℕ)
    (hh : 0 < h)
    (hM : 0 < M)
    (ha : ∀ n, N ≤ n → 2 ≤ a n)
    (hepos : ∀ n, 0 < e (N + n))
    (helt : ∀ n, e (N + n) < a (N + n))
    (hD : ∀ n, N ≤ n → D (n + 1) = a n * D n)
    (hC : ∀ n, N ≤ n → C (n + 1) = C n + e n)
    (hshape : ∀ n, N ≤ n → D n + e n = (a n - 1) * C n)
    (hperiod : ∀ n, e (N + n + h) = e (N + n))
    (hphase : ∀ n, C (N + n + h) = C (N + n) + M) :
    False := by
  sorry
end PalomarCorpus.E243.PeriodicNegativeOrbit

namespace PalomarCorpus.E243.PrimitiveRecordRigidity
export PalomarCorpus.E243_10.Shared (runningMax sylvesterNext)
/-- Supporting lemma on one primitive step with arbitrary cancellation: given `w + v = a * u`, `w = hc * u'` and `a * v = hc * v'` with `u` coprime to `v`, `v > 0` and `w > 0`, a prime power `p ^ l` dividing `v` still divides the next denominator `v'` as soon as the raw numerator satisfies `w < p ^ (l+1)`. The valuation of `p` in the denominator cannot drop while the raw numerator stays below the next power of `p`, whatever the cancellation factor `hc` is. -/
theorem primitive_valuation_no_drop
    {a u v w hc u' v' p l : ℕ}
    (hp : p.Prime)
    (hcop : Nat.Coprime u v)
    (hvpos : 0 < v)
    (hq : w + v = a * u)
    (hwpos : 0 < w)
    (hnum : w = hc * u')
    (hden : a * v = hc * v')
    (hl : p ^ l ∣ v)
    (hlt : w < p ^ (l + 1)) :
    p ^ l ∣ v' := by
  sorry
/-- Supporting lemma: along a primitive orbit with arbitrary cancellation from index `s`, satisfying `w n + v n = a n * u n`, `w n = hc n * u (n+1)`, `a n * v n = hc n * v (n+1)`, `u n` coprime to `v n`, `v n > 0`, `w n > 0` and the slow bound `2 * w n ≤ 3 * u n`, if `p` is prime with `p ^ l ∣ v s` and the height `H` obeys `3 * H < 2 * p ^ (l+1)`, then `p ^ l ∣ v n` at every index `n ≥ s` whose strictly earlier window `s ≤ k < n` keeps `u k < H`. -/
theorem protectedPrimePower_persists
    (a u v w hc : ℕ → ℕ) (p l s H : ℕ)
    (hp : p.Prime)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hheight : 3 * H < 2 * p ^ (l + 1))
    (hprot : p ^ l ∣ v s) :
    ∀ n, s ≤ n → (∀ k, s ≤ k → k < n → u k < H) → p ^ l ∣ v n := by
  sorry
/-- Supporting lemma, the odd cut: under the same primitive-orbit hypotheses from `s` with the slow bound `2 * w n ≤ 3 * u n`, a prime `p`, an exponent `l ≥ 1`, an odd height `H` divisible by `p` with `runningMax u s < H` and `3 * H < 2 * p ^ (l+1)`, `p ^ l ∣ v s`, and every record-setting step from `s` onward rising by at most `2`, the numerator satisfies `u n < H` for every `n ≥ s`. The protected prime power forbids the landing `u n = H`, and the only jump of two across an odd `H` has two even endpoints, against coprimality of consecutive numerators. -/
theorem odd_record_cut
    (a u v w hc : ℕ → ℕ) (p l s H : ℕ)
    (hp : p.Prime)
    (hl : 1 ≤ l)
    (hHodd : Odd H)
    (hpH : p ∣ H)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hheight : 3 * H < 2 * p ^ (l + 1))
    (hprot : p ^ l ∣ v s)
    (hRs : runningMax u s < H)
    (hrec : ∀ n, s ≤ n → runningMax u n < u (n + 1) → u (n + 1) ≤ u n + 2) :
    ∀ n, s ≤ n → u n < H := by
  sorry
/-- Supporting lemma: for an odd `p ≥ 2`, an exponent `l ≥ 1` and a bound `R` with `3 * R < p ^ l`, there exists an odd multiple `H` of `p` with `R < H` and `3 * H < 2 * p ^ (l+1)`, so a large odd power `p ^ l` always supplies a trap height above the current record and below the protection ceiling. -/
theorem exists_oddMultiple_trapHeight
    {p l R : ℕ} (hp2 : 2 ≤ p) (hpodd : Odd p) (hl : 1 ≤ l)
    (hbig : 3 * R < p ^ l) :
    ∃ H, Odd H ∧ p ∣ H ∧ R < H ∧ 3 * H < 2 * p ^ (l + 1) := by
  sorry
/-- Supporting lemma combining the trap height with the odd cut: for a primitive orbit from `s` with arbitrary cancellation, meaning `w n + v n = a n * u n`, `w n = hc n * u (n+1)`, `a n * v n = hc n * v (n+1)`, `v n > 0`, `w n > 0` and `u n` coprime to `v n` at every `n ≥ s`, with the slow bound `2 * w n ≤ 3 * u n`, every record-setting step rising by at most `2`, an odd prime `p`, an exponent `l ≥ 1`, `p ^ l ∣ v s` and `3 * runningMax u s < p ^ l`, the numerator is bounded: there is an `H` with `u n < H` for every `n ≥ s`. -/
theorem numerator_bounded_of_oddPrimePower
    (a u v w hc : ℕ → ℕ) (p l s : ℕ)
    (hp : p.Prime)
    (hpodd : Odd p)
    (hl : 1 ≤ l)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hprot : p ^ l ∣ v s)
    (hbig : 3 * runningMax u s < p ^ l)
    (hrec : ∀ n, s ≤ n → runningMax u n < u (n + 1) → u (n + 1) ≤ u n + 2) :
    ∃ H, ∀ n, s ≤ n → u n < H := by
  sorry
/-- Supporting lemma: at a primitive step with `u` coprime to `v`, `w + v = a * u` and `w = hc * u'`, a vanishing centred error `v - (a - 1) * u = 0` in the integers forces `u = 1`, `w = 1`, `hc = 1` and `u' = 1`, so the tail sits in its unit normal form with no cancellation at that step. -/
theorem centeredZero_forces_unit
    {a u v w hc u' : ℕ}
    (hcop : Nat.Coprime u v)
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hzero : (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ) = 0) :
    u = 1 ∧ w = 1 ∧ hc = 1 ∧ u' = 1 := by
  sorry
/-- Supporting lemma: at a primitive step with `u` coprime to `v`, `w + v = a * u`, `w = hc * u'` and `a * v = hc * v'`, if both centred errors vanish, that is `v - (a - 1) * u = 0` and `v' - (a' - 1) * u' = 0` in the integers, then the two multipliers satisfy `a' = a ^ 2 - a + 1`. -/
theorem sylvesterStep_of_centeredZero_pair
    {a a' u v w hc u' v' : ℕ}
    (hcop : Nat.Coprime u v)
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hden : a * v = hc * v')
    (hzero : (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ) = 0)
    (hzero' : (v' : ℤ) - ((a' : ℤ) - 1) * (u' : ℤ) = 0) :
    (a' : ℤ) = sylvesterNext (a : ℤ) := by
  sorry
/-- Rigidity for the class of tails whose record-setting steps rise by at most two: along a reduced reciprocal tail from index `N` with arbitrary cancellation, obeying `w n + v n = a n * u n`, `w n = hc n * u (n+1)`, `a n * v n = hc n * v (n+1)`, `v n > 0`, `w n > 0` and `u n` coprime to `v n`, with centred error `e n = v n - (a n - 1) * u n` satisfying `2 * |e n| < u n` and division-free normalised vanishing at every scale, if every record-setting step rises by at most `2` and odd prime powers `p ^ l`, `l ≥ 1`, with `p ^ l ∣ v s` and `3 * runningMax u s < p ^ l` recur at arbitrarily late `s`, then `a (n+1) = a n ^ 2 - a n + 1` from some index onward. The prime-power supply is a hypothesis. -/
theorem recordRiseTwo_sylvesterNext_eventually
    (a u v w hc : ℕ → ℕ) (e : ℕ → ℤ) (N : ℕ)
    (hvpos : ∀ n, N ≤ n → 0 < v n)
    (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n))
    (hw : ∀ n, N ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, N ≤ n → 0 < w n)
    (hnum : ∀ n, N ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, N ≤ n → a n * v n = hc n * v (n + 1))
    (he : ∀ n, N ≤ n → e n = (v n : ℤ) - ((a n : ℤ) - 1) * (u n : ℤ))
    (hcentre : ∀ n, N ≤ n → 2 * (e n).natAbs < u n)
    (hvanish : ∀ K, ∃ M, ∀ n, M ≤ n → K * (e n).natAbs < u n)
    (hrec : ∀ n, N ≤ n → runningMax u n < u (n + 1) → u (n + 1) ≤ u n + 2)
    (hsupply : ∀ M, ∃ s, M ≤ s ∧ ∃ p l, p.Prime ∧ Odd p ∧ 1 ≤ l ∧
      p ^ l ∣ v s ∧ 3 * runningMax u s < p ^ l) :
    ∃ M, ∀ n, M ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry
end PalomarCorpus.E243.PrimitiveRecordRigidity

namespace PalomarCorpus.E243.ProtectedEpochEnergy
export PalomarCorpus.E243_10.Shared (runningMax)
/-- Protected-epoch record energy: for an odd prime `p`, an exponent `l ≥ 1` and a primitive orbit from `s` with arbitrary cancellation, `u n` coprime to `v n`, `v n > 0`, `w n > 0`, `w n + v n = a n * u n`, `w n = hc n * u (n+1)`, `a n * v n = hc n * v (n+1)` and the slow bound `2 * w n ≤ 3 * u n`, if `Q = p ^ l` divides `v s` with `Q ≥ 16` and `4 * runningMax u s < p * Q`, and `s < τ` with `p * Q ≤ 2 * u τ`, then there is a finite set `J` of indices in `[s, τ)`, each a global record step with `hc n = 1` and jump `u n + 3 ≤ u (n+1)`, such that `p * Q ≤ (8 * p + 8) * J.card + 4 * ∑_{n ∈ J} (u (n+1) - u n - 2) + 8 * p`, the inner subtraction being natural subtraction. -/
theorem protected_epoch_energy_integer
    (a u v w hc : ℕ → ℕ) (p l s τ : ℕ)
    (hp : p.Prime)
    (hpodd : Odd p)
    (hl : 1 ≤ l)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hprot : p ^ l ∣ v s)
    (hQ : 16 ≤ p ^ l)
    (hRs : 4 * runningMax u s < p * p ^ l)
    (hsτ : s < τ)
    (hτ : p * p ^ l ≤ 2 * u τ) :
    ∃ J : Finset ℕ,
      (∀ n ∈ J, s ≤ n ∧ n < τ ∧ runningMax u n < u (n + 1) ∧
          u n + 3 ≤ u (n + 1) ∧ hc n = 1) ∧
      p * p ^ l ≤ (8 * p + 8) * J.card
        + 4 * ∑ n ∈ J, (u (n + 1) - u n - 2) + 8 * p := by
  sorry
end PalomarCorpus.E243.ProtectedEpochEnergy
