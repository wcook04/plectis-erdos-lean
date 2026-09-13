/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #243

The problem asks whether strictly increasing positive integers with
`a (n+1) / a n ^ 2 → 1` and rational reciprocal sum must satisfy the Sylvester
recurrence `a (n+1) = a n ^ 2 - a n + 1` for all large `n`. The problem is
open and nothing in this file closes it.

Clearing denominators turns the rational case into an exact integer orbit
`C (n+1) + D n = a n * C n`, `D (n+1) = a n * D n`, whose centred error
`E n = D n - (a n - 1) * C n` vanishes exactly on a Sylvester tail.

Principal results.

* `OriginalCoordinateBoundedDefect.original_coordinate_bounded_defect`: in the
  problem's own coordinates, an eventual upper bound on the product defect
  `(∏_{j<n} a j / a n) * (a n ^ 2 / a (n+1) - 1)` forces the recurrence. That
  bound is a hypothesis and is not derived from rationality and growth.
* `BoundedNegativePartRigidity.boundedNegativePart_completeRigidity`: an
  eventually bounded negative part of `E`, with division-free normalised
  vanishing, forces `E n = 0` and the recurrence eventually.
* `SummableNegativeMassRigidity.summableNegativeMass_completeRigidity`: the
  same conclusion under normalised vanishing when the normalised negative
  mass is summable. Both are hypotheses.

Unconditional exclusions. `BoundedRiseReducedTail` and `SlowRiseBarrier`
exclude a divergent slowly rising reduced tail. `PeriodicNegativeOrbit`
excludes periodic and eventually periodic negative-error orbits.

Exact criteria. `WeightedRecordExcess` gives two equivalences between the
eventual recurrence and convergence of a weighted record-excess series. They
reformulate the question and do not settle it.

Record coordinates. `PrimitiveRecordRigidity` and `RecordIncrementBarrier`
prove rigidity for restricted classes of tails. `ProtectedEpochEnergy`,
`RecordAmplifiedCancellationVisibility`, `SaturatedSquareTransport` and
`RepairEntropy` supply supporting identities and estimates.

Every statement carries its hypotheses explicitly. The unrestricted problem
remains open.
-/

open Filter
open scoped BigOperators
open Finset
open scoped Topology

namespace PalomarCorpus.E243.Shared
/-- The centred reciprocal-tail error `D - (a - 1) * C` of an integer state, the integer measuring the failure of the identity `D = (a - 1) * C` that holds exactly on a Sylvester tail. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- The prefix product `a 0 * a 1 * ... * a (n-1)` of the first `n` terms of a natural sequence, with the empty product `1` at `n = 0`. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- The running maximum `max_{k ≤ n} u k` of a natural-valued sequence, given by `runningMax u 0 = u 0` and `runningMax u (n+1) = max (runningMax u n) (u (n+1))`. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- The Sylvester successor map `a ↦ a ^ 2 - a + 1` on the integers, the multiplier map for which the telescope `1 / (a - 1) = 1 / a + 1 / (sylvesterNext a - 1)` holds, so that a tail with this recurrence has reciprocal sum exactly `1 / (a - 1)`. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
end PalomarCorpus.E243.Shared

namespace PalomarCorpus.E243.BoundedNegativePartRigidity
export PalomarCorpus.E243.Shared (centeredState sylvesterNext)
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
end PalomarCorpus.E243.BoundedRiseReducedTail

namespace PalomarCorpus.E243.OriginalCoordinateBoundedDefect
open Filter
export PalomarCorpus.E243.Shared (prefixProduct)
/-- The original-coordinate product defect at index `n`, the real number `(P n / a n) * (a n ^ 2 / a (n+1) - 1)` where `P n = ∏_{j < n} a j`, which weighs the departure from the Sylvester growth relation by the prefix product; the naturals `P n`, `a n` and `a (n+1)` are cast to the reals. -/
noncomputable def productDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)
/-- Principal theorem in the problem's own coordinates: if `a` is a strictly increasing sequence of positive integers whose reciprocal series has sum the rational number `p / q` with `q > 0`, whose growth satisfies `a (n+1) / a n ^ 2 → 1` in the reals, and whose product defect `(P n / a n) * (a n ^ 2 / a (n+1) - 1)` is bounded above by one constant `M` from some index onward, then `a (n+1) = a n ^ 2 - a n + 1` in the integers for all large `n`. The upper bound on the product defect is a hypothesis of the statement. It is assumed and not derived from the rational-sum and growth hypotheses. -/
theorem original_coordinate_bounded_defect
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hupper : ∃ M : ℝ, ∃ N, ∀ n, N ≤ n → productDefect a n ≤ M) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  sorry
end PalomarCorpus.E243.OriginalCoordinateBoundedDefect

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
export PalomarCorpus.E243.Shared (runningMax sylvesterNext)
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
export PalomarCorpus.E243.Shared (runningMax)
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

namespace PalomarCorpus.E243.RecordAmplifiedCancellationVisibility
export PalomarCorpus.E243.Shared (runningMax)
/-- Local visibility estimate: with `s + 1 ≤ t`, the relations `w n + v n = a n * u n`, `w n = hc n * u (n+1)`, `w n > 0` and `e n = v n - (a n - 1) * u n` for `n ≥ s`, if `e j ≥ 0` for every `j` strictly between `s` and `t` and `e t < 0`, then `u t ≤ u (s+1)` and `u s * u t ≤ runningMax u t * |e t| * u (s+1)`, so a cancellation paid at `s` is still quantitatively visible at the first later negative error. This is an estimate at one pair of indices. It bounds no excursion length, and it is not a global rigidity theorem. -/
theorem recordAmplified_error_after_cancellation
    (a u v w hc : ℕ → ℕ) (e : ℕ → ℤ) (s t : ℕ)
    (hst : s + 1 ≤ t)
    (he : ∀ n, s ≤ n → e n = (v n : ℤ) - ((a n : ℤ) - 1) * (u n : ℤ))
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnonneg : ∀ j, s < j → j < t → 0 ≤ e j)
    (hneg : e t < 0) :
    u t ≤ u (s + 1) ∧
      u s * u t ≤ runningMax u t * (e t).natAbs * u (s + 1) := by
  sorry
end PalomarCorpus.E243.RecordAmplifiedCancellationVisibility

namespace PalomarCorpus.E243.RecordIncrementBarrier
export PalomarCorpus.E243.Shared (runningMax sylvesterNext)
/-- Rigidity for tails whose running maximum increases by at most one: along a reduced reciprocal tail from `N` with arbitrary cancellation, obeying `w n + v n = a n * u n`, `w n = hc n * u (n+1)`, `a n * v n = hc n * v (n+1)`, `v n > 0`, `w n > 0` and `u n` coprime to `v n`, with centred error `e n = v n - (a n - 1) * u n` satisfying `2 * |e n| < u n` and division-free normalised vanishing at every scale, if `runningMax u (n+1) ≤ runningMax u n + 1` at every late step and prime powers `p ^ l`, `l ≥ 1`, with `p ^ l ∣ v s` and `runningMax u s + 3 ≤ p ^ l` recur at arbitrarily late `s`, then `a (n+1) = a n ^ 2 - a n + 1` from some index onward. Any prime is admitted; the supply is a hypothesis. -/
theorem recordIncrementOne_sylvesterNext_eventually
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
    (hinc : ∀ n, N ≤ n → runningMax u (n + 1) ≤ runningMax u n + 1)
    (hsupply : ∀ M, ∃ s, M ≤ s ∧ ∃ p l, p.Prime ∧ 1 ≤ l ∧
      p ^ l ∣ v s ∧ runningMax u s + 3 ≤ p ^ l) :
    ∃ M, ∀ n, M ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry
end PalomarCorpus.E243.RecordIncrementBarrier

namespace PalomarCorpus.E243.RepairEntropy
open scoped BigOperators
/-- The deletion product `∏_{s ≤ n < t} c n` of the deletion factors over the half-open window of indices from `s` to `t`, with the empty product `1` when `t ≤ s`. -/
noncomputable def deletionProduct (c : ℕ → ℕ) (s t : ℕ) : ℕ :=
  ∏ n ∈ Finset.Ico s t, c n
/-- The proposition that the modulus `m` is repaired over the window from `s` to `t`, meaning that `m` divides the deletion product `∏_{s ≤ n < t} c n`. -/
noncomputable def repairedAt (c : ℕ → ℕ) (s t m : ℕ) : Prop :=
  m ∣ deletionProduct c s t
/-- Repair-entropy inequality: for positive naturals `u n` and `h n` and integers `e n` with `h n * u (n+1) = u n - e n` in the integers, a window `[r, r+L)` with `L > 0` on which `K * |e (r+i)| < u (r+i)` for a fixed `K > 0`, a recovery `u r ≤ u (r+L)`, naturals `c n` with `c n ^ 2 ∣ h n` on the window, and a finite family `R` of moduli `m q` each dividing the product of `c` over that window, one has `K ^ L * (R.lcm m) ^ 2 < (K+1) ^ L`. Reading `c n` as deletion factors and `h n` as the payment of a recovery step is interpretation the statement does not impose. -/
theorem repairedFamily_recovery_energy_divisionFree
    {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (m : ι → ℕ)
    (u h c : ℕ → ℕ) (e : ℕ → ℤ) (K r L : ℕ)
    (hK : 0 < K)
    (hupos : ∀ n, 0 < u n)
    (hhpos : ∀ n, 0 < h n)
    (hstep : ∀ n, (h n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - e n)
    (herr : ∀ i, i < L → K * Int.natAbs (e (r + i)) < u (r + i))
    (hL : 0 < L)
    (hrecover : u r ≤ u (r + L))
    (hrepair : ∀ q ∈ R, repairedAt c r (r + L) (m q))
    (hsq : ∀ n ∈ Finset.Ico r (r + L), c n ^ 2 ∣ h n) :
    K ^ L * (R.lcm m) ^ 2 < (K + 1) ^ L := by
  sorry
/-- Corollary of the repair-entropy law for an independent family: under the same window hypotheses, if the family satisfies `2 ^ R.card ≤ R.lcm m`, then `K ^ L * 4 ^ R.card < (K+1) ^ L`, which bounds how many independent old moduli can be deleted inside a recovery carrying a fixed relative-error budget. -/
theorem repaired_card_bound_of_independent
    {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (m : ι → ℕ)
    (u h c : ℕ → ℕ) (e : ℕ → ℤ) (K r L : ℕ)
    (hK : 0 < K)
    (hupos : ∀ n, 0 < u n)
    (hhpos : ∀ n, 0 < h n)
    (hstep : ∀ n, (h n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - e n)
    (herr : ∀ i, i < L → K * Int.natAbs (e (r + i)) < u (r + i))
    (hL : 0 < L)
    (hrecover : u r ≤ u (r + L))
    (hrepair : ∀ q ∈ R, repairedAt c r (r + L) (m q))
    (hsq : ∀ n ∈ Finset.Ico r (r + L), c n ^ 2 ∣ h n)
    (hindep : 2 ^ R.card ≤ R.lcm m) :
    K ^ L * 4 ^ R.card < (K + 1) ^ L := by
  sorry
/-- For positive naturals `u n` and `h n` and integers `e n` with `h n * u (n+1) = u n - e n`, under division-free normalised vanishing at every scale `K`, each fixed window length `L > 0` has an index `N` beyond which every recovery `u r ≤ u (r+L)` with `r ≥ N` pays nothing: `∏_{i < L} h (r+i) = 1`. A surviving nontrivial reset must therefore have recovery length tending to infinity. The statement says nothing about a recovery length that varies with `r`. -/
theorem eventually_recoveryPayment_eq_one_of_fixedLength
    (u h : ℕ → ℕ) (e : ℕ → ℤ)
    (hupos : ∀ n, 0 < u n)
    (hhpos : ∀ n, 0 < h n)
    (hstep : ∀ n, (h n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - e n)
    (hvanish : ∀ K : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K * Int.natAbs (e n) < u n)
    (L : ℕ) (hL : 0 < L) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → u r ≤ u (r + L) →
      (∏ i ∈ Finset.range L, h (r + i)) = 1 := by
  sorry
end PalomarCorpus.E243.RepairEntropy

namespace PalomarCorpus.E243.SaturatedSquareTransport
/-- Exact divisibility with no hypothesis beyond the three cocycle equations `w + v = a * u`, `w = hc * u'` and `a * v = hc * v'` and the two centred-error definitions `e = v - (a - 1) * u` and `e' = v' - (a' - 1) * u'`: the whole next numerator `u'` divides `hc * e * e' - v ^ 2` in the integers. The naturals `a, u, v, w, hc, u', v'` are cast to the integers, while `a'`, `e` and `e'` are integers, and transport is modulo `u'` itself with the full removed content. -/
theorem saturated_square_transport_raw
    {a u v w hc u' v' : ℕ} {a' e e' : ℤ}
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hden : a * v = hc * v')
    (he : e = (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ))
    (he' : e' = (v' : ℤ) - (a' - 1) * (u' : ℤ)) :
    (u' : ℤ) ∣ (hc : ℤ) * e * e' - (v : ℤ) ^ 2 := by
  sorry
/-- Bare divisibility implication over naturals `b`, `s`, `u'`, `p` and integers `e`, `e'`, with no primality and no orbit hypothesis: if `u'` divides `b * e * e' - (b * s) ^ 2` in the integers, `p` divides `u'`, and the product of the images of `e` and `e'` in `ZMod p` is not a square, then `b ≠ 1`. Reading `b` as the nonsquare part of a removed content, `s` as the square part and `e`, `e'` as consecutive centred errors is interpretation the statement does not impose, and nothing follows about the size of `b`. -/
theorem legendre_defect_forces_nonsquare_content
    {b s u' p : ℕ} {e e' : ℤ}
    (hdvd : (u' : ℤ) ∣ (b : ℤ) * e * e' - ((b : ℤ) * (s : ℤ)) ^ 2)
    (hpu : p ∣ u')
    (hnr : ¬ IsSquare ((e : ZMod p) * (e' : ZMod p))) :
    b ≠ 1 := by
  sorry
end PalomarCorpus.E243.SaturatedSquareTransport

namespace PalomarCorpus.E243.SlowRiseBarrier
/-- Slow-rise exclusion, a companion to the uniform bounded-rise barrier that neither implies nor is implied by it: no reduced exact tail from index `N`, with `a n > 1`, `u n` coprime to `v n`, `u (n+1) + v n = a n * u n`, `v (n+1) = a n * v n` and `u n → ∞`, can for some block length `B` start below the product `P = ∏_{i < B} a (N+i)` at index `N + B` and then rise by at most `B` at every index `n ≥ N + B` where the numerator is below `2 * P`. The rise budget is required only on that window, and a uniform rise bound at every index is a stronger hypothesis. -/
theorem no_slowRise_reducedTail
    (a u v : ℕ → ℕ) (N B : ℕ)
    (ha : ∀ n, N ≤ n → 1 < a n)
    (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n))
    (hu : ∀ n, N ≤ n → u (n + 1) + v n = a n * u n)
    (hv : ∀ n, N ≤ n → v (n + 1) = a n * v n)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop)
    (hstart : u (N + B) < ∏ i : Fin B, a (N + i.1))
    (hrise : ∀ n, N + B ≤ n → u n < 2 * ∏ i : Fin B, a (N + i.1) →
      u (n + 1) ≤ u n + B) :
    False := by
  sorry
end PalomarCorpus.E243.SlowRiseBarrier

namespace PalomarCorpus.E243.SummableNegativeMassRigidity
open scoped BigOperators
open Finset
export PalomarCorpus.E243.Shared (centeredState prefixProduct sylvesterNext)
/-- The product-cleared denominator update `D ↦ a * D` on the integers, one step of the recurrence `D (n+1) = a n * D n`. -/
noncomputable def nextDenState (a D : ℤ) : ℤ :=
  a * D
/-- The product-cleared tail-numerator update `C ↦ a * C - D` on the integers, obtained by clearing denominators in the tail relation `x n = 1 / a n + x (n+1)`. -/
noncomputable def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D
/-- The normalised negative mass at index `n`, the real number obtained by dividing the magnitude of the negative part of the integer error `E n`, namely `|min (E n) 0|`, by the natural number `C n` cast to the reals; the definition imposes no positivity on `C n`, and division by zero returns `0` in the reals. -/
noncomputable def negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  (Int.natAbs (min (E n) 0) : ℝ) / C n
/-- Second conditional endpoint: for integer multipliers `a n` and denominators `D n` and positive natural numerators `C n` with `D (n+1) = a n * D n`, `C (n+1) = a n * C n - D n`, the step identity `C (n+1) = C n - E n` for the centred error `E n = D n - (a n - 1) * C n`, division-free normalised vanishing at every scale `K`, and summability of the normalised negative mass `n ↦ (-E n)_+ / C n`, the centred error vanishes from some index onward and `a (n+1) = a n ^ 2 - a n + 1` from some index onward. Summability and normalised vanishing are hypotheses; this statement derives neither from rationality and growth. -/
theorem summableNegativeMass_completeRigidity
    (a D : ℕ → ℤ) (C : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) = nextDenState (a n) (D n))
    (hC : ∀ n, (C (n + 1) : ℤ) = nextTailState (a n) (D n) (C n))
    (hCpos : ∀ n, 0 < C n)
    (hstep : ∀ n, (C (n + 1) : ℤ) =
      (C n : ℤ) - centeredState (a n) (D n) (C n))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (centeredState (a n) (D n) (C n)) < C n)
    (hsum : Summable (negativeRelativeMass C
      (fun n ↦ centeredState (a n) (D n) (C n)))) :
    (∃ N, ∀ n, N ≤ n → centeredState (a n) (D n) (C n) = 0) ∧
      ∃ N, ∀ n, N ≤ n → a (n + 1) = sylvesterNext (a n) := by
  sorry
/-- The cleared integer numerator `p * P n - ∑_{j < n} q * (P n / a j)` with `P n = ∏_{j < n} a j`, which is `q * P n` times the reciprocal tail `p / q - ∑_{j < n} 1 / a j`; the inner quotient is natural division and is exact for `j < n`. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- The canonical numerator state as a natural number, `Int.toNat` of the cleared integer numerator, hence equal to that integer when it is nonnegative and `0` otherwise. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
/-- The canonical cleared denominator `q * P n` with `P n = ∏_{j < n} a j`, the factor that clears the rational reciprocal sum `p / q` and every term of the preceding finite prefix. -/
noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n
/-- Scalar finite-mass criterion, with no denominator dynamics and no normalised-vanishing hypothesis: if `C n` are positive naturals, `E n` are integers with `C (n+1) = C n - E n`, and the normalised negative mass `n ↦ (-E n)_+ / C n` is summable, then `E n = 0` from some index onward. Bounding `C N` by a product of factors `1 + (-E n)_+ / C n` caps the numerator, each strict rise costs a fixed amount of mass, and the remaining nonincreasing positive integer sequence stabilises. -/
theorem finite_negative_mass_scalar (C : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hstep : ∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n)
    (hsum : Summable (negativeRelativeMass C E)) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  sorry
/-- The finite-mass criterion placed on the canonical state built from the problem's own data: for positive naturals `a n` whose reciprocal series has sum the rational number `p / q` with `q > 0`, if the real series whose terms are the positive part of the negation of the centred error of the canonical denominator `q * P n` and the canonical numerator, divided by that canonical numerator, is summable, then `a (n+1) = a n ^ 2 - a n + 1` in the integers from some index onward. The summability is a hypothesis about that canonical state and is not derived from the rational-sum hypothesis. -/
theorem canonical_finite_negative_mass
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hmass : Summable (fun n =>
      max (-(centeredState (a n : ℤ) (canonicalDenominator a q n : ℤ)
        (canonicalNaturalNumerator a p q n : ℤ) : ℝ)) 0 /
          (canonicalNaturalNumerator a p q n : ℝ))) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry
end PalomarCorpus.E243.SummableNegativeMassRigidity

namespace PalomarCorpus.E243.WeightedRecordExcess
open Filter
open scoped Topology
/-- The cumulative least common multiple `L n = lcm(q, a 0, ..., a (n-1))` of the denominator `q` of the reciprocal sum and the first `n` multipliers, defined by `L 0 = q` and `L (n+1) = lcm (L n) (a n)`. -/
noncomputable def L (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n+1 => Nat.lcm (L q a n) (a n)
/-- The overlap debt `M n`, the accumulated product of the overlaps `gcd (L j) (a j)` for `j < n`, defined by `M 0 = 1` and `M (n+1) = M n * gcd (L n) (a n)`; it records the multiplicity lost when the full cleared scale `q * ∏_{j < n} a j` is compressed to the least common multiple `L n`. -/
noncomputable def M (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => M q a n * Nat.gcd (L q a n) (a n)
/-- The canonical cleared tail numerator as a natural number: `Int.toNat` of `p * P n - ∑_{j < n} q * (P n / a j)` with `P n = ∏_{j < n} a j`, hence `q * P n` times the reciprocal tail `p / q - ∑_{j < n} 1 / a j` whenever that integer is nonnegative, and `0` otherwise. -/
noncomputable def C (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (p * ((∏ j ∈ Finset.range n, a j : ℕ) : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * ((∏ k ∈ Finset.range n, a k : ℕ) / a j : ℕ)).toNat
/-- The numerator in the least common multiple coordinates, `U n = C n / M n`, the natural division of the canonical cleared numerator by the overlap debt, which truncates whenever `M n` fails to divide `C n`. Exactness of that division on the canonical orbit is context and is not imposed by this definition. -/
noncomputable def U (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ := C a p q n / M q a n
/-- The centred error in the least common multiple coordinates, defined as the integer `L n - (a n - 1) * U n`. That it equals the cleared centred error divided by the overlap debt `M n` is a fact about the canonical orbit and is not imposed by this definition. -/
noncomputable def V (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  (L q a n : ℤ) - ((a n : ℤ)-1) * (U a p q n : ℤ)
/-- The weighted record-excess summand: at an index `n` where `U (n+1)` strictly exceeds `U j` for every `j ≤ n`, so that `n + 1` sets a strict record, the real value `(-V n - B)_+ * f (U n)` with the positive part taken by `Int.toNat`, and the value `0` at every other index. -/
noncomputable def weight (a : ℕ → ℕ) (p : ℤ) (q B : ℕ) (f : ℝ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if (∀ j ≤ n, U a p q j < U a p q (n+1)) then
    (((-V a p q n - B).toNat : ℕ) : ℝ) * f (U a p q n) else 0
/-- Exact reformulation in the record coordinates: for `a` strictly increasing positive integers with reciprocal sum the rational `p / q`, `q > 0`, and `a (n+1) / a n ^ 2 → 1`, and for a weight `f` that is nonnegative and antitone on `[1, ∞)` with `∫_1^x f → ∞`, the sequence satisfies `a (n+1) = a n ^ 2 - a n + 1` from some index onward if and only if the weighted record-excess series `∑ (-V n - B)_+ f (U n)` over strict record indices is summable for some natural baseline `B`. The hypotheses of the problem do not supply that summability, so this is an equivalent restatement of the question rather than a resolution of it. -/
theorem weighted_record_excess (a : ℕ → ℕ) (ha : StrictMono a)
    (hapos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hg : Tendsto (fun n => (a (n+1) : ℝ) / (a n : ℝ)^2) atTop (𝓝 1))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : Tendsto (fun x : ℝ => ∫ t in (1 : ℝ)..x, f t) atTop atTop) :
    (∃ N, ∀ n, N ≤ n → (a (n+1) : ℤ) = (a n : ℤ)^2 - a n + 1) ↔
      ∃ B : ℕ, Summable (weight a p q B f) := by
  sorry
/-- The growth-defect form of the weighted record-excess summand: at an index `n` where `U (n+1)` strictly exceeds `U j` for every `j ≤ n`, the real value `U n * f (U n) * max (a n ^ 2 / a (n+1) - 1 - B / U n) 0` written in the original growth coordinates, and the value `0` at every other index. -/
noncomputable def growthWeight (a : ℕ → ℕ) (p : ℤ) (q B : ℕ)
    (f : ℝ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if (∀ j ≤ n, U a p q j < U a p q (n+1)) then
    (U a p q n : ℝ) * f (U a p q n) *
      max ((a n : ℝ)^2 / (a (n+1) : ℝ) - 1 - (B : ℝ) / U a p q n) 0
  else 0
/-- The same exact reformulation with the summand expressed in the original growth coordinates: under the same hypotheses on `a` and on the weight `f`, the sequence satisfies `a (n+1) = a n ^ 2 - a n + 1` from some index onward if and only if `∑ U n f (U n) (a n ^ 2 / a (n+1) - 1 - B / U n)_+` over strict record indices is summable for some natural baseline `B`. This is an equivalent restatement of the question in the problem's own growth quantity, and it establishes nothing about the value. -/
theorem weighted_growth_record_excess (a : ℕ → ℕ) (ha : StrictMono a)
    (hapos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hg : Tendsto (fun n => (a (n+1) : ℝ) / (a n : ℝ)^2) atTop (𝓝 1))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : Tendsto (fun x : ℝ => ∫ t in (1 : ℝ)..x, f t) atTop atTop) :
    (∃ N, ∀ n, N ≤ n → (a (n+1) : ℤ) = (a n : ℤ)^2 - a n + 1) ↔
      ∃ B : ℕ, Summable (growthWeight a p q B f) := by
  sorry
end PalomarCorpus.E243.WeightedRecordExcess
