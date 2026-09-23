/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #243, the record amplified cancellation visibility, record increment barrier and repair entropy families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #243, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #243 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Finset
open Filter
open scoped Topology

namespace PalomarCorpus.E243_11.Shared
/-- The running maximum `max_{k ≤ n} u k` of a natural-valued sequence, given by `runningMax u 0 = u 0` and `runningMax u (n+1) = max (runningMax u n) (u (n+1))`. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
end PalomarCorpus.E243_11.Shared

namespace PalomarCorpus.E243.RecordAmplifiedCancellationVisibility
export PalomarCorpus.E243_11.Shared (runningMax)
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
export PalomarCorpus.E243_11.Shared (runningMax sylvesterNext)
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
export PalomarCorpus.E243_11.Shared (sylvesterNext)
/-- The product-cleared denominator update `D ↦ a * D` on the integers, one step of the recurrence `D (n+1) = a n * D n`. -/
noncomputable def nextDenState (a D : ℤ) : ℤ :=
  a * D
/-- The product-cleared tail-numerator update `C ↦ a * C - D` on the integers, obtained by clearing denominators in the tail relation `x n = 1 / a n + x (n+1)`. -/
noncomputable def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D
/-- The centred reciprocal-tail error `D - (a - 1) * C` of an integer state, the integer measuring the failure of the identity `D = (a - 1) * C` that holds exactly on a Sylvester tail. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
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
/-- The prefix product `a 0 * a 1 * ... * a (n-1)` of the first `n` terms of a natural sequence, with the empty product `1` at `n = 0`. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
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
