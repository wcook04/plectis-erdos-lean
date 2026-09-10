/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PrimitiveRecordBarrier

/-!
# Source transport for primitive record-rise-two rigidity in Erdős #243

This proof packages the eight checked declarations from
`ErdosProblems.Erdos243.PrimitiveRecordBarrier` into Mathlib-only statements.
The only extra work is showing that the locally defined `runningMax` and
`sylvesterNext` agree with the corpus definitions.
-/

namespace Erdos249257.ExternalVerification243PrimitiveRecordRigidity

def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

theorem runningMax_eq (u : ℕ → ℕ) (n : ℕ) :
    runningMax u n = ErdosProblems.Erdos243.runningMax u n := by
  induction n with
  | zero => simp [runningMax, ErdosProblems.Erdos243.runningMax]
  | succ k ih => simp [runningMax, ErdosProblems.Erdos243.runningMax, ih]

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
    p ^ l ∣ v' :=
  ErdosProblems.Erdos243.primitive_valuation_no_drop
    hp hcop hvpos hq hwpos hnum hden hl hlt

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
    ∀ n, s ≤ n → (∀ k, s ≤ k → k < n → u k < H) → p ^ l ∣ v n :=
  ErdosProblems.Erdos243.protectedPrimePower_persists
    a u v w hc p l s H hp hred hvpos hw hwpos hnum hden hslow hheight hprot

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
  have hRs' : ErdosProblems.Erdos243.runningMax u s < H := by
    simpa [runningMax_eq] using hRs
  have hrec' : ∀ n, s ≤ n →
      ErdosProblems.Erdos243.runningMax u n < u (n + 1) →
        u (n + 1) ≤ u n + 2 := by
    intro n hn h
    exact hrec n hn (by simpa [runningMax_eq] using h)
  exact ErdosProblems.Erdos243.odd_record_cut
    a u v w hc p l s H hp hl hHodd hpH hred hvpos hw hwpos hnum hden
    hslow hheight hprot hRs' hrec'

theorem exists_oddMultiple_trapHeight
    {p l R : ℕ} (hp2 : 2 ≤ p) (hpodd : Odd p) (hl : 1 ≤ l)
    (hbig : 3 * R < p ^ l) :
    ∃ H, Odd H ∧ p ∣ H ∧ R < H ∧ 3 * H < 2 * p ^ (l + 1) :=
  ErdosProblems.Erdos243.exists_oddMultiple_trapHeight hp2 hpodd hl hbig

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
  have hbig' : 3 * ErdosProblems.Erdos243.runningMax u s < p ^ l := by
    simpa [runningMax_eq] using hbig
  have hrec' : ∀ n, s ≤ n →
      ErdosProblems.Erdos243.runningMax u n < u (n + 1) →
        u (n + 1) ≤ u n + 2 := by
    intro n hn h
    exact hrec n hn (by simpa [runningMax_eq] using h)
  exact ErdosProblems.Erdos243.numerator_bounded_of_oddPrimePower
    a u v w hc p l s hp hpodd hl hred hvpos hw hwpos hnum hden hslow
    hprot hbig' hrec'

theorem centeredZero_forces_unit
    {a u v w hc u' : ℕ}
    (hcop : Nat.Coprime u v)
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hzero : (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ) = 0) :
    u = 1 ∧ w = 1 ∧ hc = 1 ∧ u' = 1 :=
  ErdosProblems.Erdos243.centeredZero_forces_unit hcop hq hnum hzero

theorem sylvesterStep_of_centeredZero_pair
    {a a' u v w hc u' v' : ℕ}
    (hcop : Nat.Coprime u v)
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hden : a * v = hc * v')
    (hzero : (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ) = 0)
    (hzero' : (v' : ℤ) - ((a' : ℤ) - 1) * (u' : ℤ) = 0) :
    (a' : ℤ) = sylvesterNext (a : ℤ) := by
  simpa [sylvesterNext, ErdosProblems.Erdos243.sylvesterNext] using
    ErdosProblems.Erdos243.sylvesterStep_of_centeredZero_pair
      hcop hq hnum hden hzero hzero'

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
  have hrec' : ∀ n, N ≤ n →
      ErdosProblems.Erdos243.runningMax u n < u (n + 1) →
        u (n + 1) ≤ u n + 2 := by
    intro n hn h
    exact hrec n hn (by simpa [runningMax_eq] using h)
  have hsupply' : ∀ M, ∃ s, M ≤ s ∧ ∃ p l, p.Prime ∧ Odd p ∧ 1 ≤ l ∧
      p ^ l ∣ v s ∧ 3 * ErdosProblems.Erdos243.runningMax u s < p ^ l := by
    intro M
    obtain ⟨s, hMs, p, l, hp, hpodd, hl, hpl, hbig⟩ := hsupply M
    exact ⟨s, hMs, p, l, hp, hpodd, hl, hpl, by simpa [runningMax_eq] using hbig⟩
  simpa [sylvesterNext, ErdosProblems.Erdos243.sylvesterNext] using
    ErdosProblems.Erdos243.recordRiseTwo_sylvesterNext_eventually
      a u v w hc e N hvpos hred hw hwpos hnum hden he hcentre hvanish
      hrec' hsupply'

end Erdos249257.ExternalVerification243PrimitiveRecordRigidity
