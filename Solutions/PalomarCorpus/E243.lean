/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.ReciprocalTailRigidity
import ErdosProblems.Erdos243.PrimitiveRecordBarrier
import ErdosProblems.Erdos243.ProtectedEpochEnergy
import ErdosProblems.Erdos243.RecordIncrementBarrier
import ErdosProblems.Erdos243.RepairEntropy
import ErdosProblems.Erdos243.SaturatedSquareTransport
import ErdosProblems.Erdos243.SlowRiseBarrier
import ErdosProblems.Erdos243.PaperCompleteR8.CanonicalNegativeMass
import ErdosProblems.Erdos243.SparseResetRecovery
import ErdosProblems.Erdos243.PaperCompleteR8.GrowthDebtSummability

open scoped BigOperators
open Finset
open Filter
open scoped Topology

namespace PalomarCorpus.E243.Shared
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

end PalomarCorpus.E243.Shared
namespace PalomarCorpus.E243.BoundedNegativePartRigidity
export PalomarCorpus.E243.Shared (centeredState sylvesterNext)

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
  have hE' : ∀ n, E n = ErdosProblems.Erdos243.centeredState
      (a n : ℤ) (D n : ℤ) (C n : ℤ) := by
    intro n
    simpa [centeredState, ErdosProblems.Erdos243.centeredState] using hE n
  have hzero : ∃ N, ∀ n, N ≤ n → E n = 0 :=
    ErdosProblems.Erdos243.eventuallyBoundedNegativePart_eventually_zero
      a C D E ha hCpos hC hD hE' hbound hvanish
  have hrec : ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
    simpa [sylvesterNext, ErdosProblems.Erdos243.sylvesterNext] using
      ErdosProblems.Erdos243.boundedNegativePart_sylvesterNext_eventually
        a C D E ha hCpos hC hD hE' hbound hvanish
  exact ⟨hzero, hrec⟩

end PalomarCorpus.E243.BoundedNegativePartRigidity

namespace PalomarCorpus.E243.BoundedRiseReducedTail

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
  apply ErdosProblems.Erdos243.no_boundedRise_of_tailAvoidance u m N B hB hm
  · intro i j hi hj hij
    exact hpair hi hj hij
  · intro i t hi hit
    exact havoid hi hit
  · exact hrise
  · exact huTop

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
  exact ErdosProblems.Erdos243.no_boundedRise_reducedTail
    a u v B hB ha hred hu hv hrise huTop

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
  exact ErdosProblems.Erdos243.no_eventuallyBoundedRise_reducedTail
    a u v N B hB ha hred hu hv hrise huTop

end PalomarCorpus.E243.BoundedRiseReducedTail

namespace PalomarCorpus.E243.PeriodicNegativeOrbit

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
  exact ErdosProblems.Erdos243.no_phasePrimitivePeriodicNegative_orbit
    a D C e h M hh hM ha hepos helt hD hC hshape hperiod hphase hprimitive

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
  exact ErdosProblems.Erdos243.no_periodicNegative_orbit
    a D C e h M hh hM ha hepos helt hD hC hshape hperiod hphase

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
  exact ErdosProblems.Erdos243.no_eventuallyPeriodicNegative_orbit
    a D C e N h M hh hM ha hepos helt hD hC hshape hperiod hphase

end PalomarCorpus.E243.PeriodicNegativeOrbit

namespace PalomarCorpus.E243.PrimitiveRecordRigidity
export PalomarCorpus.E243.Shared (runningMax sylvesterNext)

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

end PalomarCorpus.E243.PrimitiveRecordRigidity

namespace PalomarCorpus.E243.ProtectedEpochEnergy
export PalomarCorpus.E243.Shared (runningMax)

theorem runningMax_eq (u : ℕ → ℕ) (n : ℕ) :
    runningMax u n = ErdosProblems.Erdos243.runningMax u n := by
  induction n with
  | zero => simp [runningMax, ErdosProblems.Erdos243.runningMax]
  | succ k ih => simp [runningMax, ErdosProblems.Erdos243.runningMax, ih]

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
  have hRs' : 4 * ErdosProblems.Erdos243.runningMax u s < p * p ^ l := by
    simpa [runningMax_eq] using hRs
  obtain ⟨J, hJ, hbound⟩ :=
    ErdosProblems.Erdos243.protected_epoch_energy_integer a u v w hc p l s τ hp
      hpodd hl hred hvpos hw hwpos hnum hden hslow hprot hQ hRs' hsτ hτ
  exact ⟨J, fun n hn => by simpa [runningMax_eq] using hJ n hn, hbound⟩

end PalomarCorpus.E243.ProtectedEpochEnergy

namespace PalomarCorpus.E243.RecordIncrementBarrier
export PalomarCorpus.E243.Shared (runningMax sylvesterNext)

theorem runningMax_eq (u : ℕ → ℕ) (n : ℕ) :
    runningMax u n = ErdosProblems.Erdos243.runningMax u n := by
  induction n with
  | zero => simp [runningMax, ErdosProblems.Erdos243.runningMax]
  | succ k ih => simp [runningMax, ErdosProblems.Erdos243.runningMax, ih]

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
  have hinc' : ∀ n, N ≤ n →
      ErdosProblems.Erdos243.runningMax u (n + 1)
        ≤ ErdosProblems.Erdos243.runningMax u n + 1 := by
    intro n hn
    simpa [runningMax_eq] using hinc n hn
  have hsupply' : ∀ M, ∃ s, M ≤ s ∧ ∃ p l, p.Prime ∧ 1 ≤ l ∧
      p ^ l ∣ v s ∧ ErdosProblems.Erdos243.runningMax u s + 3 ≤ p ^ l := by
    intro M
    obtain ⟨s, hMs, p, l, hp, hl, hpl, hbig⟩ := hsupply M
    exact ⟨s, hMs, p, l, hp, hl, hpl, by simpa [runningMax_eq] using hbig⟩
  simpa [sylvesterNext, ErdosProblems.Erdos243.sylvesterNext] using
    ErdosProblems.Erdos243.recordIncrementOne_sylvesterNext_eventually
      a u v w hc e N hvpos hred hw hwpos hnum hden he hcentre hvanish hinc' hsupply'

end PalomarCorpus.E243.RecordIncrementBarrier

namespace PalomarCorpus.E243.RepairEntropy

open scoped BigOperators

noncomputable def deletionProduct (c : ℕ → ℕ) (s t : ℕ) : ℕ :=
  ∏ n ∈ Finset.Ico s t, c n
noncomputable def repairedAt (c : ℕ → ℕ) (s t m : ℕ) : Prop :=
  m ∣ deletionProduct c s t
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
  have hrepair' : ∀ q ∈ R,
      ErdosProblems.Erdos243.repairedAt c r (r + L) (m q) := by
    intro q hq
    simpa [repairedAt, deletionProduct, ErdosProblems.Erdos243.repairedAt,
      ErdosProblems.Erdos243.deletionProduct] using hrepair q hq
  exact ErdosProblems.Erdos243.repairedFamily_recovery_energy_divisionFree
    R m u h c e K r L hK hupos hhpos hstep herr hL hrecover hrepair' hsq

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
  have hrepair' : ∀ q ∈ R,
      ErdosProblems.Erdos243.repairedAt c r (r + L) (m q) := by
    intro q hq
    simpa [repairedAt, deletionProduct, ErdosProblems.Erdos243.repairedAt,
      ErdosProblems.Erdos243.deletionProduct] using hrepair q hq
  exact ErdosProblems.Erdos243.repaired_card_bound_of_independent
    R m u h c e K r L hK hupos hhpos hstep herr hL hrecover hrepair' hsq hindep

theorem eventually_recoveryPayment_eq_one_of_fixedLength
    (u h : ℕ → ℕ) (e : ℕ → ℤ)
    (hupos : ∀ n, 0 < u n)
    (hhpos : ∀ n, 0 < h n)
    (hstep : ∀ n, (h n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - e n)
    (hvanish : ∀ K : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K * Int.natAbs (e n) < u n)
    (L : ℕ) (hL : 0 < L) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → u r ≤ u (r + L) →
      (∏ i ∈ Finset.range L, h (r + i)) = 1 := by
  exact ErdosProblems.Erdos243.eventually_recoveryPayment_eq_one_of_fixedLength
    u h e hupos hhpos hstep hvanish L hL

end PalomarCorpus.E243.RepairEntropy

namespace PalomarCorpus.E243.SaturatedSquareTransport

/-- **Saturated square transport, unnormalised form.**  The whole next reduced
numerator divides `hc * e * e' - v ^ 2`, with no hypothesis beyond the two
cocycle equations and the two centred-error definitions. -/
theorem saturated_square_transport_raw
    {a u v w hc u' v' : ℕ} {a' e e' : ℤ}
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hden : a * v = hc * v')
    (he : e = (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ))
    (he' : e' = (v' : ℤ) - (a' - 1) * (u' : ℤ)) :
    (u' : ℤ) ∣ (hc : ℤ) * e * e' - (v : ℤ) ^ 2 :=
  ErdosProblems.Erdos243.saturated_square_transport_raw hq hnum hden he he'

/-- **The Legendre defect obstructs a unit non-square part, and nothing more.**
If the centred-error product is a quadratic non-residue modulo a prime dividing
the next numerator, then the non-square part `b` of the removed content is not
`1`. No bound on the content follows. -/
theorem legendre_defect_forces_nonsquare_content
    {b s u' p : ℕ} {e e' : ℤ}
    (hdvd : (u' : ℤ) ∣ (b : ℤ) * e * e' - ((b : ℤ) * (s : ℤ)) ^ 2)
    (hpu : p ∣ u')
    (hnr : ¬ IsSquare ((e : ZMod p) * (e' : ZMod p))) :
    b ≠ 1 :=
  ErdosProblems.Erdos243.legendre_defect_forces_nonsquare_content hdvd hpu hnr

end PalomarCorpus.E243.SaturatedSquareTransport

namespace PalomarCorpus.E243.SlowRiseBarrier

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
    False :=
  ErdosProblems.Erdos243.no_slowRise_reducedTail a u v N B ha hred hu hv huTop
    hstart hrise

end PalomarCorpus.E243.SlowRiseBarrier

/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

namespace PalomarCorpus.E243.SummableNegativeMassRigidity
export PalomarCorpus.E243.Shared (centeredState sylvesterNext)

noncomputable def nextDenState (a D : ℤ) : ℤ :=
  a * D
noncomputable def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D
noncomputable def negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  (Int.natAbs (min (E n) 0) : ℝ) / C n

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
  have hD' : ∀ n, D (n + 1) =
      ErdosProblems.Erdos243.nextDenState (a n) (D n) := by
    simpa [nextDenState, ErdosProblems.Erdos243.nextDenState] using hD
  have hC' : ∀ n, (C (n + 1) : ℤ) =
      ErdosProblems.Erdos243.nextTailState (a n) (D n) (C n) := by
    simpa [nextTailState, ErdosProblems.Erdos243.nextTailState] using hC
  have hstep' : ∀ n, (C (n + 1) : ℤ) = (C n : ℤ) -
      ErdosProblems.Erdos243.centeredState (a n) (D n) (C n) := by
    simpa [centeredState, ErdosProblems.Erdos243.centeredState] using hstep
  have hvanish' : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs
        (ErdosProblems.Erdos243.centeredState (a n) (D n) (C n)) < C n := by
    simpa [centeredState, ErdosProblems.Erdos243.centeredState] using hvanish
  have hsum' : Summable
      (ErdosProblems.Erdos243.negativeRelativeMass C
        (fun n ↦ ErdosProblems.Erdos243.centeredState (a n) (D n) (C n))) := by
    simpa [negativeRelativeMass,
      ErdosProblems.Erdos243.negativeRelativeMass, centeredState,
      ErdosProblems.Erdos243.centeredState] using hsum
  have hzero' : ∃ N, ∀ n, N ≤ n →
      ErdosProblems.Erdos243.centeredState (a n) (D n) (C n) = 0 :=
    ErdosProblems.Erdos243.eventually_zero_of_summable_negativeRelativeMass
      C (fun n ↦ ErdosProblems.Erdos243.centeredState (a n) (D n) (C n))
      hCpos hstep' hvanish' hsum'
  have hrec' : ∃ N, ∀ n, N ≤ n →
      a (n + 1) = ErdosProblems.Erdos243.sylvesterNext (a n) :=
    ErdosProblems.Erdos243.sylvesterNext_eventually_of_summable_negativeRelativeMass
      a D C hD' hC' hCpos hstep' hvanish' hsum'
  constructor
  · simpa [centeredState, ErdosProblems.Erdos243.centeredState] using hzero'
  · simpa [sylvesterNext, ErdosProblems.Erdos243.sylvesterNext] using hrec'

open scoped BigOperators
open Finset

noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n
theorem finite_negative_mass_scalar (C : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hstep : ∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n)
    (hsum : Summable (negativeRelativeMass C E)) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  exact ErdosProblems.Erdos243.eventually_zero_of_summable_negativeRelativeMass_scalar C E hCpos hstep hsum

theorem canonical_finite_negative_mass
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hmass : Summable (fun n =>
      max (-(centeredState (a n : ℤ) (canonicalDenominator a q n : ℤ)
        (canonicalNaturalNumerator a p q n : ℤ) : ℝ)) 0 /
          (canonicalNaturalNumerator a p q n : ℝ))) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  exact ErdosProblems.Erdos243.PaperCompleteR8.canonical_sylvester_of_finite_negative_mass a hpos p q hq hs hmass

end PalomarCorpus.E243.SummableNegativeMassRigidity

namespace PalomarCorpus.E243.WeightedRecordExcess
open Filter
open scoped Topology
noncomputable section

noncomputable def L (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n+1 => Nat.lcm (L q a n) (a n)
noncomputable def M (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => M q a n * Nat.gcd (L q a n) (a n)
noncomputable def C (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (p * ((∏ j ∈ Finset.range n, a j : ℕ) : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * ((∏ k ∈ Finset.range n, a k : ℕ) / a j : ℕ)).toNat
noncomputable def U (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ := C a p q n / M q a n
noncomputable def V (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  (L q a n : ℤ) - ((a n : ℤ)-1) * (U a p q n : ℤ)
noncomputable def weight (a : ℕ → ℕ) (p : ℤ) (q B : ℕ) (f : ℝ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if (∀ j ≤ n, U a p q j < U a p q (n+1)) then
    (((-V a p q n - B).toNat : ℕ) : ℝ) * f (U a p q n) else 0

theorem weighted_record_excess (a : ℕ → ℕ) (ha : StrictMono a)
    (hapos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hg : Tendsto (fun n => (a (n+1) : ℝ) / (a n : ℝ)^2) atTop (𝓝 1))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : Tendsto (fun x : ℝ => ∫ t in (1 : ℝ)..x, f t) atTop atTop) :
    (∃ N, ∀ n, N ≤ n → (a (n+1) : ℤ) = (a n : ℤ)^2 - a n + 1) ↔
      ∃ B : ℕ, Summable (weight a p q B f) := by
  classical
  have hL : ∀ n, L q a n = ErdosProblems.Erdos243.cumulativeDigitLcm q a n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [L, ErdosProblems.Erdos243.cumulativeDigitLcm, ih]
  have hM : ∀ n, M q a n = ErdosProblems.Erdos243.cumulativeOverlapDebt q a n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [M, ErdosProblems.Erdos243.cumulativeOverlapDebt, ih, hL]
  have h := ErdosProblems.Erdos243.PaperCompleteR8.canonical_weighted_record
    a ha hapos p q hq hs hg f hf hpos hdiv
  change (∃ N, ∀ n, N ≤ n → (a (n+1) : ℤ) = (a n : ℤ)^2 - a n + 1) ↔
    ∃ B : ℕ, Summable (fun n : ℕ =>
      if (∀ j ≤ n, U a p q j < U a p q (n+1)) then
        (((-V a p q n - B).toNat : ℕ) : ℝ) * f (U a p q n) else 0)
  simpa only [U, V, C, hM, hL,
    ErdosProblems.Erdos243.PaperCompleteR8.canonicalLcmOrbit,
    ErdosProblems.Erdos243.PaperCompleteR8.Record,
    ErdosProblems.Erdos243.lcmLiftedNumerator,
    ErdosProblems.Erdos243.lcmLiftedDigit,
    ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator,
    ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator,
    ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct,
    ErdosProblems.Erdos243.sylvesterNext] using h

noncomputable def growthWeight (a : ℕ → ℕ) (p : ℤ) (q B : ℕ)
    (f : ℝ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if (∀ j ≤ n, U a p q j < U a p q (n+1)) then
    (U a p q n : ℝ) * f (U a p q n) *
      max ((a n : ℝ)^2 / (a (n+1) : ℝ) - 1 - (B : ℝ) / U a p q n) 0
  else 0

theorem weighted_growth_record_excess (a : ℕ → ℕ) (ha : StrictMono a)
    (hapos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hg : Tendsto (fun n => (a (n+1) : ℝ) / (a n : ℝ)^2) atTop (𝓝 1))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : Tendsto (fun x : ℝ => ∫ t in (1 : ℝ)..x, f t) atTop atTop) :
    (∃ N, ∀ n, N ≤ n → (a (n+1) : ℤ) = (a n : ℤ)^2 - a n + 1) ↔
      ∃ B : ℕ, Summable (growthWeight a p q B f) := by
  classical
  have hL : ∀ n, L q a n = ErdosProblems.Erdos243.cumulativeDigitLcm q a n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [L, ErdosProblems.Erdos243.cumulativeDigitLcm, ih]
  have hM : ∀ n, M q a n = ErdosProblems.Erdos243.cumulativeOverlapDebt q a n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [M, ErdosProblems.Erdos243.cumulativeOverlapDebt, ih, hL]
  have h := ErdosProblems.Erdos243.PaperCompleteR8.canonical_weighted_growth_record_factored
    a ha hapos p q hq hs hg f hf hpos hdiv
  change (∃ N, ∀ n, N ≤ n → (a (n+1) : ℤ) = (a n : ℤ)^2 - a n + 1) ↔
    ∃ B : ℕ, Summable (fun n : ℕ =>
      if (∀ j ≤ n, U a p q j < U a p q (n+1)) then
        (U a p q n : ℝ) * f (U a p q n) *
          max ((a n : ℝ)^2 / (a (n+1) : ℝ) - 1 - (B : ℝ) / U a p q n) 0
      else 0)
  simpa only [U, V, C, hM, hL,
    ErdosProblems.Erdos243.PaperCompleteR8.canonicalLcmOrbit,
    ErdosProblems.Erdos243.PaperCompleteR8.Record,
    ErdosProblems.Erdos243.lcmLiftedNumerator,
    ErdosProblems.Erdos243.lcmLiftedDigit,
    ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator,
    ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator,
    ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct,
    ErdosProblems.Erdos243.sylvesterNext] using h

end
end PalomarCorpus.E243.WeightedRecordExcess
