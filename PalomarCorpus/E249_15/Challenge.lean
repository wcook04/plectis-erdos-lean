/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record section 6.4: further exact identities (part 2 of 3)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open Finset
open Filter
open Set
open Module
open scoped BigOperators
open ArithmeticFunction

namespace PalomarCorpus.E249_15.Shared
/-- The exact integer recurrence together with the subexponential boundary `u(N) = o(2^N)`, expressed as convergence of the quotient. Local copy of Erdos249257.IsTemperedBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)
/-- The shifted totient difference `φ(n + h) - φ(n)`, taken in `ℤ` through the cast from `ℕ`. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- The quotient of the first multiple of `d` strictly above `N`. Local copy of Erdos249257.TotientShiftedMobiusPulse.forwardMultipleQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def forwardMultipleQuotient (N d : ℕ) : ℕ := N / d + 1
/-- The least strictly positive shift from `N` to a multiple of `d` when `d > 0`. At a divisor of `N` it is `d`, rather than zero. Local copy of Erdos249257.TotientShiftedMobiusPulse.forwardMultipleShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def forwardMultipleShift (N d : ℕ) : ℕ := d - N % d
/-- The universal period `lcm(1, 2, ..., t)`, given recursively by `periodLcm 0 = 1` and `periodLcm (t + 1) = lcm (periodLcm t) (t + 1)`. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
/-- The height `H_a = lcm(1, 2, ..., 2 ^ a)`, used as both the basepoint and the shift of the power-of-two LCM diagonal. -/
noncomputable def actualLcmHeight (a : ℕ) : ℕ :=
  periodLcm (2 ^ a)
/-- The binary totient tail `R_N = ∑_{j ≥ 1} φ(N + j) / 2 ^ j`, a real number satisfying `2 ^ N S = Φ_N + R_N`, where `S = ∑_{n ≥ 1} φ(n) / 2 ^ n` and `Φ_N = ∑_{n ≤ N} φ(n) 2 ^ (N - n)` is an integer. It obeys `0 < R_N ≤ N + 1` for `N ≥ 1`. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- The LCM diagonal orbit value `R_{2 H_a} - R_{H_a}`, the difference of the binary totient tails at the heights `2 H_a` and `H_a`. -/
noncomputable def actualLcmTailOrbit (a : ℕ) : ℝ :=
  totientTail (2 * actualLcmHeight a) - totientTail (actualLcmHeight a)
/-- The signed binary discrepancy `D_{h,N,L} = ∑_{j < L} (φ(N + h + 1 + j) - φ(N + 1 + j)) 2 ^ (L - 1 - j)` between two length-`L` totient windows separated by the shift `h`, an integer satisfying `|2 ^ L (R_{N + h} - R_N) - D_{h,N,L}| ≤ N + h + L + 2`. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
end PalomarCorpus.E249_15.Shared

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_15.Shared (actualLcmHeight actualLcmTailOrbit certifiedKill deltaTotient periodLcm totientTail windowDiscrepancy)
/-- States prop:SK-01-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.actualLcmTailOrbit_eq_tail_difference in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem actualLcmTailOrbit_eq_tail_difference (a : ℕ) :
    actualLcmTailOrbit a =
      totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) := by
  sorry
/-- States prop:A9-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.eventual_tail_period_of_not_irrational in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem eventual_tail_period_of_not_irrational
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States prop:A9-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_iff_tail_diff_nonintegral in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_certifiedKill_iff_tail_diff_nonintegral (h N : ℕ) :
    (∃ L : ℕ, certifiedKill h N L) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States prop:TA-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_integral_tailDiff_half_pulse in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_prime_integral_tailDiff_half_pulse
    {H K N₀ : ℕ} (hK : 2 ≤ K) (hHK : K < H)
    (hint : ∀ N : ℕ, N₀ ≤ N →
      totientTail (N + H) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ))
    (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ ∃ z : ℤ,
      (z : ℝ) = totientTail (p + H) - totientTail p ∧
        z ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
  sorry
/-- States prop:TA-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_twoAdic_pulse_block in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_prime_twoAdic_pulse_block (K H B : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ H + K < p ∧ p.Prime ∧
      p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K] ∧
      2 ^ K ∣ Nat.totient (p + H) ∧
      (∀ j : ℕ, 1 ≤ j → j < K →
        2 ^ K ∣ Nat.totient (p - j) ∧ 2 ^ K ∣ Nat.totient (p - j + H)) ∧
      (∀ j : ℕ, 1 ≤ j → j < K →
        deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K]) ∧
      deltaTotient H p ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
  sorry
/-- States prop:FR-02-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.fixedRank_cleanWindow_structure in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fixedRank_cleanWindow_structure {a j : ℕ} (ha : 4 ≤ a) (hj : 0 < j)
    (hsq : j * j ≤ 2 ^ a) :
    j ∣ periodLcm (2 ^ a)
      ∧ (∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ periodLcm (2 ^ a) / j)
      ∧ 2 * j ≤ 2 ^ a
      ∧ 2 * j ∣ periodLcm (2 ^ a)
      ∧ 2 ≤ periodLcm (2 ^ a) / j
      ∧ Even (periodLcm (2 ^ a) / j)
      ∧ (∀ q : ℕ, 0 < q → q ≤ 3 →
          Nat.gcd j (q * (periodLcm (2 ^ a) / j) + 1) = 1
            ∧ Odd (q * (periodLcm (2 ^ a) / j) + 1)
            ∧ 2 < q * (periodLcm (2 ^ a) / j) + 1
            ∧ Even (Nat.totient (q * (periodLcm (2 ^ a) / j) + 1))) := by
  sorry
/-- States prop:A9-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_certificate_supply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_certificate_supply
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
export PalomarCorpus.E249_15.Shared (actualLcmHeight actualLcmTailOrbit certifiedKill deltaTotient periodLcm totientTail windowDiscrepancy)
/-- States prop:TA-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.pulse_delta_of_divisor_data in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem pulse_delta_of_divisor_data {H K p : ℕ} (hK : 2 ≤ K) (hp : p.Prime)
    (hmod : p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K])
    (htop : 2 ^ K ∣ Nat.totient (p + H))
    (hlower : ∀ j : ℕ, 1 ≤ j → j < K →
      2 ^ K ∣ Nat.totient (p - j) ∧ 2 ^ K ∣ Nat.totient (p - j + H)) :
    deltaTotient H p ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      ∀ j : ℕ, 1 ≤ j → j < K →
        deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K] := by
  sorry
/-- States prop:A9-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.rational_tail_period_explicit_witnesses in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_tail_period_explicit_witnesses
    (p : ℚ) (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (p : ℝ))
    (c v : ℕ) (hden : p.den = 2 ^ c * v) (hvodd : Odd v) :
    v ∣ 2 ^ Nat.totient v - 1 ∧
      (∀ N : ℕ, c ≤ N →
        ((2 : ℝ) ^ N * ((2 : ℝ) ^ Nat.totient v - 1)) *
            (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ∈
          Set.range ((↑) : ℤ → ℝ)) ∧
      (∀ N : ℕ, c ≤ N →
        totientTail (N + Nat.totient v) - totientTail N ∈
          Set.range ((↑) : ℤ → ℝ)) := by
  sorry
/-- States prop:SK-01-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.shortWindow_certificates_kill_omega_four_and_six in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem shortWindow_certificates_kill_omega_four_and_six :
    certifiedKill (periodLcm 16) (periodLcm 16) 23 ∧
      (23 : ℕ) < 32 ∧
      certifiedKill (periodLcm 64) (periodLcm 64) 93 ∧
      (93 : ℕ) < 128 ∧
      actualLcmTailOrbit 4 ∉ Set.range ((↑) : ℤ → ℝ) ∧
      actualLcmTailOrbit 6 ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States prop:A9-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tail_diff_notMem_int_of_irrational in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_diff_notMem_int_of_irrational
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
    {h N : ℕ} (hh : 0 < h) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States prop:FR-02-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.two_mul_totient_dvd_totient_second_difference in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_mul_totient_dvd_totient_second_difference {a j : ℕ} (ha : 4 ≤ a)
    (hj : 0 < j) (hsq : j * j ≤ 2 ^ a) :
    (2 * (Nat.totient j : ℤ)) ∣
          ((Nat.totient (3 * periodLcm (2 ^ a) + j) : ℤ)
            - 2 * (Nat.totient (2 * periodLcm (2 ^ a) + j) : ℤ)
            + (Nat.totient (periodLcm (2 ^ a) + j) : ℤ))
      ∧ ((Nat.totient (3 * periodLcm (2 ^ a) + j) : ℤ)
            - 2 * (Nat.totient (2 * periodLcm (2 ^ a) + j) : ℤ)
            + (Nat.totient (periodLcm (2 ^ a) + j) : ℤ))
          = (Nat.totient j : ℤ)
              * ((Nat.totient (3 * (periodLcm (2 ^ a) / j) + 1) : ℤ)
                  - 2 * (Nat.totient (2 * (periodLcm (2 ^ a) / j) + 1) : ℤ)
                  + (Nat.totient (periodLcm (2 ^ a) / j + 1) : ℤ)) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAU

namespace PalomarCorpus.E249.PaperStatementsBC
open Filter
open Set
open Finset
export PalomarCorpus.E249_15.Shared (IsTemperedBinaryOrbit totientTail)
/-- States prop:CP-01-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.carryShift_dvd_iff_tailDiff_integral in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem carryShift_dvd_iff_tailDiff_integral {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ) :
    (v : ℤ) ∣ u (N + k) - u N
      ↔ ∃ z : ℤ, (z : ℝ) = totientTail (N + k) - totientTail N := by
  sorry
/-- States prop:CP-01-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.temperedCarry_eq_scaledTail_and_shift in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem temperedCarry_eq_scaledTail_and_shift {v : ℕ} {u : ℕ → ℤ}
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ) :
    ((u N : ℤ) : ℝ) = (v : ℝ) * totientTail N
      ∧ ((u (N + k) - u N : ℤ) : ℝ)
          = (v : ℝ) * (totientTail (N + k) - totientTail N) := by
  sorry
end PalomarCorpus.E249.PaperStatementsBC

namespace PalomarCorpus.E249.PaperStatementsBH
open Module
open Filter
open Set
export PalomarCorpus.E249_15.Shared (IsTemperedBinaryOrbit)
/-- Uniform quotient-periodicity of all dyadic carry sections. The period is measured in the section variable; its ambient-index shift is `2^j h`. Local copy of Erdos249257.CarrySectionsEventuallyPeriodicMod, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CarrySectionsEventuallyPeriodicMod
    (v h N₀ : ℕ) (u : ℕ → ℤ) : Prop :=
  ∀ j r n : ℕ, N₀ ≤ n →
    u (2 ^ j * n + r) ≡ u (2 ^ j * (n + h) + r) [ZMOD (v : ℤ)]
/-- The full carry-section family through levels `1,...,e`. Local copy of Erdos249257.TotientCarryIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev TotientCarryIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ (j.val + 1))
/-- A dyadic section of an integer carry orbit, viewed over `ℚ`. Local copy of Erdos249257.carryKernelSeq, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryKernelSeq (u : ℕ → ℤ) (j r : ℕ) : ℕ → ℚ := fun n =>
  u (2 ^ j * n + r)
/-- Every carry section through levels `1,...,e`, without quotienting or identifying residue channels. Local copy of Erdos249257.canonicalCarryKernelFamily, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalCarryKernelFamily (u : ℕ → ℤ) (e : ℕ) :
    TotientCarryIndex e → ℕ → ℚ
  | ⟨j, r⟩ => carryKernelSeq u (j.val + 1) r.val
/-- States prop:CP-02 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.rationality_forces_mod_period_and_unbounded_rank in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rationality_forces_mod_period_and_unbounded_rank
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ, 2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u := by
  sorry
end PalomarCorpus.E249.PaperStatementsBH

namespace PalomarCorpus.E249.PaperStatementsAJ
/-- States prop:CP-05-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_totient_shift_four_mul_congr_two_mod_four in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_prime_totient_shift_four_mul_congr_two_mod_four
    (h B : ℕ) (hh : 0 < h) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧
      ((Nat.totient (p + 4 * h) : ℤ) - (Nat.totient p : ℤ)) ≡ (2 : ℤ) [ZMOD 4] := by
  sorry
/-- States prop:SK-01-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.shortWindow_inequalities in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem shortWindow_inequalities :
    (23 : ℕ) < 2 * 2 ^ 4 ∧ (93 : ℕ) < 2 * 2 ^ 6 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsBA
open scoped BigOperators
open ArithmeticFunction
export PalomarCorpus.E249_15.Shared (forwardMultipleQuotient forwardMultipleShift)
/-- States prop:MP-01-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.forwardMultipleShift_least in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem forwardMultipleShift_least (N : ℕ) {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hlt : m < forwardMultipleShift N d) : ¬ d ∣ N + m := by
  sorry
/-- States prop:MP-01-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.forwardMultiple_enumeration in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem forwardMultiple_enumeration (N : ℕ) {d : ℕ} (hd : 0 < d) (l : ℕ) :
    N + (forwardMultipleShift N d + d * l) =
      d * (forwardMultipleQuotient N d + l) := by
  sorry
/-- States prop:MP-01-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.forwardMultiple_spec in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem forwardMultiple_spec (N : ℕ) {d : ℕ} (hd : 0 < d) :
    forwardMultipleShift N d = d - N % d ∧
      forwardMultipleQuotient N d = N / d + 1 ∧
      1 ≤ forwardMultipleShift N d ∧
      forwardMultipleShift N d ≤ d ∧
      d ∣ N + forwardMultipleShift N d := by
  sorry
end PalomarCorpus.E249.PaperStatementsBA

namespace PalomarCorpus.E249.PaperStatementsBM
open ArithmeticFunction
open scoped BigOperators
open Finset
export PalomarCorpus.E249_15.Shared (forwardMultipleQuotient forwardMultipleShift totientTail)
/-- States prop:MP-01-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientTail_eq_tsum_mobius_inversion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totientTail_eq_tsum_mobius_inversion (N : ℕ) :
    totientTail N =
      ∑' d : ℕ+,
        (((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) *
            (2 : ℝ) ^ ((d : ℕ) - forwardMultipleShift N (d : ℕ))) *
          (((forwardMultipleQuotient N (d : ℕ) : ℕ) : ℝ) /
              ((2 : ℝ) ^ (d : ℕ) - 1) +
            1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := by
  sorry
end PalomarCorpus.E249.PaperStatementsBM

namespace PalomarCorpus.E249.PaperStatementsAK
/-- States prop:A9-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totient_one_eq_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_one_eq_one : Nat.totient 1 = 1 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAK
