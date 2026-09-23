/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record section 1.1: unconditional results

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open Filter
open Topology
open Finset

namespace PalomarCorpus.E249_01.Shared
/-- The universal period `lcm(1, 2, ..., t)`, given recursively by `periodLcm 0 = 1` and `periodLcm (t + 1) = lcm (periodLcm t) (t + 1)`. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
/-- The signed binary discrepancy `D_{h,N,L} = ∑_{j < L} (φ(N + h + 1 + j) - φ(N + 1 + j)) 2 ^ (L - 1 - j)` between two length-`L` totient windows separated by the shift `h`, an integer satisfying `|2 ^ L (R_{N + h} - R_N) - D_{h,N,L}| ≤ N + h + L + 2`. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
end PalomarCorpus.E249_01.Shared

namespace PalomarCorpus.E249.PaperStatementsAI
open Filter
open Topology
/-- States thm:denom from the long record for Erdős problem #249. Transported from Erdos249257.tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053 :
    ∀ p : ℚ, p.den ≤ 79639646646701375323355774875831053 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAI

namespace PalomarCorpus.E249.PaperStatementsAK
/-- `qstar` is the exact first displayed denominator at which a gap certificate fails. This is the small checker-facing contract emitted by the untrusted Stern--Brocot producer: all smaller positive denominators pass, while `qstar` itself fails. Local copy of GapFareyBound.IsFirstGapFailure, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsFirstGapFailure (V K H qstar : ℕ) : Prop :=
  (∀ q : ℕ, 0 < q → q < qstar → (q * V) % 2 ^ K + q * H < 2 ^ K) ∧
    ¬ ((qstar * V) % 2 ^ K + qstar * H < 2 ^ K)
/-- States prop:gapwindow, thm:denom from the long record for Erdős problem #249. Transported from GapFareyBound.gap_check_window_1_240_first_failure in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem gap_check_window_1_240_first_failure :
    IsFirstGapFailure
      1299094806818720335611738031537456208600423915562142231419225521361164904
      240 243 79639646646701375323355774875831054 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAK

namespace PalomarCorpus.E249.PaperStatementsAD
open Finset
export PalomarCorpus.E249_01.Shared (certifiedKill windowDiscrepancy)
/-- The residue angle used by the first additive character. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstAngle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))
/-- The complex first additive character of the endpoint discrepancy. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstExp, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)
/-- Fixed-shift fibre-free counted window-phase anti-concentration. The sample `T` may be any nonempty subset of a cofinal dyadic block. Local copy of Erdos249257.TotientTailPeriodKiller.DTWWindowSeparatedPairsAt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DTWWindowSeparatedPairsAt (h : ℕ) : Prop :=
  ∀ X₀ : ℕ, ∃ X L : ℕ, ∃ T : Finset ℕ,
      ∃ P : Finset (ℕ × ℕ), ∃ δ : ℝ,
      max X₀ 1 ≤ X ∧
      T.Nonempty ∧
      T ⊆ Finset.Ico X (2 * X) ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      P ⊆ T.product T ∧
      0 ≤ δ ∧
      (∀ p ∈ P,
        δ ≤ ‖windowFirstExp h p.1 L - windowFirstExp h p.2 L‖) ∧
      2 * (T.card : ℝ) ^ 2 / 5 ≤ (P.card : ℝ) * δ ^ 2
/-- Fibre-free counted window-phase anti-concentration at every positive shift; neither primality nor a pivot factorization is part of the statement. Local copy of Erdos249257.TotientTailPeriodKiller.DTWWindowSeparatedPairs, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DTWWindowSeparatedPairs : Prop :=
  ∀ h : ℕ, 0 < h → DTWWindowSeparatedPairsAt h
/-- States prop:deposits from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.certifiedKill_all_upto_sixteen in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedKill_all_upto_sixteen :
    ∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9 := by
  sorry
/-- States prop:iffs from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.dtwWindowSeparatedPairs_iff_irrational_totient_series in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dtwWindowSeparatedPairs_iff_irrational_totient_series :
    DTWWindowSeparatedPairs ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States catalogue:cert:a10, prop:A10, prop:iffs from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_certificate_supply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totient_series_iff_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ,
        ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L := by
  sorry
end PalomarCorpus.E249.PaperStatementsAD

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_01.Shared (certifiedKill periodLcm windowDiscrepancy)
/-- The asymmetric central-arc certificate. Its low radius is only `N+L+2`, while its high wrap radius remains `N+h+L+2`. It is therefore strictly weaker, and potentially strictly more useful, than `certifiedKill` when `h>0`. Local copy of Erdos249257.directedCertifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def directedCertifiedKill (h N L : ℕ) : Prop :=
  (N + L + 2 : ℤ) ≤ windowDiscrepancy h N L % (2 : ℤ) ^ L ∧
    windowDiscrepancy h N L % (2 : ℤ) ^ L ≤
      (2 : ℤ) ^ L - (N + h + L + 2 : ℤ)
/-- The canonical diagonal version of the directed certificate supply. Local copy of Erdos249257.CofinalDirectedLcmCertificateSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CofinalDirectedLcmCertificateSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ,
    directedCertifiedKill (periodLcm t) (periodLcm t) L
/-- Local copy of Erdos249257.TotientTailPeriodKiller.diagonalPincerCertificateScalesThroughT64, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalPincerCertificateScalesThroughT64 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59, 61, 64]
/-- Local copy of Erdos249257.TotientTailPeriodKiller.diagonalPincerKillDepthThroughT64, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalPincerKillDepthThroughT64 : ℕ → ℕ
  | 1 => 6
  | 2 => 5
  | 3 => 7
  | 4 => 7
  | 5 => 9
  | 7 => 14
  | 8 => 15
  | 9 => 14
  | 11 => 21
  | 13 => 22
  | 16 => 23
  | 17 => 26
  | 19 => 32
  | 23 => 35
  | 25 => 38
  | 27 => 40
  | 29 => 45
  | 31 => 49
  | 32 => 50
  | 37 => 56
  | 41 => 61
  | 43 => 66
  | 47 => 73
  | 49 => 76
  | 53 => 81
  | 59 => 88
  | 61 => 94
  | 64 => 93
  | _ => 0
/-- States prop:deposits from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.certifiedKill_diagonal_all_imported_through_t64 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedKill_diagonal_all_imported_through_t64 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT64,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT64 t) := by
  sorry
/-- States prop:iffs from the long record for Erdős problem #249. Transported from Erdos249257.irrational_totientSeries_iff_cofinalDirectedLcmCertificateSupply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totientSeries_iff_cofinalDirectedLcmCertificateSupply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      CofinalDirectedLcmCertificateSupply := by
  sorry
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
export PalomarCorpus.E249_01.Shared (certifiedKill periodLcm windowDiscrepancy)
/-- **The supply normal form.** For every ray `d ≥ 1` and every basepoint threshold `c`, some multiple period `t·d` admits a certified kill at some `N ≥ c`. The odd part of a hypothetical denominator selects the ray; the kill contradicts the tail-period law on it. Local copy of ErdosProblems.Erdos249.PeriodMultipleEscape.PeriodMultipleKillSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PeriodMultipleKillSupply : Prop :=
  ∀ d : ℕ, 0 < d → ∀ c : ℕ,
    ∃ t N L : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N L
/-- States prop:deposits from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_101_300 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedKill_101_300 : certifiedKill 101 300 11 := by
  sorry
/-- States prop:deposits from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_121_300 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedKill_121_300 : certifiedKill 121 300 10 := by
  sorry
/-- States prop:deposits from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_125_300 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedKill_125_300 : certifiedKill 125 300 18 := by
  sorry
/-- States prop:deposits from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_127_300 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedKill_127_300 : certifiedKill 127 300 11 := by
  sorry
/-- States prop:deposits from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_128_300 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedKill_128_300 : certifiedKill 128 300 11 := by
  sorry
/-- States prop:deposits from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_67_300 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedKill_67_300 : certifiedKill 67 300 11 := by
  sorry
/-- States prop:deposits from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_81_300 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedKill_81_300 : certifiedKill 81 300 13 := by
  sorry
/-- States prop:deposits from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_97_300 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedKill_97_300 : certifiedKill 97 300 13 := by
  sorry
/-- States prop:iffs from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PeriodMultipleEscape.periodMultipleKillSupply_iff_irrational in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem periodMultipleKillSupply_iff_irrational :
    PeriodMultipleKillSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States prop:deposits from the long record for Erdős problem #249. Transported from ErdosProblems.Skip.LadderT67.exists_diagonalKill_le_82 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_diagonalKill_le_82 (t : ℕ) (ht : t ≤ 82) :
    ∃ L, certifiedKill (periodLcm t) (periodLcm t) L := by
  sorry
end PalomarCorpus.E249.PaperStatementsAU

namespace PalomarCorpus.E249.PaperStructuresN
open Finset
export PalomarCorpus.E249_01.Shared (certifiedKill periodLcm windowDiscrepancy)
/-- States prop:deposits from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.certifiedKill_diagonal_t64 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedKill_diagonal_t64 :
    certifiedKill (periodLcm 64) (periodLcm 64) 93 := by
  sorry
end PalomarCorpus.E249.PaperStructuresN

namespace PalomarCorpus.E249.PaperStatementsA
open Finset
export PalomarCorpus.E249_01.Shared (certifiedKill periodLcm windowDiscrepancy)
/-- The window step `a_n = φ(n+h) - φ(n)` driving the carry recurrence. Local copy of Erdos249257.TotientTailPeriodKiller.deltaTotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- The integer carry orbit launched from candidate `d` at position `N`: `orbit 0 = d`, `orbit (i+1) = 2·orbit i - a_{N+i+1}`. If `D_h(N)` is the integer `d`, this orbit equals `D_h(N+i)` forever. Local copy of Erdos249257.TotientTailPeriodKiller.carryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- States prop:sign from the long record for Erdős problem #249. Transported from Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailDiff_shift_pos in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem actualLcmTailDiff_shift_pos
    {a J : ℕ} (ha : 8 ≤ a)
    (hshort : J + (a + 6) < 2 * 2 ^ a) :
    0 <
      totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J) := by
  sorry
/-- States prop:sign from the long record for Erdős problem #249. Transported from Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcm_integral_forces_topEdgeResidue in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem actualLcm_integral_forces_topEdgeResidue
    {a J K : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    {d : ℤ}
    (hd : (d : ℝ) =
      totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J))
    (hroom :
      ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) <
        (2 : ℤ) ^ K) :
    let H := periodLcm (2 ^ a)
    let e := carryOrbit H (H + J) d K
    let P := (2 : ℤ) ^ K
    let B := ((2 * H + J + K + 2 : ℕ) : ℤ)
    windowDiscrepancy H (H + J) K % P = P - e ∧
      P - B < windowDiscrepancy H (H + J) K % P ∧
      windowDiscrepancy H (H + J) K % P < P := by
  sorry
/-- States prop:sign from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.carryOrbit_eq_tail_diff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
lemma carryOrbit_eq_tail_diff {h N : ℕ} {d : ℤ}
    (hd : (d : ℝ) = totientTail (N + h) - totientTail N) (i : ℕ) :
    (carryOrbit h N d i : ℝ) = totientTail (N + i + h) - totientTail (N + i) := by
  sorry
/-- States catalogue:cert:b3, prop:B3, prop:iffs from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_lcm_diagonal_certificate_supply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totient_series_iff_lcm_diagonal_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L,
        certifiedKill (periodLcm t) (periodLcm t) L := by
  sorry
end PalomarCorpus.E249.PaperStatementsA

namespace PalomarCorpus.E249.PaperStatementsAG
open Filter
/-- States prop:parity from the long record for Erdős problem #249. Transported from Erdos249257.TotientParityCoboundaryCountermodel.exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel :
    ∃ c : ℕ → ℕ,
      (∀ N G K, ∃ k,
        N < 2 ^ (k + 3) ∧
        ∀ i : ℕ, i < K →
          2 ^ (k + i + 3) + G < 2 ^ (k + i + 4) ∧
          c (2 ^ (k + i + 3)) = 6 ∧
          c (2 ^ (k + i + 3) + 1) = 0) ∧
      (∀ n, c n ≤ 6) ∧
      (∀ n, c n ≤ n) ∧
      (∀ n, c n % 2 = Nat.totient n % 2) ∧
      (¬ ∃ p N : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → c (n + p) = c n) ∧
      ¬ Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAG
