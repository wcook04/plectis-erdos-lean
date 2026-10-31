/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record section 6.3: consequences (part 2 of 3)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open Finset
open scoped BigOperators
open Filter
open Topology
open Module
open Set

namespace PalomarCorpus.E249_12.Shared
/-- Canonical centered representative, with the positive midpoint selected in the tie case. Local copy of Erdos249257.DiagonalFreshLossBridge.actualCenteredLift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualCenteredLift (A M : ℤ) : ℤ :=
  let r := A % M
  if r ≤ M / 2 then r else r - M
/-- The shifted totient difference `φ(n + h) - φ(n)`, taken in `ℤ` through the cast from `ℕ`. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- The integer carry orbit launched from candidate `d` at position `N`: `orbit 0 = d`, `orbit (i+1) = 2·orbit i - a_{N+i+1}`. If `D_h(N)` is the integer `d`, this orbit equals `D_h(N+i)` forever. Local copy of Erdos249257.TotientTailPeriodKiller.carryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)
/-- The universal period `lcm(1, 2, ..., t)`, given recursively by `periodLcm 0 = 1` and `periodLcm (t + 1) = lcm (periodLcm t) (t + 1)`. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
/-- The binary totient tail `R_N = ∑_{j ≥ 1} φ(N + j) / 2 ^ j`, a real number satisfying `2 ^ N S = Φ_N + R_N`, where `S = ∑_{n ≥ 1} φ(n) / 2 ^ n` and `Φ_N = ∑_{n ≤ N} φ(n) 2 ^ (N - n)` is an integer. It obeys `0 < R_N ≤ N + 1` for `N ≥ 1`. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- The signed binary discrepancy `D_{h,N,L} = ∑_{j < L} (φ(N + h + 1 + j) - φ(N + 1 + j)) 2 ^ (L - 1 - j)` between two length-`L` totient windows separated by the shift `h`, an integer satisfying `|2 ^ L (R_{N + h} - R_N) - D_{h,N,L}| ≤ N + h + L + 2`. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
end PalomarCorpus.E249_12.Shared

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_12.Shared (carryOrbit certifiedKill deltaTotient periodLcm totientTail windowDiscrepancy)
/-- The asymmetric central-arc certificate. Its low radius is only `N+L+2`, while its high wrap radius remains `N+h+L+2`. It is therefore strictly weaker, and potentially strictly more useful, than `certifiedKill` when `h>0`. Local copy of Erdos249257.directedCertifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def directedCertifiedKill (h N L : ℕ) : Prop :=
  (N + L + 2 : ℤ) ≤ windowDiscrepancy h N L % (2 : ℤ) ^ L ∧
    windowDiscrepancy h N L % (2 : ℤ) ^ L ≤
      (2 : ℤ) ^ L - (N + h + L + 2 : ℤ)
/-- States prop:CP-06 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.directed_certificate_example in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem directed_certificate_example :
    periodLcm 3 = 6 ∧
      windowDiscrepancy 6 6 6 = 270 ∧
      windowDiscrepancy 6 6 6 % (2 : ℤ) ^ 6 = 14 ∧
      directedCertifiedKill 6 6 6 ∧
      (∀ L : ℕ, L ≤ 6 → ¬ certifiedKill 6 6 L) ∧
      certifiedKill 6 6 7 := by
  sorry
/-- States prop:CP-06 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.directed_certificate_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem directed_certificate_iff (h N : ℕ) :
    (∃ L : ℕ,
        ((N : ℤ) + L + 2) ≤ windowDiscrepancy h N L % (2 : ℤ) ^ L ∧
          windowDiscrepancy h N L % (2 : ℤ) ^ L ≤
            (2 : ℤ) ^ L - ((N : ℤ) + h + L + 2)) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States prop:TE-06 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.integral_carry_strictly_between in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem integral_carry_strictly_between {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    {z : ℤ}
    (hz : (z : ℝ) = totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) :
    0 < carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) ∧
      carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) <
        ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℤ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
open Finset
export PalomarCorpus.E249_12.Shared (actualCenteredLift carryOrbit deltaTotient periodLcm totientTail windowDiscrepancy)
/-- The signed diagonal window increment `φ(2·H_t+s) − φ(H_t+s)` at offset `s`. Local copy of Erdos249257.DiagonalFreshLossBridge.diagonalWindowIncrement, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalWindowIncrement (t s : ℕ) : ℤ :=
  (Nat.totient (2 * periodLcm t + s) : ℤ) -
    (Nat.totient (periodLcm t + s) : ℤ)
/-- Unreduced integer block underlying the adjacent suffix displacement. It is the exact target-specific scalar evaluated by the canonical jump probe. Local copy of Erdos249257.DiagonalFreshLossBridge.diagonalAdjacentSuffixRawBlock, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalAdjacentSuffixRawBlock (t J m : ℕ) : ℤ :=
  (∑ r ∈ Finset.range m,
      diagonalWindowIncrement t (J + 1 + r) * 2 ^ (m - 1 - r)) +
    diagonalWindowIncrement t (J + m + 1)
/-- Actual centered half-state at power-two odd rank `q`. Local copy of Erdos249257.DiagonalFreshLossBridge.actualOddHalfCenteredLift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualOddHalfCenteredLift (a q : ℕ) : ℤ :=
  actualCenteredLift
    (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2)
    ((4 : ℤ) ^ q)
/-- States prop:TE-06 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.endpoint_criterion_nonintegral in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem endpoint_criterion_nonintegral {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    (hesc : 2 * actualOddHalfCenteredLift a q ≤
          diagonalWindowIncrement (2 ^ a) (2 * q + 2) -
            ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℤ) ∨
        diagonalWindowIncrement (2 ^ a) (2 * q + 2) ≤
          2 * actualOddHalfCenteredLift a q) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) ∉
      Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States prop:TE-06 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.endpoint_identity in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem endpoint_identity {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    {z : ℤ}
    (hz : (z : ℝ) = totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) :
    2 * actualOddHalfCenteredLift a q =
      diagonalWindowIncrement (2 ^ a) (2 * q + 2) -
        carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) := by
  sorry
/-- States prop:TE-06 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.oddHalfCenteredLift_spec in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem oddHalfCenteredLift_spec {a : ℕ} (q : ℕ) (ha : 2 ≤ a) :
    Even (windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
        diagonalWindowIncrement (2 ^ a) (2 * q + 2)) ∧
      Int.ModEq ((4 : ℤ) ^ q) (actualOddHalfCenteredLift a q)
        ((windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
          diagonalWindowIncrement (2 ^ a) (2 * q + 2)) / 2) ∧
      -((4 : ℤ) ^ q) < 2 * actualOddHalfCenteredLift a q ∧
      2 * actualOddHalfCenteredLift a q ≤ (4 : ℤ) ^ q := by
  sorry
end PalomarCorpus.E249.PaperStatementsAX

namespace PalomarCorpus.E249.PaperStatementsAY
open scoped BigOperators
export PalomarCorpus.E249_12.Shared (actualCenteredLift)
/-- States prop:TE-06 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.centeredLift_range in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem centeredLift_range {A M : ℤ} (hM : 0 < M) :
    -M < 2 * actualCenteredLift A M ∧ 2 * actualCenteredLift A M ≤ M := by
  sorry
end PalomarCorpus.E249.PaperStatementsAY

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
export PalomarCorpus.E249_12.Shared (carryOrbit certifiedKill deltaTotient periodLcm totientTail windowDiscrepancy)
/-- States prop:CP-07 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_modFour_pulse_supply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_modFour_pulse_supply
    (hsupply : ∀ h : ℕ, 0 < h → ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧
      ((Nat.totient (p + 4 * h) : ℤ) - (Nat.totient p : ℤ)) ≡ (2 : ℤ) [ZMOD 4] ∧
      ∃ K : ℕ, ∀ z : ℤ, |z| ≤ ((p + 4 * h + 1 : ℕ) : ℤ) → z ≡ (2 : ℤ) [ZMOD 4] →
        ∃ i : ℕ, i ≤ K ∧
          ((p + i + 4 * h + 2 : ℕ) : ℤ) ≤ |carryOrbit (4 * h) p z i|) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States prop:CP-07 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_pulse_class_integrality in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_forces_pulse_class_integrality
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ B : ℕ, ∀ p : ℕ, B < p →
      ((Nat.totient (p + 4 * h) : ℤ) - (Nat.totient p : ℤ)) ≡ (2 : ℤ) [ZMOD 4] →
      ∃ z : ℤ, (z : ℝ) = totientTail (p + 4 * h) - totientTail p ∧
        z ≡ (2 : ℤ) [ZMOD 4] := by
  sorry
/-- States prop:SK-02 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.short_window_diagonal_through_six in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem short_window_diagonal_through_six (a₀ : ℕ) (ha₀ : a₀ ≤ 6) :
    ∃ a L : ℕ, a₀ ≤ a ∧ L < 2 * 2 ^ a ∧
      certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L := by
  sorry
/-- States prop:SK-02 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.short_window_diagonal_witnesses in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem short_window_diagonal_witnesses :
    certifiedKill (periodLcm (2 ^ 4)) (periodLcm (2 ^ 4)) 23 ∧ (23 : ℕ) < 2 * 2 ^ 4 ∧
      certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93 ∧ (93 : ℕ) < 2 * 2 ^ 6 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAU

namespace PalomarCorpus.E249.PaperStatementsAJ
/-- The exact ordering socket for the fixed-rank curvature: the rank-two totient is strictly below both outer ranks or strictly above both of them. This is the local conclusion supplied by any factor-separated ordering of the three nonproportional linear forms. The unresolved arithmetic step for Erdős #249 is to force this socket on cofinally many prescribed LCM heights, not merely on a positive-density set of unrestricted heights. Local copy of Erdos249257.TotientFixedRankLcmAsymptotic.MiddleRankTotientExtremal, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def MiddleRankTotientExtremal (H j : ℕ) : Prop :=
  (Nat.totient (2 * H + j) < Nat.totient (H + j) ∧
      Nat.totient (2 * H + j) < Nat.totient (3 * H + j)) ∨
    (Nat.totient (H + j) < Nat.totient (2 * H + j) ∧
      Nat.totient (3 * H + j) < Nat.totient (2 * H + j))
/-- The wave-17 gap certificate at window `(N, K)` for the denominator `q`: the committed totient residue avoids the thin band of width `q(N+K+2)`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.GapCertificate, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def GapCertificate (N K q : ℕ) : Prop :=
  (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K))
      % 2 ^ K + q * (N + K + 2) < 2 ^ K
/-- `sup_K (b+d)(K) = ∞`: the proved Farey-gap denominator-exclusion bounds on the `N = 1` window family are arbitrarily large, that is, every finite denominator range `[1, Q]` is excluded by some single window `K`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.FareyGapExclusionUnbounded, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FareyGapExclusionUnbounded : Prop :=
  ∀ Q : ℕ, ∃ K : ℕ, ∀ q : ℕ, 0 < q → q ≤ Q → GapCertificate 1 K q
/-- States prop:FR-01 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_ne_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem extremal_order_curvature_ne_zero {H j : ℕ} (hH : 1 ≤ H)
    (hextremal : MiddleRankTotientExtremal H j) :
    (Nat.totient (3 * H + j) : ℤ) - 2 * Nat.totient (2 * H + j) + Nat.totient (H + j) ≠ 0 := by
  sorry
/-- States prop:FR-01 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_neg in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem extremal_order_curvature_neg {H j : ℕ} (hH : 1 ≤ H)
    (hleft : Nat.totient (H + j) < Nat.totient (2 * H + j))
    (hright : Nat.totient (3 * H + j) < Nat.totient (2 * H + j)) :
    (Nat.totient (3 * H + j) : ℤ) - 2 * Nat.totient (2 * H + j) + Nat.totient (H + j) < 0 := by
  sorry
/-- States prop:FR-01 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_pos in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem extremal_order_curvature_pos {H j : ℕ} (hH : 1 ≤ H)
    (hmin : Nat.totient (2 * H + j) < min (Nat.totient (H + j)) (Nat.totient (3 * H + j))) :
    0 < (Nat.totient (3 * H + j) : ℤ) - 2 * Nat.totient (2 * H + j) + Nat.totient (H + j) := by
  sorry
/-- States prop:C2sup from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.gapCertificate_window_1_240 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem gapCertificate_window_1_240 (q : ℕ) (hq : 0 < q)
    (hqQ : q ≤ 79639646646701375323355774875831053) :
    GapCertificate 1 240 q := by
  sorry
/-- States prop:C2sup from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.gapFareyBound_window_1_240 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem gapFareyBound_window_1_240 (q : ℕ) (hq : 0 < q)
    (hqQ : q ≤ 79639646646701375323355774875831053) :
    (q * 1299094806818720335611738031537456208600423915562142231419225521361164904)
        % 2 ^ 240 + q * 243 < 2 ^ 240 := by
  sorry
/-- States prop:C2sup from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_fareyGapExclusionUnbounded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totientSeries_of_fareyGapExclusionUnbounded
    (hsup : FareyGapExclusionUnbounded) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsC
open Filter
open Topology
open Finset
export PalomarCorpus.E249_12.Shared (certifiedKill periodLcm windowDiscrepancy)
/-- States prop:B7 from the long record for Erdős problem #249. Transported from Erdos249257.irrational_totient_series_of_lcm_cone_window_kill_supply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totient_series_of_lcm_cone_window_kill_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m L : ℕ, 0 < q ∧
      certifiedKill
        (m * periodLcm t)
        (q * periodLcm t) L) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) := by
  sorry
end PalomarCorpus.E249.PaperStatementsC

namespace PalomarCorpus.E249.PaperStatementsBH
open Module
open Filter
open Set
/-- The exact integer recurrence together with the subexponential boundary `u(N) = o(2^N)`, expressed as convergence of the quotient. Local copy of Erdos249257.IsTemperedBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)
/-- The full carry-section family through levels `1,...,e`. Local copy of Erdos249257.TotientCarryIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev TotientCarryIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ (j.val + 1))
/-- The binary coefficient series `X_c = ∑_{n≥1} c(n)/2^n`. Local copy of Erdos249257.binaryCoeffSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)
/-- A dyadic section of an integer carry orbit, viewed over `ℚ`. Local copy of Erdos249257.carryKernelSeq, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryKernelSeq (u : ℕ → ℤ) (j r : ℕ) : ℕ → ℚ := fun n =>
  u (2 ^ j * n + r)
/-- Every carry section through levels `1,...,e`, without quotienting or identifying residue channels. Local copy of Erdos249257.canonicalCarryKernelFamily, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalCarryKernelFamily (u : ℕ → ℤ) (e : ℕ) :
    TotientCarryIndex e → ℕ → ℚ
  | ⟨j, r⟩ => carryKernelSeq u (j.val + 1) r.val
/-- States prop:D5cons from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.no_generic_rationality_carryRank_ceiling in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_generic_rationality_carryRank_ceiling :
    ¬ ∃ g : ℕ → ℕ,
        (∃ e : ℕ, 1 ≤ e ∧ g e < 2 ^ e - 1)
          ∧ ∀ (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ),
              (∀ n : ℕ, c n ≤ n) →
              ¬ Irrational (binaryCoeffSeries c) →
              0 < v →
              IsTemperedBinaryOrbit c v u →
              ∀ e : ℕ,
                finrank ℚ
                    (Submodule.span ℚ
                      (Set.range (canonicalCarryKernelFamily u e)))
                  ≤ g e := by
  sorry
end PalomarCorpus.E249.PaperStatementsBH
