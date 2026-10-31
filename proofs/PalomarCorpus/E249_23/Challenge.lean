/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record sections 9.3.2 to 9.3.4: an exact endpoint identity; a bound on the last totient difference; separation of a rational approximation

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Finset

namespace PalomarCorpus.E249_23.Shared
/-- The universal period `lcm(1, 2, ..., t)`, given recursively by `periodLcm 0 = 1` and `periodLcm (t + 1) = lcm (periodLcm t) (t + 1)`. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
end PalomarCorpus.E249_23.Shared

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
open Finset
export PalomarCorpus.E249_23.Shared (periodLcm)
/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`: the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- A one-sided actual-word gap which excludes the positive top-edge carry. Unlike total staircase annihilation, this condition merely asks the final `m`-bit residue to lie at or below the complement of the directed carry strip. By `windowDiscrepancy_emod_two_pow_eq_terminal`, it is a condition on the last `m` actual arithmetic letters alone. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.ActualLcmTopEdgeResidueGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ActualLcmTopEdgeResidueGap (a J K m : ℕ) : Prop :=
  m ≤ K ∧
    ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
      windowDiscrepancy (periodLcm (2 ^ a))
          (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
        (2 : ℤ) ^ m -
          ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)
/-- The canonical adjacent-suffix depth: ten guard bits beyond the binary scale of the LCM height. At this depth the analytic width budget is automatic; the only remaining arithmetic input is centrality of the adjacent residue. Local copy of Erdos249257.DiagonalFreshLossBridge.canonicalAdjacentSuffixDepth, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalAdjacentSuffixDepth (t : ℕ) : ℕ :=
  Nat.log2 (periodLcm t) + 10
/-- Make the canonical adjacent-suffix depth odd by spending at most one additional guard bit. Local copy of Erdos249257.DiagonalFreshLossBridge.oddGuardedCanonicalAdjacentSuffixDepth, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def oddGuardedCanonicalAdjacentSuffixDepth (t : ℕ) : ℕ :=
  let m := canonicalAdjacentSuffixDepth t
  if Even m then m + 1 else m
/-- The signed diagonal window increment `φ(2·H_t+s) − φ(H_t+s)` at offset `s`. Local copy of Erdos249257.DiagonalFreshLossBridge.diagonalWindowIncrement, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalWindowIncrement (t s : ℕ) : ℤ :=
  (Nat.totient (2 * periodLcm t + s) : ℤ) -
    (Nat.totient (periodLcm t + s) : ℤ)
/-- Unreduced integer block underlying the adjacent suffix displacement. It is the exact target-specific scalar evaluated by the canonical jump probe. Local copy of Erdos249257.DiagonalFreshLossBridge.diagonalAdjacentSuffixRawBlock, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalAdjacentSuffixRawBlock (t J m : ℕ) : ℤ :=
  (∑ r ∈ Finset.range m,
      diagonalWindowIncrement t (J + 1 + r) * 2 ^ (m - 1 - r)) +
    diagonalWindowIncrement t (J + m + 1)
/-- Canonical centered representative, with the positive midpoint selected in the tie case. Local copy of Erdos249257.DiagonalFreshLossBridge.actualCenteredLift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualCenteredLift (A M : ℤ) : ℤ :=
  let r := A % M
  if r ≤ M / 2 then r else r - M
/-- Actual centered half-state at power-two odd rank `q`. Local copy of Erdos249257.DiagonalFreshLossBridge.actualOddHalfCenteredLift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualOddHalfCenteredLift (a q : ℕ) : ℤ :=
  actualCenteredLift
    (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2)
    ((4 : ℤ) ^ q)
/-- Cofinal actual-state form of the exact top-edge half-word producer. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoActualFinalTopEdgeMagnitudeSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoActualFinalTopEdgeMagnitudeSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
    ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
      |actualOddHalfCenteredLift a q|
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- Cofinal supply target for the genuinely non-vacuous one-sided actual-word gap. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoActualLcmTopEdgeResidueGapSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoActualLcmTopEdgeResidueGapSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a K m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    K + (a + 6) < 2 * 2 ^ a ∧ ActualLcmTopEdgeResidueGap a 0 K m
/-- The depth-`L` window numerator `P_L(M) = Σ_{j<L} φ(M+1+j)·2^{L-1-j}`: the integer layer of `2^L·R_M`, exact up to the one-sided deep tail `0 ≤ 2^L·R_M - P_L(M) ≤ M+L+2`. Local copy of Erdos249257.TotientTailPeriodKiller.windowNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowNumerator (M L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range L, Nat.totient (M + 1 + j) * 2 ^ (L - 1 - j)
/-- The depth-`m` binary residue of the diagonal window suffix that starts after the cut `J`: the last `m` bits of the depth-`(J + m)` diagonal window, computed from the translated windows alone. Local copy of Erdos249257.DiagonalFreshLossBridge.diagonalSuffixResidue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalSuffixResidue (t J m : ℕ) : ℤ :=
  ((windowNumerator (2 * periodLcm t + J) m : ℤ) -
    (windowNumerator (periodLcm t + J) m : ℤ)) % 2 ^ m
/-- The canonical modular displacement from the suffix at cut `J` to the suffix at cut `J + 1`. Local copy of Erdos249257.DiagonalFreshLossBridge.diagonalAdjacentSuffixResidue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalAdjacentSuffixResidue (t J m : ℕ) : ℤ :=
  (diagonalSuffixResidue t (J + 1) m -
    diagonalSuffixResidue t J m) % 2 ^ m
/-- Cofinal supply of odd ranks whose centered state escapes the exact open terminal/carry corridor forced by an integral actual-LCM orbit. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
    2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
    (2 * actualOddHalfCenteredLift a q ≤
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
          ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ) ∨
      diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
        2 * actualOddHalfCenteredLift a q)
/-- Cofinal one-sided producer exposed by the exact terminal/carry identity. Unlike the two-sided magnitude target, it only asks the centered state to dominate half of the final literal arithmetic letter. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoFlexibleActualTerminalDominanceSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoFlexibleActualTerminalDominanceSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
    2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
    diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
      2 * actualOddHalfCenteredLift a q
/-- Strictly weaker cofinal producer: the witness may use any odd rank whose exact top-edge threshold fits the half-cell and whose adjacent depth remains inside the actual-LCM sign corridor. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoFlexibleActualTopEdgeMagnitudeSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoFlexibleActualTopEdgeMagnitudeSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
    2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
    ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
      |actualOddHalfCenteredLift a q|
/-- The exact inherited contribution at a reduced offset across a power-of-two LCM jump. Even reduced offsets double; odd reduced offsets are copied unchanged. Local copy of Erdos249257.DiagonalFreshLossBridge.powerTwoInheritedIncrement, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def powerTwoInheritedIncrement (a r : ℕ) : ℤ :=
  if Even r then
    2 * diagonalWindowIncrement (2 ^ a - 1) r
  else
    diagonalWindowIncrement (2 ^ a - 1) r
/-- The odd post-jump offset not reconstructed by the even-offset seam. The name records its role in the cocycle, not an arithmetic independence claim. Local copy of Erdos249257.DiagonalFreshLossBridge.powerTwoFreshOddIncrement, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def powerTwoFreshOddIncrement (a q : ℕ) : ℤ :=
  diagonalWindowIncrement (2 ^ a) (2 * q + 1)
/-- The signed correction in one odd-depth/base-four power-of-two step. Local copy of Erdos249257.DiagonalFreshLossBridge.powerTwoOddDepthCorrection, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def powerTwoOddDepthCorrection (a n : ℕ) : ℤ :=
  powerTwoFreshOddIncrement a (n + 1) -
    2 * powerTwoInheritedIncrement a (n + 1) +
    powerTwoInheritedIncrement a (n + 2)
/-- The integral half-correction cocycle. Local copy of Erdos249257.DiagonalFreshLossBridge.powerTwoOddHalfCorrectionWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def powerTwoOddHalfCorrectionWord (a : ℕ) : ℕ → ℤ
  | 0 => 0
  | q + 1 =>
      4 * powerTwoOddHalfCorrectionWord a q +
        powerTwoOddDepthCorrection a q / 2
/-- Odd-depth half-word form of the one-sided top-edge producer. If `m = 2q+1`, the adjacent suffix residue is twice the half-word residue, and both directed edge widths divide by two to the same exact threshold `periodLcm (2^a) + q + 2`. This is substantially weaker than the older fixed `1/32` central band. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoOddGuardTopEdgeHalfWordBandSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoOddGuardTopEdgeHalfWordBandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
    ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
      powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ∧
    powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ≤
      (4 : ℤ) ^ q -
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ)
/-- The normalized unreduced raw block at odd rank `q`. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmRawApprox, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualLcmRawApprox (a q : ℕ) : ℝ :=
  (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) : ℝ) /
    (2 : ℝ) ^ (2 * q + 1)
/-- **Item 1 of `prop:te-chain`, exactly as displayed.** The two-sided band on the adjacent-suffix residue at one candidate depth `m`, with the paper's upper endpoint `2^m - (2H + m + 2)`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.PaperAdjacentSuffixMidbandSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PaperAdjacentSuffixMidbandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    m + 1 + (a + 6) < 2 * 2 ^ a ∧
    ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
    ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
    diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
      (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.abs_actualLcmTailOrbit_sub_rawApprox_lt_paper_form in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem abs_actualLcmTailOrbit_sub_rawApprox_lt_paper_form (a q : ℕ) :
    |(totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)))
        - actualLcmRawApprox a q|
      < (4 * (periodLcm (2 ^ a) : ℝ) + 2 * (2 * (q : ℝ) + 1) + 4) / 2 ^ (2 * q + 2) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.actualLcmRawApprox_isRat in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem actualLcmRawApprox_isRat (a q : ℕ) :
    ∃ v : ℚ, actualLcmRawApprox a q = (v : ℝ) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.corridor_escape_and_irrational_of_magnitude in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem corridor_escape_and_irrational_of_magnitude :
    (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_lower_escape_supply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_lower_escape_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
      2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
      2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
      2 * actualOddHalfCenteredLift a q ≤
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
          ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_terminalDominanceSupply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_terminalDominanceSupply
    (hsupply : PowerTwoFlexibleActualTerminalDominanceSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_relations in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperTeChain_relations :
    (PaperAdjacentSuffixMidbandSupply → PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        PaperAdjacentSuffixMidbandSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
        PowerTwoActualFinalTopEdgeMagnitudeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PaperAdjacentSuffixMidbandSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTopEdgeMagnitudeSupply) := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband
    (hsupply : PaperAdjacentSuffixMidbandSupply) :
    PowerTwoActualLcmTopEdgeResidueGapSupply := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_five_unfolded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem teChain_item_five_unfolded :
    PowerTwoFlexibleActualTerminalDominanceSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
        2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
          2 * actualOddHalfCenteredLift a q := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_four_unfolded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem teChain_item_four_unfolded :
    PowerTwoFlexibleActualTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
        2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q| := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_three_unfolded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem teChain_item_three_unfolded :
    PowerTwoActualFinalTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
        oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q| := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_two_unfolded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem teChain_item_two_unfolded :
    PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
        oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
          powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ∧
        powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ≤
          (4 : ℤ) ^ q - ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.terminalDominance_orbit_nonintegral in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem terminalDominance_orbit_nonintegral {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    (hdom : diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
      2 * actualOddHalfCenteredLift a q) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
      ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_or_of_paperAdjacentSuffixMidband in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem topEdgeResidueGap_or_of_paperAdjacentSuffixMidband
    {a m : ℕ}
    (hroom :
      ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m)
    (hlo :
      ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m)
    (hhi :
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
        (2 : ℤ) ^ m -
          ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)) :
    ActualLcmTopEdgeResidueGap a 0 m m ∨
      ActualLcmTopEdgeResidueGap a 0 (m + 1) m := by
  sorry
end PalomarCorpus.E249.PaperStatementsAX

namespace PalomarCorpus.E249.PaperStatementsAK
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.two_pow_odd_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_pow_odd_eq (q : ℕ) : (2 : ℝ) ^ (2 * q + 1) = 2 * (4 : ℝ) ^ q := by
  sorry
end PalomarCorpus.E249.PaperStatementsAK

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_23.Shared (periodLcm)
/-- The LCM height used by the power-two endpoint at exponent `a`. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualLcmHeight (a : ℕ) : ℕ :=
  periodLcm (2 ^ a)
/-- The elementary error radius for the odd-rank raw approximation. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmRawErrorRadius, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualLcmRawErrorRadius (a q : ℕ) : ℝ :=
  ((2 * actualLcmHeight a + 2 * q + 3 : ℕ) : ℝ) /
    (2 : ℝ) ^ (2 * q + 1)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.actualLcmRawErrorRadius_tendsto_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem actualLcmRawErrorRadius_tendsto_zero (a : ℕ) :
    Filter.Tendsto (fun q : ℕ => actualLcmRawErrorRadius a q) Filter.atTop (nhds 0) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAT
