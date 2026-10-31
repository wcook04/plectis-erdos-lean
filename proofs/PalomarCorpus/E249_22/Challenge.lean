/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record sections 9.3.1 to 9.3.2: positivity and the remaining residue inequality; an exact endpoint identity

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open Finset
open scoped BigOperators

namespace PalomarCorpus.E249_22.Shared
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
/-- A one-sided actual-word gap which excludes the positive top-edge carry. Unlike total staircase annihilation, this condition merely asks the final `m`-bit residue to lie at or below the complement of the directed carry strip. By `windowDiscrepancy_emod_two_pow_eq_terminal`, it is a condition on the last `m` actual arithmetic letters alone. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.ActualLcmTopEdgeResidueGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ActualLcmTopEdgeResidueGap (a J K m : ℕ) : Prop :=
  m ≤ K ∧
    ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
      windowDiscrepancy (periodLcm (2 ^ a))
          (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
        (2 : ℤ) ^ m -
          ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)
/-- Cofinal supply target for the genuinely non-vacuous one-sided actual-word gap. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoActualLcmTopEdgeResidueGapSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoActualLcmTopEdgeResidueGapSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a K m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    K + (a + 6) < 2 * 2 ^ a ∧ ActualLcmTopEdgeResidueGap a 0 K m
end PalomarCorpus.E249_22.Shared

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_22.Shared (periodLcm totientTail)
/-- The integral correction for the primes shared by `j` and `x` in the totient of the product `j*x`. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.totientOverlapFactor, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientOverlapFactor (j x : ℕ) : ℕ :=
  (Nat.totient j / Nat.totient (Nat.gcd j x)) * Nat.gcd j x
/-- The quotient-scale letter attached to a divisor offset `j | H` on the actual diagonal. Its two overlap factors record exactly which saturated prime powers of `j` reappear in `H/j + 1` and `2*(H/j) + 1`. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.lcmDivisorRayLetter, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmDivisorRayLetter (H j : ℕ) : ℤ :=
  let a := H / j
  ((totientOverlapFactor j (2 * a + 1) *
      Nat.totient (2 * a + 1) : ℕ) : ℤ) -
    ((totientOverlapFactor j (a + 1) *
      Nat.totient (a + 1) : ℕ) : ℤ)
/-- The window step `a_n = φ(n+h) - φ(n)` driving the carry recurrence. Local copy of Erdos249257.TotientTailPeriodKiller.deltaTotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- Actual LCM-ray letter: divisor offsets use the exact quotient-scale formula, while nondivisor offsets retain the literal totient difference. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.lcmRayArithmeticLetter, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmRayArithmeticLetter (t j : ℕ) : ℤ :=
  if j ∣ periodLcm t then
    lcmDivisorRayLetter (periodLcm t) j
  else
    deltaTotient (periodLcm t) (periodLcm t + j)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.actualLcm_corridor_pos in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem actualLcm_corridor_pos {a : ℕ} (ha : 8 ≤ a) :
    (∀ J : ℕ, J + (a + 6) < 2 * 2 ^ a →
        0 < totientTail (2 * periodLcm (2 ^ a) + J)
              - totientTail (periodLcm (2 ^ a) + J)) ∧
      0 < totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.corridor_height_lt_letter in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem corridor_height_lt_letter {a j : ℕ} (ha : 8 ≤ a) (hj : 0 < j)
    (hjlt : j < 2 * 2 ^ a) :
    (periodLcm (2 ^ a) : ℤ) < 8 * (2 ^ a : ℤ) * lcmRayArithmeticLetter (2 ^ a) j := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.corridor_letter_pos in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem corridor_letter_pos {a j : ℕ} (ha : 8 ≤ a) (hj : 0 < j)
    (hjlt : j < 2 * 2 ^ a) :
    0 < lcmRayArithmeticLetter (2 ^ a) j := by
  sorry
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
export PalomarCorpus.E249_22.Shared (ActualLcmTopEdgeResidueGap PowerTwoActualLcmTopEdgeResidueGapSupply periodLcm totientTail windowDiscrepancy)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_topEdgeResidueGapSupply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_topEdgeResidueGapSupply
    (hsupply : PowerTwoActualLcmTopEdgeResidueGapSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_forces_nonintegral in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem topEdgeResidueGap_forces_nonintegral {a J K m : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a J K m) :
    totientTail (2 * periodLcm (2 ^ a) + J) - totientTail (periodLcm (2 ^ a) + J)
      ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_orbit_nonintegral in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem topEdgeResidueGap_orbit_nonintegral {a K m : ℕ} (ha : 8 ≤ a)
    (hshort : K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a 0 K m) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
      ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_unfolded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem topEdgeResidueGap_unfolded (a J K m : ℕ) :
    ActualLcmTopEdgeResidueGap a J K m ↔
      (m ≤ K ∧
        ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAU

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
open Finset
export PalomarCorpus.E249_22.Shared (ActualLcmTopEdgeResidueGap PowerTwoActualLcmTopEdgeResidueGapSupply periodLcm totientTail windowDiscrepancy)
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
/-- The LCM height used by the power-two endpoint at exponent `a`. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualLcmHeight (a : ℕ) : ℕ :=
  periodLcm (2 ^ a)
/-- The actual LCM-diagonal tail orbit at exponent `a`. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualLcmTailOrbit (a : ℕ) : ℝ :=
  totientTail (2 * actualLcmHeight a) - totientTail (actualLcmHeight a)
/-- Cofinal non-integrality of the actual power-two LCM-diagonal tail orbit. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoActualLcmOrbitNonintegralitySupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoActualLcmOrbitNonintegralitySupply : Prop :=
  ∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
    actualLcmTailOrbit a ∉ Set.range ((↑) : ℤ → ℝ)
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
/-- The exact cofinal arithmetic socket exposed by one-sided adjacent-gap geometry. At depth `m`, the adjacent suffix displacement avoids only the two individual upper-edge arcs. The buffer is stated for the larger candidate depth `m + 1`, so either branch produced below remains inside the actual-LCM sign corridor. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoAdjacentSuffixMidbandSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoAdjacentSuffixMidbandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    m + 1 + (a + 6) < 2 * 2 ^ a ∧
    ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
    ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
    diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
      (2 : ℤ) ^ m -
        ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ)
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
/-- **Item 1 of `prop:te-chain`, exactly as displayed.** The two-sided band on the adjacent-suffix residue at one candidate depth `m`, with the paper's upper endpoint `2^m - (2H + m + 2)`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.PaperAdjacentSuffixMidbandSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PaperAdjacentSuffixMidbandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    m + 1 + (a + 6) < 2 * 2 ^ a ∧
    ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
    ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
    diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
      (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_paperAdjacentSuffixMidbandSupply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_paperAdjacentSuffixMidbandSupply
    (hsupply : PaperAdjacentSuffixMidbandSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband
    (hsupply : PowerTwoAdjacentSuffixMidbandSupply) :
    PaperAdjacentSuffixMidbandSupply := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude
    (hsupply : PowerTwoFlexibleActualTopEdgeMagnitudeSupply) :
    PaperAdjacentSuffixMidbandSupply := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand
    (hsupply : PowerTwoOddGuardTopEdgeHalfWordBandSupply) :
    PaperAdjacentSuffixMidbandSupply := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_fifth_gives_nonintegrality in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperTeChain_fifth_gives_nonintegrality :
    PowerTwoFlexibleActualTerminalDominanceSupply →
      PowerTwoActualLcmOrbitNonintegralitySupply := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_first_four_imply_topEdgeSupply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperTeChain_first_four_imply_topEdgeSupply :
    (PaperAdjacentSuffixMidbandSupply → PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_five_sufficient_for_irrationality in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperTeChain_five_sufficient_for_irrationality :
    (PaperAdjacentSuffixMidbandSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTerminalDominanceSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_item_one_unfolded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperTeChain_item_one_unfolded :
    PaperAdjacentSuffixMidbandSupply ↔
      ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        m + 1 + (a + 6) < 2 * 2 ^ a ∧
        ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
          diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAX
