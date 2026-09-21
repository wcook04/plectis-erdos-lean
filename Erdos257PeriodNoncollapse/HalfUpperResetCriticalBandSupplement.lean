import Erdos257PeriodNoncollapse.HalfCylinderMiddleCarryLowerBound
import Mathlib.Tactic
import Erdos257PeriodNoncollapse.HalfUpperResetCriticalBand

/-
The paper repository's copy of this module does not declare the results below; they were proved in
this corpus. A shim can only publish a name the library has, so this module keeps them, and keeps them
exactly as they were written: it is the corpus module with every declaration the library already carries
removed, and the shim imported in their place. No statement, hypothesis, proof or name is changed here.
-/

/-!
# The single critical dyadic band at an upper reset

The existing upper-reset route for Erdős #257 asks a reset charge `E` to avoid
one linear-width interval below every power

`2^(d-j+1)`, for `0 ≤ j ≤ d`.

Only one of those intervals can be critical: the smallest dyadic power still
at least `E`.  Larger powers have more room and smaller linear widths; smaller
powers are already strictly below `E`.  This file proves that reduction in
`dyadicBandEscape_iff_exists_critical`, then specializes it to the concrete
seam reset charge.  Thus the local `∀ j` in
`SeamUpperResetDyadicBandEscape` is exactly equivalent to one certified
nearest-boundary gap at each upper reset.

This is a quantifier reduction, not an assumption that the critical gap is
large.  The remaining arithmetic obligation is displayed without hiding it
behind the former family of bands.
-/

namespace Erdos257PeriodNoncollapse.HalfUpperResetCriticalBand

open Finset
open HalfCylinderIntegerGreedy

/-- A carry row lies strictly above the half-cylinder boundary.  This is a
pure adjacent-cut consequence: separation gives
`gap ≤ remainder + overshoot`, while the carry condition gives
`4 * overshoot ≤ gap`.  For the seam gap `2^(s+1)`, those two inequalities
force `2^s < remainder`.

This lower bound is deliberately stated at the source row.  Combined with
the exact upper/right cylinder below, it rules out a second upper reset after
an arbitrary intervening right run, rather than only at the immediate next
row. -/
theorem seamSuccessorCarries_remainder_gt_pow
    {s : ℕ} (hs : 5 ≤ s)
    (hcarry : (seamAdjacentCut s hs).successorCarries) :
    2 ^ s < seamIntegerGreedyRemainder s := by
  classical
  let F := seamPerturbedFamily s (by omega)
  let K := seamAdjacentCut s hs
  have hbelowAbove : F.oldSum K.below < F.oldSum K.above :=
    lt_of_le_of_lt K.below_admissible K.above_strict
  have hsep := F.separated hbelowAbove
  have hbelow := K.old_below_add_remainder
  have habove := K.capacity_add_overshoot
  change F.oldSum K.below + K.remainder = seamSubsetTarget s at hbelow
  change seamSubsetTarget s + K.overshoot = F.oldSum K.above at habove
  have hgapRO : F.gap ≤ K.remainder + K.overshoot := by
    omega
  have hfourO : 4 * K.overshoot ≤ F.gap := by
    change 4 * K.overshoot + K.abovePulse ≤ F.gap at hcarry
    omega
  change 2 ^ (s + 1) ≤
      (seamAdjacentCut s hs).remainder +
        (seamAdjacentCut s hs).overshoot at hgapRO
  change 4 * (seamAdjacentCut s hs).overshoot ≤ 2 ^ (s + 1) at hfourO
  rw [seamAdjacentCut_remainder hs] at hgapRO
  have hpow : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by
    rw [pow_succ]
    ring
  rw [hpow] at hgapRO hfourO
  have hpos : 0 < (2 : ℕ) ^ s := pow_pos (by norm_num) s
  omega

/-- An actual upper/right run cannot be longer than the critical dyadic
index of its reset charge. -/
theorem seamUpperThenRightRun_length_le_criticalIndex
    {d k j : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1))
    (hcritical :
      CriticalDyadicBandIndex d (seamUpperResetCharge d hd5) j) :
    k ≤ j := by
  let E := seamUpperResetCharge d hd5
  have hcylinder := seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
  change seamIntegerGreedyRemainder (d + k + 1) + 4 ^ k * E +
      affineRightRunCharge
        (fun q ↦
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k =
      2 ^ (d + k + 1) at hcylinder
  have hfactor :
      4 ^ k * 2 ^ (d - k + 1) = 2 ^ (d + k + 1) := by
    rw [show 4 ^ k = 2 ^ (2 * k) by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul], ← pow_add]
    congr 1
    omega
  have hweighted : 4 ^ k * E ≤ 2 ^ (d + k + 1) := by
    omega
  have hE : E ≤ 2 ^ (d - k + 1) := by
    rw [← hfactor] at hweighted
    exact Nat.le_of_mul_le_mul_left hweighted (pow_pos (by norm_num) k)
  by_contra hnot
  have hjk : j < k := Nat.lt_of_not_ge hnot
  rcases hcritical with ⟨hjd, _hEj, hjnext⟩
  rcases hjnext with rfl | hjnext
  · omega
  · have hexp : d - k + 1 ≤ d - (j + 1) + 1 := by omega
    have hpow : 2 ^ (d - k + 1) ≤ 2 ^ (d - (j + 1) + 1) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    omega

/-- Since the run length is always at most the critical index, equality is
equivalent to crossing the immediately lower dyadic boundary (with the
terminal index handled separately).  This is the exact remaining statement
behind the computed `critical_index = right_run_length` pattern. -/
theorem seamUpperThenRightRun_criticalIndex_eq_iff_lowerBoundary_lt
    {d k j : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1))
    (hcritical :
      CriticalDyadicBandIndex d (seamUpperResetCharge d hd5) j) :
    j = k ↔
      k = d ∨
        2 ^ (d - (k + 1) + 1) < seamUpperResetCharge d hd5 := by
  constructor
  · intro hjk
    subst j
    exact hcritical.2.2
  · intro hlower
    have hkj := seamUpperThenRightRun_length_le_criticalIndex
      hd5 hk hcarry hrun hcritical
    have hjk : j ≤ k := by
      rcases hlower with hkd | hlower
      · simpa [hkd] using hcritical.1
      · by_contra hnot
        have hkj' : k < j := Nat.lt_of_not_ge hnot
        have hexp : d - j + 1 ≤ d - (k + 1) + 1 := by omega
        have hpow : 2 ^ (d - j + 1) ≤ 2 ^ (d - (k + 1) + 1) :=
          Nat.pow_le_pow_right (by norm_num) hexp
        exact (not_lt_of_ge (hcritical.2.1.trans hpow)) hlower
    exact Nat.le_antisymm hjk hkj

/-- The crude `k ≤ d` cylinder bound is never attained.  At `k=d`, the
reset charge contributes at least `4^d * 4 = 2^(2d+2)`, already twice the
entire cylinder capacity `2^(2d+1)`.  Keeping the strict form removes the
terminal-index disjunct from the critical-band identity below. -/
theorem seamUpperThenRightRun_length_lt_resetRow
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) :
    k < d := by
  have hle := seamUpperThenRightRun_length_le_resetRow hd5 hcarry hrun
  have hcylinder := seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
  let E := seamUpperResetCharge d hd5
  change seamIntegerGreedyRemainder (d + k + 1) + 4 ^ k * E +
      affineRightRunCharge
        (fun q ↦
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k =
      2 ^ (d + k + 1) at hcylinder
  have hover : 1 ≤ (seamAdjacentCut d hd5).overshoot := by
    unfold PerturbedFamily.AdjacentCut.overshoot
    have habove := (seamAdjacentCut d hd5).above_strict
    omega
  have hE : 4 ≤ E := by
    dsimp [E, seamUpperResetCharge]
    omega
  by_contra hnot
  have hkd : k = d := by omega
  subst k
  have hpow : 2 ^ (d + d + 1) < 4 ^ d * 4 := by
    calc
      2 ^ (d + d + 1) < 2 ^ (2 * (d + 1)) :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ = 4 ^ d * 4 := by
        rw [show (4 : ℕ) ^ d = 2 ^ (2 * d) by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]]
        rw [show 2 * (d + 1) = 2 * d + 2 by omega, pow_add]
        norm_num
  have hweighted : 4 ^ d * 4 ≤ 4 ^ d * E :=
    Nat.mul_le_mul_left _ hE
  omega

/-- Upper resets alternate with middle resets across whole reset blocks.  More
precisely, after an upper reset and any finite run satisfying the exact right
recurrence, the terminal row cannot itself carry.  The exact cylinder puts
its remainder at or below `2^(d+k+1)`, whereas every carry row is strictly
above that boundary by `seamSuccessorCarries_remainder_gt_pow`. -/
theorem seamUpperThenRightRun_terminal_not_successorCarries
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) :
    ¬ (seamAdjacentCut (d + k + 1) (by omega)).successorCarries := by
  intro hterminal
  have hcylinder := seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
  have hle :
      seamIntegerGreedyRemainder (d + k + 1) ≤ 2 ^ (d + k + 1) := by
    omega
  have hgt := seamSuccessorCarries_remainder_gt_pow
    (s := d + k + 1) (by omega) hterminal
  omega

/-- Consequently, if the terminal row of an upper/right block is a reset at
all, it is the middle reset. -/
theorem seamUpperThenRightRun_terminal_isMiddle
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1))
    (hreset : SeamGreedyUpperOrMiddleAt (d + k + 1) (by omega)) :
    ¬ (seamAdjacentCut (d + k + 1) (by omega)).successorCarries ∧
      4 * (seamAdjacentCut (d + k + 1) (by omega)).remainder +
            (seamPerturbedFamily (d + k + 1) (by omega)).gap -
            (seamAdjacentCut (d + k + 1) (by omega)).belowPulse <
          (seamAdjacentCut (d + k + 1) (by omega)).terminalWeight := by
  have hncarry := seamUpperThenRightRun_terminal_not_successorCarries
    hd5 hcarry hrun
  rcases hreset with hterminalCarry | hmiddle
  · exact (hncarry hterminalCarry).elim
  · exact hmiddle

/-- **Endpoint form of the critical-index identity.**  For an actual upper
reset followed by `k` right recurrences, the run reaches its unique critical
dyadic index exactly when the terminal remainder together with the complete
right-run pulse packet lies below the half-cylinder boundary.

Thus the computed `critical_index = right_run_length` law is not a diffuse
property of the whole orbit.  Its exact missing input is the single endpoint
inequality displayed on the right. -/
theorem seamUpperThenRightRun_criticalIndex_eq_iff_endpointPacket_lt_half
    {d k j : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1))
    (hcritical :
      CriticalDyadicBandIndex d (seamUpperResetCharge d hd5) j) :
    j = k ↔
      seamIntegerGreedyRemainder (d + k + 1) +
          affineRightRunCharge
            (fun q ↦
              (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k <
        2 ^ (d + k) := by
  let E := seamUpperResetCharge d hd5
  let C := affineRightRunCharge
    (fun q ↦ (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k
  have hklt := seamUpperThenRightRun_length_lt_resetRow hd5 hcarry hrun
  have hkle : k ≤ d := hklt.le
  have hlower : j = k ↔ 2 ^ (d - k) < E := by
    have hiff := seamUpperThenRightRun_criticalIndex_eq_iff_lowerBoundary_lt
      hd5 hkle hcarry hrun hcritical
    have hexp : d - (k + 1) + 1 = d - k := by omega
    simpa [E, hexp, Nat.ne_of_lt hklt] using hiff
  have hcylinder := seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
  change seamIntegerGreedyRemainder (d + k + 1) + 4 ^ k * E + C =
      2 ^ (d + k + 1) at hcylinder
  have hfactor : 4 ^ k * 2 ^ (d - k) = 2 ^ (d + k) := by
    rw [show 4 ^ k = 2 ^ (2 * k) by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul], ← pow_add]
    congr 1
    omega
  have hdouble : 2 ^ (d + k + 1) = 2 * 2 ^ (d + k) := by
    rw [pow_succ]
    ring
  rw [hlower]
  constructor
  · intro hE
    have hscaled : 2 ^ (d + k) < 4 ^ k * E := by
      rw [← hfactor]
      exact Nat.mul_lt_mul_of_pos_left hE (pow_pos (by norm_num) k)
    omega
  · intro hpacket
    by_contra hnot
    have hEle : E ≤ 2 ^ (d - k) := Nat.le_of_not_gt hnot
    have hscaled : 4 ^ k * E ≤ 2 ^ (d + k) := by
      rw [← hfactor]
      exact Nat.mul_le_mul_left _ hEle
    omega

/-- The signed earlier-row coordinate obtained by pulling the critical gap
at row `s` back through a largest false rank `d`. -/
def seamEarlierCriticalPullbackCoordinate (s d k : ℕ) : ℤ :=
  (seamIntegerGreedyRemainder (d + 1) : ℤ) -
      ((2 ^ (d + 1) : ℕ) : ℤ) - 4 +
    ((2 ^ ((2 * d + 1) - (s + k)) : ℕ) : ℤ) -
      ((2 ^ ((2 * d + 2) - s) : ℕ) : ℤ)

/-- The future right length does only one thing to the pulled-back
coordinate: it subtracts the initial segment of a dyadic staircase.  With
`a = 2*d+1-s`,

`Q_k = Q_0 - 2^a + 2^(a-k)`.

Thus every dangerous upper/right endpoint is an earlier middle coordinate
lying in a linear-width window immediately above one explicit dyadic
staircase. -/
theorem pullbackCoordinate_eq_base_sub_dyadicStaircase
    {s d k : ℕ} :
    seamEarlierCriticalPullbackCoordinate s d k =
      seamEarlierCriticalPullbackCoordinate s d 0 -
        (((2 ^ ((2 * d + 1) - s) : ℕ) : ℤ)) +
        (((2 ^ (((2 * d + 1) - s) - k) : ℕ) : ℤ)) := by
  have hexp :
      (2 * d + 1) - (s + k) = ((2 * d + 1) - s) - k := by
    omega
  unfold seamEarlierCriticalPullbackCoordinate
  simp only [Nat.add_zero]
  rw [hexp]
  ring

/-- Pure algebra behind the critical-gap pullback.  The two exponent
hypotheses are precisely what is needed to factor both dyadic boundaries by
`4^(s-d)` without truncated-exponent loss. -/
theorem backwardCriticalDistance_eq_fourPow_mul_pullback
    {s d k E C R : ℕ} (hds : d ≤ s) (hk : k ≤ s)
    (hfactor : s + k ≤ 2 * d + 1)
    (hbackward :
      4 ^ (s - d) * R + E =
        2 ^ (s + 2) + C +
          4 ^ (s - d) * (2 ^ (d + 1) + 4)) :
    (((2 ^ (s - k + 1) : ℕ) : ℤ) - (E : ℤ) + (C : ℤ)) =
      ((4 ^ (s - d) : ℕ) : ℤ) *
        ((R : ℤ) - ((2 ^ (d + 1) : ℕ) : ℤ) - 4 +
          ((2 ^ ((2 * d + 1) - (s + k)) : ℕ) : ℤ) -
            ((2 ^ ((2 * d + 2) - s) : ℕ) : ℤ)) := by
  have hfour : 4 ^ (s - d) = 2 ^ (2 * (s - d)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hsd : s - d + d = s := Nat.sub_add_cancel hds
  have hsk : s - k + k = s := Nat.sub_add_cancel hk
  have hcriticalExp :
      (2 * d + 1) - (s + k) + (s + k) = 2 * d + 1 :=
    Nat.sub_add_cancel hfactor
  have htopLe : s ≤ 2 * d + 2 := by omega
  have htopExp : (2 * d + 2) - s + s = 2 * d + 2 :=
    Nat.sub_add_cancel htopLe
  have hcriticalScale :
      4 ^ (s - d) * 2 ^ ((2 * d + 1) - (s + k)) =
        2 ^ (s - k + 1) := by
    rw [hfour, ← pow_add]
    congr 1
    omega
  have htopScale :
      4 ^ (s - d) * 2 ^ ((2 * d + 2) - s) = 2 ^ (s + 2) := by
    rw [hfour, ← pow_add]
    congr 1
    omega
  have hbackwardZ :
      (((4 ^ (s - d) : ℕ) : ℤ) * (R : ℤ)) + (E : ℤ) =
        ((2 ^ (s + 2) : ℕ) : ℤ) + (C : ℤ) +
          ((4 ^ (s - d) : ℕ) : ℤ) *
            (((2 ^ (d + 1) : ℕ) : ℤ) + 4) := by
    exact_mod_cast hbackward
  have hcriticalScaleZ :
      (((4 ^ (s - d) : ℕ) : ℤ) *
          ((2 ^ ((2 * d + 1) - (s + k)) : ℕ) : ℤ)) =
        ((2 ^ (s - k + 1) : ℕ) : ℤ) := by
    exact_mod_cast hcriticalScale
  have htopScaleZ :
      (((4 ^ (s - d) : ℕ) : ℤ) *
          ((2 ^ ((2 * d + 2) - s) : ℕ) : ℤ)) =
        ((2 ^ (s + 2) : ℕ) : ℤ) := by
    exact_mod_cast htopScale
  ring_nf at hbackwardZ hcriticalScaleZ htopScaleZ ⊢
  omega

/-- At a late largest-false row, the exact fixed-support packet therefore
pulls every admissible critical distance back to the earlier seam
coordinate.  This is the recursive descent identity selected by the exact
upper/right experiment. -/
theorem exists_backwardCriticalDistance_pullback_of_lateLargestFalse
    {s d k : ℕ} (hs5 : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) (hk : k ≤ s)
    (hfactor : s + k ≤ 2 * d + 1) :
    ∃ u : Finset ℕ,
      (∀ e ∈ u, 2 ≤ e ∧ e < d) ∧
        seamWordSupport (seamGreedyWord (d + 1)) = u ∧
          seamWordSupport (seamGreedyWord s) =
            u ∪ Finset.Ico (d + 1) s ∧
          (((2 ^ (s - k + 1) : ℕ) : ℤ) -
              (seamUpperResetCharge s hs5 : ℤ) +
            (fixedSupportPulseCharge
              (d + 1) (insert d u) (s - d) : ℤ)) =
            ((4 ^ (s - d) : ℕ) : ℤ) *
              seamEarlierCriticalPullbackCoordinate s d k := by
  obtain ⟨u, hu, hbase, hsupp, hbackward⟩ :=
    exists_fixedSupportPulseCharge_backward_identity_of_lateLargestFalse
      hs5 hd hlate
  refine ⟨u, hu, hbase, hsupp, ?_⟩
  unfold seamEarlierCriticalPullbackCoordinate
  exact backwardCriticalDistance_eq_fourPow_mul_pullback
    hd.2.1.le hk hfactor hbackward

/-- **Backward middle-barrier theorem.**  A late upper reset cannot have
arrived from a small earlier successor remainder.  Pulling back the top
critical boundary (`k=0`) makes the two residual dyadic powers consecutive,
and positivity of the current upper cylinder gives the explicit bound

`2^(d+1) + 4 + 2^((2d+1)-s) ≤ R_(d+1)`.

This is the first genuinely recursive lower bound on the upper-reset socket:
the current reset forces an exponential surplus at its preceding false
rank. -/
theorem lateUpperReset_previousRemainder_ge_dyadicBarrier
    {s d : ℕ} (hs5 : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hcarry : (seamAdjacentCut s hs5).successorCarries) :
    2 ^ (d + 1) + 4 + 2 ^ ((2 * d + 1) - s) ≤
      seamIntegerGreedyRemainder (d + 1) := by
  have hfactor : s + 0 ≤ 2 * d + 1 := by omega
  obtain ⟨u, _hu, _hbase, _hsupp, hpull⟩ :=
    exists_backwardCriticalDistance_pullback_of_lateLargestFalse
      hs5 hd hlate (k := 0) (by omega) hfactor
  simp only [Nat.sub_zero] at hpull
  have hcharge : seamUpperResetCharge s hs5 ≤ 2 ^ (s + 1) :=
    seamUpperResetCharge_le hs5 hcarry
  have hleftNonneg :
      0 ≤ (((2 ^ (s + 1) : ℕ) : ℤ) -
          (seamUpperResetCharge s hs5 : ℤ) +
        (fixedSupportPulseCharge
          (d + 1) (insert d u) (s - d) : ℤ)) := by
    have hchargeZ :
        (seamUpperResetCharge s hs5 : ℤ) ≤
          ((2 ^ (s + 1) : ℕ) : ℤ) := by
      exact_mod_cast hcharge
    exact add_nonneg (sub_nonneg.mpr hchargeZ) (by positivity)
  have hpowPos : 0 < ((4 ^ (s - d) : ℕ) : ℤ) := by positivity
  have hcoordinateNonneg :
      0 ≤ seamEarlierCriticalPullbackCoordinate s d 0 := by
    by_contra hnot
    have hneg : seamEarlierCriticalPullbackCoordinate s d 0 < 0 :=
      lt_of_not_ge hnot
    have hprodNeg :
        ((4 ^ (s - d) : ℕ) : ℤ) *
            seamEarlierCriticalPullbackCoordinate s d 0 < 0 :=
      mul_neg_of_pos_of_neg hpowPos hneg
    omega
  have hsmallExpAdd :
      (2 * d + 1) - s + s = 2 * d + 1 :=
    Nat.sub_add_cancel (by omega)
  have hlargeExpAdd :
      (2 * d + 2) - s + s = 2 * d + 2 :=
    Nat.sub_add_cancel (by omega)
  have hlargeExp : (2 * d + 2) - s = (2 * d + 1) - s + 1 := by
    omega
  have hlargePow :
      2 ^ ((2 * d + 2) - s) =
        2 * 2 ^ ((2 * d + 1) - s) := by
    rw [hlargeExp, pow_succ]
    ring
  have hlargePowZ :
      (((2 ^ ((2 * d + 2) - s) : ℕ) : ℤ)) =
        2 * (((2 ^ ((2 * d + 1) - s) : ℕ) : ℤ)) := by
    exact_mod_cast hlargePow
  unfold seamEarlierCriticalPullbackCoordinate at hcoordinateNonneg
  simp only [Nat.add_zero] at hcoordinateNonneg
  rw [hlargePowZ] at hcoordinateNonneg
  have hbarrierZ :
      (((2 ^ (d + 1) : ℕ) : ℤ) + 4 +
          ((2 ^ ((2 * d + 1) - s) : ℕ) : ℤ)) ≤
        (seamIntegerGreedyRemainder (d + 1) : ℤ) := by
    omega
  exact_mod_cast hbarrierZ

/-- Consequently, every late upper reset is preceded (at its largest false
rank) by a **middle** producer, never by another upper producer.  This turns
the formerly isolated upper-reset band into a recursive middle-to-upper
block. -/
theorem lateUpperReset_previousProducer_isMiddle
    {s d : ℕ} (hs13 : 13 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hcarry : (seamAdjacentCut s (by omega)).successorCarries) :
    ¬ (seamAdjacentCut d (by omega)).successorCarries ∧
      4 * (seamAdjacentCut d (by omega)).remainder +
            (seamPerturbedFamily d (by omega)).gap -
            (seamAdjacentCut d (by omega)).belowPulse <
        (seamAdjacentCut d (by omega)).terminalWeight := by
  obtain ⟨u, hu, hbase, _hsupp⟩ :=
    exists_lowerPrefix_with_backward_support_of_lateLargestFalse
      (s := s) (d := d) (by omega) hd hlate
  have hdnot : d ∉ seamWordSupport (seamGreedyWord (d + 1)) := by
    rw [hbase]
    intro hdu
    exact (Nat.lt_irrefl d) (hu d hdu).2
  have hfalse :
      SeamRowWord.terminal (by omega) (seamGreedyWord (d + 1)) = false :=
    (not_mem_seamWordSupport_iff_false
      (seamGreedyWord (d + 1)) (by omega) (by omega)).mp hdnot
  have hUM :=
    (seamGreedy_terminal_false_iff_upperOrMiddle d (by omega)).mp hfalse
  rcases hUM with hupper | hmiddle
  · have hbarrier := lateUpperReset_previousRemainder_ge_dyadicBarrier
      (s := s) (d := d) (by omega) hd hlate hcarry
    have hupperBound :=
      seamUpperBranch_nextRemainder_le_pow (s := d) (by omega) hupper
    have hstrict : 2 ^ (d + 1) <
        seamIntegerGreedyRemainder (d + 1) := by
      have hplus :
          2 ^ (d + 1) < 2 ^ (d + 1) +
            (4 + 2 ^ ((2 * d + 1) - s)) :=
        Nat.lt_add_of_pos_right (by positivity)
      exact lt_of_lt_of_le (by simpa [Nat.add_assoc] using hplus) hbarrier
    exact False.elim ((not_lt_of_ge hupperBound) hstrict)
  · exact hmiddle

/-- From exponent six onward, the dyadic scale dominates eight times its
index.  This elementary estimate is tuned to the late-reset substitution
`a = 2*d+1-s`, where the late inequality gives `d ≤ 2*a`. -/
theorem eight_mul_le_two_pow_of_six_le
    {a : ℕ} (ha6 : 6 ≤ a) :
    8 * a ≤ 2 ^ a := by
  induction a, ha6 using Nat.le_induction with
  | base => norm_num
  | succ a ha6 ih =>
      rw [pow_succ]
      have h8 : 8 ≤ 2 ^ a := by
        calc
          8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ a :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-- **Late upper resets have row-large middle ancestors.**  Write
`a = 2*d+1-s` for the exponent exposed by the backward pullback.  Lateness
and `s ≥ 13` force `a ≥ 6` and `d ≤ 2*a`, so `4*d ≤ 2^a`.  The backward
barrier and exact middle recurrence force `2^a+4 ≤ 4*R_d`; consequently
`R_d < d` is impossible.

This discharges the row-scale hypothesis of the middle-to-right exponential
barrier for every middle producer that is the ancestor of a late upper
reset. -/
theorem lateUpperReset_previousMiddleRemainder_ge_row
    {s d : ℕ} (hs13 : 13 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hcarry : (seamAdjacentCut s (by omega)).successorCarries) :
    d ≤ seamIntegerGreedyRemainder d := by
  have hmiddle := lateUpperReset_previousProducer_isMiddle
    (s := s) (d := d) hs13 hd hlate hcarry
  have hbarrier := lateUpperReset_previousRemainder_ge_dyadicBarrier
    (s := s) (d := d) (by omega) hd hlate hcarry
  have hadd := seamMiddleBranch_nextRemainder_add_belowPulse_eq
    (s := d) (by omega) hmiddle.1 hmiddle.2
  let a : ℕ := (2 * d + 1) - s
  have hsd : s ≤ 2 * d + 1 := by omega
  have haAdd : a + s = 2 * d + 1 := by
    simpa [a] using Nat.sub_add_cancel hsd
  have ha6 : 6 ≤ a := by omega
  have hda : d ≤ 2 * a := by omega
  have hpow : 8 * a ≤ 2 ^ a :=
    eight_mul_le_two_pow_of_six_le ha6
  have hfourD : 4 * d ≤ 2 ^ a := by omega
  change 2 ^ (d + 1) + 4 + 2 ^ a ≤
    seamIntegerGreedyRemainder (d + 1) at hbarrier
  have hsourceScale : 2 ^ a + 4 ≤
      4 * seamIntegerGreedyRemainder d := by
    omega
  by_contra hnot
  have hsmall : seamIntegerGreedyRemainder d < d :=
    Nat.lt_of_not_ge hnot
  omega

/-- Every filled terminal rank in a finite full suffix is an actual right
branch at its own row.  The proof rebases the existing backwards support
peeling theorem at `t+1`, rather than assuming that a support seen at the
final row was chosen independently of the greedy recursion. -/
theorem seamRightBranch_of_fullSuffix
    {B s t : ℕ} {u : Finset ℕ} (hB5 : 5 ≤ B)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < B)
    (hsupp : seamWordSupport (seamGreedyWord s) =
      u ∪ Finset.Ico B s)
    (hBt : B ≤ t) (hts : t < s) :
    ¬ (seamAdjacentCut t (by omega)).successorCarries ∧
      (seamAdjacentCut t (by omega)).terminalWeight ≤
        4 * (seamAdjacentCut t (by omega)).remainder +
          (seamPerturbedFamily t (by omega)).gap -
          (seamAdjacentCut t (by omega)).belowPulse := by
  classical
  have ht1s : t + 1 ≤ s := by omega
  have hrow : t + 1 + (s - (t + 1)) = s :=
    Nat.add_sub_of_le ht1s
  let v : Finset ℕ := u ∪ Finset.Ico B (t + 1)
  have hv : ∀ e ∈ v, 2 ≤ e ∧ e < t + 1 := by
    intro e he
    rcases Finset.mem_union.mp he with heu | heIco
    · exact ⟨(hu e heu).1, by have := (hu e heu).2; omega⟩
    · exact ⟨by have := (Finset.mem_Ico.mp heIco).1; omega,
        (Finset.mem_Ico.mp heIco).2⟩
  have hsuppRebased :
      seamWordSupport
          (seamGreedyWord (t + 1 + (s - (t + 1)))) =
        v ∪ Finset.Ico (t + 1) (t + 1 + (s - (t + 1))) := by
    calc
      seamWordSupport
          (seamGreedyWord (t + 1 + (s - (t + 1)))) =
          seamWordSupport (seamGreedyWord s) := by rw [hrow]
      _ = u ∪ Finset.Ico B s := hsupp
      _ = v ∪ Finset.Ico (t + 1) s := by
        dsimp [v]
        ext e
        by_cases heu : e ∈ u
        · simp [heu]
        · simp only [Finset.mem_union, Finset.mem_Ico, heu, false_or]
          omega
      _ = v ∪ Finset.Ico (t + 1)
          (t + 1 + (s - (t + 1))) := by rw [hrow]
  have hbase := seamGreedyWord_support_eq_base_of_full_suffix
    (B := t + 1) (k := s - (t + 1)) (by omega) hv hsuppRebased
  have htop : t ∈ seamWordSupport (seamGreedyWord (t + 1)) := by
    rw [hbase]
    exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_Ico.mpr ⟨hBt, by omega⟩))
  have hterminal :
      SeamRowWord.terminal (by omega) (seamGreedyWord (t + 1)) = true := by
    apply Bool.eq_true_of_not_eq_false
    intro hfalse
    have hnot : t ∉ seamWordSupport (seamGreedyWord (t + 1)) := by
      apply (not_mem_seamWordSupport_iff_false
        (seamGreedyWord (t + 1)) (by omega) (by omega)).2
      simpa [SeamRowWord.terminal] using hfalse
    exact hnot htop
  have hnotUM : ¬ SeamGreedyUpperOrMiddleAt t (by omega) := by
    intro hUM
    have hfalse :=
      (seamGreedy_terminal_false_iff_upperOrMiddle t (by omega)).2 hUM
    simpa [hfalse] using hterminal
  have hncarry : ¬ (seamAdjacentCut t (by omega)).successorCarries := by
    intro hcarry
    exact hnotUM (Or.inl hcarry)
  refine ⟨hncarry, Nat.le_of_not_gt ?_⟩
  intro hmiddle
  exact hnotUM (Or.inr ⟨hncarry, hmiddle⟩)

/-- **Recursive-block barrier.**  A late upper reset is not an isolated
producer.  Its largest false rank is a row-large middle producer, every row
between that producer and the reset is an actual right successor, and the
standard middle-to-right transport therefore gives

`2^s + s ≤ R_s`

at the upper-reset source itself.  This is an unconditional all-depth
consequence of the late largest-false geometry and the reset branch. -/
theorem lateUpperReset_sourceRemainder_ge_expBarrier
    {s d : ℕ} (hs13 : 13 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hcarry : (seamAdjacentCut s (by omega)).successorCarries) :
    2 ^ s + s ≤ seamIntegerGreedyRemainder s := by
  obtain ⟨u, hu, _hbase, hsupp⟩ :=
    exists_lowerPrefix_with_backward_support_of_lateLargestFalse
      (s := s) (d := d) (by omega) hd hlate
  have hmiddle := lateUpperReset_previousProducer_isMiddle
    (s := s) (d := d) hs13 hd hlate hcarry
  have hrow := lateUpperReset_previousMiddleRemainder_ge_row
    (s := s) (d := d) hs13 hd hlate hcarry
  have hrun : ∀ (t : ℕ) (hdt : d + 1 ≤ t), t < s →
      ¬ (seamAdjacentCut t (by omega)).successorCarries ∧
        (seamAdjacentCut t (by omega)).terminalWeight ≤
          4 * (seamAdjacentCut t (by omega)).remainder +
            (seamPerturbedFamily t (by omega)).gap -
            (seamAdjacentCut t (by omega)).belowPulse := by
    intro t hdt hts
    exact seamRightBranch_of_fullSuffix
      (B := d + 1) (s := s) (t := t) (u := u) (by omega)
      (by
        intro e he
        exact ⟨(hu e he).1, (hu e he).2.trans (Nat.lt_succ_self d)⟩)
      hsupp hdt hts
  have hrow' : d ≤ (seamAdjacentCut d (by omega)).remainder := by
    simpa [seamAdjacentCut_remainder] using hrow
  exact seamMiddleThenRightRun_expBarrier
    (d := d) (s := s) (by omega) (Nat.succ_le_iff.mpr hd.2.1) hrow'
      hmiddle.1 hmiddle.2 hrun

end Erdos257PeriodNoncollapse.HalfUpperResetCriticalBand
