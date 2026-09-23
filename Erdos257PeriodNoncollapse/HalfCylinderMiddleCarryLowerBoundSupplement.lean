import Erdos257PeriodNoncollapse.HalfCylinderLastProducerContradiction
import Erdos257PeriodNoncollapse.HalfCylinderFinalMiddleTailSocket
import Erdos257PeriodNoncollapse.HalfCylinderFiniteShadow
import Erdos257PeriodNoncollapse.HalfCylinderResetDeficitEscape
import Erdos257PeriodNoncollapse.HalfCylinderMiddleCarryLowerBound
import Erdos257PeriodNoncollapse.HalfCylinderBoundaryPulseSupplement
import Erdos257PeriodNoncollapse.HalfCylinderLastProducerContradictionSupplement

/-
The paper repository's copy of this module does not declare the results below; they were proved in
this corpus. A shim can only publish a name the library has, so this module keeps them, and keeps them
exactly as they were written: it is the corpus module with every declaration the library already carries
removed, and the shim imported in their place. No statement, hypothesis, proof or name is changed here.
-/

/-!
# A cardinality-scale bound for the last middle producer

The square-root envelope for an arbitrary divisor-incidence support is much
larger than necessary for a finite seam prefix.  If `F` is finite, every
future coefficient counts at most `F.card` divisors, and the normalized
binary geometric tail has total mass one.  Hence

`binaryCoeffTail (supportCoeff (↑F)) N ≤ F.card`.

For the concrete middle producer this gives an alternative reduction of the
remaining tail escape to the exact natural-number inequality

`card(below support) + belowPulse + 5 < 4 * remainder`.

Equivalently, the affine carry is larger than the cardinality of the
terminal-augmented support.  This is sharper than the generic square-root
strip only for sparse finite prefixes; it is not a uniform improvement when
the support cardinality grows linearly with the row.  It does handle the
exceptional middle row seven, where the square-root inequality is false.
The theorem below does not assert the remaining cardinality inequality; it
exposes its exact arithmetic content.
-/

namespace Erdos257PeriodNoncollapse

open Set Filter
open HalfCylinderIntegerGreedy
open HalfCylinderFiniteShadow
open scoped BigOperators

noncomputable section

/-! ## A sharp tail bound for finite supports -/

/-- Selected residual ranks contributing on the even new boundary. -/
def seamResidualEvenBoundary236 (s : ℕ) : Finset ℕ :=
  ((((seamWordSupport (seamGreedyWord s)).erase 2).erase 3).erase 6).filter
    (fun d => d ∣ 2 * s + 2)

/-- Selected residual ranks contributing on the odd new boundary. -/
def seamResidualOddBoundary236 (s : ℕ) : Finset ℕ :=
  ((((seamWordSupport (seamGreedyWord s)).erase 2).erase 3).erase 6).filter
    (fun d => d ∣ 2 * s + 1)

/-- The residual pulse is exactly the number of selected even-boundary
divisors plus twice the number of selected odd-boundary divisors. -/
theorem seamResidualPulse236_eq_evenCard_add_two_mul_oddCard (s : ℕ) :
    seamResidualPulse236 s =
      (seamResidualEvenBoundary236 s).card +
        2 * (seamResidualOddBoundary236 s).card := by
  simp only [seamResidualPulse236, seamResidualEvenBoundary236,
    seamResidualOddBoundary236, rowPulse, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  simp

/-- Charge `-2` fixes the seam pulse to the residue class two modulo four.
This is the source-row arithmetic that is not visible in the later
all-right phase sieve. -/
theorem wordPulse_mod_four_eq_two_of_producerCarry_eq_neg_two
    (s : ℕ) (hs : 5 ≤ s)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -2) :
    wordPulse s (seamGreedyWord s).toNatWord % 4 = 2 := by
  have hcarry := producerCarry_insert_seamWordSupport_eq
    hs (seamGreedyWord s)
  rw [hcell] at hcarry
  omega

/-- In the surviving `s ≡ 2 (mod 3)` phase, charge `-2` forces the pulse
outside the mandatory `2,3,6` ranks to be three modulo four. -/
theorem seamResidualPulse236_mod_four_eq_three_of_producerCarry_eq_neg_two
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -2) :
    seamResidualPulse236 s % 4 = 3 := by
  have hpulse := wordPulse_eq_three_add_seamResidualPulse236 s hs hmod
  have hpmod := wordPulse_mod_four_eq_two_of_producerCarry_eq_neg_two
    s (by omega) hcell
  omega

/-- Thus a `-2` cell in its only surviving mod-three phase requires at
least three units of additional source-row boundary pulse. -/
theorem three_le_seamResidualPulse236_of_producerCarry_eq_neg_two
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -2) :
    3 ≤ seamResidualPulse236 s := by
  have hres :=
    seamResidualPulse236_mod_four_eq_three_of_producerCarry_eq_neg_two
      s hs hmod hcell
  omega

/-- A `-2` cell forces genuinely coupled high-boundary incidence.  There
are either at least three selected residual divisors on the even boundary,
or exactly one there and at least one selected residual divisor on the odd
boundary.  Thus the single even divisor cannot be treated as an isolated
source-row event. -/
theorem residualBoundary_card_dichotomy_of_producerCarry_eq_neg_two
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -2) :
    3 ≤ (seamResidualEvenBoundary236 s).card ∨
      ((seamResidualEvenBoundary236 s).card = 1 ∧
        1 ≤ (seamResidualOddBoundary236 s).card) := by
  have hresmod :=
    seamResidualPulse236_mod_four_eq_three_of_producerCarry_eq_neg_two
      s hs hmod hcell
  rw [seamResidualPulse236_eq_evenCard_add_two_mul_oddCard] at hresmod
  have hevenOdd : (seamResidualEvenBoundary236 s).card % 2 = 1 := by
    omega
  by_cases hthree : 3 ≤ (seamResidualEvenBoundary236 s).card
  · exact Or.inl hthree
  · right
    constructor <;> omega

/-- The extra pulse forced by a `-2` cell is supported by an actual selected
rank `d ≥ 7` dividing one of the two new incidence boundaries.  Hence the
412 future-phase survivors must also satisfy a source-row divisor condition;
phase membership alone is not a reachable-cell certificate. -/
theorem exists_high_boundary_divisor_of_producerCarry_eq_neg_two
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -2) :
    ∃ d : ℕ,
      d ∈ seamWordSupport (seamGreedyWord s) ∧
        7 ≤ d ∧ d < s ∧ (d ∣ 2 * s + 1 ∨ d ∣ 2 * s + 2) := by
  classical
  let R := (((seamWordSupport (seamGreedyWord s)).erase 2).erase 3).erase 6
  have hres : 3 ≤ ∑ d ∈ R, rowPulse s d := by
    simpa [R, seamResidualPulse236] using
      three_le_seamResidualPulse236_of_producerCarry_eq_neg_two
        s hs hmod hcell
  have hexists : ∃ d ∈ R, 0 < rowPulse s d := by
    by_contra hnot
    have hzero : ∑ d ∈ R, rowPulse s d = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      exact Nat.eq_zero_of_not_pos fun hpos => hnot ⟨d, hd, hpos⟩
    omega
  obtain ⟨d, hdR, hdpulse⟩ := hexists
  have hdErase6 := Finset.mem_erase.mp hdR
  have hdErase3 := Finset.mem_erase.mp hdErase6.2
  have hdErase2 := Finset.mem_erase.mp hdErase3.2
  have hdmem : d ∈ seamWordSupport (seamGreedyWord s) := hdErase2.2
  have hdbounds := seamWordSupport_below hdmem
  have hskip := four_five_not_mem_seamGreedySupport s hs
  have hdne4 : d ≠ 4 := by
    intro hd4
    subst d
    exact hskip.1 hdmem
  have hdne5 : d ≠ 5 := by
    intro hd5
    subst d
    exact hskip.2 hdmem
  have hd7 : 7 ≤ d := by
    omega
  have hddiv : d ∣ 2 * s + 1 ∨ d ∣ 2 * s + 2 := by
    by_contra hnot
    rcases not_or.mp hnot with ⟨hodd, heven⟩
    simp [rowPulse, hodd, heven] at hdpulse
  exact ⟨d, hdmem, hd7, hdbounds.2, hddiv⟩

/-- In fact the additional selected divisor can be placed on the even new
boundary.  Odd-boundary incidences have pulse weight two, so without an
even-boundary incidence the residual pulse would be even, contradicting its
exact residue three modulo four. -/
theorem exists_high_even_boundary_divisor_of_producerCarry_eq_neg_two
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -2) :
    ∃ d : ℕ,
      d ∈ seamWordSupport (seamGreedyWord s) ∧
        7 ≤ d ∧ d < s ∧ d ∣ 2 * s + 2 := by
  classical
  let R := (((seamWordSupport (seamGreedyWord s)).erase 2).erase 3).erase 6
  have hresmod : (∑ d ∈ R, rowPulse s d) % 4 = 3 := by
    simpa [R, seamResidualPulse236] using
      seamResidualPulse236_mod_four_eq_three_of_producerCarry_eq_neg_two
        s hs hmod hcell
  by_contra hnone
  push_neg at hnone
  have hsumEven : ∃ q : ℕ, ∑ d ∈ R, rowPulse s d = 2 * q := by
    refine ⟨∑ d ∈ R, if d ∣ 2 * s + 1 then 1 else 0, ?_⟩
    calc
      ∑ d ∈ R, rowPulse s d =
          ∑ d ∈ R, 2 * (if d ∣ 2 * s + 1 then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdeven : ¬ d ∣ 2 * s + 2 := by
              intro hdiv
              have hdErase6 := Finset.mem_erase.mp hd
              have hdErase3 := Finset.mem_erase.mp hdErase6.2
              have hdErase2 := Finset.mem_erase.mp hdErase3.2
              have hdmem : d ∈ seamWordSupport (seamGreedyWord s) :=
                hdErase2.2
              have hdbounds := seamWordSupport_below hdmem
              have hskip := four_five_not_mem_seamGreedySupport s hs
              have hdne4 : d ≠ 4 := by
                intro hd4
                subst d
                exact hskip.1 hdmem
              have hdne5 : d ≠ 5 := by
                intro hd5
                subst d
                exact hskip.2 hdmem
              have hd7 : 7 ≤ d := by omega
              exact hnone d hdmem hd7 hdbounds.2 hdiv
            simp [rowPulse, hdeven]
      _ = 2 * ∑ d ∈ R, if d ∣ 2 * s + 1 then 1 else 0 := by
        rw [Finset.mul_sum]
  obtain ⟨q, hq⟩ := hsumEven
  omega

/-- The forced even-boundary divisor has quotient at least three.  Quotient
one is too small and quotient two would make the proper selected rank equal
to the missing terminal rank `s+1`. -/
theorem exists_high_even_boundary_divisor_scale_of_producerCarry_eq_neg_two
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -2) :
    ∃ d : ℕ,
      d ∈ seamWordSupport (seamGreedyWord s) ∧
        7 ≤ d ∧ d < s ∧ d ∣ 2 * s + 2 ∧ 3 * d ≤ 2 * s + 2 := by
  obtain ⟨d, hdmem, hd7, hdlt, hddiv⟩ :=
    exists_high_even_boundary_divisor_of_producerCarry_eq_neg_two
      s hs hmod hcell
  have hddiv' := hddiv
  obtain ⟨q, hq⟩ := hddiv'
  have hq3 : 3 ≤ q := by
    by_contra hnot
    have hqpos : 0 < q := by
      by_contra hqzero
      simp_all
    interval_cases q <;> omega
  refine ⟨d, hdmem, hd7, hdlt, hddiv, ?_⟩
  nlinarith

/-- A middle coordinate `c` is transported without loss to the next row:
the next seam remainder is exactly the new dyadic scale plus `c`.  This
turns the exceptional signed cells `-3,-2,-1` into the three concrete
lattice states `2^(s+1)+1`, `2^(s+1)+2`, `2^(s+1)+3`. -/
theorem seamMiddleBranch_nextRemainder_eq_pow_add_of_cell
    {s c : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight)
    (hcell :
      4 * (seamAdjacentCut s hs).remainder =
        (seamAdjacentCut s hs).belowPulse + c) :
    seamIntegerGreedyRemainder (s + 1) = 2 ^ (s + 1) + c := by
  have hadd :=
    seamMiddleBranch_nextRemainder_add_belowPulse_eq hs hncarry hmiddle
  rw [seamAdjacentCut_remainder hs] at hcell
  omega

/-- If the largest false rank stays strictly beyond the two-thirds boundary
for one more row, then even the exchanged boundary rank is pulse-invisible.
Consequently the actual upper and lower adjacent words have identical pulse.
This is the exact pulse cancellation seen at mature upper-to-middle
landings; it removes the incidence defect but does not by itself bound the
remaining signed pullback coordinate. -/
theorem seamAdjacentCut_abovePulse_eq_belowPulse_of_largestFalse_nextLate
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hnextLate : 2 * (s + 1) < 3 * d) :
    (seamAdjacentCut s hs).abovePulse =
      (seamAdjacentCut s hs).belowPulse := by
  have hpulse :=
    seamAdjacentCut_abovePulse_eq_belowPulse_add_rowPulse_of_largestFalse_late
      hs hd (by omega)
  have hboundary :=
    rowPulse_eq_zero_of_nextLate_boundary hd.1 hd.2.1 hnextLate
  rw [hboundary, add_zero] at hpulse
  exact hpulse

/-- Support-sensitive form of the same exact cylinder.  A failure of the
floor-error cardinality gap at the endpoint is equivalent to the weighted
upper-reset and pulse charge entering the top window whose width is exactly
`card + 2`.  No row-scale pulse estimate is used or discarded here. -/
theorem seamUpperThenRightRun_cardSmall_iff_resetCylinderWindow
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1)) :
    seamIntegerGreedyRemainder (d + k + 1) <
        (seamWordSupport (seamGreedyWord (d + k + 1))).card + 2 ↔
      4 ^ k *
            (4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse) +
          affineRightRunCharge
            (fun j ↦
              (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k ≤
        2 ^ (d + k + 1) ∧
      2 ^ (d + k + 1) <
        (seamWordSupport (seamGreedyWord (d + k + 1))).card + 2 +
          (4 ^ k *
              (4 * (seamAdjacentCut d hd5).overshoot +
                (seamAdjacentCut d hd5).abovePulse) +
            affineRightRunCharge
              (fun j ↦
                (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k) := by
  apply remainder_lt_iff_charge_in_topWindow
  simpa [Nat.add_assoc] using
    (seamUpperThenRightRun_exactCylinder hd5 hcarry hrun)

/-- Failure of the safe middle-coordinate range is therefore equivalent,
after one actual greedy step, to landing in one of three exact states just
above the dyadic boundary. -/
theorem seamMiddleBranch_nextRemainder_eq_pow_add_one_or_two_or_three
    {s : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight)
    (hunsafe :
      ¬ (4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 ≤ -4 ∨
          0 ≤ 4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4)) :
    seamIntegerGreedyRemainder (s + 1) = 2 ^ (s + 1) + 1 ∨
      seamIntegerGreedyRemainder (s + 1) = 2 ^ (s + 1) + 2 ∨
      seamIntegerGreedyRemainder (s + 1) = 2 ^ (s + 1) + 3 := by
  have hthree :=
    (seamMiddleCoordinate_not_safe_iff_three_cells hs).mp hunsafe
  have hadd :=
    seamMiddleBranch_nextRemainder_add_belowPulse_eq hs hncarry hmiddle
  rcases hthree with hcell | hcell | hcell
  · left
    rw [seamAdjacentCut_remainder hs] at hcell
    omega
  · right
    left
    rw [seamAdjacentCut_remainder hs] at hcell
    omega
  · right
    right
    rw [seamAdjacentCut_remainder hs] at hcell
    omega

/-- A middle cell has an equally rigid upper neighbour.  The terminal
largest-false gap on the successor row is `2^(s+2)+4`, so a landing
remainder `2^(s+1)+c` is paired with overshoot
`2^(s+1)+(4-c)`. -/
theorem seamMiddleBranch_nextOvershoot_eq_pow_add_of_cell
    {s c : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight)
    (hc : c ≤ 4)
    (hcell :
      4 * (seamAdjacentCut s hs).remainder =
        (seamAdjacentCut s hs).belowPulse + c) :
    (seamAdjacentCut (s + 1) (by omega)).overshoot =
      2 ^ (s + 1) + (4 - c) := by
  have hR :=
    seamMiddleBranch_nextRemainder_eq_pow_add_of_cell
      hs hncarry hmiddle hcell
  have hdNext :=
    seamGreedyWord_succ_isLargestFalseRank_terminal_of_middleBranch
      s hs hncarry hmiddle
  have hgap :=
    remainder_add_overshoot_eq_of_terminalLargestFalse
      (s := s + 1) (by omega) hdNext
  rw [seamAdjacentCut_remainder (by omega), hR] at hgap
  rw [show s + 1 + 1 = (s + 1) + 1 by omega, pow_succ] at hgap
  omega

/-- The three exceptional middle coordinates therefore land in exactly
three complementary adjacent pairs around the next dyadic boundary. -/
theorem seamMiddleBranch_next_pair_eq_one_three_or_two_two_or_three_one
    {s : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight)
    (hunsafe :
      ¬ (4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 ≤ -4 ∨
          0 ≤ 4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4)) :
    (seamIntegerGreedyRemainder (s + 1) = 2 ^ (s + 1) + 1 ∧
        (seamAdjacentCut (s + 1) (by omega)).overshoot =
          2 ^ (s + 1) + 3) ∨
      (seamIntegerGreedyRemainder (s + 1) = 2 ^ (s + 1) + 2 ∧
        (seamAdjacentCut (s + 1) (by omega)).overshoot =
          2 ^ (s + 1) + 2) ∨
      (seamIntegerGreedyRemainder (s + 1) = 2 ^ (s + 1) + 3 ∧
        (seamAdjacentCut (s + 1) (by omega)).overshoot =
          2 ^ (s + 1) + 1) := by
  have hthree :=
    (seamMiddleCoordinate_not_safe_iff_three_cells hs).mp hunsafe
  rcases hthree with hcell | hcell | hcell
  · left
    have hcellNat :
        4 * (seamAdjacentCut s hs).remainder =
          (seamAdjacentCut s hs).belowPulse + 1 := by
      omega
    exact
      ⟨seamMiddleBranch_nextRemainder_eq_pow_add_of_cell
          hs hncarry hmiddle hcellNat,
        by
          simpa using
            seamMiddleBranch_nextOvershoot_eq_pow_add_of_cell
              hs hncarry hmiddle (by omega) hcellNat⟩
  · right
    left
    have hcellNat :
        4 * (seamAdjacentCut s hs).remainder =
          (seamAdjacentCut s hs).belowPulse + 2 := by
      omega
    exact
      ⟨seamMiddleBranch_nextRemainder_eq_pow_add_of_cell
          hs hncarry hmiddle hcellNat,
        by
          simpa using
            seamMiddleBranch_nextOvershoot_eq_pow_add_of_cell
              hs hncarry hmiddle (by omega) hcellNat⟩
  · right
    right
    have hcellNat :
        4 * (seamAdjacentCut s hs).remainder =
          (seamAdjacentCut s hs).belowPulse + 3 := by
      omega
    exact
      ⟨seamMiddleBranch_nextRemainder_eq_pow_add_of_cell
          hs hncarry hmiddle hcellNat,
        by
          simpa using
            seamMiddleBranch_nextOvershoot_eq_pow_add_of_cell
              hs hncarry hmiddle (by omega) hcellNat⟩

/-- The first exceptional middle cell is transient rather than a genuine
obstruction.  Its successor pair is
`(2^(s+1)+1, 2^(s+1)+3)`.  The large upper distance rules out an upper
reset, the linear pulse bound forces the following branch to be right, and
the exact right recurrence then puts the row-`s+2` remainder back below its
dyadic boundary. -/
theorem seamMiddleBranch_cell_one_recovers_two_rows
    {s : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight)
    (hcell :
      4 * (seamAdjacentCut s hs).remainder =
        (seamAdjacentCut s hs).belowPulse + 1) :
    seamIntegerGreedyRemainder (s + 2) ≤ 2 ^ (s + 2) := by
  have hR :=
    seamMiddleBranch_nextRemainder_eq_pow_add_of_cell
      hs hncarry hmiddle hcell
  have hO :=
    seamMiddleBranch_nextOvershoot_eq_pow_add_of_cell
      hs hncarry hmiddle (by omega) hcell
  have hncarryNext :
      ¬ (seamAdjacentCut (s + 1) (by omega)).successorCarries := by
    intro hcarry
    change
      4 * (seamAdjacentCut (s + 1) (by omega)).overshoot +
          (seamAdjacentCut (s + 1) (by omega)).abovePulse ≤
        2 ^ (s + 2) at hcarry
    rw [hO] at hcarry
    have hpow : (2 : ℕ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
      rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
      ring
    rw [hpow] at hcarry
    omega
  have hpulse :=
    (seamPerturbedFamily (s + 1) (by omega)).pulse_le
      (seamAdjacentCut (s + 1) (by omega)).below
  change
    (seamAdjacentCut (s + 1) (by omega)).belowPulse ≤
      2 * (s + 1 - 2) at hpulse
  have hgrowth :=
    two_mul_add_four_lt_two_pow_succ (s := s + 1) (by omega)
  have hterminal :=
    seamAdjacentCut_terminalWeight_eq (s := s + 1) (by omega)
  have hrightNext :
      (seamAdjacentCut (s + 1) (by omega)).terminalWeight ≤
        4 * (seamAdjacentCut (s + 1) (by omega)).remainder +
          (seamPerturbedFamily (s + 1) (by omega)).gap -
          (seamAdjacentCut (s + 1) (by omega)).belowPulse := by
    have hremNext :=
      seamAdjacentCut_remainder (s := s + 1) (by omega)
    have hgapNext :=
      seamAdjacentCut_gap_eq (s := s + 1) (by omega)
    rw [hterminal, hremNext, hgapNext, hR]
    have hpow : (2 : ℕ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
      rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
      ring
    rw [hpow]
    omega
  have hstep :=
    seamRightBranch_remainder_add_charge_eq
      (s := s + 1) (by omega) hncarryNext hrightNext
  have hstep' :
      seamIntegerGreedyRemainder (s + 2) + 2 ^ (s + 2) +
          (seamAdjacentCut (s + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (s + 1) := by
    simpa [show s + 1 + 1 = s + 2 by omega] using hstep
  rw [hR] at hstep'
  have hpow : (2 : ℕ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
    ring
  rw [hpow] at hstep'
  omega

/-- Every exceptional middle cell is followed by a right branch, and the
next remainder satisfies one exact affine transition.  Thus the three-cell
obstruction is not an unstructured recurrence: after the landing
`R_(s+1) = 2^(s+1)+c`, with `1 ≤ c ≤ 3`, the following state is determined
by the single pulse at row `s+1`:

`R_(s+2) + pulse_(s+1) + 4 = 2^(s+2) + 4*c`.

For `c=1` this forces immediate recovery; for `c=2,3` any continued
lower-side failure requires respectively a pulse at most `3` or `7`. -/
theorem seamMiddleBranch_exceptionalCell_forcesRight_affine
    {s c : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight)
    (hcpos : 1 ≤ c) (hcle : c ≤ 3)
    (hcell :
      4 * (seamAdjacentCut s hs).remainder =
        (seamAdjacentCut s hs).belowPulse + c) :
    ¬ (seamAdjacentCut (s + 1) (by omega)).successorCarries ∧
      (seamAdjacentCut (s + 1) (by omega)).terminalWeight ≤
        4 * (seamAdjacentCut (s + 1) (by omega)).remainder +
          (seamPerturbedFamily (s + 1) (by omega)).gap -
          (seamAdjacentCut (s + 1) (by omega)).belowPulse ∧
      seamIntegerGreedyRemainder (s + 2) +
          (seamAdjacentCut (s + 1) (by omega)).belowPulse + 4 =
        2 ^ (s + 2) + 4 * c := by
  have hR :=
    seamMiddleBranch_nextRemainder_eq_pow_add_of_cell
      hs hncarry hmiddle hcell
  have hcle4 : c ≤ 4 := by omega
  have hO :=
    seamMiddleBranch_nextOvershoot_eq_pow_add_of_cell
      hs hncarry hmiddle hcle4 hcell
  have hncarryNext :
      ¬ (seamAdjacentCut (s + 1) (by omega)).successorCarries := by
    intro hcarry
    change
      4 * (seamAdjacentCut (s + 1) (by omega)).overshoot +
          (seamAdjacentCut (s + 1) (by omega)).abovePulse ≤
        2 ^ (s + 2) at hcarry
    rw [hO] at hcarry
    have hpow : (2 : ℕ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
      rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
      ring
    rw [hpow] at hcarry
    omega
  have hpulse :=
    (seamPerturbedFamily (s + 1) (by omega)).pulse_le
      (seamAdjacentCut (s + 1) (by omega)).below
  change
    (seamAdjacentCut (s + 1) (by omega)).belowPulse ≤
      2 * (s + 1 - 2) at hpulse
  have hgrowth :=
    two_mul_add_four_lt_two_pow_succ (s := s + 1) (by omega)
  have hterminal :=
    seamAdjacentCut_terminalWeight_eq (s := s + 1) (by omega)
  have hrightNext :
      (seamAdjacentCut (s + 1) (by omega)).terminalWeight ≤
        4 * (seamAdjacentCut (s + 1) (by omega)).remainder +
          (seamPerturbedFamily (s + 1) (by omega)).gap -
          (seamAdjacentCut (s + 1) (by omega)).belowPulse := by
    have hremNext :=
      seamAdjacentCut_remainder (s := s + 1) (by omega)
    have hgapNext :=
      seamAdjacentCut_gap_eq (s := s + 1) (by omega)
    rw [hterminal, hremNext, hgapNext, hR]
    have hpow : (2 : ℕ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
      rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
      ring
    rw [hpow]
    omega
  refine ⟨hncarryNext, hrightNext, ?_⟩
  have hstep :=
    seamRightBranch_remainder_add_charge_eq
      (s := s + 1) (by omega) hncarryNext hrightNext
  have hstep' :
      seamIntegerGreedyRemainder (s + 2) + 2 ^ (s + 2) +
          (seamAdjacentCut (s + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (s + 1) := by
    simpa [show s + 1 + 1 = s + 2 by omega] using hstep
  rw [hR] at hstep'
  have hpow : (2 : ℕ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
    ring
  rw [hpow] at hstep'
  omega

/-- Continued lower-side failure after the `c=2` exceptional landing is
possible only when the next pulse lies in the four-value window `0,…,3`. -/
theorem seamMiddleBranch_cell_two_recovers_or_nextPulse_le_three
    {s : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight)
    (hcell :
      4 * (seamAdjacentCut s hs).remainder =
        (seamAdjacentCut s hs).belowPulse + 2) :
    seamIntegerGreedyRemainder (s + 2) ≤ 2 ^ (s + 2) ∨
      (seamAdjacentCut (s + 1) (by omega)).belowPulse ≤ 3 := by
  have htransition :=
    (seamMiddleBranch_exceptionalCell_forcesRight_affine
      hs hncarry hmiddle (by norm_num) (by norm_num) hcell).2.2
  omega

/-- Continued lower-side failure after the `c=3` exceptional landing is
possible only when the next pulse lies in the eight-value window `0,…,7`. -/
theorem seamMiddleBranch_cell_three_recovers_or_nextPulse_le_seven
    {s : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight)
    (hcell :
      4 * (seamAdjacentCut s hs).remainder =
        (seamAdjacentCut s hs).belowPulse + 3) :
    seamIntegerGreedyRemainder (s + 2) ≤ 2 ^ (s + 2) ∨
      (seamAdjacentCut (s + 1) (by omega)).belowPulse ≤ 7 := by
  have htransition :=
    (seamMiddleBranch_exceptionalCell_forcesRight_affine
      hs hncarry hmiddle (by norm_num) (by norm_num) hcell).2.2
  omega

/-- A forbidden-band certificate at one upper reset excludes every row-small
endpoint reached from that reset by a right run. -/
theorem not_rowSmall_after_upperRightRun_of_band
    {d k : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1))
    (hband : ∀ j : ℕ, j ≤ d →
      2 ^ (d - j + 1) <
          4 * (seamAdjacentCut d hd5).overshoot +
            (seamAdjacentCut d hd5).abovePulse ∨
        4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
          2 ^ (d - j + 1)) :
    ¬ seamIntegerGreedyRemainder (d + k + 1) < d + k + 1 := by
  intro hsmall
  let E := 4 * (seamAdjacentCut d hd5).overshoot +
    (seamAdjacentCut d hd5).abovePulse
  have hlower := seamUpperThenRightRun_rowSmall_forces_resetCharge_lower
    hd5 hk hcarry hrun hsmall
  change 2 ^ (d - k + 1) < E + 2 * (d + k) at hlower
  rcases hband k hk with hhigh | hlow
  · change 2 ^ (d - k + 1) < E at hhigh
    have hcylinder :=
      seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
    change seamIntegerGreedyRemainder (d + k + 1) + 4 ^ k * E +
        affineRightRunCharge
          (fun j ↦
            (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k =
          2 ^ (d + k + 1) at hcylinder
    have hweighted : 4 ^ k * E ≤ 2 ^ (d + k + 1) := by omega
    have hfactor :
        4 ^ k * 2 ^ (d - k + 1) = 2 ^ (d + k + 1) := by
      rw [show 4 ^ k = 2 ^ (2 * k) by
        rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul], ← pow_add]
      congr 1
      omega
    rw [← hfactor] at hweighted
    have hle : E ≤ 2 ^ (d - k + 1) :=
      Nat.le_of_mul_le_mul_left hweighted (pow_pos (by norm_num) k)
    omega
  · change E + 2 * (d + k) ≤ 2 ^ (d - k + 1) at hlow
    omega

private theorem seamIntegerGreedyRemainder_thirteen_ge :
    13 ≤ seamIntegerGreedyRemainder 13 := by
  rw [seamIntegerGreedyRemainder_thirteen_eq]
  norm_num

/-- The row-thirteen transition is a concrete non-right producer.  This is
extracted from the already certified largest-false base at row fourteen. -/
private theorem thirteen_not_mem_seamGreedyWord_fourteen :
    13 ∉ seamWordSupport (seamGreedyWord (13 + 1)) := by
  apply (not_mem_seamWordSupport_iff_false
    (seamGreedyWord (13 + 1)) (by omega) (by omega)).2
  simpa [SeamRowWord.terminal] using seamGreedy_terminal_false_at_thirteen

/-- **A row-small state exposes its last upper ancestor and actual danger
band.**  Given any row-small state at or after row thirteen, take the first
such row `D` and the last false terminal `d < D`.  The last producer cannot
be middle, because the first-bad-row lower bound feeds the preserved
middle/right exponential barrier.  Hence it is an upper reset, every
intervening transition is an actual right recurrence, and row-smallness at
the endpoint puts the reset charge in the forbidden band indexed by that
actual run length.

The endpoint may occur before the originally supplied row `s`; this is the
deliberate first-bad-row localization.  The returned recurrence is exactly
the interface consumed by the upper/right cylinder and endpoint-packet
theorems. -/
theorem exists_lastUpperAncestorRightRun_danger_of_rowSmall
    {s : ℕ} (hs13 : 13 ≤ s)
    (hsmall : seamIntegerGreedyRemainder s < s) :
    ∃ (d : ℕ) (hd13 : 13 ≤ d) (k : ℕ),
      d < s ∧ k ≤ d ∧ d + k + 1 ≤ s ∧
        (seamAdjacentCut d (by omega)).successorCarries ∧
        (∀ j : ℕ, j < k →
          seamIntegerGreedyRemainder (d + j + 2) +
              2 ^ (d + j + 2) +
              (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
            4 * seamIntegerGreedyRemainder (d + j + 1)) ∧
        seamIntegerGreedyRemainder (d + k + 1) < d + k + 1 ∧
        2 ^ (d - k + 1) <
          4 * (seamAdjacentCut d (by omega)).overshoot +
            (seamAdjacentCut d (by omega)).abovePulse + 2 * (d + k) := by
  classical
  let bad : Finset ℕ :=
    (Finset.Icc 13 s).filter
      (fun n ↦ seamIntegerGreedyRemainder n < n)
  have hbadNonempty : bad.Nonempty := by
    refine ⟨s, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hs13, le_rfl⟩, hsmall⟩
  let D : ℕ := bad.min' hbadNonempty
  have hDmem : D ∈ bad := Finset.min'_mem bad hbadNonempty
  have hDdata := Finset.mem_filter.mp hDmem
  have hDbounds := Finset.mem_Icc.mp hDdata.1
  have hD13 : 13 ≤ D := hDbounds.1
  have hDs : D ≤ s := hDbounds.2
  have hDsmall : seamIntegerGreedyRemainder D < D := hDdata.2
  have hDgt13 : 13 < D := by
    by_contra hle
    have hD : D = 13 := by omega
    rw [hD] at hDsmall
    exact (Nat.not_lt_of_ge seamIntegerGreedyRemainder_thirteen_ge)
      hDsmall
  have hprior : ∀ n : ℕ, 13 ≤ n → n < D →
      n ≤ seamIntegerGreedyRemainder n := by
    intro n hn13 hnD
    by_contra hn
    have hnsmall : seamIntegerGreedyRemainder n < n :=
      Nat.lt_of_not_ge hn
    have hnmem : n ∈ bad := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hn13, by omega⟩, hnsmall⟩
    have hDle : D ≤ n := by
      dsimp [D]
      exact Finset.min'_le bad n hnmem
    omega

  let producers : Finset ℕ :=
    (Finset.Icc 13 (D - 1)).filter
      (fun t ↦ t ∉ seamWordSupport (seamGreedyWord (t + 1)))
  have hproducersNonempty : producers.Nonempty := by
    refine ⟨13, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩,
        thirteen_not_mem_seamGreedyWord_fourteen⟩
  let d : ℕ := producers.max' hproducersNonempty
  have hdmem : d ∈ producers := Finset.max'_mem producers hproducersNonempty
  have hddata := Finset.mem_filter.mp hdmem
  have hdbounds := Finset.mem_Icc.mp hddata.1
  have hd13 : 13 ≤ d := hdbounds.1
  have hdD : d < D := by omega
  have hdrow : d ≤ seamIntegerGreedyRemainder d :=
    hprior d hd13 hdD
  have hUMd : SeamGreedyUpperOrMiddleAt d (by omega) := by
    apply (seamGreedy_terminal_false_iff_upperOrMiddle d (by omega)).mp
    have hfalse :=
      (not_mem_seamWordSupport_iff_false
        (seamGreedyWord (d + 1)) (by omega) (by omega)).mp hddata.2
    simpa [SeamRowWord.terminal] using hfalse
  have hnotUMAfter : ∀ (t : ℕ) (ht5 : 5 ≤ t), d < t → t < D →
      ¬ SeamGreedyUpperOrMiddleAt t ht5 := by
    intro t ht5 hdt htD hUMt
    have hfalse :=
      (seamGreedy_terminal_false_iff_upperOrMiddle t (by omega)).mpr hUMt
    have htnot : t ∉ seamWordSupport (seamGreedyWord (t + 1)) := by
      apply (not_mem_seamWordSupport_iff_false
        (seamGreedyWord (t + 1)) (by omega) (by omega)).mpr
      simpa [SeamRowWord.terminal] using hfalse
    have htmem : t ∈ producers := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, htnot⟩
    have htd : t ≤ d := by
      dsimp [d]
      exact Finset.le_max' producers t htmem
    omega
  have hrightBetween : ∀ (t : ℕ) (ht5 : 5 ≤ t), d + 1 ≤ t → t < D →
      ¬ (seamAdjacentCut t ht5).successorCarries ∧
        (seamAdjacentCut t ht5).terminalWeight ≤
          4 * (seamAdjacentCut t ht5).remainder +
            (seamPerturbedFamily t (by omega)).gap -
            (seamAdjacentCut t ht5).belowPulse := by
    intro t ht5 hdt htD
    have hnotUM := hnotUMAfter t ht5 (by omega) htD
    have hncarry : ¬ (seamAdjacentCut t ht5).successorCarries := by
      intro hcarry
      exact hnotUM (Or.inl hcarry)
    refine ⟨hncarry, Nat.le_of_not_gt ?_⟩
    intro hmiddle
    exact hnotUM (Or.inr ⟨hncarry, hmiddle⟩)

  rcases hUMd with hcarry | ⟨hncarry, hmiddle⟩
  · let k : ℕ := D - d - 1
    have hDdk : D = d + k + 1 := by
      dsimp [k]
      omega
    have hrun : ∀ j : ℕ, j < k →
        seamIntegerGreedyRemainder (d + j + 2) +
            2 ^ (d + j + 2) +
            (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
          4 * seamIntegerGreedyRemainder (d + j + 1) := by
      intro j hj
      have htD : d + j + 1 < D := by
        dsimp [k] at hj
        omega
      rcases hrightBetween (d + j + 1) (by omega) (by omega) htD with
        ⟨hncarry', hright'⟩
      exact seamRightBranch_remainder_add_charge_eq
        (by omega) hncarry' hright'
    have hk : k ≤ d :=
      seamUpperThenRightRun_length_le_resetRow
        (by omega) hcarry hrun
    have hdSmall :
        seamIntegerGreedyRemainder (d + k + 1) < d + k + 1 := by
      simpa [← hDdk] using hDsmall
    have hdanger := seamUpperThenRightRun_rowSmall_forces_resetCharge_lower
      (by omega) hk hcarry hrun hdSmall
    refine ⟨d, hd13, k, ?_, hk, ?_, hcarry, hrun, hdSmall, ?_⟩
    · omega
    · omega
    · simpa using hdanger
  · have hd5 : 5 ≤ d := by omega
    have hdDsucc : d + 1 ≤ D := by omega
    have hdrow' : d ≤ (seamAdjacentCut d hd5).remainder := by
      simpa [seamAdjacentCut_remainder] using hdrow
    have hrightBetween' : ∀ (t : ℕ) (hdt : d + 1 ≤ t), t < D →
        ¬ (seamAdjacentCut t (by omega)).successorCarries ∧
          (seamAdjacentCut t (by omega)).terminalWeight ≤
            4 * (seamAdjacentCut t (by omega)).remainder +
              (seamPerturbedFamily t (by omega)).gap -
              (seamAdjacentCut t (by omega)).belowPulse := by
      intro t hdt htD
      exact hrightBetween t (by omega) hdt htD
    have hbarrier := seamMiddleThenRightRun_expBarrier
      (d := d) (s := D) hd5 hdDsucc hdrow' hncarry hmiddle
      hrightBetween'
    have hDle : D ≤ 2 ^ D + D := Nat.le_add_left D (2 ^ D)
    exact False.elim ((Nat.not_lt_of_ge (hDle.trans hbarrier)) hDsmall)

/-- If every upper reset strictly before a row avoids the dyadic danger
bands, then that row's seam remainder is at least its index.  The locality is
exact: the first-bad-row/last-ancestor proof never queries a reset at or after
the target row. -/
theorem seamIntegerGreedyRemainder_ge_row_of_upperResetDyadicBandEscape_below
    {s : ℕ} (hs13 : 13 ≤ s)
    (hband : ∀ (d : ℕ) (hd5 : 5 ≤ d), 13 ≤ d → d < s →
      (seamAdjacentCut d hd5).successorCarries →
        ∀ j : ℕ, j ≤ d →
          2 ^ (d - j + 1) <
              4 * (seamAdjacentCut d hd5).overshoot +
                (seamAdjacentCut d hd5).abovePulse ∨
            4 * (seamAdjacentCut d hd5).overshoot +
                  (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
              2 ^ (d - j + 1)) :
    s ≤ seamIntegerGreedyRemainder s := by
  classical
  by_contra hnot
  have hsmall : seamIntegerGreedyRemainder s < s :=
    Nat.lt_of_not_ge hnot
  let bad : Finset ℕ :=
    (Finset.Icc 13 s).filter
      (fun n ↦ seamIntegerGreedyRemainder n < n)
  have hbadNonempty : bad.Nonempty := by
    refine ⟨s, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hs13, le_rfl⟩, hsmall⟩
  let D : ℕ := bad.min' hbadNonempty
  have hDmem : D ∈ bad := Finset.min'_mem bad hbadNonempty
  have hDdata := Finset.mem_filter.mp hDmem
  have hDbounds := Finset.mem_Icc.mp hDdata.1
  have hD13 : 13 ≤ D := hDbounds.1
  have hDsmall : seamIntegerGreedyRemainder D < D := hDdata.2
  have hDgt13 : 13 < D := by
    by_contra hle
    have hD : D = 13 := by omega
    rw [hD] at hDsmall
    exact (Nat.not_lt_of_ge seamIntegerGreedyRemainder_thirteen_ge)
      hDsmall
  have hprior : ∀ n : ℕ, 13 ≤ n → n < D →
      n ≤ seamIntegerGreedyRemainder n := by
    intro n hn13 hnD
    by_contra hn
    have hnsmall : seamIntegerGreedyRemainder n < n :=
      Nat.lt_of_not_ge hn
    have hnmem : n ∈ bad := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hn13, by omega⟩, hnsmall⟩
    have hDle : D ≤ n := by
      dsimp [D]
      exact Finset.min'_le bad n hnmem
    omega

  let producers : Finset ℕ :=
    (Finset.Icc 13 (D - 1)).filter
      (fun t ↦ t ∉ seamWordSupport (seamGreedyWord (t + 1)))
  have hproducersNonempty : producers.Nonempty := by
    refine ⟨13, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩,
        thirteen_not_mem_seamGreedyWord_fourteen⟩
  let d : ℕ := producers.max' hproducersNonempty
  have hdmem : d ∈ producers := Finset.max'_mem producers hproducersNonempty
  have hddata := Finset.mem_filter.mp hdmem
  have hdbounds := Finset.mem_Icc.mp hddata.1
  have hd13 : 13 ≤ d := hdbounds.1
  have hdD : d < D := by omega
  have hdrow : d ≤ seamIntegerGreedyRemainder d :=
    hprior d hd13 hdD
  have hUMd : SeamGreedyUpperOrMiddleAt d (by omega) := by
    apply (seamGreedy_terminal_false_iff_upperOrMiddle d (by omega)).mp
    have hfalse :=
      (not_mem_seamWordSupport_iff_false
        (seamGreedyWord (d + 1)) (by omega) (by omega)).mp hddata.2
    simpa [SeamRowWord.terminal] using hfalse
  have hnotUMAfter : ∀ (t : ℕ) (ht5 : 5 ≤ t), d < t → t < D →
      ¬ SeamGreedyUpperOrMiddleAt t ht5 := by
    intro t ht5 hdt htD hUMt
    have hfalse :=
      (seamGreedy_terminal_false_iff_upperOrMiddle t (by omega)).mpr hUMt
    have htnot : t ∉ seamWordSupport (seamGreedyWord (t + 1)) := by
      apply (not_mem_seamWordSupport_iff_false
        (seamGreedyWord (t + 1)) (by omega) (by omega)).mpr
      simpa [SeamRowWord.terminal] using hfalse
    have htmem : t ∈ producers := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, htnot⟩
    have htd : t ≤ d := by
      dsimp [d]
      exact Finset.le_max' producers t htmem
    omega
  have hrightBetween : ∀ (t : ℕ) (ht5 : 5 ≤ t), d + 1 ≤ t → t < D →
      ¬ (seamAdjacentCut t ht5).successorCarries ∧
        (seamAdjacentCut t ht5).terminalWeight ≤
          4 * (seamAdjacentCut t ht5).remainder +
            (seamPerturbedFamily t (by omega)).gap -
            (seamAdjacentCut t ht5).belowPulse := by
    intro t ht5 hdt htD
    have hnotUM := hnotUMAfter t ht5 (by omega) htD
    have hncarry : ¬ (seamAdjacentCut t ht5).successorCarries := by
      intro hcarry
      exact hnotUM (Or.inl hcarry)
    refine ⟨hncarry, Nat.le_of_not_gt ?_⟩
    intro hmiddle
    exact hnotUM (Or.inr ⟨hncarry, hmiddle⟩)

  rcases hUMd with hcarry | ⟨hncarry, hmiddle⟩
  · let k : ℕ := D - d - 1
    have hDdk : D = d + k + 1 := by
      dsimp [k]
      omega
    have hrun : ∀ j : ℕ, j < k →
        seamIntegerGreedyRemainder (d + j + 2) +
            2 ^ (d + j + 2) +
            (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
          4 * seamIntegerGreedyRemainder (d + j + 1) := by
      intro j hj
      have htD : d + j + 1 < D := by
        dsimp [k] at hj
        omega
      rcases hrightBetween (d + j + 1) (by omega) (by omega) htD with
        ⟨hncarry', hright'⟩
      exact seamRightBranch_remainder_add_charge_eq
        (by omega) hncarry' hright'
    have hk : k ≤ d :=
      seamUpperThenRightRun_length_le_resetRow
        (by omega) hcarry hrun
    have hnotSmall :=
      not_rowSmall_after_upperRightRun_of_band
        (by omega) hk hcarry hrun
          (hband d (by omega) hd13 (by omega) hcarry)
    apply hnotSmall
    simpa [hDdk] using hDsmall
  · have hd5 : 5 ≤ d := by omega
    have hdDsucc : d + 1 ≤ D := by omega
    have hdrow' : d ≤ (seamAdjacentCut d hd5).remainder := by
      simpa [seamAdjacentCut_remainder] using hdrow
    have hrightBetween' : ∀ (t : ℕ) (hdt : d + 1 ≤ t), t < D →
        ¬ (seamAdjacentCut t (by omega)).successorCarries ∧
          (seamAdjacentCut t (by omega)).terminalWeight ≤
            4 * (seamAdjacentCut t (by omega)).remainder +
              (seamPerturbedFamily t (by omega)).gap -
              (seamAdjacentCut t (by omega)).belowPulse := by
      intro t hdt htD
      exact hrightBetween t (by omega) hdt htD
    have hbarrier := seamMiddleThenRightRun_expBarrier
      (d := d) (s := D) hd5 hdDsucc hdrow' hncarry hmiddle
      hrightBetween'
    have hDle : D ≤ 2 ^ D + D := Nat.le_add_left D (2 ^ D)
    exact (Nat.not_lt_of_ge (hDle.trans hbarrier)) hDsmall

end

end Erdos257PeriodNoncollapse
