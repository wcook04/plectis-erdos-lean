/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band o

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open Matrix

namespace PalomarCorpus.E257.PaperStructuresO
open Matrix
/-- A finite or infinite coefficient word together with a binary-normalized reverse carry. The intended equation is `bit m + 2 * carry m = coeff m + carry (m + 1)`. No Boolean hypothesis is built into the structure: the overlap theorem needs only the explicit seam and overlap bits that it consumes. Local copy of Erdos249257.HalfTrappingReturnCarry.ReverseCarryWord, restated so the compared statements elaborate against Mathlib alone. -/
structure ReverseCarryWord where
  coeff : ℕ → ℤ
  bit : ℕ → ℤ
  carry : ℕ → ℤ
  normalized : ∀ m : ℕ,
    bit m + 2 * carry m = coeff m + carry (m + 1)
/-- Carry difference between two reverse-carry words. Local copy of Erdos249257.HalfTrappingReturnCarry.carryDifference, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryDifference (left right : ReverseCarryWord) (m : ℕ) : ℤ :=
  left.carry m - right.carry m
/-- States record:257bm-i16 from the long record for Erdős problem #257. Transported from Erdos249257.HalfTrappingReturnCarry.overlappingMidpointReturns_twoPow_le_realBound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem overlappingMidpointReturns_twoPow_le_realBound
    (left right : ReverseCarryWord) (N M : ℕ) (bound : ℝ) (hN : 1 ≤ N)
    (hNM : M ≤ 2 * N - 2)
    (hcoeffSeam : left.coeff (M + 1) = right.coeff (M + 1))
    (hleftSeam : left.bit (M + 1) = 1)
    (hrightSeam : right.bit (M + 1) = 0)
    (hcoeffOverlap : ∀ j < 2 * N - M - 1,
      left.coeff (M + 2 + j) = right.coeff (M + 2 + j))
    (hbitOverlap : ∀ j < 2 * N - M - 1,
      left.bit (M + 2 + j) = right.bit (M + 2 + j))
    (hleftNonneg : 0 ≤ left.carry (2 * N + 1))
    (hrightNonneg : 0 ≤ right.carry (2 * N + 1))
    (hleftBound : (left.carry (2 * N + 1) : ℝ) ≤ bound)
    (hrightBound : (right.carry (2 * N + 1) : ℝ) ≤ bound) :
    (2 : ℝ) ^ (2 * N - M - 1) ≤ bound := by
  sorry
/-- States record:257bm-i16 from the long record for Erdős problem #257. Transported from Erdos249257.HalfTrappingReturnCarry.overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd
    (left right : ReverseCarryWord) (seam length : ℕ)
    (hcoeffSeam : left.coeff seam = right.coeff seam)
    (hleftSeam : left.bit seam = 1)
    (hrightSeam : right.bit seam = 0)
    (hcoeffOverlap : ∀ j < length,
      left.coeff (seam + 1 + j) = right.coeff (seam + 1 + j))
    (hbitOverlap : ∀ j < length,
      left.bit (seam + 1 + j) = right.bit (seam + 1 + j)) :
    ∃ z : ℤ, Odd z ∧
      carryDifference left right (seam + 1 + length) =
        (2 : ℤ) ^ length * z := by
  sorry
/-- States record:257bm-i16 from the long record for Erdős problem #257. Transported from Erdos249257.HalfTrappingReturnCarry.overlappingReverseCarryWords_twoPow_le_realBound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem overlappingReverseCarryWords_twoPow_le_realBound
    (left right : ReverseCarryWord) (seam length : ℕ) (bound : ℝ)
    (hcoeffSeam : left.coeff seam = right.coeff seam)
    (hleftSeam : left.bit seam = 1)
    (hrightSeam : right.bit seam = 0)
    (hcoeffOverlap : ∀ j < length,
      left.coeff (seam + 1 + j) = right.coeff (seam + 1 + j))
    (hbitOverlap : ∀ j < length,
      left.bit (seam + 1 + j) = right.bit (seam + 1 + j))
    (hleftNonneg : 0 ≤ left.carry (seam + 1 + length))
    (hrightNonneg : 0 ≤ right.carry (seam + 1 + length))
    (hleftBound : (left.carry (seam + 1 + length) : ℝ) ≤ bound)
    (hrightBound : (right.carry (seam + 1 + length) : ℝ) ≤ bound) :
    (2 : ℝ) ^ length ≤ bound := by
  sorry
end PalomarCorpus.E257.PaperStructuresO
