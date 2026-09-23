/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.HalfTrappingReturnCarry
import Solutions.PalomarCorpus.E257_32.Statement

open Matrix

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresO

/-- The copied structure `ReverseCarryWord` and its source `Erdos249257.HalfTrappingReturnCarry.ReverseCarryWord` carry the same
fields, so each converts into the other field by field. -/
noncomputable def ReverseCarryWord_transport_toSrc (x : ReverseCarryWord) :
    Erdos249257.HalfTrappingReturnCarry.ReverseCarryWord :=
  ⟨x.coeff, x.bit, x.carry, x.normalized⟩

/-- The inverse of `ReverseCarryWord_transport_toSrc`. -/
noncomputable def ReverseCarryWord_transport_ofSrc (x : Erdos249257.HalfTrappingReturnCarry.ReverseCarryWord) :
    ReverseCarryWord :=
  ⟨x.coeff, x.bit, x.carry, x.normalized⟩

@[simp] theorem ReverseCarryWord_transport_toSrc_coeff
    (x : ReverseCarryWord) :
    (ReverseCarryWord_transport_toSrc x).coeff = x.coeff := rfl

@[simp] theorem ReverseCarryWord_transport_ofSrc_coeff
    (x : Erdos249257.HalfTrappingReturnCarry.ReverseCarryWord) :
    (ReverseCarryWord_transport_ofSrc x).coeff = x.coeff := rfl

@[simp] theorem ReverseCarryWord_transport_toSrc_bit
    (x : ReverseCarryWord) :
    (ReverseCarryWord_transport_toSrc x).bit = x.bit := rfl

@[simp] theorem ReverseCarryWord_transport_ofSrc_bit
    (x : Erdos249257.HalfTrappingReturnCarry.ReverseCarryWord) :
    (ReverseCarryWord_transport_ofSrc x).bit = x.bit := rfl

@[simp] theorem ReverseCarryWord_transport_toSrc_carry
    (x : ReverseCarryWord) :
    (ReverseCarryWord_transport_toSrc x).carry = x.carry := rfl

@[simp] theorem ReverseCarryWord_transport_ofSrc_carry
    (x : Erdos249257.HalfTrappingReturnCarry.ReverseCarryWord) :
    (ReverseCarryWord_transport_ofSrc x).carry = x.carry := rfl

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
    (2 : ℝ) ^ (2 * N - M - 1) ≤ bound := @Erdos249257.HalfTrappingReturnCarry.overlappingMidpointReturns_twoPow_le_realBound (ReverseCarryWord_transport_toSrc left) (ReverseCarryWord_transport_toSrc right) N M bound hN hNM hcoeffSeam hleftSeam hrightSeam hcoeffOverlap hbitOverlap hleftNonneg hrightNonneg hleftBound hrightBound

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
        (2 : ℤ) ^ length * z := @Erdos249257.HalfTrappingReturnCarry.overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd (ReverseCarryWord_transport_toSrc left) (ReverseCarryWord_transport_toSrc right) seam length hcoeffSeam hleftSeam hrightSeam hcoeffOverlap hbitOverlap

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
    (2 : ℝ) ^ length ≤ bound := @Erdos249257.HalfTrappingReturnCarry.overlappingReverseCarryWords_twoPow_le_realBound (ReverseCarryWord_transport_toSrc left) (ReverseCarryWord_transport_toSrc right) seam length bound hcoeffSeam hleftSeam hrightSeam hcoeffOverlap hbitOverlap hleftNonneg hrightNonneg hleftBound hrightBound

end PalomarCorpus.E257.PaperStructuresO
