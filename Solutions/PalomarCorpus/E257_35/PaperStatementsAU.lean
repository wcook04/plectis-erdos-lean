/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusCarry
import Erdos249257.CertificateKernel
import Erdos249257.GenericTailOrbitRigidity
import Solutions.PalomarCorpus.E257_35.Statement

open ArithmeticFunction
open Filter
open Set
open scoped ArithmeticFunction.Moebius
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAU
export PalomarCorpus.E257_35.Shared (IsTemperedBinaryOrbit binaryCoeffSeries erdosSupportSeries supportCoeff)

noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

theorem binaryCoeffTail_supportCoeff_le_two_sqrt_add_four
    (A : Set ℕ) (N : ℕ) :
    binaryCoeffTail (supportCoeff A) N ≤
      2 * Real.sqrt (N : ℝ) + 4 := @Erdos249257.binaryCoeffTail_supportCoeff_le_two_sqrt_add_four A N

theorem erdosSupportSeries_rational_iff_exists_temperedCarry (A : Set ℕ) :
    HasRationalValue (erdosSupportSeries 2 A) ↔
      ∃ q : ℕ, 0 < q ∧ ∃ U : ℕ → ℤ,
        IsTemperedBinaryOrbit (supportCoeff A) q U := @Erdos249257.erdosSupportSeries_rational_iff_exists_temperedCarry A

theorem erdosSupportSeries_two_eq_binaryCoeffSeries (A : Set ℕ) :
    erdosSupportSeries 2 A = binaryCoeffSeries (supportCoeff A) := @Erdos249257.erdosSupportSeries_two_eq_binaryCoeffSeries A

theorem mobius_supportCoeff_boolean (A : Set ℕ) (n : ℕ) :
    (ArithmeticFunction.moebius * supportCoeffAF A) n = 0 ∨
      (ArithmeticFunction.moebius * supportCoeffAF A) n = 1 := @Erdos249257.mobius_supportCoeff_boolean A n

theorem mobius_supportCoeff_eq_one_iff (A : Set ℕ) {n : ℕ} (hn : 0 < n) :
    (ArithmeticFunction.moebius * supportCoeffAF A) n = 1 ↔ n ∈ A := @Erdos249257.mobius_supportCoeff_eq_one_iff A n hn

theorem moebius_mul_supportCoeffAF (A : Set ℕ) :
    ArithmeticFunction.moebius * supportCoeffAF A = positiveSupportBitAF A := @Erdos249257.moebius_mul_supportCoeffAF A

end PalomarCorpus.E257.PaperStatementsAU
