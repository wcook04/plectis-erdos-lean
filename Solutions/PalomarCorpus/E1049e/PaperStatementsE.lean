/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.AllRow.Filtered
import ErdosProblems.Erdos1049.AllRow.FiniteStates
import ErdosProblems.Erdos1049.PaperCompleteR21.AllRowInitialCoefficient
import ErdosProblems.Erdos1049.RationalBaseLambert
import Solutions.PalomarCorpus.E1049e.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStatementsE

theorem paperE_eq_rowExponent (m j : ℕ) (hjm : j ≤ m) :
    m * j - j * (j - 1) / 2 = rowExponent j (m - j) := @ErdosProblems.Erdos1049.PaperCompleteR21.paperE_eq_rowExponent m j hjm

theorem paperRatio_agree (a : ℕ → S) (n D K : ℕ) (hDK : D ≤ K) :
    Agree D (paperRatio a n) (finiteRatio a K n) := @ErdosProblems.Erdos1049.PaperCompleteR21.paperRatio_agree a n D K hDK

theorem paperReciprocal_rec (a : ℕ → S) (i : ℕ) :
    paperReciprocal a (i + 1) =
      -(∑ s ∈ Finset.range (i + 1),
          PowerSeries.constantCoeff (a (s + 1)) * paperReciprocal a (i - s)) := @ErdosProblems.Erdos1049.PaperCompleteR21.paperReciprocal_rec a i

theorem paperReciprocal_zero (a : ℕ → S) : paperReciprocal a 0 = 1 := @ErdosProblems.Erdos1049.PaperCompleteR21.paperReciprocal_zero a

theorem coordinatewiseCorridor_implies_pow_lt_linear
    {a b N K Q digit : ℕ}
    (h : CoordinatewiseCorridor a b N K Q digit) :
    b ^ (N + K + 1) < a * (N + K) := @ErdosProblems.Erdos1049.coordinatewiseCorridor_implies_pow_lt_linear a b N K Q digit h

theorem sevenHalves_archimedean_height_condition :
    Real.log 7 / Real.log ((7 : ℝ) / 2) <
      ((1 : ℝ) / 2 + 1 / Real.pi ^ 2)⁻¹ := @ErdosProblems.Erdos1049.sevenHalves_archimedean_height_condition

theorem three_mul_lt_two_pow_succ {x : ℕ} (hx : 2 ≤ x) :
    3 * x < 2 ^ (x + 1) := @ErdosProblems.Erdos1049.three_mul_lt_two_pow_succ x hx

end PalomarCorpus.E1049.PaperStatementsE
