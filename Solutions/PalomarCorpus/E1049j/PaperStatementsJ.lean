/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.PaperCompleteR21.RationalBaseThreshold
import ErdosProblems.Erdos1049.PaperLinearFormsR7
import ErdosProblems.Erdos1049.RationalBaseContour
import Solutions.PalomarCorpus.E1049j.Statement

open Filter
open scoped Topology
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStatementsJ

theorem rational_base_threshold (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b) (h : (b : ℝ) ^ zudilinMu < (a : ℝ)) :
    Irrational (paperLambert ((a : ℝ) / b)) := @ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold a b hb hab _hcop h

theorem rational_base_threshold_log (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b)
    (h : Real.log (b : ℝ) / Real.log (a : ℝ) < zudilinContour) :
    Irrational (paperLambert ((a : ℝ) / b)) := @ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold_log a b hb hab _hcop h

theorem thirtyoneFour_irrational : Irrational (paperLambert ((31 : ℝ) / 4)) := @ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_irrational

theorem thirtyoneFour_pow_irrational (r : ℕ) (hr : 0 < r) :
    Irrational (paperLambert (((31 : ℝ) / 4) ^ r)) := @ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_pow_irrational r hr

end PalomarCorpus.E1049.PaperStatementsJ
