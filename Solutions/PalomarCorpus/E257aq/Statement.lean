/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257aq

Every non-theorem declaration of `PalomarCorpus/E257aq/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open ArithmeticFunction
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

namespace PalomarCorpus.E257.PaperStatementsAQ
open ArithmeticFunction
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
/-- The real Mersenne weight `1 / (2^n - 1)`. Local copy of Erdos249257.mersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The Boolean support term selected by the negative Möbius sign. Local copy of Erdos249257.MobiusSignSupportNoGo.negativeMobiusTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def negativeMobiusTerm (d : ℕ+) : ℝ :=
  if moebius (d : ℕ) = -1 then mersenneWeight (d : ℕ) else 0
/-- The positive Möbius tail, with the exceptional `d = 1` term removed. Local copy of Erdos249257.MobiusSignSupportNoGo.positiveMobiusTailTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMobiusTailTerm (d : ℕ+) : ℝ :=
  if moebius (d : ℕ) = 1 ∧ (d : ℕ) ≠ 1 then mersenneWeight (d : ℕ) else 0
end PalomarCorpus.E257.PaperStatementsAQ
