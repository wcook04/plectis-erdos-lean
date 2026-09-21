/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041f

Every non-theorem declaration of `PalomarCorpus/E1041f/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Set
open Filter
open MeasureTheory
open scoped Topology

namespace PalomarCorpus.E1041.PaperStatementsF
open Set
open Filter
open MeasureTheory
open scoped Topology
/-- `coth t = cosh t / sinh t`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.coth, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def coth (t : ℝ) : ℝ := Real.cosh t / Real.sinh t
/-- The integrand `1 / log (coth t)` of the paper's `Φ`, carrying the paper's continuous limiting value `0` at `t = 0`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.orliczKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def orliczKernel (t : ℝ) : ℝ := 1 / Real.log (coth t)
/-- `Φ(x) = ∫_0^x dt / log (coth t)`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Phi, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Phi (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, orliczKernel t
/-- `I_k(r) = ∫_r^1 dq / (q * log ((1 + q ^ (2/k)) / (1 - q ^ (2/k))))`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.mergerIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mergerIntegral (k : ℕ) (r : ℝ) : ℝ :=
  ∫ q in r..(1 : ℝ),
    1 / (q * Real.log ((1 + q ^ ((2 : ℝ) / k)) / (1 - q ^ ((2 : ℝ) / k))))
end PalomarCorpus.E1041.PaperStatementsF
