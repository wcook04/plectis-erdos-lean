/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257ai

Every non-theorem declaration of `PalomarCorpus/E257ai/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Topology
open Classical

namespace PalomarCorpus.E257.PaperStatementsAI
open Filter
open Topology
open Classical
/-- The manuscript's `w_n^{(J)} = ∑_{q=1}^{J} 2^{-qn}`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungWeight (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / 2 ^ (q * n)
/-- The greedy residual just before rank `n` is examined; `rungRem J 0 = 1/2`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungRem, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungRem (J : ℕ) : ℕ → ℝ
  | 0 => 1 / 2
  | n + 1 => if rungWeight J n ≤ rungRem J n then rungRem J n - rungWeight J n else rungRem J n
/-- The greedy support: the ranks the greedy rule takes. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungGreedySupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungGreedySupport (J : ℕ) : Set ℕ := {n | rungWeight J n ≤ rungRem J n}
/-- The manuscript's `T_{n+1}^{(J)} = ∑_{q=1}^{J} 2^{-qn}/(2^q-1)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rungTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rungTail (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / (2 ^ (q * n) * (2 ^ q - 1))
end PalomarCorpus.E257.PaperStatementsAI
