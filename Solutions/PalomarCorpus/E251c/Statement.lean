/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E251c

Every non-theorem declaration of `PalomarCorpus/E251c/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Finset
open scoped BigOperators
open scoped Topology

namespace PalomarCorpus.E251.PaperStatementsC
open Filter
open Finset
open scoped BigOperators
open scoped Topology
/-- Local copy of ErdosProblems.Erdos251.PaperCompleteR20.realDyadicTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realDyadicTail (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, a (N + j + 1) / 2 ^ (j + 1)
end PalomarCorpus.E251.PaperStatementsC
