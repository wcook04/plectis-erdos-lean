/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E251a

Every non-theorem declaration of `PalomarCorpus/E251a/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Topology
open Finset

namespace PalomarCorpus.E251.PaperStatementsA
open Filter
open Topology
open Finset
/-- Local copy of ErdosProblems.Erdos251.PaperR11.GrowingBlocks.testMean, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def testMean {α : Type*} (a : ℕ → α) (X m : ℕ)
    (Φ : ℕ → (Fin m → α) → ℝ) : ℝ :=
  (∑ N ∈ Ico X (2 * X), Φ N (fun i => a (N + i.val))) / X
end PalomarCorpus.E251.PaperStatementsA
