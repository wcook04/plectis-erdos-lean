/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E269h

Every non-theorem declaration of `PalomarCorpus/E269h/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Module
open Submodule

namespace PalomarCorpus.E269.PaperStructuresH
open scoped BigOperators
open Module
open Submodule
/-- A cut at `k`, with `m` rows. Local copy of ErdosProblems.Erdos269.PaperR7.cutVector, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cutVector {F : Type*} [Field F] (c : F) (m k : ℕ) : Fin m → F :=
  fun i => if (i : ℕ) < k then 1 else c
end PalomarCorpus.E269.PaperStructuresH
