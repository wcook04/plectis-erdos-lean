/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041r

Every non-theorem declaration of `PalomarCorpus/E1041r/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Polynomial
open Finset

namespace PalomarCorpus.E1041.PaperStatementsR
open Polynomial
open Finset
/-- The stored sextic guardrail family `f_r z = z^6 + (1/5) r^2 z^4 - (1/5) r^4 z^2 - r^6`. Local copy of ErdosProblems.Erdos1041.AbelControlPolygon.sextic, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sextic (r z : ℂ) : ℂ :=
  z ^ 6 + (1 / 5) * r ^ 2 * z ^ 4 - (1 / 5) * r ^ 4 * z ^ 2 - r ^ 6
end PalomarCorpus.E1041.PaperStatementsR
