/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041z

Every non-theorem declaration of `PalomarCorpus/E1041z/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Real
open Set
open MeasureTheory

namespace PalomarCorpus.E1041.PaperStatementsZ
open Real
open Set
open MeasureTheory
/-- The paper's `w(d,r) = arccos (clamp ((cosh d cosh r - cosh (D/2))/(sinh d sinh r)))`, the half-width of the arc cut from the hyperbolic circle of radius `r` about the centre by the open hyperbolic ball of radius `D/2` about a point at distance `d` from the centre. `clamp` truncates to `[-1,1]`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.sliceHalfAngle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sliceHalfAngle (D d r : ℝ) : ℝ :=
  arccos (max (-1) (min 1 ((cosh d * cosh r - cosh (D / 2)) / (sinh d * sinh r))))
end PalomarCorpus.E1041.PaperStatementsZ
