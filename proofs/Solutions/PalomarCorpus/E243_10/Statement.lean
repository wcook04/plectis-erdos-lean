/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243_10

Every non-theorem declaration of `PalomarCorpus/E243_10/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

namespace PalomarCorpus.E243_10.Shared
/-- The running maximum `max_{k ≤ n} u k` of a natural-valued sequence, given by `runningMax u 0 = u 0` and `runningMax u (n+1) = max (runningMax u n) (u (n+1))`. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
end PalomarCorpus.E243_10.Shared

namespace PalomarCorpus.E243.BoundedNegativePartRigidity
export PalomarCorpus.E243_10.Shared (sylvesterNext)
/-- The centred reciprocal-tail error `D - (a - 1) * C` of an integer state, the integer measuring the failure of the identity `D = (a - 1) * C` that holds exactly on a Sylvester tail. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
end PalomarCorpus.E243.BoundedNegativePartRigidity

namespace PalomarCorpus.E243.BoundedRiseReducedTail
end PalomarCorpus.E243.BoundedRiseReducedTail

namespace PalomarCorpus.E243.PeriodicNegativeOrbit
end PalomarCorpus.E243.PeriodicNegativeOrbit

namespace PalomarCorpus.E243.PrimitiveRecordRigidity
export PalomarCorpus.E243_10.Shared (runningMax sylvesterNext)
end PalomarCorpus.E243.PrimitiveRecordRigidity

namespace PalomarCorpus.E243.ProtectedEpochEnergy
export PalomarCorpus.E243_10.Shared (runningMax)
end PalomarCorpus.E243.ProtectedEpochEnergy
