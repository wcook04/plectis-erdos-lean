/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.GenericTailOrbitRigidity
import ErdosProblems.Erdos249.PaperCompleteR21.CarryDescriptionInformationLoss
import Solutions.PalomarCorpus.E249_03.Statement

open Filter
open Set

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsD

theorem affineBinaryOrbit_difference_and_reset (a : ℕ → ℤ) (u0 v0 : ℤ) (L : ℕ) :
    affineBinaryOrbit a u0 L - affineBinaryOrbit a v0 L = (2 : ℤ) ^ L * (u0 - v0)
      ∧ affineBinaryOrbit a u0 L ≡ affineBinaryOrbit a v0 L [ZMOD (2 : ℤ) ^ L] := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos249.PaperCompleteR21.affineBinaryOrbit_difference_and_reset a u0 v0 L

end PalomarCorpus.E249.PaperStatementsD
