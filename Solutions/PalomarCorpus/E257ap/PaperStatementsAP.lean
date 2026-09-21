/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CyclicTensorMobiusShadow
import Erdos249257.MersenneShadowCyclotomicNoncollapse
import Erdos249257.MersenneShadowDenominatorGrowth
import Erdos249257.RadicalMobiusShadow
import Solutions.PalomarCorpus.E257ap.Statement

open scoped BigOperators
open scoped Polynomial

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAP

theorem lcmHeight_scaledMobiusShadow_den_exact (t : ℕ) :
    ((lcmHeight t : ℚ) *
        numericMobiusShadow (lcmHeight t)).den =
      mersenne (lcmRadical t) /
        Nat.gcd (mersenne (lcmRadical t))
          (lcmScale t *
            (oddJordanScalar (lcmRadical t)).natAbs) := @Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_scaledMobiusShadow_den_exact t

end PalomarCorpus.E257.PaperStatementsAP
