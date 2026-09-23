/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CertificateKernel
import Erdos249257.MaximalOmegaLayer
import Erdos249257.SupportDilationDifferences
import Erdos249257.SupportSunflowerDichotomy
import Solutions.PalomarCorpus.E257_30.Statement

open Filter
open Topology
open scoped ArithmeticFunction.Omega

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAO
export PalomarCorpus.E257_30.Shared (supportCoeff)

noncomputable def exactPrimePowerPullback (p e : ℕ) (A : Set ℕ) : Set ℕ :=
  {d | d.Coprime p ∧ p ^ e * d ∈ A}

theorem mixedPrimePowerLayerTwo_supportCoeffInt
    (A : Set ℕ) {p e q f n : ℕ}
    (hp : p.Prime) (he : 0 < e) (hq : q.Prime) (hf : 0 < f)
    (hpq : p ≠ q) (hn : n.Coprime (p * q)) :
    mixedPrimePowerLayerTwo p e q f (supportCoeffInt A) n =
      supportCoeffInt
        (exactPrimePowerPullback q f (exactPrimePowerPullback p e A)) n := @Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo_supportCoeffInt A p e q f n hp he hq hf hpq hn

theorem mixedPrimePowerLayerTwo_twelve_fixture :
    mixedPrimePowerLayerTwo 2 2 3 1
      (supportCoeffInt ({12} : Set ℕ)) 1 = 1 := @Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo_twelve_fixture

end PalomarCorpus.E257.PaperStatementsAO
