/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.CertificateKernel
import Erdos249257.MaximalOmegaLayer
import Erdos249257.SupportDilationDifferences
import Erdos249257.SupportSunflowerDichotomy

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CertificateKernel`, `Erdos249257.MaximalOmegaLayer`,
`Erdos249257.SupportDilationDifferences`, `Erdos249257.SupportSunflowerDichotomy`.
-/

open Filter
open Topology
open scoped ArithmeticFunction.Omega

namespace Erdos249257.ExternalVerification257PaperStatementsAO

noncomputable def primePowerLayer (p e : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  g (p ^ e * n) - g (p ^ (e - 1) * n)

noncomputable def mixedPrimePowerLayerTwo
    (p e q f : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  primePowerLayer q f (primePowerLayer p e g) n

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

noncomputable def supportCoeffInt (A : Set ℕ) (n : ℕ) : ℤ :=
  supportCoeff A n

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

end Erdos249257.ExternalVerification257PaperStatementsAO
