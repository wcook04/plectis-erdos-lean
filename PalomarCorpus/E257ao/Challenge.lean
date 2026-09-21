/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band o

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Topology
open scoped ArithmeticFunction.Omega

namespace PalomarCorpus.E257.PaperStatementsAO
open Filter
open Topology
open scoped ArithmeticFunction.Omega
/-- The signed coefficient layer between exact `p`-adic levels `e-1` and `e`. Local copy of Erdos249257.MaximalOmegaLayer.primePowerLayer, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primePowerLayer (p e : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  g (p ^ e * n) - g (p ^ (e - 1) * n)
/-- The two-signature mixed layer. Further list-level iteration can use this as its checked algebraic step without committing to a factorization API. Local copy of Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mixedPrimePowerLayerTwo
    (p e q f : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  primePowerLayer q f (primePowerLayer p e g) n
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}` — the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- Integer-valued packaging of the support divisor-count coefficient. Local copy of Erdos249257.SupportDilationDifferences.supportCoeffInt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeffInt (A : Set ℕ) (n : ℕ) : ℤ :=
  supportCoeff A n
/-- Support elements with exact `p`-adic exponent `e`, after removing the prime-power layer. Local copy of Erdos249257.SupportSunflowerDichotomy.exactPrimePowerPullback, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exactPrimePowerPullback (p e : ℕ) (A : Set ℕ) : Set ℕ :=
  {d | d.Coprime p ∧ p ^ e * d ∈ A}
/-- States lem:mixed-prime-power-layer, record:257rig-i5 from the long record for Erdős problem #257. Transported from Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo_supportCoeffInt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mixedPrimePowerLayerTwo_supportCoeffInt
    (A : Set ℕ) {p e q f n : ℕ}
    (hp : p.Prime) (he : 0 < e) (hq : q.Prime) (hf : 0 < f)
    (hpq : p ≠ q) (hn : n.Coprime (p * q)) :
    mixedPrimePowerLayerTwo p e q f (supportCoeffInt A) n =
      supportCoeffInt
        (exactPrimePowerPullback q f (exactPrimePowerPullback p e A)) n := by
  sorry
/-- States record:257rig-i5 from the long record for Erdős problem #257. Transported from Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo_twelve_fixture in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mixedPrimePowerLayerTwo_twelve_fixture :
    mixedPrimePowerLayerTwo 2 2 3 1
      (supportCoeffInt ({12} : Set ℕ)) 1 = 1 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAO
