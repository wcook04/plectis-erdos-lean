/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.CertificateKernel
import Solutions.PalomarCorpus.E257_50.Statement

namespace PalomarCorpus.E257.FinitePeriodNoncollapse

theorem finite_period_noncollapse_rat_den
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    ∃ hcop : Nat.Coprime b (finiteErdosSum F b).den,
      orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id := by
  exact ⟨Erdos257PeriodNoncollapse.coprime_base_den_finiteErdosSum F b h0 hb,
    Erdos257PeriodNoncollapse.finite_period_noncollapse_rat_den F b hF h0 hb⟩

theorem lcm_lt_den_finiteErdosSum
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (h2 : 2 ≤ F.lcm id) :
    F.lcm id < (finiteErdosSum F b).den := by
  simpa [finiteErdosSum,
      Erdos257PeriodNoncollapse.finiteErdosSum] using
      Erdos257PeriodNoncollapse.lcm_lt_den_finiteErdosSum
        F b hF h0 hb h2

end PalomarCorpus.E257.FinitePeriodNoncollapse
