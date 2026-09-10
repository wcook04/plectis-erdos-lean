/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.PrimePoleCriterion

open scoped BigOperators

namespace PalomarCorpus.E68.PrimePole

noncomputable def factorialGapPrefixLCM (M : ℕ) : ℕ :=
  (Finset.Icc 2 M).lcm fun n => n.factorial - 1

noncomputable def factorialGapPrefixLCMNumerator (M : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 2 M,
    factorialGapPrefixLCM M / (n.factorial - 1)

noncomputable def factorialGapMaxHits (q M e : ℕ) : Finset ℕ :=
  (Finset.Icc 2 M).filter fun n =>
    q ^ e ∣ n.factorial - 1 ∧
      ¬q ^ (e + 1) ∣ n.factorial - 1

noncomputable def factorialGapPrincipalResidue (q M e : ℕ) : ZMod q :=
  ∑ n ∈ factorialGapMaxHits q M e,
    (((n.factorial - 1) / q ^ e : ℕ) : ZMod q)⁻¹

theorem factorialGapPrefixLCMNumerator_mod_prime
    {q M e : ℕ}
    (hq : q.Prime)
    (he : 1 ≤ e)
    (hmax :
      ∀ n ∈ Finset.Icc 2 M,
        ¬q ^ (e + 1) ∣ n.factorial - 1)
    (hattain :
      ∃ n ∈ Finset.Icc 2 M,
        q ^ e ∣ n.factorial - 1) :
    (factorialGapPrefixLCMNumerator M : ZMod q) =
      ((factorialGapPrefixLCM M / q ^ e : ℕ) : ZMod q) *
        factorialGapPrincipalResidue q M e := by
  simpa [factorialGapPrefixLCM, factorialGapPrefixLCMNumerator,
    factorialGapMaxHits, factorialGapPrincipalResidue,
    ErdosProblems.Erdos68.factorialGapPrefixLCM,
    ErdosProblems.Erdos68.factorialGapPrefixLCMNumerator,
    ErdosProblems.Erdos68.factorialGapMaxHits,
    ErdosProblems.Erdos68.factorialGapPrincipalResidue] using
    ErdosProblems.Erdos68.factorialGapPrefixLCMNumerator_mod_prime
      hq he hmax hattain

end PalomarCorpus.E68.PrimePole
