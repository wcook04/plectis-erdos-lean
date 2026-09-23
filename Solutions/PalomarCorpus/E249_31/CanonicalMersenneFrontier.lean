/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.CyclotomicAnchoredKill
import Erdos257PeriodNoncollapse.CarrySurvivorExtinction
import Solutions.PalomarCorpus.E249_31.Statement

open scoped BigOperators

namespace PalomarCorpus.E249.CanonicalMersenneFrontier

theorem fullMersenneBlockResidue_succ
    {H N M : ℕ} (hM : M ∣ 2 ^ H - 1) :
    fullMersenneBlockResidue H (N + 1) M =
      (2 * fullMersenneBlockResidue H N M -
        deltaTotient H (N + 1)) % (M : ℤ) := by
  simpa [fullMersenneBlockResidue, totientBlock, deltaTotient,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.fullMersenneBlockResidue,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.totientBlock,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.deltaTotient] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.fullMersenneBlockResidue_succ hM

theorem fullMersenneCenteredResidueGapSupply_of_canonicalBasepoint
    (hsupply : FullMersenneCanonicalBasepointResidueGapSupply) :
    FullMersenneCenteredResidueGapSupply := by
  simpa [FullMersenneCanonicalBasepointResidueGapSupply,
    FullMersenneCenteredResidueGapSupply,
    FullMersenneCenteredResidueGap, fullMersenneBlockResidue, totientBlock,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.FullMersenneCanonicalBasepointResidueGapSupply,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.FullMersenneCenteredResidueGapSupply,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.FullMersenneCenteredResidueGap,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.fullMersenneBlockResidue,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.totientBlock] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.fullMersenneCenteredResidueGapSupply_of_canonicalBasepoint
      hsupply

theorem fullMersenneCanonicalBasepointResidueGapSupply_iff_irrational :
    FullMersenneCanonicalBasepointResidueGapSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  simpa [FullMersenneCanonicalBasepointResidueGapSupply,
    FullMersenneCenteredResidueGap, fullMersenneBlockResidue, totientBlock,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.FullMersenneCanonicalBasepointResidueGapSupply,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.FullMersenneCenteredResidueGap,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.fullMersenneBlockResidue,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.totientBlock] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.fullMersenneCanonicalBasepointResidueGapSupply_iff_irrational

end PalomarCorpus.E249.CanonicalMersenneFrontier
