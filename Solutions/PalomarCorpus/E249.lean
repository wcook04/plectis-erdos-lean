/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.TotientActualLcmOrbitNonintegrality
import ErdosProblems.Erdos249.CyclotomicAnchoredKill
import Erdos257PeriodNoncollapse.TotientTailCarryPeriod
import Erdos257PeriodNoncollapse.TotientMahlerDefect
import Erdos257PeriodNoncollapse.CertificateKernel
import ErdosProblems.Erdos249.FullDepthRayAmplifier
import Erdos257PeriodNoncollapse.SignedQMomentObstruction
import ErdosProblems.Erdos249.MobiusMersenneLadderSeparation
import ErdosProblems.Erdos249.PrefixValuationAndControlRigidity
import ErdosProblems.Erdos249.RankOneSharpFloor
import ErdosProblems.Erdos249.ResidueClassTotientSeries
import Erdos257PeriodNoncollapse.AllBaseTotientKernel

open scoped BigOperators
open Module
open ArithmeticFunction

namespace PalomarCorpus.E249.Shared
noncomputable abbrev TotientCanonicalIndex (e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)

noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)

noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n

noncomputable def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)

noncomputable def canonicalTotientKernelFamily (e : ℕ) :
    TotientCanonicalIndex e → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ =>
      totientKernelSeq (j.val + 1) (2 * r.val + 1)

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) -
      (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

end PalomarCorpus.E249.Shared
namespace PalomarCorpus.E249.ActualLcmOrbit
export PalomarCorpus.E249.Shared (totientTail)

open scoped BigOperators

noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)
noncomputable def actualLcmHeight (a : ℕ) : ℕ :=
  periodLcm (2 ^ a)
noncomputable def actualLcmTailOrbit (a : ℕ) : ℝ :=
  totientTail (2 * actualLcmHeight a) - totientTail (actualLcmHeight a)

noncomputable def PowerTwoActualLcmOrbitNonintegralitySupply : Prop :=
  ∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
    actualLcmTailOrbit a ∉ Set.range ((↑) : ℤ → ℝ)
private theorem periodLcm_eq_source :
    ∀ t : ℕ, periodLcm t =
      Erdos257PeriodNoncollapse.TotientTailPeriodKiller.periodLcm t
  | 0 => rfl
  | t + 1 => by
      simp only [periodLcm,
        Erdos257PeriodNoncollapse.TotientTailPeriodKiller.periodLcm]
      rw [periodLcm_eq_source t]

theorem actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix (a : ℕ) :
    actualLcmTailOrbit a =
      (2 : ℝ) ^ actualLcmHeight a *
          ((2 : ℝ) ^ actualLcmHeight a - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) -
        ((totientPrefix (2 * actualLcmHeight a) : ℝ) -
          (totientPrefix (actualLcmHeight a) : ℝ)) := by
  simpa [actualLcmTailOrbit, actualLcmHeight, totientTail, totientPrefix,
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit,
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmHeight,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientTail,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientPrefix,
    periodLcm_eq_source] using
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix a

theorem irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      PowerTwoActualLcmOrbitNonintegralitySupply := by
  simpa [PowerTwoActualLcmOrbitNonintegralitySupply,
    actualLcmTailOrbit, actualLcmHeight, totientTail,
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoActualLcmOrbitNonintegralitySupply,
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit,
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmHeight,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientTail,
    periodLcm_eq_source] using
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply

end PalomarCorpus.E249.ActualLcmOrbit

namespace PalomarCorpus.E249.BinaryCyclotomicAnchors
export PalomarCorpus.E249.Shared (certifiedKill totientTail windowDiscrepancy)

open scoped BigOperators

noncomputable def binaryCyclotomicLayer (n : ℕ) : ℕ :=
  ((Polynomial.cyclotomic n ℤ).eval (2 : ℤ)).natAbs

noncomputable def UnboundedPrimeDivisorSupply (C : ℕ → ℕ) (h : ℕ) : Prop :=
  ∀ B N₀ : ℕ, ∃ q p : ℕ,
    q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (h * q) ∧ B < p
noncomputable def CyclotomicAnchoredKillSupply (C : ℕ → ℕ) : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ q p L : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ C (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 ∧
      certifiedKill (h * q) (p - 1) L
theorem exists_clean_binaryCyclotomicAnchor
    (h N₀ : ℕ) (hh : 0 < h) :
    ∃ q p : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ binaryCyclotomicLayer (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 := by
  simpa [binaryCyclotomicLayer,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.exists_clean_binaryCyclotomicAnchor
      h N₀ hh

theorem binaryCyclotomicLayer_unboundedPrimeDivisorSupply
    (h : ℕ) (hh : 0 < h) :
    UnboundedPrimeDivisorSupply binaryCyclotomicLayer h := by
  simpa [UnboundedPrimeDivisorSupply, binaryCyclotomicLayer,
    ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.UnboundedPrimeDivisorSupply,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer_unboundedPrimeDivisorSupply
      h hh

theorem binaryCyclotomicAnchoredKillSupply_iff_irrational :
    CyclotomicAnchoredKillSupply binaryCyclotomicLayer ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  simpa [CyclotomicAnchoredKillSupply, certifiedKill, windowDiscrepancy,
    binaryCyclotomicLayer,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.CyclotomicAnchoredKillSupply,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.certifiedKill,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.windowDiscrepancy] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicAnchoredKillSupply_iff_irrational

theorem exists_unbounded_binaryCyclotomicSupport_with_periodLock_of_not_irrational
    (hrat : ¬ Irrational
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧
      UnboundedPrimeDivisorSupply binaryCyclotomicLayer h ∧
      ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
        totientTail (N + h) - totientTail N ∈
          Set.range ((↑) : ℤ → ℝ) := by
  simpa [UnboundedPrimeDivisorSupply, binaryCyclotomicLayer, totientTail,
    ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.UnboundedPrimeDivisorSupply,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientTail] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.exists_unbounded_binaryCyclotomicSupport_with_periodLock_of_not_irrational
      hrat

end PalomarCorpus.E249.BinaryCyclotomicAnchors

namespace PalomarCorpus.E249.CanonicalMersenneFrontier

open scoped BigOperators

noncomputable def deltaTotient (h n : ℕ) : ℤ :=
  (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
noncomputable def totientBlock (H N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range H,
    (Nat.totient (N + 1 + j) : ℤ) * 2 ^ (H - 1 - j)
noncomputable def fullMersenneBlockResidue (H N M : ℕ) : ℤ :=
  (-totientBlock H N) % (M : ℤ)
noncomputable def FullMersenneCenteredResidueGap (H N M : ℕ) : Prop :=
  let B : ℤ := N + H + 1
  B < fullMersenneBlockResidue H N M ∧
    fullMersenneBlockResidue H N M < (M : ℤ) - B
noncomputable def FullMersenneCenteredResidueGapSupply : Prop :=
  ∀ c v : ℕ, 0 < v → Nat.Coprime 2 v →
    ∀ N₀ : ℕ, ∃ H N M : ℕ,
      0 < H ∧ Nat.totient v ∣ H ∧ max c N₀ ≤ N ∧
      v * M = 2 ^ H - 1 ∧ FullMersenneCenteredResidueGap H N M
noncomputable def FullMersenneCanonicalBasepointResidueGapSupply : Prop :=
  ∀ c v : ℕ, 0 < v → Nat.Coprime 2 v →
    ∃ H M : ℕ,
      0 < H ∧ Nat.totient v ∣ H ∧ v * M = 2 ^ H - 1 ∧
      FullMersenneCenteredResidueGap H c M
theorem fullMersenneBlockResidue_succ
    {H N M : ℕ} (hM : M ∣ 2 ^ H - 1) :
    fullMersenneBlockResidue H (N + 1) M =
      (2 * fullMersenneBlockResidue H N M -
        deltaTotient H (N + 1)) % (M : ℤ) := by
  simpa [fullMersenneBlockResidue, totientBlock, deltaTotient,
    ErdosProblems.Erdos249.fullMersenneBlockResidue,
    ErdosProblems.Erdos249.totientBlock,
    Erdos257PeriodNoncollapse.deltaTotient] using
    ErdosProblems.Erdos249.fullMersenneBlockResidue_succ hM

theorem fullMersenneCenteredResidueGapSupply_of_canonicalBasepoint
    (hsupply : FullMersenneCanonicalBasepointResidueGapSupply) :
    FullMersenneCenteredResidueGapSupply := by
  simpa [FullMersenneCanonicalBasepointResidueGapSupply,
    FullMersenneCenteredResidueGapSupply,
    FullMersenneCenteredResidueGap, fullMersenneBlockResidue, totientBlock,
    ErdosProblems.Erdos249.FullMersenneCanonicalBasepointResidueGapSupply,
    ErdosProblems.Erdos249.FullMersenneCenteredResidueGapSupply,
    ErdosProblems.Erdos249.FullMersenneCenteredResidueGap,
    ErdosProblems.Erdos249.fullMersenneBlockResidue,
    ErdosProblems.Erdos249.totientBlock] using
    ErdosProblems.Erdos249.fullMersenneCenteredResidueGapSupply_of_canonicalBasepoint
      hsupply

theorem fullMersenneCanonicalBasepointResidueGapSupply_iff_irrational :
    FullMersenneCanonicalBasepointResidueGapSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  simpa [FullMersenneCanonicalBasepointResidueGapSupply,
    FullMersenneCenteredResidueGap, fullMersenneBlockResidue, totientBlock,
    ErdosProblems.Erdos249.FullMersenneCanonicalBasepointResidueGapSupply,
    ErdosProblems.Erdos249.FullMersenneCenteredResidueGap,
    ErdosProblems.Erdos249.fullMersenneBlockResidue,
    ErdosProblems.Erdos249.totientBlock] using
    ErdosProblems.Erdos249.fullMersenneCanonicalBasepointResidueGapSupply_iff_irrational

end PalomarCorpus.E249.CanonicalMersenneFrontier

namespace PalomarCorpus.E249.CarryRankFrontier
export PalomarCorpus.E249.Shared (TotientCanonicalIndex canonicalTotientKernelFamily totientKernelSeq totientTail)

noncomputable section

noncomputable abbrev binaryCoeffSeries :=
  Erdos257PeriodNoncollapse.binaryCoeffSeries
noncomputable abbrev IsTemperedBinaryOrbit :=
  Erdos257PeriodNoncollapse.IsTemperedBinaryOrbit
noncomputable abbrev carryKernelSeq := Erdos257PeriodNoncollapse.carryKernelSeq
noncomputable abbrev TotientCarryIndex := Erdos257PeriodNoncollapse.TotientCarryIndex
noncomputable abbrev canonicalCarryKernelFamily :=
  Erdos257PeriodNoncollapse.canonicalCarryKernelFamily
noncomputable abbrev SeparatedMinorCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ℕ → ℚ) :=
  Erdos257PeriodNoncollapse.SeparatedMinorCertificate family
noncomputable abbrev CarrySectionsEventuallyPeriodicMod :=
  Erdos257PeriodNoncollapse.CarrySectionsEventuallyPeriodicMod
theorem not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    ¬ Irrational (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
        IsTemperedBinaryOrbit c v u :=
  Erdos257PeriodNoncollapse.not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
    c hgrowth

theorem totient_carryKernel_diff
    {v : ℕ} {u : ℕ → ℤ}
    (hu : IsTemperedBinaryOrbit Nat.totient v u)
    {j r : ℕ} (hr : 0 < r) :
    (fun n => (v : ℚ) * totientKernelSeq j r n) =
      fun n => 2 * carryKernelSeq u j (r - 1) n -
        carryKernelSeq u j r n :=
  Erdos257PeriodNoncollapse.totient_carryKernel_diff hu hr

theorem finrank_canonicalCarryKernel_ge_of_certificate
    {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (e : ℕ)
    (cert : SeparatedMinorCertificate (canonicalTotientKernelFamily e)) :
    2 ^ e - 1 ≤
      Module.finrank ℚ
        (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) :=
  Erdos257PeriodNoncollapse.finrank_canonicalCarryKernel_ge_of_certificate
    hv hu e cert

theorem not_irrational_totientSeries_implies_unbounded_carryRank_unconditional
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        ∀ e : ℕ,
          2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e))) :=
  Erdos257PeriodNoncollapse.not_irrational_totientSeries_implies_unbounded_carryRank_unconditional
    hirr

theorem carryShift_dvd_iff_tailDiff_mem_int
    {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ) :
    (v : ℤ) ∣ u (N + k) - u N ↔
      totientTail (N + k) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ) :=
  Erdos257PeriodNoncollapse.carryShift_dvd_iff_tailDiff_mem_int
    hv hu N k

theorem not_irrational_totientSeries_implies_mod_period_and_unbounded_rank
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ,
          2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u :=
  Erdos257PeriodNoncollapse.not_irrational_totientSeries_implies_mod_period_and_unbounded_rank
    hirr

end

end PalomarCorpus.E249.CarryRankFrontier

namespace PalomarCorpus.E249.DyadicTotientKernel
export PalomarCorpus.E249.Shared (TotientCanonicalIndex canonicalTotientKernelFamily totientKernelSeq)

open Module

noncomputable abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)
noncomputable def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val
noncomputable abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)
noncomputable def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val
noncomputable abbrev TotientOddCoreIndex := Fin 2 ⊕ Σ j : ℕ, Fin (2 ^ j)
noncomputable def oddCoreTotientKernelFamily : TotientOddCoreIndex → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j + 1) (2 * r.val + 1)
theorem dyadicTotientKernelOddCoreBasisAndFiniteRanks :
    LinearIndependent ℚ oddCoreTotientKernelFamily ∧
      Submodule.span ℚ (Set.range fullTotientKernelFamily) =
        Submodule.span ℚ (Set.range oddCoreTotientKernelFamily) ∧
      ∀ e : ℕ, 1 ≤ e →
        Submodule.span ℚ
            (Set.range (totientKernelThroughLevelFamily e)) =
          Submodule.span ℚ
            (Set.range (canonicalTotientKernelFamily e)) ∧
        finrank ℚ
            (Submodule.span ℚ
              (Set.range (totientKernelThroughLevelFamily e))) = 2 ^ e + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [oddCoreTotientKernelFamily, totientKernelSeq,
      Erdos257PeriodNoncollapse.oddCoreTotientKernelFamily,
      Erdos257PeriodNoncollapse.totientKernelSeq] using
      Erdos257PeriodNoncollapse.linearIndependent_oddCoreTotientKernelFamily
  · simpa [fullTotientKernelFamily, oddCoreTotientKernelFamily,
      totientKernelSeq, Erdos257PeriodNoncollapse.fullTotientKernelFamily,
      Erdos257PeriodNoncollapse.oddCoreTotientKernelFamily,
      Erdos257PeriodNoncollapse.totientKernelSeq] using
      Erdos257PeriodNoncollapse.span_range_fullTotientKernel_eq_span_range_oddCore
  · intro e he
    constructor
    · simpa [totientKernelThroughLevelFamily,
        canonicalTotientKernelFamily, totientKernelSeq,
        Erdos257PeriodNoncollapse.totientKernelThroughLevelFamily,
        Erdos257PeriodNoncollapse.canonicalTotientKernelFamily,
        Erdos257PeriodNoncollapse.totientKernelSeq] using
        Erdos257PeriodNoncollapse.span_totientKernelThroughLevelFamily_eq_canonical
          e he
    · simpa [totientKernelThroughLevelFamily, totientKernelSeq,
        Erdos257PeriodNoncollapse.totientKernelThroughLevelFamily,
        Erdos257PeriodNoncollapse.totientKernelSeq] using
        Erdos257PeriodNoncollapse.finrank_totientKernelThroughLevelFamily_eq e he

end PalomarCorpus.E249.DyadicTotientKernel

namespace PalomarCorpus.E249.FareyWindowExclusion
noncomputable def fareyDenBound : ℕ := 79639646646701375323355774875831053
theorem farey_int_exclusion :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ fareyDenBound →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (a : ℝ) / (d : ℝ) :=
  Erdos257PeriodNoncollapse.tsum_totient_div_pow_two_ne_int_div_of_den_le_79639646646701375323355774875831053

theorem farey_rat_exclusion :
    ∀ p : ℚ, p.den ≤ fareyDenBound →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ) :=
  Erdos257PeriodNoncollapse.tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053

end PalomarCorpus.E249.FareyWindowExclusion

namespace PalomarCorpus.E249.FullDepthRayAmplifier
export PalomarCorpus.E249.Shared (certifiedKill totientTail windowDiscrepancy)

open scoped BigOperators

noncomputable def PeriodMultipleKillSupply : Prop := ∀ d : ℕ, 0 < d → ∀ c : ℕ, ∃ t N L : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N L
noncomputable def ApFullDepthEscape : Prop := ∀ d : ℕ, 0 < d → ∀ N : ℕ, ∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)
noncomputable def fullDepthKillMultipliers (d N : ℕ) : Set ℕ := {t | certifiedKill (t * d) N (t * d)}
noncomputable def CofinalFullDepthKillSupply : Prop := ∀ d : ℕ, 0 < d → ∀ c : ℕ, ∃ t N : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N (t * d)
theorem eventually_twoSyndetic_fullDepthKillMultipliers_of_seed
    {d N L : ℕ} (hd : 0 < d) (hseed : certifiedKill d N L) :
    ∃ T : ℕ, 0 < T ∧ ∀ t : ℕ, T ≤ t →
      ∃ m : ℕ, m ∈ fullDepthKillMultipliers d N ∧ t ≤ m ∧ m ≤ t + 1 := by
  simpa [certifiedKill, windowDiscrepancy, fullDepthKillMultipliers,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.certifiedKill,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.windowDiscrepancy,
    ErdosProblems.Erdos249.FullDepthRayAmplifier.fullDepthKillMultipliers] using
    ErdosProblems.Erdos249.FullDepthRayAmplifier.eventually_twoSyndetic_fullDepthKillMultipliers_of_seed hd hseed

theorem exists_fullDepthKill_on_ray_iff_shift_notMem_int
    {d N : ℕ} (hd : 0 < d) :
    (∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔
      totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  simpa [certifiedKill, windowDiscrepancy, totientTail,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.certifiedKill,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.windowDiscrepancy,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientTail] using
    ErdosProblems.Erdos249.FullDepthRayAmplifier.exists_fullDepthKill_on_ray_iff_shift_notMem_int hd

theorem apFullDepthEscape_iff_irrational :
    ApFullDepthEscape ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  simpa [ApFullDepthEscape, certifiedKill, windowDiscrepancy,
    ErdosProblems.Erdos249.PeriodMultipleEscape.ApFullDepthEscape,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.certifiedKill,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.windowDiscrepancy] using
    ErdosProblems.Erdos249.FullDepthRayAmplifier.apFullDepthEscape_iff_irrational

theorem cofinalFullDepthKillSupply_iff_periodMultipleKillSupply :
    CofinalFullDepthKillSupply ↔ PeriodMultipleKillSupply := by
  simpa [CofinalFullDepthKillSupply, PeriodMultipleKillSupply, certifiedKill,
    windowDiscrepancy,
    ErdosProblems.Erdos249.FullDepthRayAmplifier.CofinalFullDepthKillSupply,
    ErdosProblems.Erdos249.PeriodMultipleEscape.PeriodMultipleKillSupply,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.certifiedKill,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.windowDiscrepancy] using
    ErdosProblems.Erdos249.FullDepthRayAmplifier.cofinalFullDepthKillSupply_iff_periodMultipleKillSupply

theorem cofinalFullDepthKillSupply_iff_irrational :
    CofinalFullDepthKillSupply ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  simpa [CofinalFullDepthKillSupply, certifiedKill, windowDiscrepancy,
    ErdosProblems.Erdos249.FullDepthRayAmplifier.CofinalFullDepthKillSupply,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.certifiedKill,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.windowDiscrepancy] using
    ErdosProblems.Erdos249.FullDepthRayAmplifier.cofinalFullDepthKillSupply_iff_irrational

end PalomarCorpus.E249.FullDepthRayAmplifier

namespace PalomarCorpus.E249.MobiusMersenneLadderStructure
export PalomarCorpus.E249.Shared (mobiusMersenneTerm mobiusMersenneTheta)

open scoped BigOperators
open ArithmeticFunction

noncomputable def mobiusMersenneLambertRung (r : ℕ) : ℝ :=
  ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (r * (d : ℕ)) - 1)

private lemma theta_eq (r : ℕ) :
    mobiusMersenneTheta r =
      _root_.Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta r :=
  rfl

private lemma rung_eq (r : ℕ) :
    mobiusMersenneLambertRung r =
      _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.mobiusMersenneLambertRung r :=
  rfl

theorem mobiusMersenneTheta_no_linearRecurrence_of_eventually
    {m : ℕ} (c : Fin (m + 1) → ℝ) (n₀ : ℕ) (hc : ∃ k, c k ≠ 0)
    (hrec : ∀ n : ℕ, n₀ ≤ n →
      ∑ k : Fin (m + 1), c k * mobiusMersenneTheta (n + (k : ℕ)) = 0) : False := by
  refine _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.mobiusMersenneTheta_no_linearRecurrence_of_eventually
    c n₀ hc (fun n hn => ?_)
  simpa only [theta_eq] using hrec n hn

theorem mobiusMersenneTheta_no_linearRecurrence :
    ¬ ∃ (m : ℕ) (c : Fin (m + 1) → ℝ), (∃ k, c k ≠ 0) ∧
        ∀ n : ℕ, 1 ≤ n →
          ∑ k : Fin (m + 1), c k * mobiusMersenneTheta (n + (k : ℕ)) = 0 := by
  simpa only [theta_eq] using
    _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.mobiusMersenneTheta_no_linearRecurrence

theorem mobiusMersenneTheta_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) <
      mobiusMersenneTheta (r + 1) ^ 2 := by
  simpa only [theta_eq] using
    _root_.Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta_strict_logConcave
      r hr

theorem mobiusMersenneTheta_hankel_two_neg (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) -
      mobiusMersenneTheta (r + 1) ^ 2 < 0 := by
  simpa only [theta_eq] using
    _root_.Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta_hankel_two_neg
      r hr

theorem mobiusMersenneLambertRung_eq (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneLambertRung r = ((1 : ℝ) / 2) ^ r := by
  simpa only [rung_eq] using
    _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.mobiusMersenneLambertRung_eq r hr

theorem lambertRung_shifted_hankelDet_eq_zero (s N : ℕ) (hs : 1 ≤ s) (hN : 2 ≤ N) :
    Matrix.det (Matrix.of fun i j : Fin N =>
      mobiusMersenneLambertRung (s + (i : ℕ) + (j : ℕ))) = 0 := by
  simpa only [rung_eq] using
    _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.lambertRung_shifted_hankelDet_eq_zero
      s N hs hN

theorem mobiusMersenneTheta_ne_mobiusMersenneLambertRung :
    ¬ ∀ r : ℕ, 1 ≤ r → mobiusMersenneTheta r = mobiusMersenneLambertRung r := by
  simpa only [theta_eq, rung_eq] using
    _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.mobiusMersenneTheta_ne_mobiusMersenneLambertRung

end PalomarCorpus.E249.MobiusMersenneLadderStructure

namespace PalomarCorpus.E249.PrefixTwoAdicExclusion

set_option linter.unusedVariables false

noncomputable def totientPrefix (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 2 ^ (n - 1 - i) * Nat.totient (i + 1)
theorem totientPrefix_succ (n : ℕ) :
    totientPrefix (n + 1) = 2 * totientPrefix n + Nat.totient (n + 1) := by
  simpa [totientPrefix, ErdosProblems.Erdos249.totientPrefix] using
    ErdosProblems.Erdos249.totientPrefix_succ n

theorem totientPrefix_eq_corpusForm (n : ℕ) :
    totientPrefix n = ∑ i ∈ Finset.range (n + 1), Nat.totient i * 2 ^ (n - i) := by
  simpa [totientPrefix, ErdosProblems.Erdos249.totientPrefix] using
    ErdosProblems.Erdos249.totientPrefix_eq_corpusForm n

noncomputable def prefixTail (S : ℝ) (n : ℕ) : ℝ :=
  2 ^ n * S - (totientPrefix n : ℝ)

theorem oddPart_mul_prefixTail_eq_intCast
    {S : ℝ} {a : ℤ} {c v n : ℕ} (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ))) (hcn : c ≤ n) :
    (v : ℝ) * prefixTail S n
      = (((2 : ℤ) ^ (n - c) * a - (v : ℤ) * (totientPrefix n : ℤ) : ℤ) : ℝ) := by
  simpa [totientPrefix, prefixTail, ErdosProblems.Erdos249.totientPrefix,
      ErdosProblems.Erdos249.prefixTail] using
    ErdosProblems.Erdos249.oddPart_mul_prefixTail_eq_intCast hvpos hS hcn

theorem prefix_twoAdic_denominator_exclusion
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t ≤ (v : ℝ) * prefixTail S n := by
  simpa [totientPrefix, prefixTail, ErdosProblems.Erdos249.totientPrefix,
      ErdosProblems.Erdos249.prefixTail] using
    ErdosProblems.Erdos249.prefix_twoAdic_denominator_exclusion hvodd hvpos hS hpos hct hdvd

theorem prefix_twoAdic_denominator_lower_bound
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (htail : prefixTail S n ≤ (n : ℝ) + 2)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t ≤ (v : ℝ) * ((n : ℝ) + 2) := by
  simpa [totientPrefix, prefixTail, ErdosProblems.Erdos249.totientPrefix,
      ErdosProblems.Erdos249.prefixTail] using
    ErdosProblems.Erdos249.prefix_twoAdic_denominator_lower_bound
      hvodd hvpos hS hpos htail hct hdvd

theorem prefix_twoAdic_odd_denominator_floor
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (htail : prefixTail S n ≤ (n : ℝ) + 2)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t / ((n : ℝ) + 2) ≤ (v : ℝ) := by
  simpa [totientPrefix, prefixTail, ErdosProblems.Erdos249.totientPrefix,
      ErdosProblems.Erdos249.prefixTail] using
    ErdosProblems.Erdos249.prefix_twoAdic_odd_denominator_floor
      hvodd hvpos hS hpos htail hct hdvd

end PalomarCorpus.E249.PrefixTwoAdicExclusion

namespace PalomarCorpus.E249.RankOneSharpFloor
export PalomarCorpus.E249.Shared (mobiusMersenneTerm mobiusMersenneTheta)

open scoped BigOperators
open ArithmeticFunction

noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n

noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ :=
  mobiusMersennePrefix Y (e + 2) ^ 2 /
    mobiusMersennePrefix Y (2 * e + 2)

theorem rankOneSubrankQuotient_ge_one_five
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    rankOneSubrankQuotient 1 5 ≤ rankOneSubrankQuotient e Y := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_ge_one_five
      he hY

theorem rankOneSubrankQuotient_eq_one_five_iff
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    rankOneSubrankQuotient e Y = rankOneSubrankQuotient 1 5 ↔
      e = 1 ∧ Y = 5 := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_eq_one_five_iff
      he hY

theorem rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (21 : ℝ) / 320 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty
      he hY

theorem rankOneSubrankQuotient_sub_theta_two_gt_one_div_sixteen
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 16 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_sub_theta_two_gt_one_div_sixteen
      he hY

theorem not_forall_rankOneSubrankQuotient_sub_theta_two_gt_one_div_fifteen :
    ¬ ∀ {e Y : ℕ}, 1 ≤ e → 4 ≤ Y →
      (1 : ℝ) / 15 <
        rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.not_forall_rankOneSubrankQuotient_sub_theta_two_gt_one_div_fifteen

theorem positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (e Y : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < w i)
    (he : ∀ i ∈ s, 1 ≤ e i)
    (hY : ∀ i ∈ s, 4 ≤ Y i) :
    (21 : ℝ) / 320 <
      (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) /
          (∑ i ∈ s, w i) -
        mobiusMersenneTheta 2 := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty
      s hs w e Y hw he hY

theorem primitive_form_abs_gt_twentyOne_div_threeTwenty
    {e Y q : ℕ} {p : ℤ}
    (he : 1 ≤ e) (hY : 4 ≤ Y) (hq : 1 ≤ q)
    (hquot : rankOneSubrankQuotient e Y = (p : ℝ) / q) :
    (q : ℝ) * (21 : ℝ) / 320 <
      |(q : ℝ) * mobiusMersenneTheta 2 - p| := by
  have hquot' :
      ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient e Y =
        (p : ℝ) / q := by
    simpa [rankOneSubrankQuotient, mobiusMersennePrefix, mobiusMersenneTerm,
      ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
      ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
      Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using hquot
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.primitive_form_abs_gt_twentyOne_div_threeTwenty
      he hY hq hquot'

end PalomarCorpus.E249.RankOneSharpFloor

namespace PalomarCorpus.E249.ResidueClassTotientSeries

noncomputable def dyadicValue (a : ℕ → ℤ) : ℝ := ∑' n : ℕ, (a n : ℝ) / 2 ^ n

noncomputable def totientObservableValue (f : ℕ → ℤ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((f (Nat.totient n % m) : ℤ) : ℝ) / 2 ^ n

noncomputable def totientResidueValue (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((Nat.totient n % m : ℕ) : ℝ) / 2 ^ n

theorem isolated_pulse_separation {a : ℕ → ℤ} {C : ℝ} (hC : ∀ n, |(a n : ℝ)| ≤ C)
    {N L q : ℕ} {t : ℤ} (hq : 1 ≤ q) (hL : 2 * (q : ℝ) * C < 2 ^ L)
    (hcentre : a (N + 1 + L) = t) (ht : t ≠ 0)
    (hzero : ∀ i, i ≤ 2 * L → i ≠ L → a (N + 1 + i) = 0) (k : ℤ) :
    (q : ℝ) * (|(t : ℝ)| - C / 2 ^ L) / 2 ^ (N + 1 + L)
      ≤ |(q : ℝ) * dyadicValue a - (k : ℝ)| := by
  simpa only [dyadicValue, ErdosProblems.Erdos249.dyadicValue] using
    ErdosProblems.Erdos249.isolated_pulse_separation hC hq hL hcentre ht hzero k

theorem irrational_dyadicValue_of_pulses {a : ℕ → ℤ} {C : ℝ} (hC : ∀ n, |(a n : ℝ)| ≤ C)
    (hpulse : ∀ L : ℕ, ∃ p : ℕ, L + 1 < p ∧ a p ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (p - j) = 0 ∧ a (p + j) = 0) :
    Irrational (dyadicValue a) := by
  simpa only [dyadicValue, ErdosProblems.Erdos249.dyadicValue] using
    ErdosProblems.Erdos249.irrational_dyadicValue_of_pulses hC hpulse

theorem two_sided_prime_isolation {m : ℕ} (hm : 2 ≤ m) (L N r : ℕ)
    (hr : Nat.Coprime (r + 1) m) :
    ∃ p : ℕ, N < p ∧ L + 1 < p ∧ p.Prime ∧ Nat.totient p ≡ r [MOD m] ∧
      ∀ j, 0 < j → j ≤ L → m ∣ Nat.totient (p - j) ∧ m ∣ Nat.totient (p + j) :=
  ErdosProblems.Erdos249.two_sided_prime_isolation hm L N r hr

theorem irrational_totientObservable {m : ℕ} (hm : 2 ≤ m) (f : ℕ → ℤ) (hf0 : f 0 = 0)
    {r : ℕ} (hr : r < m) (hcop : Nat.Coprime (r + 1) m) (hfr : f r ≠ 0) :
    Irrational (totientObservableValue f m) := by
  simpa only [totientObservableValue,
    ErdosProblems.Erdos249.totientObservableValue] using
    ErdosProblems.Erdos249.irrational_totientObservable hm f hf0 hr hcop hfr

theorem fixed_resolution_observable_irrational {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℤ)
    (hf0 : f 0 = 0) {r : ℕ} (hr : r < 2 ^ k) (hreven : r % 2 = 0) (hfr : f r ≠ 0) :
    Irrational (totientObservableValue f (2 ^ k)) := by
  simpa only [totientObservableValue,
    ErdosProblems.Erdos249.totientObservableValue] using
    ErdosProblems.Erdos249.fixed_resolution_observable_irrational hk f hf0 hr hreven hfr

theorem residue_series_irrational {m : ℕ} (hm : 3 ≤ m) :
    Irrational (totientResidueValue m) := by
  simpa only [totientResidueValue,
    ErdosProblems.Erdos249.totientResidueValue] using
    ErdosProblems.Erdos249.residue_series_irrational hm

end PalomarCorpus.E249.ResidueClassTotientSeries

namespace PalomarCorpus.E249.TermwiseDyadicVacuous

set_option linter.unusedVariables false

theorem termwise_dyadic_window_vacuous
    {N t v : ℕ} (ht : 1 ≤ t) (hNt : 2 ≤ N + t) (hv : 1 ≤ v)
    (hdvd : 2 ^ t ∣ Nat.totient (N + t)) :
    2 ^ t ≤ v * (N + t + 2) :=
  ErdosProblems.Erdos249.termwise_dyadic_window_vacuous ht hNt hv hdvd

end PalomarCorpus.E249.TermwiseDyadicVacuous

namespace PalomarCorpus.E249.TotientKernelBasis

open Module

theorem allSlopeAffineTotientFormsLinearIndependent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i) :
    LinearIndependent ℚ (fun (i : ι) (n : ℕ) => (Nat.totient (a i * n + b i) : ℚ)) :=
  Erdos257PeriodNoncollapse.linearIndependent_totientAffineForms a b ha hb hcross

noncomputable def kernelSeq (k j r : ℕ) : ℕ → ℚ := fun n =>
  (Nat.totient (k ^ j * n + r) : ℚ)
noncomputable abbrev CanonicalIndex (k e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)
noncomputable def canonicalResidue (k : ℕ) {e : ℕ}
    (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) : ℕ :=
  k * x.2.1.val + (x.2.2.val + 1)
noncomputable def canonicalFamily (k e : ℕ) : CanonicalIndex k e → ℕ → ℚ
  | Sum.inl i => kernelSeq k i.val 0
  | Sum.inr x => kernelSeq k (x.1.val + 1) (canonicalResidue k x)
noncomputable abbrev ThroughLevelIndex (k e : ℕ) := Σ j : Fin (e + 1), Fin (k ^ j.val)
noncomputable def throughLevelFamily (k e : ℕ) : ThroughLevelIndex k e → ℕ → ℚ
  | ⟨j, r⟩ => kernelSeq k j.val r.val
noncomputable def relationMap (k e : ℕ) :
    (ThroughLevelIndex k e → ℚ) →ₗ[ℚ] (ℕ → ℚ) :=
  Fintype.linearCombination ℚ (throughLevelFamily k e)

theorem kernelSeq_eq (k j r : ℕ) :
    kernelSeq k j r = Erdos257PeriodNoncollapse.allBaseTotientKernelSeq k j r := rfl

theorem canonicalResidue_eq (k : ℕ) {e : ℕ}
    (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) :
    canonicalResidue k x = Erdos257PeriodNoncollapse.allBaseCanonicalResidue k x := rfl

theorem canonicalFamily_eq (k e : ℕ) :
    canonicalFamily k e = Erdos257PeriodNoncollapse.allBaseCanonicalFamily k e := by
  funext i
  cases i with
  | inl i => rfl
  | inr x => rfl

theorem throughLevelFamily_eq (k e : ℕ) :
    throughLevelFamily k e = Erdos257PeriodNoncollapse.allBaseThroughLevelFamily k e := by
  funext x
  rcases x with ⟨j, r⟩
  rfl

theorem relationMap_eq (k e : ℕ) :
    relationMap k e = Erdos257PeriodNoncollapse.allBaseRelationMap k e := by
  simp only [relationMap, Erdos257PeriodNoncollapse.allBaseRelationMap,
    throughLevelFamily_eq]

theorem allBaseTotientKernelBasisRankAndRelationDimension
    (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    LinearIndependent ℚ (canonicalFamily k e) ∧
      Submodule.span ℚ (Set.range (throughLevelFamily k e)) =
        Submodule.span ℚ (Set.range (canonicalFamily k e)) ∧
      Nonempty (Basis (CanonicalIndex k e) ℚ
        (Submodule.span ℚ (Set.range (throughLevelFamily k e)))) ∧
      finrank ℚ (Submodule.span ℚ (Set.range (throughLevelFamily k e))) =
        k ^ e + 1 ∧
      finrank ℚ (LinearMap.ker (relationMap k e)) =
        ∑ j ∈ Finset.Ico 1 e, k ^ j := by
  rw [canonicalFamily_eq, throughLevelFamily_eq, relationMap_eq]
  exact ⟨Erdos257PeriodNoncollapse.linearIndependent_allBaseCanonicalFamily k e hk,
    Erdos257PeriodNoncollapse.span_allBaseThroughLevelFamily_eq k e hk he,
    ⟨Erdos257PeriodNoncollapse.allBaseTotientKernelBasis k e hk he⟩,
    Erdos257PeriodNoncollapse.finrank_allBaseThroughLevelFamily_eq k e hk he,
    Erdos257PeriodNoncollapse.finrank_allBaseRelationModule_eq k e hk he⟩

end PalomarCorpus.E249.TotientKernelBasis

namespace PalomarCorpus.E249.TotientRigidity

noncomputable def totientDefect (g : ℕ → ℤ) (n : ℕ) : ℤ := g n - (Nat.totient n : ℤ)
theorem totient_prime_mul_of_dvd {p n : ℕ} (hp : p.Prime) (h : p ∣ n) :
    (Nat.totient (p * n) : ℤ) = (p : ℤ) * (Nat.totient n : ℤ) :=
  ErdosProblems.Erdos249.totient_prime_mul_of_dvd hp h

theorem totient_prime_mul_of_not_dvd {p n : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) :
    (Nat.totient (p * n) : ℤ) = ((p : ℤ) - 1) * (Nat.totient n : ℤ) :=
  ErdosProblems.Erdos249.totient_prime_mul_of_not_dvd hp h

theorem totient_two_mul_of_odd {m : ℕ} (hm : Odd m) :
    Nat.totient (2 * m) = Nat.totient m :=
  ErdosProblems.Erdos249.totient_two_mul_of_odd hm

theorem totient_two_mul_of_even {m : ℕ} (hm : Even m) :
    Nat.totient (2 * m) = 2 * Nat.totient m :=
  ErdosProblems.Erdos249.totient_two_mul_of_even hm

theorem one_prime_law_and_little_o_forces_totient
    {p : ℕ} (hp : p.Prime) {g : ℕ → ℤ}
    (hlaw_not_dvd : ∀ n : ℕ, 1 ≤ n → ¬ p ∣ n → g (p * n) = ((p : ℤ) - 1) * g n)
    (hlaw_dvd : ∀ n : ℕ, 1 ≤ n → p ∣ n → g (p * n) = (p : ℤ) * g n)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |(g n : ℝ) - (Nat.totient n : ℝ)| ≤ ε * (n : ℝ))
    {n : ℕ} (hn : 1 ≤ n) :
    g n = (Nat.totient n : ℤ) :=
  ErdosProblems.Erdos249.one_prime_law_and_little_o_forces_totient
    hp hlaw_not_dvd hlaw_dvd hsmall hn

theorem even_law_and_eventual_congruence_forces_totient
    {g : ℕ → ℤ}
    (hodd : ∀ m : ℕ, Odd m → 1 ≤ m → g (2 * m) = g m)
    (heven : ∀ m : ℕ, Even m → 2 ≤ m → g (2 * m) = 2 * g m)
    (hcong : ∀ q : ℕ, 1 ≤ q → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (q : ℤ) ∣ totientDefect g n)
    {n : ℕ} (hn : 1 ≤ n) :
    g n = (Nat.totient n : ℤ) := by
  simpa [totientDefect, ErdosProblems.Erdos249.totientDefect] using
    ErdosProblems.Erdos249.even_law_and_eventual_congruence_forces_totient
      hodd heven hcong hn

end PalomarCorpus.E249.TotientRigidity
