/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
/-! Palomar challenge for Erdős problem #249. Parent problem remains open. See `PalomarCorpus/README.md`. -/
namespace PalomarCorpus.E249.Shared
noncomputable abbrev TotientCanonicalIndex (e : ℕ) := Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)
noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ := ((moebius (n + 1) : ℤ) : ℝ) / (((2 : ℝ) ^ (n + 1) - 1) ^ r) /-- The Möbius–Mersenne power ladder `Θᵣ = ∑_{d ≥ 1} μ(d) / (2^d - 1)^r`. -/
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ := ∑' n : ℕ, mobiusMersenneTerm r n /-- The literal Möbius–Lambert rung `Θ̂ᵣ = ∑_{d ≥ 1} μ(d) / (2^(r·d) - 1)`. -/
noncomputable def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n => Nat.totient (2 ^ j * n + r)
noncomputable def canonicalTotientKernelFamily (e : ℕ) : TotientCanonicalIndex e → ℕ → ℚ | Sum.inl i => totientKernelSeq i.val 0 | Sum.inr ⟨j, r⟩ => totientKernelSeq (j.val + 1) (2 * r.val + 1)
noncomputable def totientTail (N : ℕ) : ℝ := ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1) /-- The integer prefix of the scaled binary totient series. -/
def windowDiscrepancy (h N L : ℕ) : ℤ := ∑ j ∈ Finset.range L, ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
def certifiedKill (h N L : ℕ) : Prop := (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧ windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
end PalomarCorpus.E249.Shared
namespace PalomarCorpus.E249.ActualLcmOrbit
open scoped BigOperators
export PalomarCorpus.E249.Shared (totientTail)
def periodLcm : ℕ → ℕ | 0 => 1 | t + 1 => Nat.lcm (periodLcm t) (t + 1) /-- The local binary totient tail. -/
def totientPrefix (N : ℕ) : ℕ := ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n) /-- The actual LCM height at the power-two endpoint `2^a`. -/
def actualLcmHeight (a : ℕ) : ℕ := periodLcm (2 ^ a) /-- The actual power-two LCM-diagonal tail orbit. -/
noncomputable def actualLcmTailOrbit (a : ℕ) : ℝ := totientTail (2 * actualLcmHeight a) - totientTail (actualLcmHeight a) /-- Cofinal non-integrality of the actual LCM-diagonal orbit. -/
def PowerTwoActualLcmOrbitNonintegralitySupply : Prop := ∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧ actualLcmTailOrbit a ∉ Set.range ((↑) : ℤ → ℝ) /-- The actual orbit is an integer translate of a scaled copy of the target. -/
theorem actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix (a : ℕ) : actualLcmTailOrbit a = (2 : ℝ) ^ actualLcmHeight a * ((2 : ℝ) ^ actualLcmHeight a - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - ((totientPrefix (2 * actualLcmHeight a) : ℝ) - (totientPrefix (actualLcmHeight a) : ℝ)) := by sorry
theorem irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔ PowerTwoActualLcmOrbitNonintegralitySupply := by sorry
end PalomarCorpus.E249.ActualLcmOrbit
namespace PalomarCorpus.E249.BinaryCyclotomicAnchors
open scoped BigOperators
export PalomarCorpus.E249.Shared (certifiedKill totientTail windowDiscrepancy)
noncomputable def binaryCyclotomicLayer (n : ℕ) : ℕ := ((Polynomial.cyclotomic n ℤ).eval (2 : ℤ)).natAbs
def UnboundedPrimeDivisorSupply (C : ℕ → ℕ) (h : ℕ) : Prop := ∀ B N₀ : ℕ, ∃ q p : ℕ, q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (h * q) ∧ B < p
def CyclotomicAnchoredKillSupply (C : ℕ → ℕ) : Prop := ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ q p L : ℕ, q.Prime ∧ p.Prime ∧ Nat.Coprime p (h * q) ∧ p ∣ C (h * q) ∧ h * q ∣ p - 1 ∧ N₀ ≤ p - 1 ∧ certifiedKill (h * q) (p - 1) L
theorem exists_clean_binaryCyclotomicAnchor (h N₀ : ℕ) (hh : 0 < h) : ∃ q p : ℕ, q.Prime ∧ p.Prime ∧ Nat.Coprime p (h * q) ∧ p ∣ binaryCyclotomicLayer (h * q) ∧ h * q ∣ p - 1 ∧ N₀ ≤ p - 1 := by sorry
theorem binaryCyclotomicLayer_unboundedPrimeDivisorSupply (h : ℕ) (hh : 0 < h) : UnboundedPrimeDivisorSupply binaryCyclotomicLayer h := by sorry
theorem binaryCyclotomicAnchoredKillSupply_iff_irrational : CyclotomicAnchoredKillSupply binaryCyclotomicLayer ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by sorry
theorem exists_unbounded_binaryCyclotomicSupport_with_periodLock_of_not_irrational (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) : ∃ h : ℕ, 0 < h ∧ UnboundedPrimeDivisorSupply binaryCyclotomicLayer h ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by sorry
end PalomarCorpus.E249.BinaryCyclotomicAnchors
namespace PalomarCorpus.E249.CanonicalMersenneFrontier
open scoped BigOperators
def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
def totientBlock (H N : ℕ) : ℤ := ∑ j ∈ Finset.range H, (Nat.totient (N + 1 + j) : ℤ) * 2 ^ (H - 1 - j)
def fullMersenneBlockResidue (H N M : ℕ) : ℤ := (-totientBlock H N) % (M : ℤ)
def FullMersenneCenteredResidueGap (H N M : ℕ) : Prop := let B : ℤ := N + H + 1 B < fullMersenneBlockResidue H N M ∧ fullMersenneBlockResidue H N M < (M : ℤ) - B
def FullMersenneCenteredResidueGapSupply : Prop := ∀ c v : ℕ, 0 < v → Nat.Coprime 2 v → ∀ N₀ : ℕ, ∃ H N M : ℕ, 0 < H ∧ Nat.totient v ∣ H ∧ max c N₀ ≤ N ∧ v * M = 2 ^ H - 1 ∧ FullMersenneCenteredResidueGap H N M
def FullMersenneCanonicalBasepointResidueGapSupply : Prop := ∀ c v : ℕ, 0 < v → Nat.Coprime 2 v → ∃ H M : ℕ, 0 < H ∧ Nat.totient v ∣ H ∧ v * M = 2 ^ H - 1 ∧ FullMersenneCenteredResidueGap H c M
theorem fullMersenneBlockResidue_succ {H N M : ℕ} (hM : M ∣ 2 ^ H - 1) : fullMersenneBlockResidue H (N + 1) M = (2 * fullMersenneBlockResidue H N M - deltaTotient H (N + 1)) % (M : ℤ) := by sorry
theorem fullMersenneCenteredResidueGapSupply_of_canonicalBasepoint (hsupply : FullMersenneCanonicalBasepointResidueGapSupply) : FullMersenneCenteredResidueGapSupply := by sorry
theorem fullMersenneCanonicalBasepointResidueGapSupply_iff_irrational : FullMersenneCanonicalBasepointResidueGapSupply ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by sorry
end PalomarCorpus.E249.CanonicalMersenneFrontier
namespace PalomarCorpus.E249.CarryRankFrontier
export PalomarCorpus.E249.Shared (TotientCanonicalIndex canonicalTotientKernelFamily totientKernelSeq totientTail)
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ := ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)
def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop := (∀ N : ℕ, u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧ Filter.Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) Filter.atTop (nhds 0)
def carryKernelSeq (u : ℕ → ℤ) (j r : ℕ) : ℕ → ℚ := fun n => u (2 ^ j * n + r)
abbrev TotientCarryIndex (e : ℕ) := Σ j : Fin e, Fin (2 ^ (j.val + 1))
def canonicalCarryKernelFamily (u : ℕ → ℤ) (e : ℕ) : TotientCarryIndex e → ℕ → ℚ | ⟨j, r⟩ => carryKernelSeq u (j.val + 1) r.val
structure SeparatedMinorCertificate {ι : Type*} [Fintype ι] [DecidableEq ι] (family : ι → ℕ → ℚ) where rowIndex : ι → ℕ det_ne_zero : Matrix.det (fun i j : ι => family j (rowIndex i)) ≠ 0
def CarrySectionsEventuallyPeriodicMod (v h N₀ : ℕ) (u : ℕ → ℤ) : Prop := ∀ j r n : ℕ, N₀ ≤ n → u (2 ^ j * n + r) ≡ u (2 ^ j * (n + h) + r) [ZMOD (v : ℤ)] /-- Subexponential binary coefficient tails are non-irrational exactly when they admit a positive-multiplier integral tempered orbit. -/
theorem not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) : ¬ Irrational (binaryCoeffSeries c) ↔ ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u := by sorry
theorem totient_carryKernel_diff {v : ℕ} {u : ℕ → ℤ} (hu : IsTemperedBinaryOrbit Nat.totient v u) {j r : ℕ} (hr : 0 < r) : (fun n => (v : ℚ) * totientKernelSeq j r n) = fun n => 2 * carryKernelSeq u j (r - 1) n - carryKernelSeq u j r n := by sorry
theorem finrank_canonicalCarryKernel_ge_of_certificate {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v) (hu : IsTemperedBinaryOrbit Nat.totient v u) (e : ℕ) (cert : SeparatedMinorCertificate (canonicalTotientKernelFamily e)) : 2 ^ e - 1 ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) := by sorry
theorem not_irrational_totientSeries_implies_unbounded_carryRank_unconditional (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) : ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit Nat.totient v u ∧ ∀ e : ℕ, 2 ^ e - 1 ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) := by sorry
theorem carryShift_dvd_iff_tailDiff_mem_int {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v) (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ) : (v : ℤ) ∣ u (N + k) - u N ↔ totientTail (N + k) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by sorry
theorem not_irrational_totientSeries_implies_mod_period_and_unbounded_rank (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) : ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit Nat.totient v u ∧ (∀ e : ℕ, 2 ^ e - 1 ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e)))) ∧ ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, CarrySectionsEventuallyPeriodicMod v h N₀ u := by sorry
end PalomarCorpus.E249.CarryRankFrontier
namespace PalomarCorpus.E249.DyadicTotientKernel
open Module
export PalomarCorpus.E249.Shared (TotientCanonicalIndex canonicalTotientKernelFamily totientKernelSeq)
abbrev TotientKernelThroughLevelIndex (e : ℕ) := Σ j : Fin (e + 1), Fin (2 ^ j.val) /-- The complete finite dyadic kernel through level `e`. -/
def totientKernelThroughLevelFamily (e : ℕ) : TotientKernelThroughLevelIndex e → ℕ → ℚ | ⟨j, r⟩ => totientKernelSeq j.val r.val /-- All canonical dyadic sections. -/
abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)
def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ | ⟨j, r⟩ => totientKernelSeq j r.val /-- The two zero-residue base channels and one odd residue per positive level. -/
abbrev TotientOddCoreIndex := Fin 2 ⊕ Σ j : ℕ, Fin (2 ^ j)
def oddCoreTotientKernelFamily : TotientOddCoreIndex → ℕ → ℚ | Sum.inl i => totientKernelSeq i.val 0 | Sum.inr ⟨j, r⟩ => totientKernelSeq (j + 1) (2 * r.val + 1) /-- The odd-core sections form the complete independent spanning family, and the unreduced finite kernel through level `e` has exact rank `2^e+1`. -/
theorem dyadicTotientKernelOddCoreBasisAndFiniteRanks : LinearIndependent ℚ oddCoreTotientKernelFamily ∧ Submodule.span ℚ (Set.range fullTotientKernelFamily) = Submodule.span ℚ (Set.range oddCoreTotientKernelFamily) ∧ ∀ e : ℕ, 1 ≤ e → Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)) = Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e)) ∧ finrank ℚ (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) = 2 ^ e + 1 := by sorry
end PalomarCorpus.E249.DyadicTotientKernel
namespace PalomarCorpus.E249.FareyWindowExclusion
def fareyDenBound : ℕ := 79639646646701375323355774875831053
theorem farey_int_exclusion : ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ fareyDenBound → (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (a : ℝ) / (d : ℝ) := by sorry
theorem farey_rat_exclusion : ∀ p : ℚ, p.den ≤ fareyDenBound → (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ) := by sorry
end PalomarCorpus.E249.FareyWindowExclusion
namespace PalomarCorpus.E249.FullDepthRayAmplifier
open scoped BigOperators
export PalomarCorpus.E249.Shared (certifiedKill totientTail windowDiscrepancy)
def PeriodMultipleKillSupply : Prop := ∀ d : ℕ, 0 < d → ∀ c : ℕ, ∃ t N L : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N L
def ApFullDepthEscape : Prop := ∀ d : ℕ, 0 < d → ∀ N : ℕ, ∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)
def fullDepthKillMultipliers (d N : ℕ) : Set ℕ := {t | certifiedKill (t * d) N (t * d)}
def CofinalFullDepthKillSupply : Prop := ∀ d : ℕ, 0 < d → ∀ c : ℕ, ∃ t N : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N (t * d)
theorem eventually_twoSyndetic_fullDepthKillMultipliers_of_seed {d N L : ℕ} (hd : 0 < d) (hseed : certifiedKill d N L) : ∃ T : ℕ, 0 < T ∧ ∀ t : ℕ, T ≤ t → ∃ m : ℕ, m ∈ fullDepthKillMultipliers d N ∧ t ≤ m ∧ m ≤ t + 1 := by sorry
theorem exists_fullDepthKill_on_ray_iff_shift_notMem_int {d N : ℕ} (hd : 0 < d) : (∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔ totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by sorry
theorem apFullDepthEscape_iff_irrational : ApFullDepthEscape ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by sorry
theorem cofinalFullDepthKillSupply_iff_periodMultipleKillSupply : CofinalFullDepthKillSupply ↔ PeriodMultipleKillSupply := by sorry
theorem cofinalFullDepthKillSupply_iff_irrational : CofinalFullDepthKillSupply ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by sorry
end PalomarCorpus.E249.FullDepthRayAmplifier
namespace PalomarCorpus.E249.MobiusMersenneLadderStructure
open scoped BigOperators
export PalomarCorpus.E249.Shared (mobiusMersenneTerm mobiusMersenneTheta)
theorem mobiusMersenneTheta_strict_logConcave (r : ℕ) (hr : 1 ≤ r) : mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) < mobiusMersenneTheta (r + 1) ^ 2 := by sorry
theorem mobiusMersenneTheta_hankel_two_neg (r : ℕ) (hr : 1 ≤ r) : mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) - mobiusMersenneTheta (r + 1) ^ 2 < 0 := by sorry
end PalomarCorpus.E249.MobiusMersenneLadderStructure
namespace PalomarCorpus.E249.PrefixTwoAdicExclusion
def totientPrefix (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, 2 ^ (n - 1 - i) * Nat.totient (i + 1) /-- The defining recurrence `P_{n+1} = 2 P_n + φ(n+1)`. -/
theorem totientPrefix_succ (n : ℕ) : totientPrefix (n + 1) = 2 * totientPrefix n + Nat.totient (n + 1) := by sorry
theorem totientPrefix_eq_corpusForm (n : ℕ) : totientPrefix n = ∑ i ∈ Finset.range (n + 1), Nat.totient i * 2 ^ (n - i) := by sorry
noncomputable def prefixTail (S : ℝ) (n : ℕ) : ℝ := 2 ^ n * S - (totientPrefix n : ℝ) /-- Under `S = a / (2^c v)` and `c ≤ n`, the rescaled tail `v·R_n` is an integer. -/
theorem oddPart_mul_prefixTail_eq_intCast {S : ℝ} {a : ℤ} {c v n : ℕ} (hvpos : 0 < v) (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ))) (hcn : c ≤ n) : (v : ℝ) * prefixTail S n = (((2 : ℤ) ^ (n - c) * a - (v : ℤ) * (totientPrefix n : ℤ) : ℤ) : ℝ) := by sorry
theorem prefix_twoAdic_denominator_exclusion {S : ℝ} {a : ℤ} {c v n t : ℕ} (hvodd : Odd v) (hvpos : 0 < v) (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ))) (hpos : 0 < prefixTail S n) (hct : c + t ≤ n) (hdvd : 2 ^ t ∣ totientPrefix n) : (2 : ℝ) ^ t ≤ (v : ℝ) * prefixTail S n := by sorry
theorem prefix_twoAdic_denominator_lower_bound {S : ℝ} {a : ℤ} {c v n t : ℕ} (hvodd : Odd v) (hvpos : 0 < v) (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ))) (hpos : 0 < prefixTail S n) (htail : prefixTail S n ≤ (n : ℝ) + 2) (hct : c + t ≤ n) (hdvd : 2 ^ t ∣ totientPrefix n) : (2 : ℝ) ^ t ≤ (v : ℝ) * ((n : ℝ) + 2) := by sorry
theorem prefix_twoAdic_odd_denominator_floor {S : ℝ} {a : ℤ} {c v n t : ℕ} (hvodd : Odd v) (hvpos : 0 < v) (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ))) (hpos : 0 < prefixTail S n) (htail : prefixTail S n ≤ (n : ℝ) + 2) (hct : c + t ≤ n) (hdvd : 2 ^ t ∣ totientPrefix n) : (2 : ℝ) ^ t / ((n : ℝ) + 2) ≤ (v : ℝ) := by sorry
end PalomarCorpus.E249.PrefixTwoAdicExclusion
namespace PalomarCorpus.E249.RankOneSharpFloor
open scoped BigOperators
export PalomarCorpus.E249.Shared (mobiusMersenneTerm mobiusMersenneTheta)
noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ := ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n /-- The positive rank-one strict-subrank quotient. -/
noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ := mobiusMersennePrefix Y (e + 2) ^ 2 / mobiusMersennePrefix Y (2 * e + 2) /-- The five-atom first-depth kernel minimises the admissible quotient. -/
theorem rankOneSubrankQuotient_ge_one_five {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) : rankOneSubrankQuotient 1 5 ≤ rankOneSubrankQuotient e Y := by sorry
theorem rankOneSubrankQuotient_eq_one_five_iff {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) : rankOneSubrankQuotient e Y = rankOneSubrankQuotient 1 5 ↔ e = 1 ∧ Y = 5 := by sorry
theorem rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) : (21 : ℝ) / 320 < rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by sorry
theorem rankOneSubrankQuotient_sub_theta_two_gt_one_div_sixteen {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) : (1 : ℝ) / 16 < rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by sorry
theorem not_forall_rankOneSubrankQuotient_sub_theta_two_gt_one_div_fifteen : ¬ ∀ {e Y : ℕ}, 1 ≤ e → 4 ≤ Y → (1 : ℝ) / 15 < rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by sorry
theorem positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ) (e Y : ι → ℕ) (hw : ∀ i ∈ s, 0 < w i) (he : ∀ i ∈ s, 1 ≤ e i) (hY : ∀ i ∈ s, 4 ≤ Y i) : (21 : ℝ) / 320 < (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) / (∑ i ∈ s, w i) - mobiusMersenneTheta 2 := by sorry
theorem primitive_form_abs_gt_twentyOne_div_threeTwenty {e Y q : ℕ} {p : ℤ} (he : 1 ≤ e) (hY : 4 ≤ Y) (hq : 1 ≤ q) (hquot : rankOneSubrankQuotient e Y = (p : ℝ) / q) : (q : ℝ) * (21 : ℝ) / 320 < |(q : ℝ) * mobiusMersenneTheta 2 - p| := by sorry
end PalomarCorpus.E249.RankOneSharpFloor
namespace PalomarCorpus.E249.ResidueClassTotientSeries
noncomputable def dyadicValue (a : ℕ → ℤ) : ℝ := ∑' n : ℕ, (a n : ℝ) / 2 ^ n /-- The binary value of a fixed-resolution observable of the totient word. -/
noncomputable def totientObservableValue (f : ℕ → ℤ) (m : ℕ) : ℝ := ∑' n : ℕ, ((f (Nat.totient n % m) : ℤ) : ℝ) / 2 ^ n /-- `A_m = ∑_{n} (φ n mod m) / 2 ^ n`, least nonnegative residues. -/
noncomputable def totientResidueValue (m : ℕ) : ℝ := ∑' n : ℕ, ((Nat.totient n % m : ℕ) : ℝ) / 2 ^ n /-- **Isolated pulse separation.**  A bounded integer sequence with a nonzero letter `t` at `p = N + 1 + L` and a two-sided block of `L` zeros around it keeps `q * dyadicValue a` at an explicit distance from every integer. -/
theorem isolated_pulse_separation {a : ℕ → ℤ} {C : ℝ} (hC : ∀ n, |(a n : ℝ)| ≤ C) {N L q : ℕ} {t : ℤ} (hq : 1 ≤ q) (hL : 2 * (q : ℝ) * C < 2 ^ L) (hcentre : a (N + 1 + L) = t) (ht : t ≠ 0) (hzero : ∀ i, i ≤ 2 * L → i ≠ L → a (N + 1 + i) = 0) (k : ℤ) : (q : ℝ) * (|(t : ℝ)| - C / 2 ^ L) / 2 ^ (N + 1 + L) ≤ |(q : ℝ) * dyadicValue a - (k : ℝ)| := by sorry
theorem irrational_dyadicValue_of_pulses {a : ℕ → ℤ} {C : ℝ} (hC : ∀ n, |(a n : ℝ)| ≤ C) (hpulse : ∀ L : ℕ, ∃ p : ℕ, L + 1 < p ∧ a p ≠ 0 ∧ ∀ j, 0 < j → j ≤ L → a (p - j) = 0 ∧ a (p + j) = 0) : Irrational (dyadicValue a) := by sorry
theorem two_sided_prime_isolation {m : ℕ} (hm : 2 ≤ m) (L N r : ℕ) (hr : Nat.Coprime (r + 1) m) : ∃ p : ℕ, N < p ∧ L + 1 < p ∧ p.Prime ∧ Nat.totient p ≡ r [MOD m] ∧ ∀ j, 0 < j → j ≤ L → m ∣ Nat.totient (p - j) ∧ m ∣ Nat.totient (p + j) := by sorry
theorem irrational_totientObservable {m : ℕ} (hm : 2 ≤ m) (f : ℕ → ℤ) (hf0 : f 0 = 0) {r : ℕ} (hr : r < m) (hcop : Nat.Coprime (r + 1) m) (hfr : f r ≠ 0) : Irrational (totientObservableValue f m) := by sorry
theorem fixed_resolution_observable_irrational {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℤ) (hf0 : f 0 = 0) {r : ℕ} (hr : r < 2 ^ k) (hreven : r % 2 = 0) (hfr : f r ≠ 0) : Irrational (totientObservableValue f (2 ^ k)) := by sorry
theorem residue_series_irrational {m : ℕ} (hm : 3 ≤ m) : Irrational (totientResidueValue m) := by sorry
end PalomarCorpus.E249.ResidueClassTotientSeries
namespace PalomarCorpus.E249.TermwiseDyadicVacuous
theorem termwise_dyadic_window_vacuous {N t v : ℕ} (ht : 1 ≤ t) (hNt : 2 ≤ N + t) (hv : 1 ≤ v) (hdvd : 2 ^ t ∣ Nat.totient (N + t)) : 2 ^ t ≤ v * (N + t + 2) := by sorry
end PalomarCorpus.E249.TermwiseDyadicVacuous
namespace PalomarCorpus.E249.TotientKernelBasis
open Module
theorem allSlopeAffineTotientFormsLinearIndependent {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i) : LinearIndependent ℚ (fun (i : ι) (n : ℕ) => (Nat.totient (a i * n + b i) : ℚ)) := by sorry
def kernelSeq (k j r : ℕ) : ℕ → ℚ := fun n => (Nat.totient (k ^ j * n + r) : ℚ) /-- The canonical level-`e` index: two zero-residue base channels, and one channel per canonical residue at each level `1, …, e`.  A canonical residue at level `j + 1` is written `k * s + (u + 1)` with `s < k^j` and `u < k - 1`, which is exactly the parametrisation of `1 ≤ r < k^(j+1)` with `k ∤ r`. -/
abbrev CanonicalIndex (k e : ℕ) := Fin 2 ⊕ Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1) /-- The canonical residue `k * s + (u + 1)` named by a positive-level index. -/
def canonicalResidue (k : ℕ) {e : ℕ} (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) : ℕ := k * x.2.1.val + (x.2.2.val + 1) /-- The canonical level-`e` family of base-`k` totient channels. -/
def canonicalFamily (k e : ℕ) : CanonicalIndex k e → ℕ → ℚ | Sum.inl i => kernelSeq k i.val 0 | Sum.inr x => kernelSeq k (x.1.val + 1) (canonicalResidue k x) /-- The complete base-`k` kernel index through level `e`, before any reduction: every pair `(j, r)` with `j ≤ e` and `r < k^j`. -/
abbrev ThroughLevelIndex (k e : ℕ) := Σ j : Fin (e + 1), Fin (k ^ j.val) /-- Every base-`k` section `n ↦ φ(k^j n + r)` at levels `0, …, e`. -/
def throughLevelFamily (k e : ℕ) : ThroughLevelIndex k e → ℕ → ℚ | ⟨j, r⟩ => kernelSeq k j.val r.val /-- Evaluation of a formal `ℚ`-combination of the symbols `E_{j,r}`, `j ≤ e`, `r < k^j`, at the corresponding kernel channels.  Its kernel is the module of `ℚ`-linear relations among the unreduced level-`e` channels. -/
noncomputable def relationMap (k e : ℕ) : (ThroughLevelIndex k e → ℚ) →ₗ[ℚ] (ℕ → ℚ) := Fintype.linearCombination ℚ (throughLevelFamily k e) /-- **The all-base totient kernel structure theorem.**  For every integer base `k ≥ 2` and every depth `e ≥ 1`: 1. the canonical family is `ℚ`-linearly independent; 2. it spans the whole unreduced level-`e` kernel; 3. it therefore indexes a basis of that span; 4. the span has dimension exactly `k^e + 1`; 5. the relation module has dimension exactly `∑_{1 ≤ j < e} k^j`. Part 5 is the complement of part 4 inside the `∑_{j ≤ e} k^j` unreduced channels.  It states the dimension of the relation space only; it does not assert that any particular family of relations generates it. -/
theorem allBaseTotientKernelBasisRankAndRelationDimension (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) : LinearIndependent ℚ (canonicalFamily k e) ∧ Submodule.span ℚ (Set.range (throughLevelFamily k e)) = Submodule.span ℚ (Set.range (canonicalFamily k e)) ∧ Nonempty (Basis (CanonicalIndex k e) ℚ (Submodule.span ℚ (Set.range (throughLevelFamily k e)))) ∧ finrank ℚ (Submodule.span ℚ (Set.range (throughLevelFamily k e))) = k ^ e + 1 ∧ finrank ℚ (LinearMap.ker (relationMap k e)) = ∑ j ∈ Finset.Ico 1 e, k ^ j := by sorry
end PalomarCorpus.E249.TotientKernelBasis
namespace PalomarCorpus.E249.TotientRigidity
def totientDefect (g : ℕ → ℤ) (n : ℕ) : ℤ := g n - (Nat.totient n : ℤ) /-- `φ(pn) = p φ(n)` when `p` is prime and `p ∣ n`. -/
theorem totient_prime_mul_of_dvd {p n : ℕ} (hp : p.Prime) (h : p ∣ n) : (Nat.totient (p * n) : ℤ) = (p : ℤ) * (Nat.totient n : ℤ) := by sorry
theorem totient_prime_mul_of_not_dvd {p n : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) : (Nat.totient (p * n) : ℤ) = ((p : ℤ) - 1) * (Nat.totient n : ℤ) := by sorry
theorem totient_two_mul_of_odd {m : ℕ} (hm : Odd m) : Nat.totient (2 * m) = Nat.totient m := by sorry
theorem totient_two_mul_of_even {m : ℕ} (hm : Even m) : Nat.totient (2 * m) = 2 * Nat.totient m := by sorry
theorem one_prime_law_and_little_o_forces_totient {p : ℕ} (hp : p.Prime) {g : ℕ → ℤ} (hlaw_not_dvd : ∀ n : ℕ, 1 ≤ n → ¬ p ∣ n → g (p * n) = ((p : ℤ) - 1) * g n) (hlaw_dvd : ∀ n : ℕ, 1 ≤ n → p ∣ n → g (p * n) = (p : ℤ) * g n) (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |(g n : ℝ) - (Nat.totient n : ℝ)| ≤ ε * (n : ℝ)) {n : ℕ} (hn : 1 ≤ n) : g n = (Nat.totient n : ℤ) := by sorry
theorem even_law_and_eventual_congruence_forces_totient {g : ℕ → ℤ} (hodd : ∀ m : ℕ, Odd m → 1 ≤ m → g (2 * m) = g m) (heven : ∀ m : ℕ, Even m → 2 ≤ m → g (2 * m) = 2 * g m) (hcong : ∀ q : ℕ, 1 ≤ q → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (q : ℤ) ∣ totientDefect g n) {n : ℕ} (hn : 1 ≤ n) : g n = (Nat.totient n : ℤ) := by sorry
end PalomarCorpus.E249.TotientRigidity
