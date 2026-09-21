/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.BooleanMobiusCriticalCapacityGeometric`,
`Erdos249257.BooleanMobiusExactRowRankTwo`, `Erdos249257.BooleanMobiusExactTransition`,
`Erdos249257.BooleanMobiusLocalRepair`, `Erdos249257.HalfCylinderConcreteSeamAdapter`,
`Erdos249257.HalfCylinderIntegerGreedy`, `Erdos249257.MersenneShadowCyclotomicNoncollapse`,
`Erdos249257.MersenneShadowDenominatorGrowth`, `Erdos249257.RadicalMobiusShadow`,
`ErdosProblems.Erdos257.PaperCompleteR21.MersenneChannelSurvivalAllHeights`,
`ErdosProblems.Erdos257.PaperCompleteR21.OddReciprocalDenominators`,
`ErdosProblems.Erdos257.PaperCompleteR21.ThreeBranchRowDynamics`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification257PaperStatementsAD

noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool

noncomputable def ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)

noncomputable def toNatWord {s : ℕ} (b : SeamRowWord s) : ℕ → Bool :=
  fun d => if h : 2 ≤ d ∧ d < s then b ⟨d - 2, by omega⟩ else false

noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C

noncomputable def rowPulse (s d : ℕ) : ℕ :=
  (if d ∣ 2 * s + 2 then 1 else 0) +
    2 * (if d ∣ 2 * s + 1 then 1 else 0)

noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s

noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)

noncomputable def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega

noncomputable def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2

noncomputable def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])

noncomputable def lcmHeight (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).lcm (fun n ↦ n)

noncomputable def upperHalfPrimes (t : ℕ) : Finset ℕ :=
  (Finset.Ioc (t / 2) t).filter Nat.Prime

noncomputable def mersenne (n : ℕ) : ℕ := 2 ^ n - 1

noncomputable def mobiusNumerator (r : ℕ) : ℤ :=
  ∑ s ∈ r.primeFactors.powerset,
    (-1 : ℤ) ^ s.card *
      ((r / s.prod id : ℕ) : ℤ) *
        (((mersenne r) / (mersenne (s.prod id)) : ℕ) : ℤ)

noncomputable def baseMobiusShadow (r : ℕ) : ℚ :=
  Rat.divInt (mobiusNumerator r) (mersenne r : ℤ)

noncomputable def squarefreeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

noncomputable def numericMobiusShadow (H : ℕ) : ℚ :=
  baseMobiusShadow (squarefreeKernel H) / (squarefreeKernel H : ℚ)

noncomputable def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card

noncomputable def localMersenneGeometricQuotient (M d : ℕ) : ℕ :=
  2 ^ (M % d) * ∑ j ∈ Finset.range (M / d), (2 ^ d) ^ j

noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)

noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d

noncomputable def IsRowLower (n : ℕ) (D : Finset ℕ) : Prop :=
  D ⊆ Finset.Ico 2 n ∧
    localPrefixQuotient D (2 * n) ≤ seamSubsetTarget n ∧
      ∀ S, S ⊆ Finset.Ico 2 n →
        localPrefixQuotient S (2 * n) ≤ seamSubsetTarget n →
          localPrefixQuotient S (2 * n) ≤ localPrefixQuotient D (2 * n)

noncomputable def IsRowUpper (n : ℕ) (B : Finset ℕ) : Prop :=
  B ⊆ Finset.Ico 2 n ∧
    seamSubsetTarget n < localPrefixQuotient B (2 * n) ∧
      ∀ S, S ⊆ Finset.Ico 2 n →
        seamSubsetTarget n < localPrefixQuotient S (2 * n) →
          localPrefixQuotient B (2 * n) ≤ localPrefixQuotient S (2 * n)

noncomputable def rowSupport (n : ℕ) (b : SeamRowWord n) : Finset ℕ :=
  (Finset.Ico 2 n).filter (fun d => b.toNatWord d = true)

noncomputable def greedySupport (n : ℕ) : Finset ℕ := rowSupport n (seamGreedyWord n)

noncomputable def paperA (r : ℕ) : ℤ :=
  ∑ d ∈ r.divisors,
    ArithmeticFunction.moebius d * (((r / d : ℕ)) : ℤ) *
      (((mersenne r /
        mersenne d : ℕ)) : ℤ)

noncomputable def paperB (r : ℕ) : ℚ :=
  ∑ d ∈ r.divisors,
    ((ArithmeticFunction.moebius d : ℤ) : ℚ) * ((r : ℚ) / (d : ℚ)) /
      ((2 : ℚ) ^ d - 1)

/-- States thm:mersenne-channel-growth from the long record for Erdős problem #257. Transported
from
Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_scaledMobiusShadow_den_lower_bound in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem lcmHeight_scaledMobiusShadow_den_lower_bound
    {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤
      ((lcmHeight t : ℚ) *
        numericMobiusShadow (lcmHeight t)).den := by
  sorry

/-- States thm:mersenne-channel-growth from the long record for Erdős problem #257. Transported
from Erdos249257.MersenneShadowDenominatorGrowth.upperHalfMersenneProduct_lower_bound in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem upperHalfMersenneProduct_lower_bound {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤
      ∏ p ∈ upperHalfPrimes t, mersenne p := by
  sorry

/-- States record:257bm-c9 from the long record for Erdős problem #257. Transported from
Erdos249257.exists_boolean_word_of_lt_two_pow in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem exists_boolean_word_of_lt_two_pow
    {V L : ℕ} (hV : V < 2 ^ L) :
    ∃ y : List ℕ,
      y.length = L ∧
      (∀ b ∈ y, b = 0 ∨ b = 1) ∧
      Nat.ofDigits 2 y = V := by
  sorry

/-- States record:257bm-i12 from the long record for Erdős problem #257. Transported from
Erdos249257.localMersenneQuotient_eq_geometric in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem localMersenneQuotient_eq_geometric
    {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient M d = localMersenneGeometricQuotient M d := by
  sorry

/-- States record:257bm-c9 from the long record for Erdős problem #257. Transported from
Erdos249257.localMersenneQuotient_eq_two_pow_sub_of_half_lt in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem localMersenneQuotient_eq_two_pow_sub_of_half_lt
    {M d : ℕ} (hd2 : 2 ≤ d) (hhalf : M / 2 < d) (hdM : d ≤ M) :
    localMersenneQuotient M d = 2 ^ (M - d) := by
  sorry

/-- States record:257bm-i1b from the long record for Erdős problem #257. Transported from
Erdos249257.localPrefixQuotient_succ in the substantive development, whose statement was
refereed against the paper in the coverage ledger. -/
theorem localPrefixQuotient_succ
    {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D (M + 1) =
      2 * localPrefixQuotient D M +
        endpointDivisorContribution D (M + 1) := by
  sorry

/-- States record:257bm-i-rank2 from the long record for Erdős problem #257. Transported from
Erdos249257.two_mem_of_exact_localMersenneQuotient in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem two_mem_of_exact_localMersenneQuotient
    {D : Finset ℕ} {n : ℕ}
    (hn : 3 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) :
    2 ∈ D := by
  sorry

/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257.
Transported from
ErdosProblems.Erdos257.PaperCompleteR21.channelProduct_coprime_mobiusNumerator_of_one_le in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem channelProduct_coprime_mobiusNumerator_of_one_le
    {P : Finset ℕ} {t r : ℕ} (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    Nat.Coprime (∏ p ∈ P, mersenne p)
      (mobiusNumerator r).natAbs := by
  sorry

/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257.
Transported from ErdosProblems.Erdos257.PaperCompleteR21.paperA_eq_mobiusNumerator in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paperA_eq_mobiusNumerator {r : ℕ} (hr : Squarefree r) :
    paperA r = mobiusNumerator r := by
  sorry

/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257.
Transported from ErdosProblems.Erdos257.PaperCompleteR21.paperB_eq_baseMobiusShadow in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paperB_eq_baseMobiusShadow {r : ℕ} (hr : Squarefree r) :
    paperB r = baseMobiusShadow r := by
  sorry

/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257.
Transported from ErdosProblems.Erdos257.PaperCompleteR21.paperB_eq_divInt_paperA in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paperB_eq_divInt_paperA {r : ℕ} (hr : Squarefree r) :
    paperB r = Rat.divInt (paperA r) (mersenne r : ℤ) := by
  sorry

/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257.
Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_channel_factor_gcd_eq_one in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_channel_factor_gcd_eq_one
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 2 ^ Nat.gcd p q - 1 ∧
      Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 1 := by
  sorry

/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257.
Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_channel_factors_pairwise_coprime in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_channel_factors_pairwise_coprime
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime) :
    (P : Set ℕ).Pairwise fun p q => Nat.Coprime (2 ^ p - 1) (2 ^ q - 1) := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_consecutive_not_both_divisible in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_consecutive_not_both_divisible {d m : ℕ} (hd : 2 ≤ d) :
    ¬ (d ∣ m + 1 ∧ d ∣ m + 2) := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_dynamics in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem paper_dynamics {n : ℕ} (hn : 5 ≤ n) {D B D' : Finset ℕ}
    (hD : IsRowLower n D) (hB : IsRowUpper n B) (hD' : IsRowLower (n + 1) D')
    {r o pm pp rem : ℕ}
    (hr : localPrefixQuotient D (2 * n) + r = seamSubsetTarget n)
    (ho : seamSubsetTarget n + o = localPrefixQuotient B (2 * n))
    (hpm : pm = ∑ d ∈ D, rowPulse n d)
    (hpp : pp = ∑ d ∈ B, rowPulse n d)
    (hrem : localPrefixQuotient D' (2 * (n + 1)) + rem = seamSubsetTarget (n + 1)) :
    D = greedySupport n ∧
      pm ≤ 2 * (n - 2) ∧ pp ≤ 2 * (n - 2) ∧
      ((rem : ℤ) =
        if 4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1) then
          (2 : ℤ) ^ (n + 1) - 4 * (o : ℤ) - (pp : ℤ)
        else if 4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4 then
          4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ)
        else 4 * (r : ℤ) - 2 ^ (n + 1) - (pm : ℤ) - 4) ∧
      (((rem : ℚ) - 2 ^ (n + 1)) / 2 ^ (n + 1) =
        if 4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1) then
          -((4 * (o : ℚ) + (pp : ℚ)) / 2 ^ (n + 1))
        else if 4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4 then
          2 * (((r : ℚ) - 2 ^ n) / 2 ^ n) + 2 - (pm : ℚ) / 2 ^ (n + 1)
        else 2 * (((r : ℚ) - 2 ^ n) / 2 ^ n) - ((pm : ℚ) + 4) / 2 ^ (n + 1)) := by
  sorry

/-- States record:257bm-i10 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_sum_inv_odd_den_odd in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_finite_sum_inv_odd_den_odd {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hodd : ∀ i ∈ s, Odd (f i)) :
    Odd (∑ i ∈ s, (1 : ℚ) / ((f i : ℤ) : ℚ)).den := by
  sorry

/-- States record:257bm-i10 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_sum_inv_odd_ne_half in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_finite_sum_inv_odd_ne_half {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hodd : ∀ i ∈ s, Odd (f i)) :
    (∑ i ∈ s, (1 : ℚ) / ((f i : ℤ) : ℚ)) ≠ (1 : ℚ) / 2 := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_greedy_rule in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedySupport_greedy_rule {n : ℕ} (hn : 5 ≤ n) {d : ℕ}
    (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔
      truncatedMersenneWeight n d +
          ∑ e ∈ (greedySupport n).filter (fun e => e < d),
            truncatedMersenneWeight n e ≤ seamSubsetTarget n := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_isRowLower in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedySupport_isRowLower {n : ℕ} (hn : 5 ≤ n) :
    IsRowLower n (greedySupport n) := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_mem in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedySupport_mem {n d : ℕ} (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔ seamGreedyWord n ⟨d - 2, by omega⟩ = true := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_greedy_step in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedy_step {n d : ℕ} (hd : d < n) (C : ℕ) :
    integerGreedyBits (seamWeightsFrom n d) C =
      (decide (truncatedMersenneWeight n d ≤ C)) ::
        integerGreedyBits (seamWeightsFrom n (d + 1))
          (if truncatedMersenneWeight n d ≤ C then
            C - truncatedMersenneWeight n d else C) := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_isRowLower_unique in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_isRowLower_unique {n : ℕ} (hn : 5 ≤ n) {D D₀ : Finset ℕ}
    (hD : IsRowLower n D) (hD₀ : IsRowLower n D₀) : D = D₀ := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_isRowUpper_unique in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_isRowUpper_unique {n : ℕ} (hn : 5 ≤ n) {B B₀ : Finset ℕ}
    (hB : IsRowUpper n B) (hB₀ : IsRowUpper n B₀) : B = B₀ := by
  sorry

/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257.
Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_channel_survival in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_mersenne_channel_survival
    (P : Finset ℕ) {t h r : ℕ}
    (ht : 1 ≤ t) (hh : 1 ≤ h) (hr1 : 1 ≤ r) (hrsf : Squarefree r)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p) :
    (∏ p ∈ P, (2 ^ p - 1)) / Nat.gcd (∏ p ∈ P, (2 ^ p - 1)) h ∣
      ((h : ℚ) * paperB r).den := by
  sorry

/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257.
Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_channel_survival_of_coprime_scale in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_mersenne_channel_survival_of_coprime_scale
    (P : Finset ℕ) {t h r : ℕ}
    (ht : 1 ≤ t) (hh : 1 ≤ h) (hr1 : 1 ≤ r) (hrsf : Squarefree r)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hscale : Nat.gcd (∏ p ∈ P, (2 ^ p - 1)) h = 1) :
    (∏ p ∈ P, (2 ^ p - 1)) ∣ ((h : ℚ) * paperB r).den := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_rowLower_existsUnique in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowLower_existsUnique {n : ℕ} (hn : 5 ≤ n) :
    ∃! D : Finset ℕ, IsRowLower n D := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_rowPulse_eq_indicators in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowPulse_eq_indicators (n d : ℕ) :
    rowPulse n d =
      2 * (if d ∣ 2 * n + 1 then 1 else 0) +
        (if d ∣ 2 * n + 2 then 1 else 0) := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_rowQuotient_eq_weightSum in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowQuotient_eq_weightSum (n : ℕ) (S : Finset ℕ) :
    localPrefixQuotient S (2 * n) = ∑ d ∈ S, truncatedMersenneWeight n d := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_rowTarget_eq in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowTarget_eq (n : ℕ) :
    seamSubsetTarget n = 2 ^ (2 * n - 1) - 2 ^ n := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_rowUpper_existsUnique in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowUpper_existsUnique {n : ℕ} (hn : 5 ≤ n) :
    ∃! B : Finset ℕ, IsRowUpper n B := by
  sorry

/-- States thm:dynamics from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_rowWeight_eq_floor in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_rowWeight_eq_floor (n d : ℕ) :
    truncatedMersenneWeight n d = 4 ^ n / (2 ^ d - 1) := by
  sorry

/-- States thm:mersenne-channel-survival from the long record for Erdős problem #257.
Transported from
ErdosProblems.Erdos257.PaperCompleteR21.upperHalfChannel_survivorProduct_dvd_den_of_one_le
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem upperHalfChannel_survivorProduct_dvd_den_of_one_le
    (P : Finset ℕ) {t r h : ℕ} (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    (∏ p ∈ P, mersenne p) /
        Nat.gcd (∏ p ∈ P, mersenne p) h ∣
      (Rat.divInt ((h : ℤ) * mobiusNumerator r)
        (mersenne r : ℤ)).den := by
  sorry

end Erdos249257.ExternalVerification257PaperStatementsAD
