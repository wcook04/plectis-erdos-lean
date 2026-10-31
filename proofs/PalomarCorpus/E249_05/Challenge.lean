/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record sections 5 to 6: series identities and finite exclusions; detailed statements

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Finset
open Filter Topology
open scoped ArithmeticFunction.Moebius
open scoped Polynomial

namespace PalomarCorpus.E249_05.Shared
/-- The Mersenne denominator at exponent `n`. Local copy of Erdos249257.RadicalMobiusShadow.mersenne, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenne (n : ℕ) : ℕ := 2 ^ n - 1
/-- The integral numerator, written as its squarefree-divisor expansion. For `s ⊆ primeFactors(r)`, put `d = ∏ p ∈ s, p`. Then the summand is `(-1)^|s| (r/d) ((2^r-1)/(2^d-1))`. This is exactly the nonzero part of `Σ_{d ∣ r} μ(d) (r/d) ((2^r-1)/(2^d-1))`: nonsquarefree divisors have Möbius coefficient zero. The subset form makes that finite support explicit and keeps the definition executable without factoring irrelevant divisors. Local copy of Erdos249257.RadicalMobiusShadow.mobiusNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusNumerator (r : ℕ) : ℤ :=
  ∑ s ∈ r.primeFactors.powerset,
    (-1 : ℤ) ^ s.card *
      ((r / s.prod id : ℕ) : ℤ) *
        (((mersenne r) / (mersenne (s.prod id)) : ℕ) : ℤ)
/-- The unscaled radical shadow `B(r) = M_r / (2^r - 1)`. Local copy of Erdos249257.RadicalMobiusShadow.baseMobiusShadow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def baseMobiusShadow (r : ℕ) : ℚ :=
  Rat.divInt (mobiusNumerator r) (mersenne r : ℤ)
/-- The binary totient tail `R_N = ∑_{j ≥ 1} φ(N + j) / 2 ^ j`, a real number satisfying `2 ^ N S = Φ_N + R_N`, where `S = ∑_{n ≥ 1} φ(n) / 2 ^ n` and `Φ_N = ∑_{n ≤ N} φ(n) 2 ^ (N - n)` is an integer. It obeys `0 < R_N ≤ N + 1` for `N ≥ 1`. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
end PalomarCorpus.E249_05.Shared

namespace PalomarCorpus.E249.PaperStatementsAJ
/-- States prop:mobsq from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.moebius_three_values in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem moebius_three_values (d : ℕ) :
    ArithmeticFunction.moebius d = -1 ∨ ArithmeticFunction.moebius d = 0 ∨
      ArithmeticFunction.moebius d = 1 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsAY
open scoped BigOperators
/-- The #249 constant, named locally for the generic-scale transport. Local copy of Erdos249257.FullTargetPrimeAdjunctionNoGo.totientSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientSeries : ℝ :=
  ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n
/-- States prop:mobsq from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.irrational_totient_iff_mobius_square in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totient_iff_mobius_square :
    Irrational totientSeries ↔
      Irrational (∑' d : ℕ+, (ArithmeticFunction.moebius (d : ℕ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := by
  sorry
/-- States prop:mobsq from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.mobius_square_reduction in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobius_square_reduction :
    totientSeries = (1 : ℝ) / 2 +
      ∑' d : ℕ+, (ArithmeticFunction.moebius (d : ℕ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAY

namespace PalomarCorpus.E249.PaperStatementsAK
/-- States catalogue:mob:a2, prop:lambertengine from the long record for Erdős problem #249. Transported from GcdMomentCalculus.tsum_lambert_linear_weight_sq_pure in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_lambert_linear_weight_sq_pure
    (w : ℕ → ℝ) (hw : ∀ d : ℕ, 0 < d → |w d| ≤ (d : ℝ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ))) ^ 2
      = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e * ((((n : ℕ) / e : ℕ) : ℝ) - 1))
          * r ^ (n : ℕ) := by
  sorry
/-- States catalogue:mob:a5, prop:pillai from the long record for Erdős problem #249. Transported from GcdMomentCalculus.tsum_totient_div_mersenne_sq_eq_gcd_moment_series in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_totient_div_mersenne_sq_eq_gcd_moment_series :
    ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ))
            - ((n : ℕ) : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAK

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
export PalomarCorpus.E249_05.Shared (baseMobiusShadow mersenne mobiusNumerator)
/-- The squarefree kernel used by the numeric shadow: the product of the distinct prime factors of `n`. For `n = 0` this convention gives `1`; all development-facing scaling theorems assume `0 < n`. Local copy of Erdos249257.RadicalMobiusShadow.squarefreeKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def squarefreeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p
/-- The numeric shadow at an arbitrary scale. By construction it only sees the distinct prime factors of `H`. Local copy of Erdos249257.RadicalMobiusShadow.numericMobiusShadow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def numericMobiusShadow (H : ℕ) : ℚ :=
  baseMobiusShadow (squarefreeKernel H) / (squarefreeKernel H : ℚ)
/-- `Hₜ = lcm(1, ..., t)`. The interval avoids inserting zero into the finite LCM. Local copy of Erdos249257.MersenneShadowCyclotomicNoncollapse.lcmHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmHeight (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).lcm (fun n ↦ n)
/-- Prime indices in the development's upper half `(t/2, t]`. Local copy of Erdos249257.MersenneShadowCyclotomicNoncollapse.upperHalfPrimes, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def upperHalfPrimes (t : ℕ) : Finset ℕ :=
  (Finset.Ioc (t / 2) t).filter Nat.Prime
/-- Pillai's gcd-sum function, transcribed from the manuscript's defining divisor sum `P(n) = ∑_{e ∣ n} φ(e)·(n/e)`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.pillaiP, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def pillaiP (n : ℕ) : ℕ := ∑ e ∈ n.divisors, Nat.totient e * (n / e)
/-- `φ` as an `ArithmeticFunction` (`Nat.totient 0 = 0` already holds), so that the manuscript's `φ * Id` is the Dirichlet convolution it names. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.totientArith, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientArith : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩
/-- States catalogue:mob:b6 from the long record for Erdős problem #249. Transported from Erdos249257.MersenneShadowCyclotomicNoncollapse.lcmHeight_upperHalf_product_dvd_den in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lcmHeight_upperHalf_product_dvd_den
    {t : ℕ} (ht : 5 ≤ t) :
    (∏ p ∈ upperHalfPrimes t, mersenne p) ∣
      ((lcmHeight t : ℚ) *
        numericMobiusShadow (lcmHeight t)).den := by
  sorry
/-- States catalogue:mob:b6 from the long record for Erdős problem #249. Transported from Erdos249257.MersenneShadowCyclotomicNoncollapse.upperHalfChannel_product_dvd_den_of_coprime_scale in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem upperHalfChannel_product_dvd_den_of_coprime_scale
    (P : Finset ℕ) {t r h : ℕ} (ht : 5 ≤ t) (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hscale : Nat.Coprime
      (∏ p ∈ P, mersenne p) h) :
    (∏ p ∈ P, mersenne p) ∣
      (Rat.divInt ((h : ℤ) * mobiusNumerator r)
        (mersenne r : ℤ)).den := by
  sorry
/-- States catalogue:mob:b6 from the long record for Erdős problem #249. Transported from Erdos249257.MersenneShadowCyclotomicNoncollapse.upperHalfChannel_product_dvd_den_of_scale_primeFactors_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem upperHalfChannel_product_dvd_den_of_scale_primeFactors_le
    (P : Finset ℕ) {t r h : ℕ} (ht : 5 ≤ t) (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hhcut : ∀ q : ℕ, q.Prime → q ∣ h → q ≤ t) :
    (∏ p ∈ P, mersenne p) ∣
      (Rat.divInt ((h : ℤ) * mobiusNumerator r)
        (mersenne r : ℤ)).den := by
  sorry
/-- States catalogue:mob:b7b from the long record for Erdős problem #249. Transported from Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_five_scaledMobiusShadow_den_exact in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lcmHeight_five_scaledMobiusShadow_den_exact :
    ((lcmHeight 5 : ℚ) *
        numericMobiusShadow (lcmHeight 5)).den =
      mersenne 30 / 3 := by
  sorry
/-- States catalogue:mob:b7a from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.upper_half_product_denominator_bounds in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem upper_half_product_denominator_bounds {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤ (∏ p ∈ upperHalfPrimes t, mersenne p) ∧
    (∏ p ∈ upperHalfPrimes t, mersenne p) ≤
      ((lcmHeight t : ℚ) * numericMobiusShadow (lcmHeight t)).den := by
  sorry
/-- States catalogue:mob:a5, prop:pillai from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.gcd_moment_identity_three_members in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem gcd_moment_identity_three_members :
    (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
        = ∑' n : ℕ+, (((pillaiP (n : ℕ) : ℕ) : ℝ) - ((n : ℕ) : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ))
      ∧ (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
        = ∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2
            then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0) := by
  sorry
/-- States catalogue:mob:a5, prop:pillai from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.pillaiP_eq_totient_mul_id in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem pillaiP_eq_totient_mul_id (n : ℕ) :
    (totientArith * ArithmeticFunction.id) n = pillaiP n := by
  sorry
/-- States catalogue:mob:a5, prop:pillai from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.sum_gcd_Icc_eq_pillaiP in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sum_gcd_Icc_eq_pillaiP (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, Nat.gcd k n = pillaiP n := by
  sorry
/-- States catalogue:mob:a5, prop:pillai from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2
        then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAE

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
open Finset
export PalomarCorpus.E249_05.Shared (totientTail)
/-- States catalogue:cert:a9 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.specified_euler_tail_period in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem specified_euler_tail_period
    (a : ℤ) (c v : ℕ) (hv : 0 < v) (hodd : Odd v)
    (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) =
      (a : ℝ) / ((2 : ℝ) ^ c * (v : ℝ))) :
    0 < Nat.totient v ∧ ∀ N : ℕ, c ≤ N →
      totientTail (N + Nat.totient v) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAX

namespace PalomarCorpus.E249.CompleteKernelBases
open Filter Topology
open scoped BigOperators
/-- The rational-valued sequence n ↦ φ(k^j n + r). -/
noncomputable def allBaseTotientKernelSeq (k j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (k ^ j * n + r)
/-- All base-k kernel indices at levels zero through e, inclusive. -/
noncomputable abbrev AllBaseThroughLevelIndex (k e : ℕ) := Σ j : Fin (e + 1), Fin (k ^ j.val)
/-- All rational-valued base-k totient subsequences through level e. -/
noncomputable def allBaseThroughLevelFamily (k e : ℕ) : AllBaseThroughLevelIndex k e → ℕ → ℚ
  | ⟨j, r⟩ => allBaseTotientKernelSeq k j.val r.val
/-- The dyadic section `n ↦ φ(2 ^ j n + r)` of Euler's totient at level `j` and residue `r`, with values in `ℚ` through the cast from `ℕ`. -/
noncomputable def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)
/-- Index type for the canonical duplicate-free family of dyadic totient sections through level `e`: a left index `i ∈ Fin 2` names the zero-residue channel `n ↦ φ(2 ^ i n)`, and a right index `⟨j, r⟩` with `j < e` and `r < 2 ^ j` names the odd residue `2 r + 1` at level `j + 1`, so the type has `2 ^ e + 1` elements. -/
noncomputable abbrev TotientCanonicalIndex (e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)
/-- The canonical duplicate-free family of dyadic totient sections through level `e`: a left index `i ∈ Fin 2` gives `n ↦ φ(2 ^ i n)`, and a right index `⟨j, r⟩` gives the odd-residue channel `n ↦ φ(2 ^ (j + 1) n + 2 r + 1)`. -/
noncomputable def canonicalTotientKernelFamily (e : ℕ) :
    TotientCanonicalIndex e → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j.val + 1) (2 * r.val + 1)
/-- The dyadic kernel indices at levels zero through e, inclusive. -/
noncomputable abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)
/-- The family of rational-valued totient subsequences through dyadic level e. -/
noncomputable def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val
/-- All pairs of a dyadic level j and a residue below 2^j. -/
noncomputable abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)
/-- Every dyadic subsequence n ↦ φ(2^j n + r), viewed as a rational-valued sequence. -/
noncomputable def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val
/-- Two initial channels together with every odd-residue channel at a positive dyadic level. -/
noncomputable abbrev TotientOddCoreIndex := Fin 2 ⊕ Σ j : ℕ, Fin (2 ^ j)
/-- The two initial zero-residue channels and all odd-residue dyadic channels, as rational-valued sequences. -/
noncomputable def oddCoreTotientKernelFamily : TotientOddCoreIndex → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j + 1) (2 * r.val + 1)
/-- The finite canonical families have cardinality 2^e + 1 and are linearly independent; the odd-core family is a basis of the full dyadic span, with the stated finite-level ranks and level-zero exception. -/
theorem displayed_canonical_and_full_dyadic :
    (∀ e : ℕ, Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1 ∧
      LinearIndependent ℚ (canonicalTotientKernelFamily e)) ∧
    (∃ b : Module.Basis TotientOddCoreIndex ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily)),
      ∀ i, (b i : ℕ → ℚ) = oddCoreTotientKernelFamily i) ∧
    (∀ e : ℕ, 1 ≤ e → Module.finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) = 2 ^ e + 1) ∧
    Module.finrank ℚ (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily 2 0))) = 1 := by
  sorry
end PalomarCorpus.E249.CompleteKernelBases

namespace PalomarCorpus.E249.PaperStatementsAD
open Finset
export PalomarCorpus.E249_05.Shared (totientTail)
/-- States catalogue:cert:a8 from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.tail_diff_int_of_den_dvd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_diff_int_of_den_dvd (r : ℚ)
    (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (r : ℝ))
    (h N : ℕ) (hdvd : (r.den : ℕ) ∣ 2 ^ N * (2 ^ h - 1)) :
    totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAD

namespace PalomarCorpus.E249.PaperStatementsAQ
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial
export PalomarCorpus.E249_05.Shared (baseMobiusShadow mersenne mobiusNumerator)
/-- Integer evaluation `Φ_m(2)`. Local copy of Erdos249257.CyclotomicProjectionOfShadow.cyclotomicEval, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cyclotomicEval (m : ℕ) : ℤ :=
  (Polynomial.cyclotomic m ℤ).eval 2
/-- The unsigned cyclotomic channel modulus `|Φ_m(2)|`. Local copy of Erdos249257.CyclotomicProjectionOfShadow.cyclotomicValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cyclotomicValue (m : ℕ) : ℕ :=
  (cyclotomicEval m).natAbs
/-- `1 + X^d + ... + X^((q - 1)d)`. Local copy of Erdos249257.RepunitMobiusNumerator.spacedRepunit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def spacedRepunit (d q : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range q, Polynomial.monomial (d * j) 1
/-- The divisor-signed polynomial numerator. For positive `r`, evaluation at `X = 2` is the common-denominator Möbius numerator; the public bridge below is stated only on the formal development.s squarefree boundary. Local copy of Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusNumeratorPolynomial (r : ℕ) : ℤ[X] :=
  ∑ d ∈ r.divisors,
    Polynomial.C (ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))) *
      spacedRepunit d (r / d)
/-- States catalogue:mob:b5 from the long record for Erdős problem #249. Transported from Erdos249257.CyclotomicProjectionOfShadow.cyclotomicValue_dvd_baseMobiusShadow_den in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cyclotomicValue_dvd_baseMobiusShadow_den
    {r : ℕ} (hr : Squarefree r) :
    cyclotomicValue r ∣ (baseMobiusShadow r).den := by
  sorry
/-- States catalogue:mob:b5 from the long record for Erdős problem #249. Transported from Erdos249257.CyclotomicProjectionOfShadow.mobiusNumerator_gcd_cyclotomicValue in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusNumerator_gcd_cyclotomicValue
    {r : ℕ} (hr : Squarefree r) :
    Nat.gcd
      (mobiusNumerator r).natAbs
      (cyclotomicValue r) = 1 := by
  sorry
/-- States catalogue:mob:b2, catalogue:mob:b5 from the long record for Erdős problem #249. Transported from Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial_eval_two in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusNumeratorPolynomial_eval_two {r : ℕ} (hr : Squarefree r) :
    (mobiusNumeratorPolynomial r).eval 2 =
      mobiusNumerator r := by
  sorry
end PalomarCorpus.E249.PaperStatementsAQ
