/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record sections 6.6.9 to 6.6.13: coprime-pair sums; the single-parameter diagonal condition; prime divisors of Mersenne factors and finite exclusions

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open Finset
open scoped BigOperators
open Matrix
open ArithmeticFunction

namespace PalomarCorpus.E249_19.Shared
/-- Large prime-ray layers escape every prescribed finite prime support. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.FinitePrimeSupportEscape, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FinitePrimeSupportEscape (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ,
    q.Prime → Q₀ ≤ q →
      ∀ p ∈ S, p.Prime → ¬ p ∣ C (m * q)
/-- The atom of index `n` at rung `r` of the Möbius-Mersenne ladder, namely `μ(n + 1) / (2 ^ (n + 1) - 1) ^ r` with `μ` the Möbius function; the index is shifted so that `n = 0` carries the divisor `d = 1`. -/
noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)
/-- The rung `Θ_r = ∑_{d ≥ 1} μ(d) / (2 ^ d - 1) ^ r` of the Möbius-Mersenne ladder, defined as the real sum of the atoms above. The divisor convolution `φ = μ * id` gives `Θ_2 = S - 1/2` for the binary totient series `S = ∑_{n ≥ 1} φ(n) / 2 ^ n`. At `r = 0` the family is not summable and the Lean sum takes its default value `0`; every compared theorem uses the ladder only at `r ≥ 1`. -/
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n
/-- The universal period `lcm(1, 2, ..., t)`, given recursively by `periodLcm 0 = 1` and `periodLcm (t + 1) = lcm (periodLcm t) (t + 1)`. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
end PalomarCorpus.E249_19.Shared

namespace PalomarCorpus.E249.PaperStatementsAJ
export PalomarCorpus.E249_19.Shared (FinitePrimeSupportEscape)
/-- The unsigned binary cyclotomic layer `|Φ_n(2)|`. Local copy of ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCyclotomicLayer (n : ℕ) : ℕ :=
  ((Polynomial.cyclotomic n ℤ).eval (2 : ℤ)).natAbs
/-- Every rational prime divisor of a layer supplies an exact-order witness in extension degree at most `d`. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.BoundedDegreeOrderConsumer, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def BoundedDegreeOrderConsumer
    (C : ℕ → ℕ) (m d : ℕ) : Prop :=
  ∀ q p : ℕ,
    q.Prime → p.Prime → p ∣ C (m * q) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1
/-- Bounded-degree order witnesses beyond a prime-index cutoff. Unlike `BoundedDegreeOrderConsumer`, this permits the finitely many characteristic primes that occur naturally in cyclotomic layers. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.EventualBoundedDegreeOrderConsumer, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def EventualBoundedDegreeOrderConsumer
    (C : ℕ → ℕ) (m d : ℕ) : Prop :=
  ∃ Q₀ : ℕ, ∀ q p : ℕ,
    q.Prime → Q₀ ≤ q → p.Prime → p ∣ C (m * q) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1
/-- Eventual nontrivial, clean cyclotomic layers on the prime ray `m*q`. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.PrimeRayLayerSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PrimeRayLayerSupply (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∃ Q₀ : ℕ, ∀ q : ℕ,
    q.Prime → Q₀ ≤ q →
      1 < C (m * q) ∧ Nat.Coprime (C (m * q)) (m * q)
/-- The prime divisors appearing on the ray `m*q` are unbounded, even after imposing an arbitrary lower bound on the prime index `q`. Local copy of ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.UnboundedPrimeDivisorSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def UnboundedPrimeDivisorSupply (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ B N₀ : ℕ, ∃ q p : ℕ,
    q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.binaryCyclotomicLayer_eventual_instance in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem binaryCyclotomicLayer_eventual_instance (m : ℕ) (hm : 0 < m) :
    EventualBoundedDegreeOrderConsumer binaryCyclotomicLayer m 1 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.binaryCyclotomic_allPrime_form_fails in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem binaryCyclotomic_allPrime_form_fails :
    ((Polynomial.cyclotomic 6 ℤ).eval 2).natAbs = 3 ∧ ¬ (6 ∣ 3 - 1) ∧
      ¬ BoundedDegreeOrderConsumer binaryCyclotomicLayer 2 1 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.boundedDegreeOrderConsumer_unfolded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem boundedDegreeOrderConsumer_unfolded (C : ℕ → ℕ) (m d : ℕ) :
    BoundedDegreeOrderConsumer C m d ↔
      ∀ q p : ℕ, q.Prime → p.Prime → p ∣ C (m * q) →
        ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.boundedOrder_witness_iff_orderOf_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem boundedOrder_witness_iff_orderOf_le {n p d : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hcop : Nat.Coprime p n) :
    (∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ n ∣ p ^ k - 1) ↔ orderOf ((p : ℕ) : ZMod n) ≤ d := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_plain_half_eq_series_sub_half in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem coprimeLattice_plain_half_eq_series_sub_half :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then (1 / 2 : ℝ) ^ (p.1 + p.2) else 0)
        = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 ∧
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2
        ≠ ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprime_of_dvd_pow_sub_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem coprime_of_dvd_pow_sub_one {n p k : ℕ} (hp : 0 < p) (hk : 1 ≤ k)
    (hdvd : n ∣ p ^ k - 1) : Nat.Coprime p n := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_layer_prime_order_decomposition_paper in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cyclotomic_layer_prime_order_decomposition_paper {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime)
    (hpdvd : p ∣ ((Polynomial.cyclotomic n ℤ).eval 2).natAbs) :
    ∃ a : ℕ, n = p ^ a * orderOf ((2 : ℕ) : ZMod p) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.dvd_pow_sub_one_iff_orderOf_dvd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dvd_pow_sub_one_iff_orderOf_dvd {n p k : ℕ} (hn : 0 < n) (hp : 0 < p) :
    n ∣ p ^ k - 1 ↔ orderOf ((p : ℕ) : ZMod n) ∣ k := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.eventual_orderConsumer_conclusions in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem eventual_orderConsumer_conclusions {C : ℕ → ℕ} {m d : ℕ}
    (hm : 1 ≤ m) (horder : EventualBoundedDegreeOrderConsumer C m d) :
    FinitePrimeSupportEscape C m ∧
      (∀ hsupply : PrimeRayLayerSupply C m, UnboundedPrimeDivisorSupply C m) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.exists_clean_cyclotomic_anchor_paper in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_clean_cyclotomic_anchor_paper (h N₀ : ℕ) (hh : 0 < h) :
    ∃ q p : ℕ, q.Prime ∧ p.Prime ∧
      p ∣ ((Polynomial.cyclotomic (h * q) ℤ).eval 2).natAbs ∧
      Nat.Coprime p (h * q) ∧ h * q ∣ p - 1 ∧ N₀ ≤ p - 1 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.mersenneLayer_orderConsumer_instance in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneLayer_orderConsumer_instance :
    BoundedDegreeOrderConsumer (fun n => 2 ^ n - 1) 1 1 ∧
      ∀ q p : ℕ, q.Prime → p.Prime → p ∣ 2 ^ q - 1 →
        orderOf ((p : ℕ) : ZMod q) = 1 ∧ orderOf ((2 : ℕ) : ZMod p) = q := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.mersenneLayer_prime_divisor_order in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneLayer_prime_divisor_order {q p : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hdvd : p ∣ 2 ^ q - 1) :
    orderOf ((2 : ℕ) : ZMod p) = q ∧ q ∣ p - 1 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.mersenneLayer_unbounded_prime_support in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneLayer_unbounded_prime_support (B N₀ : ℕ) :
    ∃ q p : ℕ, q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ 2 ^ q - 1 ∧ B < p := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.orderConsumer_finite_prime_escape in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orderConsumer_finite_prime_escape {C : ℕ → ℕ} {m d : ℕ}
    (hm : 1 ≤ m) (horder : BoundedDegreeOrderConsumer C m d) :
    ∀ S : Finset ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q →
      ∀ p ∈ S, p.Prime → ¬ p ∣ C (m * q) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.orderConsumer_index_lt_pow in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orderConsumer_index_lt_pow {C : ℕ → ℕ} {m d q p : ℕ}
    (horder : BoundedDegreeOrderConsumer C m d)
    (hq : q.Prime) (hp : p.Prime) (hpC : p ∣ C (m * q)) :
    m * q < p ^ d := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.orderConsumer_unbounded_prime_divisors in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orderConsumer_unbounded_prime_divisors {C : ℕ → ℕ} {m d : ℕ}
    (hm : 1 ≤ m)
    (hlayer : ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q →
      1 < C (m * q) ∧ Nat.Coprime (C (m * q)) (m * q))
    (horder : BoundedDegreeOrderConsumer C m d) :
    ∀ B N₀ : ℕ, ∃ q p : ℕ,
      q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p := by
  sorry
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsA
open Finset
export PalomarCorpus.E249_19.Shared (periodLcm)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from Erdos249257.TotientTailPeriodKiller.dvd_periodLcm in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
lemma dvd_periodLcm {h t : ℕ} (h1 : 1 ≤ h) (ht : h ≤ t) : h ∣ periodLcm t := by
  sorry
end PalomarCorpus.E249.PaperStatementsA

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_19.Shared (periodLcm)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.short_lcm_window_nondivisor in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem short_lcm_window_nondivisor (t j : ℕ) (ht : 1 ≤ t) (hj : 1 ≤ j)
    (hlt : j < 2 * t) (hnd : ¬ j ∣ periodLcm t) :
    ∃ p a : ℕ, Nat.Prime p ∧ 1 ≤ a ∧ j = p ^ a ∧ t < j := by
  sorry
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAK
export PalomarCorpus.E249_19.Shared (FinitePrimeSupportEscape)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.unbounded_prime_divisors_of_escape_of_nontrivial in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem unbounded_prime_divisors_of_escape_of_nontrivial {C : ℕ → ℕ} {m : ℕ}
    (hnontrivial : ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q → 1 < C (m * q))
    (hescape : FinitePrimeSupportEscape C m) :
    ∀ B N₀ : ℕ, ∃ q p : ℕ,
      q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p := by
  sorry
end PalomarCorpus.E249.PaperStatementsAK

namespace PalomarCorpus.E249.PaperStatementsAF
open scoped BigOperators
open Matrix
open ArithmeticFunction
export PalomarCorpus.E249_19.Shared (mobiusMersenneTerm mobiusMersenneTheta)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from Erdos249257.SignedQMomentObstruction.mobiusMersenneTheta_two_eq_totient_offset in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusMersenneTheta_two_eq_totient_offset :
    mobiusMersenneTheta 2 =
      (∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) *
        ((1 : ℝ) / 2) ^ (n : ℕ)) - 1 / 2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAF

namespace PalomarCorpus.E249.PaperStatementsBG
open scoped BigOperators
open Matrix
open ArithmeticFunction
export PalomarCorpus.E249_19.Shared (mobiusMersenneTerm mobiusMersenneTheta)
/-- The first `Y` atoms of the Möbius--Mersenne rung `r`. Local copy of ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n
/-- The rank-one strict-subrank quotient from the first `Y` atoms. Local copy of ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ :=
  mobiusMersennePrefix Y (e + 2) ^ 2 /
    mobiusMersennePrefix Y (2 * e + 2)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.abs_mobiusMersenneTheta_sub_prefix_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem abs_mobiusMersenneTheta_sub_prefix_le
    {Y r : ℕ} (hY : 4 ≤ Y) (hr : 3 ≤ r) :
    |mobiusMersenneTheta r - mobiusMersennePrefix Y r| ≤
      (1 : ℝ) / 3584 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersenneTheta_ge_alpha in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusMersenneTheta_ge_alpha
    {r : ℕ} (hr : 3 ≤ r) :
    (1429 : ℝ) / 1512 ≤ mobiusMersenneTheta r := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersenneTheta_lt_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusMersenneTheta_lt_one
    {r : ℕ} (hr : 3 ≤ r) :
    mobiusMersenneTheta r < 1 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_sub_theta_two_gt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rankOneSubrankQuotient_sub_theta_two_gt
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 480 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsBG
