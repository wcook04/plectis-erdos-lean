/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record section 6.2.1: initial implications (part 2 of 2)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial
open scoped Pointwise
open ArithmeticFunction
open Finset
open Filter
open Topology

namespace PalomarCorpus.E249_08.Shared
/-- Support divisors created by multiplication by `a`, excluding the distinguished divisor `a` itself. Local copy of Erdos249257.CompositeDilationDefect.compositeDilationDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def compositeDilationDefect (A : Set ℕ) (a x : ℕ) : ℕ :=
  by
    classical
    exact ((a * x).divisors.filter fun d =>
      d ∈ A ∧ ¬ d ∣ x ∧ d ≠ a).card
/-- The second Jordan totient, as the integer-valued Dirichlet convolution `μ * id²`. Local copy of Erdos249257.CyclotomicProjectionOfShadow.jordanTotientTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def jordanTotientTwo : ArithmeticFunction ℤ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℤ) *
    (ArithmeticFunction.pow 2 : ArithmeticFunction ℤ)
/-- The manuscript's Lambert value `L(f) = ∑_{n≥1} f(n)/(2ⁿ-1)`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.lambertValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lambertValue (f : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ+, f (n : ℕ) / ((2 : ℝ) ^ (n : ℕ) - 1)
/-- The manuscript's `K_d(N) = N/(d(2ᵈ-1)) + 2ᵈ/(2ᵈ-1)²`, the `d`th term of the Möbius expansion of `R_N` with its sign `μ(d)` removed. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusTermKernel (d N : ℕ) : ℝ :=
  (N : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ d - 1)) + (2 : ℝ) ^ d / (((2 : ℝ) ^ d - 1) ^ 2)
/-- `1 + X^d + ... + X^((q - 1)d)`. Local copy of Erdos249257.RepunitMobiusNumerator.spacedRepunit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def spacedRepunit (d q : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range q, Polynomial.monomial (d * j) 1
/-- The divisor-signed polynomial numerator. For positive `r`, evaluation at `X = 2` is the common-denominator Möbius numerator; the public bridge below is stated only on the formal development.s squarefree boundary. Local copy of Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusNumeratorPolynomial (r : ℕ) : ℤ[X] :=
  ∑ d ∈ r.divisors,
    Polynomial.C (ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))) *
      spacedRepunit d (r / d)
end PalomarCorpus.E249_08.Shared

namespace PalomarCorpus.E249.PaperStatementsAC
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial
export PalomarCorpus.E249_08.Shared (jordanTotientTwo mobiusNumeratorPolynomial spacedRepunit)
/-- States catalogue:mob:b4 from the long record for Erdős problem #249. Transported from Erdos249257.CyclotomicProjectionOfShadow.cyclotomic_dvd_mobiusNumeratorPolynomial_sub in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cyclotomic_dvd_mobiusNumeratorPolynomial_sub
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      mobiusNumeratorPolynomial r -
        Polynomial.C
          (ArithmeticFunction.moebius m * jordanTotientTwo (r / m)) := by
  sorry
/-- States catalogue:mob:b4 from the long record for Erdős problem #249. Transported from Erdos249257.CyclotomicProjectionOfShadow.jordanTotientTwo_eq_prod_primeFactors in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem jordanTotientTwo_eq_prod_primeFactors
    {n : ℕ} (hn : Squarefree n) :
    jordanTotientTwo n =
      ∏ p ∈ n.primeFactors, ((p : ℤ) ^ 2 - 1) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAC

namespace PalomarCorpus.E249.PaperStatementsAQ
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped Polynomial
export PalomarCorpus.E249_08.Shared (jordanTotientTwo)
/-- Integer evaluation `Φ_m(2)`. Local copy of Erdos249257.CyclotomicProjectionOfShadow.cyclotomicEval, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cyclotomicEval (m : ℕ) : ℤ :=
  (Polynomial.cyclotomic m ℤ).eval 2
/-- The Mersenne denominator at exponent `n`. Local copy of Erdos249257.RadicalMobiusShadow.mersenne, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenne (n : ℕ) : ℕ := 2 ^ n - 1
/-- The integral numerator, written as its squarefree-divisor expansion. For `s ⊆ primeFactors(r)`, put `d = ∏ p ∈ s, p`. Then the summand is `(-1)^|s| (r/d) ((2^r-1)/(2^d-1))`. This is exactly the nonzero part of `Σ_{d ∣ r} μ(d) (r/d) ((2^r-1)/(2^d-1))`: nonsquarefree divisors have Möbius coefficient zero. The subset form makes that finite support explicit and keeps the definition executable without factoring irrelevant divisors. Local copy of Erdos249257.RadicalMobiusShadow.mobiusNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusNumerator (r : ℕ) : ℤ :=
  ∑ s ∈ r.primeFactors.powerset,
    (-1 : ℤ) ^ s.card *
      ((r / s.prod id : ℕ) : ℤ) *
        (((mersenne r) / (mersenne (s.prod id)) : ℕ) : ℤ)
/-- States catalogue:mob:b4 from the long record for Erdős problem #249. Transported from Erdos249257.CyclotomicProjectionOfShadow.mobiusNumerator_mod_cyclotomicEval in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusNumerator_mod_cyclotomicEval
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    cyclotomicEval m ∣
      mobiusNumerator r -
        ArithmeticFunction.moebius m * jordanTotientTwo (r / m) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAQ

namespace PalomarCorpus.E249.PaperStatementsAS
open scoped ArithmeticFunction.Moebius
open scoped BigOperators
open scoped Pointwise
open scoped Polynomial
export PalomarCorpus.E249_08.Shared (mobiusNumeratorPolynomial spacedRepunit)
/-- States catalogue:mob:b8a from the long record for Erdős problem #249. Transported from Erdos249257.PrimePowerJumpDynamics.cyclotomic_dvd_primeJump_new_fibre in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cyclotomic_dvd_primeJump_new_fibre
    {r p m : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) (hm : m ∣ r) :
    Polynomial.cyclotomic (m * p) ℤ ∣
      mobiusNumeratorPolynomial (r * p) +
        Polynomial.expand ℤ p (mobiusNumeratorPolynomial r) := by
  sorry
/-- States catalogue:mob:b8b from the long record for Erdős problem #249. Transported from Erdos249257.PrimePowerJumpDynamics.cyclotomic_dvd_primeJump_old_fibre in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cyclotomic_dvd_primeJump_old_fibre
    {r p m : ℕ} (hr : Squarefree r) (hp : p.Prime)
    (hpr : ¬ p ∣ r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      mobiusNumeratorPolynomial (r * p) -
        Polynomial.C ((p : ℤ) ^ 2 - 1) *
          mobiusNumeratorPolynomial r := by
  sorry
end PalomarCorpus.E249.PaperStatementsAS

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
export PalomarCorpus.E249_08.Shared (lambertValue mobiusTermKernel)
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.joint35_coefficient_moments in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem joint35_coefficient_moments :
    ((4 : ℝ) + (-3) + (-2) + 1 = 0)
      ∧ ((4 : ℝ) * 1 + (-3) * 3 + (-2) * 5 + 1 * 15 = 0)
      ∧ ((4 : ℝ) * 1 ^ 2 + (-3) * 3 ^ 2 + (-2) * 5 ^ 2 + 1 * 15 ^ 2 = 152)
      ∧ ((1 : ℝ) * 1 - 3 * 1 - 2 * 1 + 4 = 0)
      ∧ ((3 : ℝ) * 5 - 3 * 3 - 2 * 5 + 4 = 0)
      ∧ ((9 : ℝ) * 25 - 3 * 9 - 2 * 25 + 4 = 152) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.joint35_mobiusTermKernel_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem joint35_mobiusTermKernel_zero (d H : ℕ) :
    mobiusTermKernel d (15 * H) - 3 * mobiusTermKernel d (3 * H)
      - 2 * mobiusTermKernel d (5 * H) + 4 * mobiusTermKernel d H = 0 := by
  sorry
/-- States catalogue:cert:d7 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lambertValue_eq_divisor_sum_series in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lambertValue_eq_divisor_sum_series (f : ℕ → ℝ)
    (hf : Summable (fun p : ℕ+ × ℕ+ =>
      f (p.1 : ℕ) * ((1 : ℝ) / 2) ^ ((p.1 : ℕ) * (p.2 : ℕ)))) :
    lambertValue f
      = ∑' m : ℕ+, (∑ e ∈ (m : ℕ).divisors, f e) * ((1 : ℝ) / 2) ^ (m : ℕ) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel_affine_in_multiplier in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusTermKernel_affine_in_multiplier (d H m : ℕ) :
    mobiusTermKernel d (m * H)
      = (m : ℝ) * ((H : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ d - 1)))
        + (2 : ℝ) ^ d / (((2 : ℝ) ^ d - 1) ^ 2) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel_moment_annihilation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobiusTermKernel_moment_annihilation
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (m : ι → ℕ) (d H : ℕ)
    (hzero : ∑ i, c i = 0) (hfirst : ∑ i, c i * (m i : ℝ) = 0) :
    ∑ i, c i * mobiusTermKernel d (m i * H) = 0 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAE

namespace PalomarCorpus.E249.PaperStatementsBA
open scoped BigOperators
open ArithmeticFunction
export PalomarCorpus.E249_08.Shared (lambertValue)
/-- The Euler totient as an integer-valued arithmetic function. Local copy of MersenneLambertLadder.totientZ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientZ : ArithmeticFunction ℤ :=
  ⟨fun n => (Nat.totient n : ℤ), by simp⟩
/-- **The primitive-conductor weight** `A = φ * μ` (Dirichlet convolution). `A(n)` counts the primitive Dirichlet characters of conductor `n` (OEIS A007431); it is multiplicative, nonnegative, vanishes exactly on `n ≡ 2 (mod 4)`, and satisfies `A(p) = p - 2`, `A(p^e) = (p-1)²·p^(e-2)`. Local copy of MersenneLambertLadder.primWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primWeight : ArithmeticFunction ℤ := totientZ * moebius
/-- States catalogue:cert:d7 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.alpha_divisor_sum_eq_totient in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem alpha_divisor_sum_eq_totient (n : ℕ) :
    ∑ e ∈ n.divisors, ((primWeight e : ℤ) : ℝ) = (Nat.totient n : ℝ) := by
  sorry
/-- States catalogue:cert:d7 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lambertValue_alpha_eq_totientSeries in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lambertValue_alpha_eq_totientSeries :
    lambertValue (fun d => ((primWeight d : ℤ) : ℝ))
      = ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n := by
  sorry
end PalomarCorpus.E249.PaperStatementsBA

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
open Finset
/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`: the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- The integer window obtained from the three cone differences based at `H`. Local copy of Erdos249257.JointExponentTransport.joint35ConeWindow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def joint35ConeWindow (H L : ℕ) : ℤ :=
  windowDiscrepancy (14 * H) H L -
    3 * windowDiscrepancy (2 * H) H L -
    2 * windowDiscrepancy (4 * H) H L
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.joint35ConeWindow_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem joint35ConeWindow_eq (H L : ℕ) :
    joint35ConeWindow H L
      = ∑ j ∈ Finset.range L,
          ((Nat.totient (15 * H + (j + 1)) : ℤ)
            - 3 * (Nat.totient (3 * H + (j + 1)) : ℤ)
            - 2 * (Nat.totient (5 * H + (j + 1)) : ℤ)
            + 4 * (Nat.totient (H + (j + 1)) : ℤ)) * 2 ^ (L - (j + 1)) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.joint35_nonintegral_of_separated_window in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem joint35_nonintegral_of_separated_window {H L : ℕ} (hH : 1 ≤ H)
    (hlow : ((19 * H + 5 * L + 5 : ℕ) : ℤ) < joint35ConeWindow H L % 2 ^ L)
    (hhigh : joint35ConeWindow H L % 2 ^ L
      < 2 ^ L - ((19 * H + 5 * L + 5 : ℕ) : ℤ)) :
    (totientTail (15 * H) - 3 * totientTail (3 * H)
      - 2 * totientTail (5 * H) + 4 * totientTail H) ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.joint35_truncation_error in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem joint35_truncation_error (H L : ℕ) (hH : 1 ≤ H) :
    (2 : ℝ) ^ L * (totientTail (15 * H) - 3 * totientTail (3 * H)
        - 2 * totientTail (5 * H) + 4 * totientTail H)
        - (joint35ConeWindow H L : ℝ)
      = (totientTail (15 * H + L) + 4 * totientTail (H + L))
        - (3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L))
    ∧ |(2 : ℝ) ^ L * (totientTail (15 * H) - 3 * totientTail (3 * H)
        - 2 * totientTail (5 * H) + 4 * totientTail H)
        - (joint35ConeWindow H L : ℝ)|
      ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ)
    ∧ (0 ≤ totientTail (15 * H + L) + 4 * totientTail (H + L)
        ∧ totientTail (15 * H + L) + 4 * totientTail (H + L)
          ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ))
    ∧ (0 ≤ 3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L)
        ∧ 3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L)
          ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ)) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientTail_enclosure in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totientTail_enclosure (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ totientTail n ∧ totientTail n ≤ (n : ℝ) + 1 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAX

namespace PalomarCorpus.E249.PaperStatementsBE
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
export PalomarCorpus.E249_08.Shared (mobiusTermKernel)
/-- Least positive shift sending `N` to a multiple of `d`. Local copy of Erdos249257.ExponentOnlyTransport.transportResidueOffset, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def transportResidueOffset (d N : ℕ) : ℕ := d - N % d
/-- Exact Möbius residue kernel, stated locally so this disjoint transport owner can be validated independently of adjacent projection files. Local copy of Erdos249257.ExponentOnlyTransport.transportResidueKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def transportResidueKernel (d N : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    (2 : ℝ) ^ (d - transportResidueOffset d N) *
      (((N + transportResidueOffset d N : ℕ) : ℝ) /
          ((d : ℝ) * ((2 : ℝ) ^ d - 1)) +
        1 / (((2 : ℝ) ^ d - 1) ^ 2))
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.transportResidueKernel_eq_mobiusTermKernel in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem transportResidueKernel_eq_mobiusTermKernel {d N : ℕ}
    (hd : 0 < d) (hdN : d ∣ N) :
    transportResidueKernel d N
      = ((ArithmeticFunction.moebius d : ℤ) : ℝ) * mobiusTermKernel d N := by
  sorry
end PalomarCorpus.E249.PaperStatementsBE

namespace PalomarCorpus.E249.PaperStatementsAJ
export PalomarCorpus.E249_08.Shared (compositeDilationDefect)
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_eq_zero_of_prime_support in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem composite_dilation_defect_eq_zero_of_prime_support (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (hAprime : ∀ d ∈ A, d.Prime) :
    compositeDilationDefect A a x = 0 := by
  sorry
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_univ_six_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem composite_dilation_defect_univ_six_one :
    ((6 * 1 : ℕ).divisors.filter
        fun d => (d ∈ (Set.univ : Set ℕ) ∧ ¬ d ∣ 1 ∧ d ≠ 6)) = ({2, 3} : Finset ℕ) := by
  sorry
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_univ_six_one_card in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem composite_dilation_defect_univ_six_one_card :
    compositeDilationDefect (Set.univ : Set ℕ) 6 1 = 2 := by
  sorry
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.sum_divisors_totient_ne_totient in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sum_divisors_totient_ne_totient :
    (∀ n : ℕ, ∑ d ∈ n.divisors, Nat.totient d = n) ∧
      (∑ d ∈ (2 : ℕ).divisors, Nat.totient d) = 2 ∧ Nat.totient 2 = 1 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsBD
open Filter
open Topology
export PalomarCorpus.E249_08.Shared (compositeDilationDefect)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_divisor_count in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem composite_dilation_divisor_count (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (ha1 : 1 ≤ a) (hx1 : 1 ≤ x) :
    supportCoeff A (a * x) =
      supportCoeff A x + (if a ∣ x then 0 else 1) +
        compositeDilationDefect A a x := by
  sorry
end PalomarCorpus.E249.PaperStatementsBD
