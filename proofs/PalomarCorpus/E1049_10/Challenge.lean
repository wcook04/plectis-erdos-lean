/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1049, the prime support selectors, published height regions and rational base barrier families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1049, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #1049 remains open, and no theorem
in this entry decides it.
-/

open Filter
open scoped BigOperators

namespace PalomarCorpus.E1049.PrimeSupportSelectors
open Filter
/-- At a rational target a/q with q > 0, two integral rows whose exterior determinant A_1 B_2 - A_2 B_1 is nonzero cannot both have remainder below 1/q: at least one of |B_1 (a/q) - A_1| and |B_2 (a/q) - A_2| is at least 1/q. Nonvanishing of the determinant is the only hypothesis on the rows; no primality, no denominator support condition and no coprimality of a and q is assumed. -/
theorem twoSelector_rationalGap
    (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q)
    (hdet : A₁ * B₂ - A₂ * B₁ ≠ 0) :
    (1 : ℝ) / q ≤
        |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨
      (1 : ℝ) / q ≤
        |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| := by
  sorry
/-- At a rational target a/q with q > 0, an integral linear form B (a/q) - A that does not vanish has absolute value at least 1/q. Nonvanishing of the form is the only hypothesis; no primality, no denominator support condition and no coprimality of a and q is assumed. -/
theorem integerLinearForm_rationalGap
    (a q A B : ℤ) (hq : 0 < q)
    (hne : (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) ≠ 0) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  sorry
/-- For sequences of integral rows whose exterior determinant is nonzero at every index, the two real linear forms B_1 (a/q) - A_1 and B_2 (a/q) - A_2 cannot both tend to zero at a rational target a/q with q > 0. No such pair of selectors jointly witnesses vanishing at a rational point. -/
theorem rationalTwoSelector_notBothTendstoZero
    (a q : ℤ) (hq : 0 < q)
    (A₁ B₁ A₂ B₂ : ℕ → ℤ)
    (hdet : ∀ n, A₁ n * B₂ n - A₂ n * B₁ n ≠ 0) :
    ¬(Tendsto
        (fun n ↦ (B₁ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ n : ℝ))
        atTop (nhds 0) ∧
      Tendsto
        (fun n ↦ (B₂ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ n : ℝ))
        atTop (nhds 0)) := by
  sorry
/-- If two real linear forms at a common real target F have remainders |B_1 F - A_1| and |B_2 F - A_2| at most eps, then their exterior determinant satisfies |A_1 B_2 - A_2 B_1| <= eps (|B_1| + |B_2|), so joint decay is paid for in determinant size. The statement is about real data and uses no change of basis, no integrality and no coefficient-height hypothesis. -/
theorem twoSelector_detHeightDecay_tradeoff
    (A₁ B₁ A₂ B₂ F ε : ℝ)
    (h₁ : |B₁ * F - A₁| ≤ ε) (h₂ : |B₂ * F - A₂| ≤ ε) :
    |A₁ * B₂ - A₂ * B₁| ≤ ε * (|B₁| + |B₂|) := by
  sorry
/-- If a real two by two recombination with |u z - v w| = 1 and all four entries bounded in absolute value by H makes both recombined remainders at most eps >= 0 at a common real target F, then the original exterior determinant satisfies |A_1 B_2 - A_2 B_1| <= 2 H eps (|B_1| + |B_2|). Joint decay reached through a bounded change of basis is still paid for in determinant size; integer unimodular recombination is a special case. -/
theorem twoSelector_unimodularHeightDecay_tradeoff
    (A₁ B₁ A₂ B₂ u v w z F H ε : ℝ)
    (hunimod : |u * z - v * w| = 1)
    (hε : 0 ≤ ε)
    (hu : |u| ≤ H) (hv : |v| ≤ H) (hw : |w| ≤ H) (hz : |z| ≤ H)
    (h₁ : |(u * B₁ + v * B₂) * F - (u * A₁ + v * A₂)| ≤ ε)
    (h₂ : |(w * B₁ + z * B₂) * F - (w * A₁ + z * A₂)| ≤ ε) :
    |A₁ * B₂ - A₂ * B₁| ≤
      2 * H * ε * (|B₁| + |B₂|) := by
  sorry
/-- Let ell be prime, let q > 0 with ell not dividing q, let ell divide both B_1 and B_2, and let ell^2 not divide A_1 B_2 - A_2 B_1. Then at least one of the two rows has the full gap 1/q at the target a/q. This is the arithmetic-facing specialisation of the two-row gap: the hypothesis on ell^2 already forces the determinant to be nonzero, and the prime data records the divisibility interface an approximation family would have to supply. -/
theorem primeSupportedTwoSelector_rationalGap
    {ell : ℕ} (hell : ell.Prime)
    (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q)
    (hellq : ¬ (ell : ℤ) ∣ q)
    (hellB₁ : (ell : ℤ) ∣ B₁)
    (hellB₂ : (ell : ℤ) ∣ B₂)
    (hdet : ¬ (ell : ℤ) ^ 2 ∣ A₁ * B₂ - A₂ * B₁) :
    (1 : ℝ) / q ≤
        |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨
      (1 : ℝ) / q ≤
        |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| := by
  sorry
/-- Let ell be prime with ell dividing B, ell not dividing A, and ell not dividing q > 0. Then |B (a/q) - A| >= 1/q. The prime data certifies the nonvanishing that the unconditional one-row gap takes as a hypothesis. -/
theorem primeSupportedOneRow_rationalGap
    {ell : ℕ} (hell : ell.Prime)
    (a q A B : ℤ) (hq : 0 < q)
    (hellB : (ell : ℤ) ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  sorry
/-- The same conclusion |B (a/q) - A| >= 1/q under prime-power support: ell prime, r nonzero, ell^r dividing B, ell not dividing A, and ell not dividing q > 0. A single copy of ell already suffices for the conclusion; the stronger hypothesis is retained so that a tail exponent can be passed through unchanged. -/
theorem primePowerSupportedOneRow_rationalGap
    {ell r : ℕ} (hell : ell.Prime) (hr : r ≠ 0)
    (a q A B : ℤ) (hq : 0 < q)
    (hellPowB : (ell : ℤ) ^ r ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  sorry
/-- If the second coordinate of each of k pairs of residues modulo N vanishes, then N < 2^k already forces two distinct Boolean selectors with equal selected sums in both coordinates. With one coordinate identically zero the pigeonhole only has to see the other, so the threshold is N rather than N^2. -/
theorem zeroDenominatorCoordinates_binaryCollision
    {N k : ℕ} [NeZero N]
    (w : Fin k → ZMod N × ZMod N)
    (hzero : ∀ i, (w i).2 = 0)
    (hcard : N < 2 ^ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  sorry
end PalomarCorpus.E1049.PrimeSupportSelectors

namespace PalomarCorpus.E1049.PublishedHeightRegions
/-- The parameter region log b / log a < 1/2 - 1/pi^2 of the published Bundschuh-Vaananen criterion, written for a reduced rational base a/b, the definition itself imposing no coprimality, positivity or ordering on a and b. This records only the elementary parameter inequality; their analytic irrationality theorem is not internalised, so membership is applicability of a method rather than an irrationality statement. -/
noncomputable def BundschuhVaananenHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < 1 / 2 - 1 / Real.pi ^ 2
/-- The parameter region log b / log a < 81/200 for a reduced rational base a/b, the definition itself imposing no coprimality, positivity or ordering on a and b. This threshold is defined here as an elementary sub-boundary of the region reached by the project's separate ordinary rational-base theorem; it is not a published criterion and carries no analytic hypothesis. -/
noncomputable def ZudilinHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < (81 : ℝ) / 200
/-- The exact integer comparison 3^81 < 2^200, the verified numerical fact that places the base 3/2 beyond the 81/200 threshold. -/
theorem threeHalves_zudilin_power_obstruction :
    3 ^ 81 < 2 ^ 200 := by
  sorry
/-- The real inequality 81/200 < log 2 / log 3, obtained by taking logarithms in the integer comparison above. -/
theorem eightyOneTwoHundredths_lt_threeHalves_log_ratio :
    (81 : ℝ) / 200 < Real.log 2 / Real.log 3 := by
  sorry
/-- The base 3/2 does not satisfy log 2 / log 3 < 81/200, so it lies outside the region defined above. This is a boundary of method applicability; it proves neither rationality nor irrationality of the corresponding Lambert value. -/
theorem threeHalves_outside_zudilinHeightRegion :
    ¬ ZudilinHeightRegion 3 2 := by
  sorry
/-- The base 3/2 also lies outside the Bundschuh-Vaananen region, since 1/2 - 1/pi^2 = 0.398678816... is below 81/200 and log 2 / log 3 = 0.63092975... already exceeds the larger threshold. Inapplicability of that published criterion proves neither rationality nor irrationality. -/
theorem threeHalves_outside_bundschuhVaananenHeightRegion :
    ¬ BundschuhVaananenHeightRegion 3 2 := by
  sorry
end PalomarCorpus.E1049.PublishedHeightRegions

namespace PalomarCorpus.E1049.RationalBaseBarrier
open scoped BigOperators
/-- The natural number B coeff(N+1) s^(N+1): the magnitude of the forcing term that the cleared-tail recurrence leaves behind at step N, for natural data. -/
noncomputable def rationalBaseForcingNat
    (s B : ℕ) (coeff : ℕ → ℕ) (N : ℕ) : ℕ :=
  B * coeff (N + 1) * s ^ (N + 1)
/-- For a genuine rational base, meaning denominator s >= 2, together with B >= 1 and coeff(N+1) >= 1, the forcing term is at least 2^(N+1). The hypothesis s >= 2 is what separates a rational base from an integer base, where the factor s^(N+1) is 1 and the classical coordinatewise argument survives. -/
theorem twoPow_le_rationalBaseForcingNat
    {s B : ℕ} {coeff : ℕ → ℕ} {N : ℕ}
    (hs : 2 ≤ s) (hB : 1 ≤ B) (hc : 1 ≤ coeff (N + 1)) :
    2 ^ (N + 1) ≤ rationalBaseForcingNat s B coeff N := by
  sorry
end PalomarCorpus.E1049.RationalBaseBarrier

namespace PalomarCorpus.E1049.RationalBaseRegion
open scoped BigOperators
/-- The real Lambert series F(x)=sum over n at least 1 of 1/(x^n-1), with Lean tsum conventions outside its convergence domain; the irrationality theorems use x>1. -/
noncomputable def paperLambert (x : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (x ^ (n + 1) - 1)
/-- The real series sum over k at least zero of 1/(k+x)^2, used at the positive rational arguments in the contour constant. -/
noncomputable def trigammaSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ, 1 / ((k : ℝ) + x) ^ 2
/-- The difference of two trigamma-series values used in the exact contour constant. -/
noncomputable def zudilinJTerm (u v : ℝ) : ℝ :=
  trigammaSeries u - trigammaSeries v
/-- The displayed sum of thirteen trigamma differences at the rational endpoints of the Zudilin parameter intervals. -/
noncomputable def zudilinJ : ℝ :=
  zudilinJTerm (1 / 14) (1 / 12) + zudilinJTerm (1 / 7) (1 / 6) +
    zudilinJTerm (3 / 14) (1 / 4) + zudilinJTerm (2 / 7) (1 / 3) +
    zudilinJTerm (5 / 14) (2 / 5) + zudilinJTerm (3 / 7) (7 / 15) +
    zudilinJTerm (1 / 2) (8 / 15) + zudilinJTerm (4 / 7) (3 / 5) +
    zudilinJTerm (9 / 14) (2 / 3) + zudilinJTerm (5 / 7) (11 / 15) +
    zudilinJTerm (11 / 14) (4 / 5) + zudilinJTerm (6 / 7) (13 / 15) +
    zudilinJTerm (13 / 14) (14 / 15)
/-- The exact homogeneous width-rate constant 1091/2 in the constructed approximation family. -/
noncomputable def zudilinC1 : ℝ := 1091 / 2
/-- The exact cancellation constant 266-(3/pi^2)(225-J), with J given by the thirteen displayed trigamma differences. -/
noncomputable def zudilinC0 : ℝ := 266 - 3 / Real.pi ^ 2 * (225 - zudilinJ)
/-- The exact contour C0/C1 controlling rational-base decay after homogeneous denominator clearing. -/
noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1
/-- The strict inequality log(b)/log(a)<C0/C1; the result separately requires natural a>b>0. -/
noncomputable def ZudilinContourRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < zudilinContour
/-- Reduced integer-numerator, positive-natural-denominator rational approximants to xi with error strictly below q^(-nu). -/
noncomputable def reducedApproximationPairs (ξ ν : ℝ) : Set (ℤ × ℕ) :=
  {r | 0 < r.2 ∧ Nat.Coprime r.1.natAbs r.2 ∧
    |ξ - (r.1 : ℝ) / (r.2 : ℝ)| < (r.2 : ℝ) ^ (-ν)}
/-- The real exponents admitting infinitely many reduced rational approximants at the stated strict error bound. -/
noncomputable def approximationExponents (ξ : ℝ) : Set ℝ :=
  {ν | (reducedApproximationPairs ξ ν).Infinite}
/-- The supremum of approximation exponents for the real target; the theorem applies it to the irrational Lambert values supplied by the same construction. -/
noncomputable def irrationalityExponent (ξ : ℝ) : ℝ :=
  sSup (approximationExponents ξ)
/-- The exact exponent bound (1-log(b)/log(a))/(C0/C1-log(b)/log(a)), with positive denominator on the strict contour region. -/
noncomputable def rationalBaseMeasureBound (a b : ℕ) : ℝ :=
  (1 - Real.log b / Real.log a) /
    (zudilinContour - Real.log b / Real.log a)
/-- For natural a>b>0 in the exact contour region, the literal Lambert value F(a/b) is irrational. The proof supplies the integer forms, positive remainder and decay internally, with no source-supply hypothesis. -/
theorem rational_base_region (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : ZudilinContourRegion a b) :
    Irrational (paperLambert ((a : ℝ) / b)) := by
  sorry
/-- The Lambert value F(31/4) is irrational. -/
theorem thirtyone_four : Irrational (paperLambert ((31 : ℝ) / 4)) := by
  sorry
/-- On the strict contour region for natural a>b>0, bounds the irrationality exponent of F(a/b) by the displayed exact rational-base expression. -/
theorem rational_base_measure (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : ZudilinContourRegion a b) :
    irrationalityExponent (paperLambert ((a : ℝ) / b)) ≤
      rationalBaseMeasureBound a b := by
  sorry
/-- For every positive natural r, the irrationality exponent of F((31/4)^r) is strictly less than the paper fraction 2981509/9909. -/
theorem thirtyone_four_power_measure_lt_paper_fraction (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) <
      (2981509 : ℝ) / 9909 := by
  sorry
end PalomarCorpus.E1049.RationalBaseRegion
