/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #68, the multiplicative successor rigidity, prime pole and prime unit translator families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #68, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #68 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators

namespace PalomarCorpus.E68.MultiplicativeSuccessorRigidity
open scoped BigOperators
/-- The Erdős 68 series `S = ∑_{n ≥ 2} 1/(n! - 1)` as a real infinite sum, with the terms at `n ≤ 1` set to zero so that the vanishing modulus `1! - 1` never occurs. -/
noncomputable def factorialGapSeries : ℝ :=
  ∑' n : ℕ, if 1 < n then (1 : ℝ) / (((n.factorial : ℤ) - 1 : ℤ) : ℝ) else 0
/-- The exact rational partial sum `H n = ∑_{2 ≤ k ≤ n} 1/(k! - 1)`, computed in `ℚ` with no real approximation; it is `0` for `n < 2`. -/
noncomputable def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)
/-- Computable rational form of `strictFacTop`, used for exact finite certificates while retaining the real-valued statement needed for the series. Local copy of ErdosProblems.Erdos68.strictFacTopRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1
/-- The strict successor `Z m = ⌊m! * H m⌋ + 1` of the exact rational prefix, the least integer strictly above the factorially scaled prefix at index `m`. -/
noncomputable def gapSuccessor (m : ℕ) : ℤ :=
  strictFacTopRat (factorialGapPrefix m) m
/-- If `d` is a positive natural number and `S` fails to be irrational, then there is a bound `B` with `d ∣ Z m` for every `m > B`; on the rational branch every fixed modulus eventually divides the strict successor. -/
theorem eventually_dvd_gapSuccessor_of_not_irrational
    {d : ℕ} (hd : 0 < d)
    (hrat : ¬ Irrational factorialGapSeries) :
    ∃ B : ℕ, ∀ m : ℕ, B < m → (d : ℤ) ∣ gapSuccessor m := by
  sorry
/-- The contrapositive producer: if `d` is a positive natural number and for every bound `B` there is `m > B` with `d` not dividing `Z m`, then `S` is irrational. The hypothesis is cofinal failure of one congruence fixed in advance, and this entry does not establish it for any `d`. -/
theorem irrational_factorialGapSeries_of_cofinal_not_dvd_gapSuccessor
    {d : ℕ} (hd : 0 < d)
    (h : ∀ B : ℕ, ∃ m : ℕ, B < m ∧ ¬ (d : ℤ) ∣ gapSuccessor m) :
    Irrational factorialGapSeries := by
  sorry
/-- The case `d = 2` of the preceding criterion: if for every bound `B` there is `m > B` with `Z m` odd, then `S` is irrational. -/
theorem irrational_factorialGapSeries_of_cofinal_odd_gapSuccessor
    (h : ∀ B : ℕ, ∃ m : ℕ, B < m ∧ ¬ (2 : ℤ) ∣ gapSuccessor m) :
    Irrational factorialGapSeries := by
  sorry
/-- If `S` fails to be irrational, then there is a bound `B` beyond which `Z m` is even, so the strict successors cannot be odd cofinally on the rational branch. -/
theorem not_eventually_odd_gapSuccessor_of_not_irrational
    (hrat : ¬ Irrational factorialGapSeries) :
    ∃ B : ℕ, ∀ m : ℕ, B < m → (2 : ℤ) ∣ gapSuccessor m := by
  sorry
end PalomarCorpus.E68.MultiplicativeSuccessorRigidity

namespace PalomarCorpus.E68.PrimePole
open scoped BigOperators
/-- The prefix common denominator, the least common multiple of `n! - 1` over `2 ≤ n ≤ M`. -/
noncomputable def factorialGapPrefixLCM (M : ℕ) : ℕ :=
  (Finset.Icc 2 M).lcm fun n => n.factorial - 1
/-- The numerator obtained by writing the finite prefix sum over the literal prefix common denominator, namely the sum over `2 ≤ n ≤ M` of `factorialGapPrefixLCM M / (n! - 1)`. -/
noncomputable def factorialGapPrefixLCMNumerator (M : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 2 M,
    factorialGapPrefixLCM M / (n.factorial - 1)
/-- The set of indices `n` with `2 ≤ n ≤ M` whose denominator `n! - 1` has exact `q`-adic exponent `e`, that is `q^e` divides `n! - 1` and `q^(e + 1)` does not. -/
noncomputable def factorialGapMaxHits (q M e : ℕ) : Finset ℕ :=
  (Finset.Icc 2 M).filter fun n =>
    q ^ e ∣ n.factorial - 1 ∧
      ¬q ^ (e + 1) ∣ n.factorial - 1
/-- The reciprocal residue of the maximal valuation layer, the sum in `ZMod q` over those indices of the inverses of the cofactors `(n! - 1) / q^e`. -/
noncomputable def factorialGapPrincipalResidue (q M e : ℕ) : ZMod q :=
  ∑ n ∈ factorialGapMaxHits q M e,
    (((n.factorial - 1) / q ^ e : ℕ) : ZMod q)⁻¹
/-- If `q` is prime, `e ≥ 1`, no index `n` with `2 ≤ n ≤ M` has `q^(e + 1)` dividing `n! - 1`, and some index has `q^e` dividing `n! - 1`, then in `ZMod q` the prefix numerator equals the image of the cofactor `factorialGapPrefixLCM M / q^e` times the reciprocal residue of the maximal layer; since that cofactor is a unit modulo `q`, the prime power `q^e` survives reduction of the prefix exactly when the reciprocal residue is nonzero. The statement assigns no valuation to the infinite series. -/
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
  sorry
end PalomarCorpus.E68.PrimePole

namespace PalomarCorpus.E68.PrimeUnitTranslator
/-- The factorial moment of a finite family of integer coefficients placed at natural indices, the sum over the index type of `coeff j * (index j)!`. -/
noncomputable def factorialMoment {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) : ℤ :=
  ∑ j, coeff j * (index j).factorial
/-- The `d`-th channel numerator of such a family, the sum over the index type of `coeff j * ((index j)! / (d!)^(index j / d))`, the inner weight being an exact natural division. -/
noncomputable def channelNumerator {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℤ :=
  ∑ j, coeff j * ((index j).factorial /
    d.factorial ^ (index j / d) : ℕ)
/-- The coefficient pair `(p, -1)` of the prime translator, as a function on `Fin 2`. -/
noncomputable def primeTranslatorCoeff (p : ℕ) : Fin 2 → ℤ := ![(p : ℤ), -1]
/-- The index pair `(p - 1, p)` carrying the prime translator coefficients, with the subtraction taken in the natural numbers. -/
noncomputable def primeTranslatorIndex (p : ℕ) : Fin 2 → ℕ := ![p - 1, p]
/-- The contribution of the channel `d` to the residual beyond a cutoff `D`, equal to the channel numerator at `d` divided by `d! - 1` when `D < d`, and `0` otherwise. -/
noncomputable def channelResidualTerm {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℝ :=
  if D < d then
    (channelNumerator coeff index d : ℝ) /
      (((d.factorial : ℤ) - 1 : ℤ) : ℝ)
  else 0
/-- The residual of a finite coefficient family beyond the cutoff `D`, the infinite sum over `d` of the contributions `channelResidualTerm D coeff index d`. -/
noncomputable def channelResidual {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) : ℝ :=
  ∑' d : ℕ, channelResidualTerm D coeff index d
/-- The coefficients of the family enlarged by `z` copies of the prime translator at `p`, defined on the disjoint union of the original index type with `Fin 2`. -/
noncomputable def appendPrimeTranslatorCoeff {ι : Type*}
    (coeff : ι → ℤ) (p : ℕ) (z : ℤ) : Sum ι (Fin 2) → ℤ :=
  Sum.elim coeff (fun j => z * primeTranslatorCoeff p j)
/-- The indices of that enlarged family, the original indices together with `p - 1` and `p`. -/
noncomputable def appendPrimeTranslatorIndex {ι : Type*}
    (index : ι → ℕ) (p : ℕ) : Sum ι (Fin 2) → ℕ :=
  Sum.elim index (primeTranslatorIndex p)
/-- For a family of `n + 1` indices, the square integer matrix whose first row holds the factorial values `(index j)!` and whose row `d + 1` holds the channel weight of `index j` at the channel `d + 2`. -/
noncomputable def augmentedChannelMomentMatrix {n : ℕ}
    (index : Fin (n + 1) → ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun r j =>
    Fin.cases ((index j).factorial : ℤ)
      (fun d : Fin n =>
        ((index j).factorial /
          (d.val + 2).factorial ^ (index j / (d.val + 2)) : ℕ)) r
/-- The integer coefficient vector obtained by Cramer's rule from the augmented matrix and the first standard basis vector; applying the matrix to it returns the determinant times that basis vector, so the channel numerators at `2` through `n + 1` vanish and the factorial moment equals the determinant. -/
noncomputable def cramerChannelKernelCoeff {n : ℕ}
    (index : Fin (n + 1) → ℕ) : Fin (n + 1) → ℤ :=
  (augmentedChannelMomentMatrix index).cramer (Pi.single 0 1)
/-- The common grid scale `(D!)^2` at cutoff `D`, a step divisible by every `d` with `2 ≤ d ≤ D`. -/
noncomputable def factorialGridScale (D : ℕ) : ℕ := D.factorial ^ 2
/-- The arithmetic grid of `n + 2` indices `(t + j) * ((n + 2)!)^2` for `j < n + 2`, an equally spaced block of support indices starting at `t * ((n + 2)!)^2`. -/
noncomputable def factorialGridIndex (n t : ℕ) (j : Fin (n + 2)) : ℕ :=
  (t + j.val) * factorialGridScale (n + 2)
/-- Component fact: for `p > 0` the prime translator has factorial moment zero, since `p * (p - 1)! = p!`. -/
theorem primeTranslator_moment_zero
    {p : ℕ} (hp : 0 < p) :
    factorialMoment (primeTranslatorCoeff p) (primeTranslatorIndex p) = 0 := by
  sorry
/-- Component fact: for a prime `p` and a channel `d` with `2 ≤ d < p`, the channel numerator of the prime translator vanishes. -/
theorem primeTranslator_channel_zero_of_lt_p
    {p d : ℕ} (hp : p.Prime) (hd2 : 2 ≤ d) (hdp : d < p) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by
  sorry
/-- Component fact: for a prime `p` the channel numerator of the prime translator at the channel `p` equals `p! - 1`, exactly the modulus of that channel. -/
theorem primeTranslator_channel_at_prime
    {p : ℕ} (hp : p.Prime) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) p =
      (p.factorial : ℤ) - 1 := by
  sorry
/-- Component fact: for `p > 0` and any channel `d > p`, the channel numerator of the prime translator vanishes. -/
theorem primeTranslator_channel_zero_of_p_lt
    {p d : ℕ} (hp : 0 < p) (hpd : p < d) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by
  sorry
/-- For `2 ≤ D` and a prime `p > D`, the residual of the prime translator beyond the cutoff `D` equals exactly `1`, so the translator is an exact unit direction for the residual. -/
theorem primeTranslator_channelResidual_eq_one
    {D p : ℕ} (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (primeTranslatorCoeff p) (primeTranslatorIndex p) = 1 := by
  sorry
/-- For any finite coefficient family, any `2 ≤ D` and any prime `p > D`, enlarging the family by `z` copies of the prime translator changes the residual beyond `D` by exactly the integer `z` and leaves the rest of the residual unchanged. -/
theorem channelResidual_appendPrimeTranslator
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) {D p : ℕ} (z : ℤ)
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (appendPrimeTranslatorCoeff coeff p z)
        (appendPrimeTranslatorIndex index p) =
      channelResidual D coeff index + (z : ℝ) := by
  sorry
/-- For every cutoff parameter `n` and every support threshold `B` there exist a prime `p` and an integer `z` such that the Cramer coefficient vector on the factorial grid starting at `B + 1`, enlarged by `z` copies of the prime translator at `p`, has every support index above `B`, has vanishing channel numerator at every `d` with `2 ≤ d ≤ n + 2`, has nonzero factorial moment, and has residual beyond `n + 2` of absolute value at most `1/2`. The bound is not strict, so the reduced residual may be an integer, and no nonintegrality is asserted. -/
theorem exists_remote_factorialGrid_primeTranslator_reduction
    (n B : ℕ) :
    ∃ p : ℕ, ∃ z : ℤ,
      p.Prime ∧
      (∀ j : Sum (Fin (n + 2)) (Fin 2),
        B < appendPrimeTranslatorIndex
          (factorialGridIndex n (B + 1)) p j) ∧
      (∀ d ∈ Finset.Icc 2 (n + 2),
        channelNumerator
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p) d = 0) ∧
      factorialMoment
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p) ≠ 0 ∧
      |channelResidual (n + 2)
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p)| ≤ (1 : ℝ) / 2 := by
  sorry
end PalomarCorpus.E68.PrimeUnitTranslator
