/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #269, the actual shell orbit, all scale lattice and carry mechanism families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #269, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #269 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators

namespace PalomarCorpus.E269_09.Shared
/-- The smooth lattice value `p ^ i * q ^ j * r ^ k` attached to the exponent triple `(i, j, k)`. -/
noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k
/-- The finite set of exponent triples `(i, j, k)`, each entry smaller than `x`, whose smooth value `p ^ i * q ^ j * r ^ k` is strictly less than `x`; for generators at least 2 the entrywise cap is never binding, so the set is exactly the triples whose smooth value is below `x`, and for pairwise distinct primes those values are exactly the `{p, q, r}`-smooth numbers below `x`. -/
noncomputable def strictSmoothExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range x).product ((Finset.range x).product (Finset.range x))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 < x
/-- The exponent triples counted by `strictSmoothExponents` at `y` and not at `x`; for generators at least 2 and `x ≤ y` these are exactly the triples whose smooth value lies in the half open interval from `x` to `y`. -/
noncomputable def strictSmoothShell (p q r x y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothExponents p q r y \ strictSmoothExponents p q r x
/-- The `a`th dyadic shell for the primes 2, 3 and 5: the exponent triples `(i, j, k)` with `2 ^ a ≤ 2 ^ i * 3 ^ j * 5 ^ k < 2 ^ (a + 1)`. -/
noncomputable def dyadicSmoothShell235 (a : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothShell 2 3 5 (2 ^ a) (2 ^ (a + 1))
/-- The three-prime height `H x = p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x`, the product of the largest powers of `p`, `q` and `r` not exceeding `x`; the `Nat.log` convention makes `H 0 = H 1 = 1`, and for pairwise distinct primes and `x` at least 1 this is the least common multiple of the smooth numbers at most `x`. -/
noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x
/-- The normalized state at scale `a` of an arbitrary real tail function `tail`, namely `(H (2 ^ a) / 2) * tail a` with the three-prime height for 2, 3 and 5 cast to the reals and the division taken in the reals. -/
noncomputable def dyadicNormalizedTailStateR235
    (tail : ℕ → ℝ) (a : ℕ) : ℝ :=
  ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a
/-- The rational mass of the `a`th dyadic shell, the sum over that shell of the reciprocal of the three-prime height of the corresponding smooth value. -/
noncomputable def dyadicShellMassQ235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    ((threePrimeHeight 2 3 5
      (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹)
/-- The real cast of the rational shell mass `dyadicShellMassQ235`. -/
noncomputable def dyadicShellMassR235 (a : ℕ) : ℝ :=
  dyadicShellMassQ235 a
/-- The tail of the shell masses from scale `a` onward, taken as the Mathlib unconditional sum of `dyadicShellMassR235 (a + n)` over `n`; summability is proved in `actual_dyadicShellOrbit_recurrence_and_escape`, so this is the genuine infinite sum, and the value at `a = 0` is the reciprocal running least common multiple sum of Erdős problem 269 for the prime set `{2, 3, 5}`. -/
noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ :=
  ∑' n : ℕ, dyadicShellMassR235 (a + n)
end PalomarCorpus.E269_09.Shared

namespace PalomarCorpus.E269.ActualShellOrbit
open scoped BigOperators
export PalomarCorpus.E269_09.Shared (dyadicNormalizedTailStateR235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight)
/-- The predicate that the power `p ^ e` lies strictly inside the dyadic block from `2 ^ a` to `2 ^ (a + 1)`, that is `2 ^ a < p ^ e` and `p ^ e < 2 ^ (a + 1)`; for an odd prime `p` it records that a new pure `p`-power is crossed strictly between two consecutive powers of two, so that the running least common multiple gains one further factor `p` inside that block. -/
noncomputable def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)
/-- The radix of the `a`th dyadic block for the primes 2, 3 and 5: the product of 2 with 3 when some power of 3 lies strictly inside the block from `2 ^ a` to `2 ^ (a + 1)` and with 5 when some power of 5 does, so its value is 2, 6, 10 or 30. It equals the ratio `H (2 ^ (a + 1)) / H (2 ^ a)` of consecutive three-prime running heights. -/
noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 *
        (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
        (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)
/-- The number of points of the `a`th dyadic shell whose smooth value is strictly below `p ^ Nat.log p (2 ^ (a + 1))`, the largest power of `p` not exceeding `2 ^ (a + 1)`; for odd `p`, when no power of `p` lies strictly inside the shell that threshold is at most `2 ^ a` and the count is 0, while at `p = 2` the threshold is `2 ^ (a + 1)` and the count is the whole shell. -/
noncomputable def dyadicBeforeThresholdCount235 (p a : ℕ) : ℕ :=
  ((dyadicSmoothShell235 a).filter fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      p ^ Nat.log p (2 ^ (a + 1))).card
/-- The forcing digit of the `a`th dyadic block for the primes 2, 3 and 5: the shell cardinality corrected by the two threshold counts, with coefficients 10 and 4 when the largest power of 3 below `2 ^ (a + 1)` does not exceed the largest power of 5 below it and with coefficients 2 and 12 otherwise. Its ordinary meaning is the sum over the shell of `H (2 ^ (a + 1)) / (2 * H x)`, a positive integer, and the two coefficient patterns record which of the two odd prime thresholds is the smaller. -/
noncomputable def dyadicOrderedBlockDigit235 (a : ℕ) : ℕ :=
  if 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤ 5 ^ Nat.log 5 (2 ^ (a + 1)) then
    (dyadicSmoothShell235 a).card +
      10 * dyadicBeforeThresholdCount235 3 a +
      4 * dyadicBeforeThresholdCount235 5 a
  else
    (dyadicSmoothShell235 a).card +
      2 * dyadicBeforeThresholdCount235 3 a +
      12 * dyadicBeforeThresholdCount235 5 a
/-- The predicate that the real number `x` lies at distance at least `δ` from every integer, that is `δ ≤ |x - z|` for every integer `z`. -/
noncomputable def FarFromIntegers (x δ : ℝ) : Prop :=
  ∀ z : ℤ, δ ≤ |x - (z : ℝ)|
/-- Three unconditional assertions about the literal `{2,3,5}` shell orbit: the shell masses are summable; at every scale the normalized state satisfies the exact affine recurrence `X (a + 1) = b a * X a - m a` with the actual radix `dyadicBlockBase235 a` and the actual ordered digit `dyadicOrderedBlockDigit235 a` cast to the reals; and either some normalized state equals an integer, or for every index there is a later scale whose state lies at distance at least `1/31` from every integer. The integral branch is not excluded, and no irrationality, transcendence, equidistribution or density conclusion follows. -/
theorem actual_dyadicShellOrbit_recurrence_and_escape :
    Summable dyadicShellMassR235 ∧
      (∀ a : ℕ,
        dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (a + 1) =
          dyadicBlockBase235 a *
              dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a -
            dyadicOrderedBlockDigit235 a) ∧
      ((∃ a : ℕ, ∃ z : ℤ,
          dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a = (z : ℝ)) ∨
        ∀ a₀, ∃ a, a₀ ≤ a ∧
          FarFromIntegers
            (dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a)
            ((1 : ℝ) / 31)) := by
  sorry
end PalomarCorpus.E269.ActualShellOrbit

namespace PalomarCorpus.E269.AllScaleLattice
open scoped BigOperators
export PalomarCorpus.E269_09.Shared (dyadicNormalizedTailStateR235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight)
/-- The integer normalizer `H (2 ^ a) / 2` for the primes 2, 3 and 5, with the division taken in the natural numbers; for `a` at least 1 the height is even and the division is exact, while the value at `a = 0` is 0 because `H 1 = 1`. -/
noncomputable def heightNormalizer235 (a : ℕ) : ℕ :=
  threePrimeHeight 2 3 5 (2 ^ a) / 2
/-- The rational mass of the finite window of `count` consecutive dyadic shells beginning at index `start`, the sum of `dyadicShellMassQ235 (start + i)` over `i < count`. -/
noncomputable def dyadicSmoothWindowMassQ235 (start count : ℕ) : ℚ :=
  ∑ i ∈ Finset.range count, dyadicShellMassQ235 (start + i)
/-- For `p` equal to 2, 3 or 5, for `x` positive and `x < p ^ m`, the product `p * H x` divides `H (p ^ m)`, where `H` is the three-prime height for 2, 3 and 5. This is the prime-power boundary clearing law used by the lattice reduction, and it is a supporting lemma rather than an advertised result. -/
theorem smoothHeight_mul_prime_dvd_boundaryHeight
    {p m x : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 5) (hx : 0 < x) (hlt : x < p ^ m) :
    p * threePrimeHeight 2 3 5 x ∣ threePrimeHeight 2 3 5 (p ^ m) := by
  sorry
/-- For `a` at least 1, twice the natural-number normalizer `H (2 ^ a) / 2` equals `H (2 ^ a)`, so the three-prime height at a dyadic boundary is even and the truncating division is exact. The hypothesis `1 ≤ a` is needed because `H (2 ^ 0) = 1`. Supporting lemma for the clearing arguments. -/
theorem two_mul_heightNormalizer235 (a : ℕ) (ha : 1 ≤ a) :
    2 * heightNormalizer235 a = threePrimeHeight 2 3 5 (2 ^ a) := by
  sorry
/-- For every start index and window length, the normalizer at the top of the window, `H (2 ^ (start + count)) / 2`, multiplied by the rational mass of that window of shells is a natural number, so a finite window of shell masses is cleared exactly by the height at its upper endpoint. -/
theorem heightNormalizer235_mul_windowMass_eq_int (start count : ℕ) :
    ∃ z : ℕ,
      (heightNormalizer235 (start + count) : ℚ) *
        dyadicSmoothWindowMassQ235 start count = (z : ℚ) := by
  sorry
/-- For all `a` and `k`, the tail at `a` equals the finite sum of the shell masses at `a, ..., a + k - 1` plus the tail at `a + k`, the exact finite-depth splitting identity for the actual infinite tail. -/
theorem dyadicShellTsumTailR235_eq_range_add (a k : ℕ) :
    dyadicShellTsumTailR235 a =
      ∑ i ∈ Finset.range k, dyadicShellMassR235 (a + i) +
        dyadicShellTsumTailR235 (a + k) := by
  sorry
/-- If `q` is positive and the tail from the first dyadic shell onward equals `p / q` as a real number, then for every `a` at least 1 the product of `q` with the normalized state at scale `a` is an integer. Rationality of the value therefore places the normalized state on the single lattice of multiples of `1/q`, simultaneously at all dyadic scales from 1 onward. The hypothesis is rationality; nothing here shows the value is irrational. -/
theorem qsmul_normalizedTailState_eq_int_of_value_eq_rat
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ))
    {a : ℕ} (ha : 1 ≤ a) :
    ∃ k : ℤ,
      (q : ℝ) * dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a =
        (k : ℝ) := by
  sorry
/-- If `q` is positive and the tail from the first dyadic shell onward equals `p / q`, then there are indices `i < j` and an integer `z` with the difference of the normalized states at scales `1 + j` and `1 + i` equal to `z`, so rationality forces two distinct scales whose normalized states are congruent modulo 1. Excluding such a collision is not proved here. -/
theorem exists_normalizedTailState_collision_of_value_eq_rat
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) :
    ∃ i j : ℕ, i < j ∧ ∃ z : ℤ,
      dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + j) -
        dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + i) =
          (z : ℝ) := by
  sorry
end PalomarCorpus.E269.AllScaleLattice

namespace PalomarCorpus.E269.CarryMechanism
open scoped BigOperators
/-- The defect `base n * z n - z (n + 1) - digit n`, measuring how far the integer sequence `z` is from satisfying the affine recurrence with radix `base` and digit sequence `digit` at index `n`; it vanishes at every index exactly when `z` is an exact integral orbit of that recurrence. -/
noncomputable def carryLiftPerturbation
    (base digit z : ℕ → ℤ) (n : ℕ) : ℤ :=
  base n * z n - z (n + 1) - digit n
/-- The discrepancy `D * z n - carry n` between `D` times the candidate lift `z` and the actual carry sequence at index `n`. -/
noncomputable def carryLiftError
    (D : ℤ) (z carry : ℕ → ℤ) (n : ℕ) : ℤ :=
  D * z n - carry n
/-- The partial sum of the first `N` terms of a sequence taking values in an additive commutative group. -/
noncomputable def channelPrefix {G : Type*} [AddCommGroup G]
    (ε : ℕ → G) (N : ℕ) : G :=
  ∑ n ∈ Finset.range N, ε n
/-- The condition that the prefix sums of `ε` depend only on the channel label: whenever `jumpBase a` and `jumpBase b` are equal, the prefixes of `ε` at `a` and at `b` are equal. Equivalently, the sum of `ε` over every block of indices between two positions carrying the same label vanishes. The labels range over an arbitrary index type and the values over an arbitrary additive commutative group. -/
noncomputable def ChannelBlockNull {ι G : Type*} [AddCommGroup G]
    (jumpBase : ℕ → ι) (ε : ℕ → G) : Prop :=
  ∀ a b, jumpBase a = jumpBase b →
    channelPrefix ε a = channelPrefix ε b
/-- The three-element type of channel labels `two`, `three` and `five`, with decidable equality, recording which prime channel supplies the jump at a given index. -/
inductive Prime235
  | two
  | three
  | five
  deriving DecidableEq
/-- A contradiction from the following hypotheses taken together: an integer carry with `carry (n + 1) = base n * carry n - D * digit n` at every index; a surjective channel labelling into `Prime235`; block-nullity of the perturbation of a candidate integer lift `z`; genuine `two` to `three` and `two` to `five` transitions at which that perturbation vanishes; a nonzero lift error at index 0; a bound sequence dominating the absolute lift error everywhere; every radix at least 2; and one index `N` at which the bound is smaller than `2 ^ N`. Each of these is assumed, and none is produced for the actual `{2,3,5}` orbit. -/
theorem no_carryLift_of_errorBound_below_twoPow
    (D : ℤ)
    (base digit z carry : ℕ → ℤ)
    (jumpBase : ℕ → Prime235)
    (hcarry :
      ∀ n, carry (n + 1) =
        base n * carry n - D * digit n)
    (hchannel : Function.Surjective jumpBase)
    (hnull :
      ChannelBlockNull jumpBase
        (carryLiftPerturbation base digit z))
    {n23 n25 : ℕ}
    (h23start : jumpBase n23 = .two)
    (h23end : jumpBase (n23 + 1) = .three)
    (h25start : jumpBase n25 = .two)
    (h25end : jumpBase (n25 + 1) = .five)
    (hanchor23 :
      carryLiftPerturbation base digit z n23 = 0)
    (hanchor25 :
      carryLiftPerturbation base digit z n25 = 0)
    (herror0 : carryLiftError D z carry 0 ≠ 0)
    (bound : ℕ → ℕ)
    (hbounded :
      ∀ n, Int.natAbs (carryLiftError D z carry n) ≤ bound n)
    (hbaseTwo : ∀ n, (2 : ℤ) ≤ base n)
    (N : ℕ) (hbelow : bound N < 2 ^ N) :
    False := by
  sorry
/-- A finite four-state incompatibility: four reals in the open unit interval, four integers each within distance strictly less than 1 of the corresponding real, the two anchor equations `2 * z0 - z1 - 1 = 0` and `2 * z2 - z3 - 1 = 0`, and the vanishing first block sum `(2 * z0 - z1 - 1) + (3 * z1 - z2 - 1) = 0` cannot hold together. The statement concerns four abstract states and asserts nothing about the actual shell orbit. -/
theorem no_unitAccurateLift_with_twoAnchors_and_firstTwoBlockNull
    (T0 T1 T2 T3 : ℝ)
    (z0 z1 z2 z3 : ℤ)
    (hT0 : 0 < T0 ∧ T0 < 1)
    (hT1 : 0 < T1 ∧ T1 < 1)
    (hT2 : 0 < T2 ∧ T2 < 1)
    (hT3 : 0 < T3 ∧ T3 < 1)
    (hacc0 : |(z0 : ℝ) - T0| < 1)
    (hacc1 : |(z1 : ℝ) - T1| < 1)
    (hacc2 : |(z2 : ℝ) - T2| < 1)
    (hacc3 : |(z3 : ℝ) - T3| < 1)
    (hanchor23 : 2 * z0 - z1 - 1 = 0)
    (hanchor25 : 2 * z2 - z3 - 1 = 0)
    (hfirstBlock :
      (2 * z0 - z1 - 1) +
        (3 * z1 - z2 - 1) = 0) :
    False := by
  sorry
/-- If the channel labelling into `Prime235` is surjective, the integer sequence `ε` is block-null for it, and `ε` vanishes at an index carrying a genuine `two` to `three` transition and at an index carrying a genuine `two` to `five` transition, then `ε` vanishes at every index. Supporting rigidity lemma for the carry-lift no-go theorems. -/
theorem perturbation_eq_zero_of_blockNull_twoAnchors
    {jumpBase : ℕ → Prime235}
    {ε : ℕ → ℤ}
    (hbase : Function.Surjective jumpBase)
    (hnull : ChannelBlockNull jumpBase ε)
    {n23 n25 : ℕ}
    (h23start : jumpBase n23 = .two)
    (h23end : jumpBase (n23 + 1) = .three)
    (h25start : jumpBase n25 = .two)
    (h25end : jumpBase (n25 + 1) = .five)
    (hanchor23 : ε n23 = 0)
    (hanchor25 : ε n25 = 0) :
    ∀ n, ε n = 0 := by
  sorry
/-- An exact identity for any integer carry obeying `carry (n + 1) = base n * carry n - D * digit n` and any `a ≤ b`: `D` times the sum of the lift perturbation over the interval from `a` to `b` equals the lift error at `a` minus the lift error at `b`, plus the sum over that interval of `(base n - 1)` times the lift error at `n`. The identity displays the endpoint and weighted interior error terms and cancels neither. -/
theorem carryLift_blockDefect
    (D : ℤ)
    (base digit z carry : ℕ → ℤ)
    (hcarry :
      ∀ n, carry (n + 1) =
        base n * carry n - D * digit n)
    (a b : ℕ) (hab : a ≤ b) :
    D * (∑ n ∈ Finset.Ico a b,
      carryLiftPerturbation base digit z n) =
      carryLiftError D z carry a -
        carryLiftError D z carry b +
      ∑ n ∈ Finset.Ico a b,
        (base n - 1) * carryLiftError D z carry n := by
  sorry
/-- The residue of the carry value `c` modulo `B`, using integer remainder. -/
noncomputable def carryResidue (B c : ℤ) : ℤ := c % B
/-- The quotient of the carry value `c` by `B`, using integer division. -/
noncomputable def carryQuotient (B c : ℤ) : ℤ := c / B
/-- The digit read off from one step of the residue coordinate, `(base * residue - nextResidue) / B`, using integer division. -/
noncomputable def residueDigit (B base residue nextResidue : ℤ) : ℤ :=
  (base * residue - nextResidue) / B
/-- For `B` positive and any integer carry with `carry (n + 1) = base n * carry n - B * digit n`, writing the residue as `carry n` modulo `B` and the quotient as `carry n` divided by `B`, every digit decomposes as the residue digit at that step plus `base n` times the quotient at `n` minus the quotient at `n + 1`. The decomposition separates a finite residue part from an integral coboundary; the quotient coordinate remains uncontrolled. -/
theorem carry_eq_residueDigit_add_coboundary
    (B : ℤ) (hB : 0 < B)
    (base carry digit : ℕ → ℤ)
    (hrec : ∀ n,
      carry (n + 1) = base n * carry n - B * digit n) :
    let residue := fun n => carryResidue B (carry n)
    let quotient := fun n => carryQuotient B (carry n)
    ∀ n,
      digit n =
        residueDigit B (base n)
          (residue n) (residue (n + 1)) +
        base n * quotient n - quotient (n + 1) := by
  sorry
end PalomarCorpus.E269.CarryMechanism
