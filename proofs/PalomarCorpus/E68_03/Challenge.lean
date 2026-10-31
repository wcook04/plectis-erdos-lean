/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #68, record section 5.1: all solutions and their remainders modulo integers (part 1 of 2)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #68, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #68 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Finsupp

namespace PalomarCorpus.E68_03.Shared
/-- The common denominator `L D = lcm (d! - 1)` taken over the channel indices `2 ≤ d ≤ D`, the least common multiple of the denominators of the partial sum through `D`; the index set is empty and the value is `1` when `D < 2`. -/
noncomputable def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)
end PalomarCorpus.E68_03.Shared

namespace PalomarCorpus.E68.ResidualIntegerClass
open scoped BigOperators
open Finsupp
export PalomarCorpus.E68_03.Shared (channelLCM)
/-- The channel weight `W d i = i! / (d!)^(i / d)`, computed with natural division and an exact integer because `(d!)^(i / d)` divides `i!`; the value is `i!` whenever `d ≤ 1` or `d > i`. -/
noncomputable def channelWeight (i d : ℕ) : ℕ :=
  i.factorial / (d.factorial ^ (i / d))
/-- The `d`-th divisor channel numerator `V d (lam)`, the finite sum of `lam i * channelWeight i d` over the support of `lam`; because `d!` is congruent to `1` modulo `d! - 1`, this integer agrees with the factorial moment of `lam` modulo `d! - 1`. -/
noncomputable def channelNumerator (lam : ℕ →₀ ℤ) (d : ℕ) : ℤ :=
  lam.sum fun i z => z * (channelWeight i d : ℤ)
/-- The factorial moment `M (lam) = ∑ lam i * i!` of a finitely supported integer vector. -/
noncomputable def factorialMoment (lam : ℕ →₀ ℤ) : ℤ :=
  lam.sum fun i z => z * (i.factorial : ℤ)
/-- The adjacent factorial difference `T n = n * e (n - 1) - e n`, the finitely supported integer vector with coefficient `n` at index `n - 1` and coefficient `-1` at index `n`, the subtraction `n - 1` taken in the natural numbers; for `n ≥ 1` its factorial moment vanishes because `n * (n - 1)! = n!`. -/
noncomputable def adjacentDifference (n : ℕ) : ℕ →₀ ℤ :=
  single (n - 1) (n : ℤ) - single n 1
/-- The isolated channel unit `U n`, defined by strong recursion as `T n` minus the sum of `channelWeight n d * U d` over the divisors `d` of `n` with `2 ≤ d < n`, and as the zero vector for `n ≤ 1`; the recursion cancels every proper divisor channel, so `U n` has zero factorial moment and acts only on the channel at `n`. -/
noncomputable def isolatedChannelUnit (n : ℕ) : ℕ →₀ ℤ :=
  n.strongRecOn' fun n rec =>
    if n ≤ 1 then 0
    else
      adjacentDifference n -
        ∑ d ∈ (Finset.Ico 2 n).attach,
          if d.1 ∣ n then
            (channelWeight n d.1 : ℤ) • rec d.1 (Finset.mem_Ico.mp d.2).2
          else 0
/-- The `j`-th column of the divisor channel basis: the unit vector at index `1` when `j = 0`, and the isolated channel unit `U (j + 1)` when `j ≥ 1`. -/
noncomputable def channelBasisColumn (j : ℕ) : ℕ →₀ ℤ :=
  if j = 0 then single 1 1 else isolatedChannelUnit (j + 1)
/-- The finitely supported integer vector assembled from coordinates `a` in the divisor channel basis, namely the finite sum of `a j` scaled copies of `channelBasisColumn j`. -/
noncomputable def channelSynthesis (a : ℕ →₀ ℤ) : ℕ →₀ ℤ :=
  a.sum (fun j z => z • channelBasisColumn j)
/-- The divisor channel coordinates of the canonical low channel kernel at depth `D`: the value `L D` in coordinate `0`, which carries the unit vector at index `1`, and the value `-(L D / (d! - 1))` in coordinate `d - 1`, which carries `U d`, for each `d` with `2 ≤ d ≤ D`. -/
noncomputable def kernelCoordinates (D : ℕ) : ℕ →₀ ℤ :=
  single 0 (channelLCM D : ℤ) -
    ∑ d ∈ Finset.Icc 2 D,
      single (d - 1) ((channelLCM D : ℤ) / ((d.factorial : ℤ) - 1))
/-- The canonical low channel kernel `K D = L D * e 1 - ∑_{2 ≤ d ≤ D} (L D / (d! - 1)) * U d`, the vector of factorial moment `L D` whose channel numerators vanish at every `d` with `2 ≤ d ≤ D`. -/
noncomputable def canonicalKernel (D : ℕ) : ℕ →₀ ℤ :=
  channelSynthesis (kernelCoordinates D)
/-- The condition that the divisor channel coordinates `z` vanish below index `D`, so for `D ≥ 1` the vector they synthesise uses only the isolated channel units `U n` with `n > D`. -/
noncomputable def TailCoordinates (D : ℕ) (z : ℕ →₀ ℤ) : Prop :=
  ∀ j, j < D → z j = 0
/-- The pairing `∑ z i * w i` of finitely supported integer coordinates `z` against an integer weight function `w`. -/
noncomputable def integerEvaluation (w : ℕ → ℤ) (z : ℕ →₀ ℤ) : ℤ :=
  z.sum (fun i c => c * w i)
/-- The coordinate mass of `z`, the sum of its coordinates, obtained by pairing `z` with the constant weight `1`. -/
noncomputable def coordinateMass (z : ℕ →₀ ℤ) : ℤ :=
  integerEvaluation (fun _ => 1) z
/-- The contribution of the channel `d` to the full residual, equal to the channel numerator `V d (f)` divided by `d! - 1` for `d > 1` and `0` for `d ≤ 1`, the guard excluding the vanishing moduli at `d = 0` and `d = 1`. -/
noncomputable def fullResidualTerm (f : ℕ →₀ ℤ) (d : ℕ) : ℝ :=
  if 1 < d then (channelNumerator f d : ℝ) /
    ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ) else 0
/-- The full residual of a finitely supported integer vector, the infinite sum over all `d` of the contributions `fullResidualTerm f d`. -/
noncomputable def fullResidual (f : ℕ →₀ ℤ) : ℝ :=
  ∑' d : ℕ, fullResidualTerm f d
/-- The real value of the exact prefix `H D = ∑_{2 ≤ d ≤ D} 1/(d! - 1)`. -/
noncomputable def gapPrefixReal (D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 D, (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)
/-- The Erdős 68 series `S = ∑_{n ≥ 2} 1/(n! - 1)` as a real infinite sum, with the terms at `n ≤ 1` set to zero so that the vanishing modulus `1! - 1` never occurs. -/
noncomputable def factorialGapSeries : ℝ :=
  ∑' n : ℕ, if 1 < n then (1 : ℝ) / (((n.factorial : ℤ) - 1 : ℤ) : ℝ) else 0
/-- The transparency identity: for `D ≥ 2`, an integer `t` and coordinates `z` vanishing below `D`, the full residual of `t • K D + channelSynthesis z` equals `t * L D * (S - H D) + coordinateMass z`; the residual of every vector written in the low channel normal form of the statement is therefore the scaled factorial gap tail plus an integer, so an integral channel correction can move it only by an integer. -/
theorem residual_transparency {D : ℕ} (hD : 2 ≤ D) (t : ℤ)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    fullResidual (t • canonicalKernel D + channelSynthesis z) =
      (t : ℝ) * (channelLCM D : ℝ) *
        (factorialGapSeries - gapPrefixReal D) +
      (coordinateMass z : ℝ) := by
  sorry
/-- Supporting convergence lemma: for a finitely supported integer vector `f` with `f 0 = 0`, the family of channel contributions `fullResidualTerm f` is summable. The hypothesis `f 0 = 0` excludes the index 0 coefficient, whose channel weight is 1 in every channel; the statement assumes it and this entry does not establish whether it can be dropped. -/
theorem summable_fullResidual {f : ℕ →₀ ℤ} (h0 : f 0 = 0) :
    Summable (fullResidualTerm f) := by
  sorry
/-- If `f 0 = 0` and the factorial moment of `f` vanishes, then the full residual of `f` is an integer. The hypothesis `f 0 = 0` excludes the index 0 coefficient, whose channel weight is 1 in every channel; the statement assumes it and this entry does not establish whether it can be dropped. -/
theorem zero_moment_residual_integral {f : ℕ →₀ ℤ}
    (h0 : f 0 = 0) (hm : factorialMoment f = 0) :
    ∃ k : ℤ, fullResidual f = (k : ℝ) := by
  sorry
/-- If `f 0 = 0`, `g 0 = 0` and `f` and `g` have the same factorial moment, then their full residuals differ by an integer, so on vectors vanishing at index `0` the factorial moment fixes the residual class modulo the integers. The hypothesis `f 0 = 0` excludes the index 0 coefficient, whose channel weight is 1 in every channel; the statement assumes it and this entry does not establish whether it can be dropped. -/
theorem equal_moment_residual_integer_difference {f g : ℕ →₀ ℤ}
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hm : factorialMoment f = factorialMoment g) :
    ∃ k : ℤ, fullResidual f - fullResidual g = (k : ℝ) := by
  sorry
end PalomarCorpus.E68.ResidualIntegerClass

namespace PalomarCorpus.E68.PaperStatementsB
open scoped BigOperators
export PalomarCorpus.E68_03.Shared (channelLCM)
/-- States long68:res:channel-radius from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.radius_no_eventual_ratio_upper in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem radius_no_eventual_ratio_upper (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      (((R t : ℕ) : ℝ) + 1) / (t : ℝ) ^ 3 ≤ (3 : ℝ) / 2 := by
  sorry
/-- States long68:res:channel-radius from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.radius_not_littleO in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem radius_not_littleO (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    ¬ (fun t : ℕ => (R t : ℝ)) =o[Filter.atTop]
      (fun t : ℕ => (t : ℝ) ^ 3) := by
  sorry
/-- States long68:res:channel-radius from the long record for Erdős problem #68. Transported from ErdosProblems.Erdos68.PaperComplete.square_subsequence_radius in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem square_subsequence_radius {t M R : ℕ}
    (ht : 2 ^ 32 ≤ t) (hM : 0 < M)
    (hdiv : channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    3 * t ^ 3 < 2 * (R + 1) := by
  sorry
end PalomarCorpus.E68.PaperStatementsB
