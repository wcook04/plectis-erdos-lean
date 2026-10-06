/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, the paper structures s, paper structures t and paper structures u families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Filter
open Finset
open Topology
open ArithmeticFunction

namespace PalomarCorpus.E249_33.Shared
/-- The signed binary discrepancy `D_{h,N,L} = ∑_{j < L} (φ(N + h + 1 + j) - φ(N + 1 + j)) 2 ^ (L - 1 - j)` between two length-`L` totient windows separated by the shift `h`, an integer satisfying `|2 ^ L (R_{N + h} - R_N) - D_{h,N,L}| ≤ N + h + L + 2`. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
end PalomarCorpus.E249_33.Shared

namespace PalomarCorpus.E249.PaperStructuresS
open scoped BigOperators
/-- Local definition positiveRadixValue, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def positiveRadixValue (B : ℕ) (f : ℕ → ℚ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, (f (Nat.totient (n + 1) % m) : ℝ) / (B : ℝ) ^ (n + 1)
/-- Local definition radixValue, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def radixValue (B : ℕ) (a : ℕ → ℤ) : ℝ :=
  ∑' n : ℕ, (a n : ℝ) / (B : ℝ) ^ n
/-- States prop:dilations from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.FiniteDilationLinearIndependent.linearIndependent_one_and_least_residue_values in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem linearIndependent_one_and_least_residue_values
    (m B : ℕ) (hm : 3 ≤ m) (hB : 2 ≤ B) :
    LinearIndependent ℚ (fun d : ℕ =>
      if d = 0 then (1 : ℝ) else
        positiveRadixValue (B ^ d) (fun r : ℕ => (r : ℚ)) m) := by
  sorry
/-- States prop:dilations from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.FiniteDilationMixedModuli.rational_mixed_moduli_with_constant_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_mixed_moduli_with_constant_iff
    (D : Finset ℕ) (k : ℕ → ℕ)
    (f : (d : ℕ) → ZMod (2 ^ (k d)) → ℚ) (B : ℕ) (q₀ : ℚ)
    (hB : 2 ≤ B)
    (hpos : ∀ d ∈ D, 0 < d)
    (hk : ∀ d ∈ D, 0 < k d) :
    (∃ q : ℚ, (q₀ : ℝ) + (∑ d ∈ D, ∑' n : ℕ,
      (f d (Nat.totient (n + 1) : ZMod (2 ^ (k d))) : ℝ) /
        ((B : ℝ) ^ d) ^ (n + 1)) = (q : ℝ)) ↔
      ∀ d ∈ D, ∀ r : ℕ, r < 2 ^ (k d) → Even r →
        f d (r : ZMod (2 ^ (k d))) = f d 0 := by
  sorry
/-- States prop:radixresidue from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables.positiveRadixValue_eq_of_even_constant in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem positiveRadixValue_eq_of_even_constant
    (B : ℕ) (hB : 2 ≤ B) {k : ℕ} (hk : 1 ≤ k)
    (f : ℕ → ℚ) (c : ℚ)
    (hc : ∀ r, r < 2 ^ k → r % 2 = 0 → f r = c) :
    positiveRadixValue B f (2 ^ k) =
      ((B : ℝ) + 1) / (B : ℝ) ^ 2 * (f 1 : ℝ) +
        (c : ℝ) / ((B : ℝ) ^ 2 * ((B : ℝ) - 1)) := by
  sorry
/-- States prop:radixresidue from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.radix_residue_series_irrational in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem radix_residue_series_irrational
    (B : ℕ) (hB : 2 ≤ B) {m : ℕ} (hm : 3 ≤ m) :
    Irrational (radixValue B (fun n => (Nat.totient n % m : ℤ))) := by
  sorry
/-- States prop:radixresidue from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.rational_zmod_radix_observable_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_zmod_radix_observable_iff
    (B : ℕ) (hB : 2 ≤ B) {k : ℕ} (hk : 1 ≤ k)
    (f : ZMod (2 ^ k) → ℚ) :
    (∃ q : ℚ,
      (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
        (B : ℝ) ^ (n + 1)) = (q : ℝ)) ↔
      ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = f 0 := by
  sorry
end PalomarCorpus.E249.PaperStructuresS

namespace PalomarCorpus.E249.PaperStructuresT
open Filter
open Finset
open Topology
export PalomarCorpus.E249_33.Shared (windowDiscrepancy)
/-- Local definition pivotOffset, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pivotOffset (L s : ℕ) : ℕ := L - s + 1
/-- Local definition pivotArgument, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pivotArgument (N L s : ℕ) : ℕ := N + pivotOffset L s
/-- Local definition pivotPrime, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pivotPrime (N L s : ℕ) : ℕ :=
  (pivotArgument N L s).primeFactors.toList.foldl Nat.max 1
/-- Local definition pivotCofactor, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pivotCofactor (N L s : ℕ) : ℕ :=
  pivotArgument N L s / pivotPrime N L s
/-- Local definition pivotGoodCofactor, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pivotGoodCofactor (L s N : ℕ) (η : ℝ) : Prop :=
  η * pivotCofactor N L s ≤ Nat.totient (pivotCofactor N L s)
/-- Local definition pivotSupplier, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pivotSupplier (X L s N : ℕ) : Prop :=
  let p := pivotPrime N L s
  let m := pivotCofactor N L s
  p.Prime ∧ m * p = pivotArgument N L s ∧ 0 < m ∧
    m ≤ Nat.sqrt X / 2 ∧ 2 * Nat.sqrt X < p
/-- Local definition pivotSupplierBases, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pivotSupplierBases (X L s : ℕ) : Finset ℕ :=
  (Finset.Ico X (2 * X)).filter (pivotSupplier X L s)
/-- Local definition pivotGoodBases, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pivotGoodBases (X L s : ℕ) (η : ℝ) : Finset ℕ :=
  (pivotSupplierBases X L s).filter fun N => pivotGoodCofactor L s N η
/-- The residue angle used by the first additive character. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstAngle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))
/-- The complex first additive character of the endpoint discrepancy. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstExp, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)
/-- Local definition AdmissibleDepth, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def AdmissibleDepth (h s X L : ℕ) : Prop :=
  h ≤ L - s ∧ 16 * (2 * X + h + L + 2) ≤ 2 ^ L
/-- Local definition admissibleDepth_witness, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def admissibleDepth_witness (h s X : ℕ) :
    AdmissibleDepth h s X (h + s + Nat.log 2 X + 10) := by
  refine ⟨by omega, ?_⟩
  have hA : h + s + 1 ≤ 2 ^ (h + s) := Nat.lt_two_pow_self
  have hB : X + 1 ≤ 2 * 2 ^ (Nat.log 2 X) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    rw [pow_succ] at this; omega
  have hlog : Nat.log 2 X ≤ X := Nat.log_le_self 2 X
  have hpow : 2 ^ (h + s + Nat.log 2 X + 10) = 2 ^ (h + s) * 2 ^ (Nat.log 2 X) * 1024 := by
    rw [pow_add, pow_add]; norm_num
  rw [hpow]
  have hprod : (h + s + 1) * (X + 1) ≤ 2 ^ (h + s) * (2 * 2 ^ (Nat.log 2 X)) :=
    Nat.mul_le_mul hA hB
  have h1 : 16 * (2 * X + h + (h + s + Nat.log 2 X + 10) + 2)
      ≤ 512 * ((h + s + 1) * (X + 1)) := by
    nlinarith [Nat.zero_le (h * X), Nat.zero_le (s * X)]
  have h2 : 512 * ((h + s + 1) * (X + 1)) ≤ 2 ^ (h + s) * 2 ^ (Nat.log 2 X) * 1024 := by
    calc 512 * ((h + s + 1) * (X + 1))
        ≤ 512 * (2 ^ (h + s) * (2 * 2 ^ (Nat.log 2 X))) := Nat.mul_le_mul_left _ hprod
      _ = 2 ^ (h + s) * 2 ^ (Nat.log 2 X) * 1024 := by ring
  omega
/-- Local definition exists_admissibleDepth, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def exists_admissibleDepth (h s X : ℕ) : ∃ L, AdmissibleDepth h s X L :=
  ⟨_, admissibleDepth_witness h s X⟩
/-- Local definition minimalDepth, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def minimalDepth (h s X : ℕ) : ℕ := Nat.find (exists_admissibleDepth h s X)
/-- States thm:goodbasegap from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_goodBase_gap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totient_series_of_goodBase_gap
    (hgap : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        windowFirstExp h N (minimalDepth h 26 X)).re ≤ (603 / 1000 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
end PalomarCorpus.E249.PaperStructuresT

namespace PalomarCorpus.E249.PaperStructuresU
open Filter
open Finset
export PalomarCorpus.E249_33.Shared (windowDiscrepancy)
/-- Real part of the first additive character of the endpoint discrepancy modulo `2^L`. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstCos, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstCos (h N L : ℕ) : ℝ :=
  Real.cos
    (2 * Real.pi *
      (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
        ((2 ^ L : ℤ) : ℝ)))
/-- States thm:goodbasegap from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_support_gap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_totient_series_of_support_gap
    (hgap : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X L : ℕ, ∃ T : Finset ℕ,
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧ T.Nonempty ∧ (∀ N ∈ T, A ≤ N ∧ N < 2 * X) ∧
      (∑ N ∈ T, windowFirstCos h N L) ≤ (9 / 10 : ℝ) * T.card) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
end PalomarCorpus.E249.PaperStructuresU

namespace PalomarCorpus.E249.PrefixTwoAdicExclusion
/-- The integer prefix `P_n = ∑_{i < n} 2 ^ (n - 1 - i) φ(i + 1)` of `2 ^ n S`, written over the first `n` positive arguments; `P_0 = 0`. -/
noncomputable def totientPrefix (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 2 ^ (n - 1 - i) * Nat.totient (i + 1)
/-- Supporting recurrence: `P_{n + 1} = 2 P_n + φ(n + 1)`. -/
theorem totientPrefix_succ (n : ℕ) :
    totientPrefix (n + 1) = 2 * totientPrefix n + Nat.totient (n + 1) := by
  sorry
/-- Supporting identity: `P_n = ∑_{i ≤ n} φ(i) 2 ^ (n - i)`, the form used elsewhere in this file and in the shared namespace; the two agree because `φ(0) = 0`. -/
theorem totientPrefix_eq_corpusForm (n : ℕ) :
    totientPrefix n = ∑ i ∈ Finset.range (n + 1), Nat.totient i * 2 ^ (n - i) := by
  sorry
/-- The local tail `R_n = 2 ^ n S - P_n` of an arbitrary real number `S` against the totient prefix. It is stated for a general `S` so that the exclusion theorems below can carry a rational form for `S` as an explicit hypothesis. -/
noncomputable def prefixTail (S : ℝ) (n : ℕ) : ℝ :=
  2 ^ n * S - (totientPrefix n : ℝ)
/-- Supporting integrality: if `S = a / (2 ^ c v)` with `v > 0` and `c ≤ n`, then `v · prefixTail S n` is the integer `2 ^ (n - c) a - v P_n`. -/
theorem oddPart_mul_prefixTail_eq_intCast
    {S : ℝ} {a : ℤ} {c v n : ℕ} (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ))) (hcn : c ≤ n) :
    (v : ℝ) * prefixTail S n
      = (((2 : ℤ) ^ (n - c) * a - (v : ℤ) * (totientPrefix n : ℤ) : ℤ) : ℝ) := by
  sorry
/-- Finite exclusion step: if `S = a / (2 ^ c v)` with `v` odd and positive, the local tail `R_n` is positive, `c + t ≤ n`, and `2 ^ t` divides `P_n`, then `2 ^ t ≤ v R_n`. One exact power of two dividing the prefix therefore constrains the admissible denominators. -/
theorem prefix_twoAdic_denominator_exclusion
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t ≤ (v : ℝ) * prefixTail S n := by
  sorry
/-- The same finite exclusion with the tail bound inserted as a hypothesis: if `S = a / (2 ^ c v)` with `v` odd and positive, the local tail satisfies `0 < R_n ≤ n + 2`, `c + t ≤ n`, and `2 ^ t` divides `P_n`, then `2 ^ t ≤ v (n + 2)`. -/
theorem prefix_twoAdic_denominator_lower_bound
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (htail : prefixTail S n ≤ (n : ℝ) + 2)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t ≤ (v : ℝ) * ((n : ℝ) + 2) := by
  sorry
/-- The same finite exclusion read as a floor on the odd part of the denominator: if `S = a / (2 ^ c v)` with `v` odd and positive, `0 < R_n ≤ n + 2`, `c + t ≤ n`, and `2 ^ t` divides `P_n`, then `2 ^ t / (n + 2) ≤ v`. This excludes a finite rectangle of candidate denominators `2 ^ c v` and is not a proof of irrationality. -/
theorem prefix_twoAdic_odd_denominator_floor
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (htail : prefixTail S n ≤ (n : ℝ) + 2)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t / ((n : ℝ) + 2) ≤ (v : ℝ) := by
  sorry
end PalomarCorpus.E249.PrefixTwoAdicExclusion

namespace PalomarCorpus.E249.RankOneSharpFloor
open scoped BigOperators
open ArithmeticFunction
/-- The atom of index `n` at rung `r` of the Möbius-Mersenne ladder, namely `μ(n + 1) / (2 ^ (n + 1) - 1) ^ r` with `μ` the Möbius function; the index is shifted so that `n = 0` carries the divisor `d = 1`. -/
noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) / (((2 : ℝ) ^ (n + 1) - 1) ^ r)
/-- The rung `Θ_r = ∑_{d ≥ 1} μ(d) / (2 ^ d - 1) ^ r` of the Möbius-Mersenne ladder, defined as the real sum of the atoms above. The divisor convolution `φ = μ * id` gives `Θ_2 = S - 1/2` for the binary totient series `S = ∑_{n ≥ 1} φ(n) / 2 ^ n`. At `r = 0` the family is not summable and the Lean sum takes its default value `0`; every compared theorem uses the ladder only at `r ≥ 1`. -/
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n
/-- The truncation `t_Y(r) = ∑_{d = 1}^{Y} μ(d) / (2 ^ d - 1) ^ r` of the Möbius-Mersenne rung `r` to its first `Y` atoms. -/
noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n
/-- The quotient `Q(e, Y) = t_Y(e + 2) ^ 2 / t_Y(2 e + 2)` of Möbius-Mersenne prefixes, called the positive rank-one strict-subrank quotient in the surrounding development. The definition imposes neither positivity nor any admissibility condition: at `Y = 0` both prefixes are empty sums and the Lean division returns `0`. The theorems below restrict to `e ≥ 1` and `Y ≥ 4`. -/
noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ :=
  mobiusMersennePrefix Y (e + 2) ^ 2 /
    mobiusMersennePrefix Y (2 * e + 2)
/-- Sharp minimum: on the admissible range `e ≥ 1` and `Y ≥ 4`, `Q(1, 5) ≤ Q(e, Y)`, so the five-atom first-depth kernel minimises the quotient. -/
theorem rankOneSubrankQuotient_ge_one_five
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    rankOneSubrankQuotient 1 5 ≤ rankOneSubrankQuotient e Y := by
  sorry
/-- The same separation stated with the unit-fraction floor `1 / 16`, valid on the whole admissible range `e ≥ 1`, `Y ≥ 4`. -/
theorem rankOneSubrankQuotient_sub_theta_two_gt_one_div_sixteen
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 16 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  sorry
/-- Sharpness of the unit-fraction floor: the universally quantified bound `Q(e, Y) - Θ_2 > 1 / 15` over the admissible range is false, so `1 / 16` is the largest unit fraction that works. The statement is the negation of that quantified inequality. -/
theorem not_forall_rankOneSubrankQuotient_sub_theta_two_gt_one_div_fifteen :
    ¬ ∀ {e Y : ℕ}, 1 ≤ e → 4 ≤ Y →
      (1 : ℝ) / 15 <
        rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  sorry
/-- Rational linear-form obstruction: if an admissible quotient satisfies `Q(e, Y) = p / q` with `q ≥ 1`, then `|q Θ_2 - p| > 21 q / 320`. Such an approximant stays far from `Θ_2` in the linear-form scale, so it cannot belong to a sequence witnessing irrationality. -/
theorem primitive_form_abs_gt_twentyOne_div_threeTwenty
    {e Y q : ℕ} {p : ℤ}
    (he : 1 ≤ e) (hY : 4 ≤ Y) (hq : 1 ≤ q)
    (hquot : rankOneSubrankQuotient e Y = (p : ℝ) / q) :
    (q : ℝ) * (21 : ℝ) / 320 <
      |(q : ℝ) * mobiusMersenneTheta 2 - p| := by
  sorry
end PalomarCorpus.E249.RankOneSharpFloor
