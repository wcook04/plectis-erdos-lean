/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, note sections 1 to 4: a basis and all its relations; bounded residues and rationality; tail differences and finite residue tests

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Filter Topology
open Finset
open Matrix
open ArithmeticFunction

namespace PalomarCorpus.E249_30.Shared
/-- The atom of index `n` at rung `r` of the Möbius-Mersenne ladder, namely `μ(n + 1) / (2 ^ (n + 1) - 1) ^ r` with `μ` the Möbius function; the index is shifted so that `n = 0` carries the divisor `d = 1`. -/
noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)
/-- The finite sum of the Möbius-Mersenne terms at indices strictly below Y. -/
noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n
/-- The rung `Θ_r = ∑_{d ≥ 1} μ(d) / (2 ^ d - 1) ^ r` of the Möbius-Mersenne ladder, defined as the real sum of the atoms above. The divisor convolution `φ = μ * id` gives `Θ_2 = S - 1/2` for the binary totient series `S = ∑_{n ≥ 1} φ(n) / 2 ^ n`. At `r = 0` the family is not summable and the Lean sum takes its default value `0`; every compared theorem uses the ladder only at `r ≥ 1`. -/
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n
/-- The quotient `Q(e, Y) = t_Y(e + 2) ^ 2 / t_Y(2 e + 2)` of Möbius-Mersenne prefixes, called the positive rank-one strict-subrank quotient in the surrounding development. The definition imposes neither positivity nor any admissibility condition: at `Y = 0` both prefixes are empty sums and the Lean division returns `0`. The theorems below restrict to `e ≥ 1` and `Y ≥ 4`. -/
noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ :=
  mobiusMersennePrefix Y (e + 2) ^ 2 /
    mobiusMersennePrefix Y (2 * e + 2)
end PalomarCorpus.E249_30.Shared

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
/-- The natural argument of an integer-intercept affine form. Its values before the form becomes nonnegative are irrelevant to an eventual relation. Local copy of ErdosProblems.Erdos249.PaperCompleteR20.integerAffineValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerAffineValue {ι : Type*} (a : ι → ℕ) (b : ι → ℤ)
    (i : ι) (n : ℕ) : ℕ :=
  Int.toNat ((a i : ℤ) * (n : ℤ) + b i)
/-- States cor:periodic-freezing from the short record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.periodic_freezing_integer_affine in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem periodic_freezing_integer_affine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (b : ι → ℤ) (ha : ∀ i, 0 < a i)
    (hcross : ∀ i j, i ≠ j → (a i : ℤ) * b j ≠ (a j : ℤ) * b i)
    (w : ι → ℕ → ℚ)
    (hperiodic : ∀ i, ∃ q : ℕ, 0 < q ∧ ∀ n, w i (n + q) = w i n)
    (hrel : ∃ N₀, ∀ n, N₀ ≤ n →
      ∑ i, w i n * (Nat.totient (integerAffineValue a b i n) : ℚ) = 0) :
    ∀ i n, w i n = 0 := by
  sorry
/-- States lem:bounded-pulse from the short record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR7.bounded_isolated_pulse in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem bounded_isolated_pulse
    (a : ℕ → ℤ) (C : ℝ) (hC : ∀ n, |(a n : ℝ)| ≤ C)
    (hpulse : ∀ L₀ : ℕ, ∃ L N : ℕ, L₀ ≤ L ∧ L < N ∧ a N ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (N - j) = 0 ∧ a (N + j) = 0) :
    Irrational (∑' n : ℕ, (a (n + 1) : ℝ) / 2 ^ (n + 1)) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAE

namespace PalomarCorpus.E249.RationalObservableClassification
open Filter Topology
open scoped BigOperators
/-- The binary-weighted sum of the least nonnegative residues φ(n) modulo m. -/
noncomputable def totientResidueValue (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((Nat.totient n % m : ℕ) : ℝ) / 2 ^ n
/-- The short-note bundle: irrationality of residue series for moduli at least three, the exact rational-observable classification for dyadic moduli, and the explicit value in the rational case. -/
theorem short_note_residue_theorem :
    (∀ m : ℕ, 3 ≤ m → Irrational (totientResidueValue m)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ f : ZMod (2 ^ k) → ℚ,
      ((∃ q : ℚ,
        (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
          2 ^ (n + 1)) = (q : ℝ)) ↔
        ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = f 0)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ f : ZMod (2 ^ k) → ℚ, ∀ c : ℚ,
      (∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = c) →
      (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
        2 ^ (n + 1)) = ((3 * f 1 / 4 + c / 4 : ℚ) : ℝ)) := by
  sorry
end PalomarCorpus.E249.RationalObservableClassification

namespace PalomarCorpus.E249.PaperStatementsM
open scoped BigOperators
open Finset
/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`: the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- States res:fulldepth from the short record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR7.fullDepth_amplification in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fullDepth_amplification :
    (∀ d N : ℕ, 0 < d →
      (totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) →
      ∃ T : ℕ, 0 < T ∧ ∀ t : ℕ, T ≤ t →
        certifiedKill (t * d) N (t * d) ∨
          certifiedKill ((t + 1) * d) N ((t + 1) * d)) ∧
    (∀ d N : ℕ, 0 < d →
      ((∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔
        totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ))) ∧
    ((∀ d : ℕ, 0 < d → ∀ N : ℕ,
        ∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) := by
  sorry
end PalomarCorpus.E249.PaperStatementsM

namespace PalomarCorpus.E249.PaperStatementsBG
open scoped BigOperators
open Matrix
open ArithmeticFunction
export PalomarCorpus.E249_30.Shared (mobiusMersennePrefix mobiusMersenneTerm mobiusMersenneTheta rankOneSubrankQuotient)
/-- States res:rankonefloor from the short record for Erdős problem #249. Transported from ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_one_five_sub_theta_two_lt_one_div_fifteen in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rankOneSubrankQuotient_one_five_sub_theta_two_lt_one_div_fifteen :
    rankOneSubrankQuotient 1 5 - mobiusMersenneTheta 2 <
      (1 : ℝ) / 15 := by
  sorry
end PalomarCorpus.E249.PaperStatementsBG

namespace PalomarCorpus.E249.RankOneDenominator
open Filter Topology
open scoped BigOperators
open ArithmeticFunction
export PalomarCorpus.E249_30.Shared (mobiusMersennePrefix mobiusMersenneTerm)
/-- For e ≥ 1 and Y ≥ 4, the finite Möbius-Mersenne prefix at exponent 2e + 2 is strictly positive. -/
theorem rankOne_denominator_pos {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    0 < mobiusMersennePrefix Y (2 * e + 2) := by
  sorry
end PalomarCorpus.E249.RankOneDenominator

namespace PalomarCorpus.E249.RankOneSharpFloor
open scoped BigOperators
open ArithmeticFunction
export PalomarCorpus.E249_30.Shared (mobiusMersennePrefix mobiusMersenneTerm mobiusMersenneTheta rankOneSubrankQuotient)
/-- Uniqueness of the minimiser: on the admissible range `e ≥ 1` and `Y ≥ 4`, `Q(e, Y) = Q(1, 5)` holds exactly when `e = 1` and `Y = 5`. -/
theorem rankOneSubrankQuotient_eq_one_five_iff
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    rankOneSubrankQuotient e Y = rankOneSubrankQuotient 1 5 ↔
      e = 1 ∧ Y = 5 := by
  sorry
/-- Sharp separation: on the admissible range `e ≥ 1` and `Y ≥ 4`, `Q(e, Y)` exceeds the rung `Θ_2 = ∑_{d ≥ 1} μ(d) / (2 ^ d - 1) ^ 2` by more than `21 / 320`. -/
theorem rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (21 : ℝ) / 320 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  sorry
/-- Closure under positive mixing: for a nonempty finite index set `s`, strictly positive weights `w i` and admissible pairs `(e i, Y i)` for `i ∈ s`, the weighted mean of the quotients still exceeds `Θ_2` by more than `21 / 320`, so no positive combination of rank-one blocks approaches `Θ_2`. -/
theorem positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (e Y : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < w i)
    (he : ∀ i ∈ s, 1 ≤ e i)
    (hY : ∀ i ∈ s, 4 ≤ Y i) :
    (21 : ℝ) / 320 <
      (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) /
          (∑ i ∈ s, w i) -
        mobiusMersenneTheta 2 := by
  sorry
end PalomarCorpus.E249.RankOneSharpFloor
