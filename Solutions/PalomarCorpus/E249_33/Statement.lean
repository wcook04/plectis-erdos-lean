/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_33

Every non-theorem declaration of `PalomarCorpus/E249_33/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E249.PaperStructuresU

namespace PalomarCorpus.E249.PrefixTwoAdicExclusion
/-- The integer prefix `P_n = ∑_{i < n} 2 ^ (n - 1 - i) φ(i + 1)` of `2 ^ n S`, written over the first `n` positive arguments; `P_0 = 0`. -/
noncomputable def totientPrefix (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 2 ^ (n - 1 - i) * Nat.totient (i + 1)
/-- The local tail `R_n = 2 ^ n S - P_n` of an arbitrary real number `S` against the totient prefix. It is stated for a general `S` so that the exclusion theorems below can carry a rational form for `S` as an explicit hypothesis. -/
noncomputable def prefixTail (S : ℝ) (n : ℕ) : ℝ :=
  2 ^ n * S - (totientPrefix n : ℝ)
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
end PalomarCorpus.E249.RankOneSharpFloor
