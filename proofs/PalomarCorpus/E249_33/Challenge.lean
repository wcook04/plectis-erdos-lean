/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, the prefix two adic exclusion, rank one sharp floor and rational observable classification families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open ArithmeticFunction
open Filter Topology

namespace PalomarCorpus.E249_33.Shared
/-- The binary-weighted sum of the least nonnegative residues φ(n) modulo m. -/
noncomputable def totientResidueValue (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((Nat.totient n % m : ℕ) : ℝ) / 2 ^ n
end PalomarCorpus.E249_33.Shared

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

namespace PalomarCorpus.E249.RationalObservableClassification
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E249_33.Shared (totientResidueValue)
/-- For k ≥ 1, a rational-valued observable on residues modulo 2^k has a rational binary-weighted totient sum exactly when it is constant on the even residues. -/
theorem rational_zmod_observable_iff
    {k : ℕ} (hk : 1 ≤ k) (f : ZMod (2 ^ k) → ℚ) :
    (∃ q : ℚ,
      (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
        2 ^ (n + 1)) = (q : ℝ)) ↔
      ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = f 0 := by
  sorry
/-- If the observable equals c on the even residues modulo 2^k, its binary-weighted totient sum is 3f(1)/4 + c/4. -/
theorem zmod_observable_value
    {k : ℕ} (hk : 1 ≤ k) (f : ZMod (2 ^ k) → ℚ) (c : ℚ)
    (hc : ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = c) :
    (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
      2 ^ (n + 1)) = ((3 * f 1 / 4 + c / 4 : ℚ) : ℝ) := by
  sorry
/-- The totient residue series is irrational for every modulus at least three; its values at moduli one and two are respectively zero and three quarters. -/
theorem residue_series_sharp_range :
    (∀ m : ℕ, 3 ≤ m → Irrational (totientResidueValue m)) ∧
    totientResidueValue 1 = 0 ∧ totientResidueValue 2 = 3 / 4 := by
  sorry
end PalomarCorpus.E249.RationalObservableClassification

namespace PalomarCorpus.E249.ResidueClassTotientSeries
export PalomarCorpus.E249_33.Shared (totientResidueValue)
/-- The binary value `∑_{n ≥ 0} a(n) / 2 ^ n` of an integer coefficient sequence `a`, with the terms cast from `ℤ` to `ℝ`. -/
noncomputable def dyadicValue (a : ℕ → ℤ) : ℝ := ∑' n : ℕ, (a n : ℝ) / 2 ^ n
/-- The binary value `∑_{n ≥ 0} f(φ(n) mod m) / 2 ^ n` of a fixed-resolution observable of the totient word, where `f` is an integer-valued letter map on residues and `m` is the fixed resolution. -/
noncomputable def totientObservableValue (f : ℕ → ℤ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((f (Nat.totient n % m) : ℤ) : ℝ) / 2 ^ n
/-- Quantitative Diophantine core: let `a` be an integer sequence with `|a n| ≤ C`, let `q ≥ 1` satisfy `2 q C < 2 ^ L`, and suppose `a (N + 1 + L) = t` with `t ≠ 0` while `a (N + 1 + i) = 0` for every `i ≤ 2 L` with `i ≠ L`. Then every integer `k` satisfies `q (|t| - C / 2 ^ L) / 2 ^ (N + 1 + L) ≤ |q · dyadicValue a - k|`. One isolated nonzero letter inside a two-sided block of zeros keeps `q` times the value away from every integer. -/
theorem isolated_pulse_separation {a : ℕ → ℤ} {C : ℝ} (hC : ∀ n, |(a n : ℝ)| ≤ C)
    {N L q : ℕ} {t : ℤ} (hq : 1 ≤ q) (hL : 2 * (q : ℝ) * C < 2 ^ L)
    (hcentre : a (N + 1 + L) = t) (ht : t ≠ 0)
    (hzero : ∀ i, i ≤ 2 * L → i ≠ L → a (N + 1 + i) = 0) (k : ℤ) :
    (q : ℝ) * (|(t : ℝ)| - C / 2 ^ L) / 2 ^ (N + 1 + L)
      ≤ |(q : ℝ) * dyadicValue a - (k : ℝ)| := by
  sorry
/-- Number-theory-free irrationality criterion: a bounded integer coefficient sequence whose support carries arbitrarily long two-sided isolated pulses has irrational binary value. The pulse hypothesis asks that for every `L` there be `p > L + 1` with `a p ≠ 0` and `a (p - j) = a (p + j) = 0` for every `0 < j ≤ L`. -/
theorem irrational_dyadicValue_of_pulses {a : ℕ → ℤ} {C : ℝ} (hC : ∀ n, |(a n : ℝ)| ≤ C)
    (hpulse : ∀ L : ℕ, ∃ p : ℕ, L + 1 < p ∧ a p ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (p - j) = 0 ∧ a (p + j) = 0) :
    Irrational (dyadicValue a) := by
  sorry
/-- Arithmetic supply: for `m ≥ 2` and any residue `r` with `r + 1` coprime to `m`, and for any `L` and `N`, there is a prime `p` with `p > N`, `p > L + 1`, `φ(p) ≡ r` modulo `m`, and `m` dividing both `φ(p - j)` and `φ(p + j)` for every `0 < j ≤ L`. The proof combines the Chinese remainder theorem with Dirichlet's theorem on primes in arithmetic progressions. -/
theorem two_sided_prime_isolation {m : ℕ} (hm : 2 ≤ m) (L N r : ℕ)
    (hr : Nat.Coprime (r + 1) m) :
    ∃ p : ℕ, N < p ∧ L + 1 < p ∧ p.Prime ∧ Nat.totient p ≡ r [MOD m] ∧
      ∀ j, 0 < j → j ≤ L → m ∣ Nat.totient (p - j) ∧ m ∣ Nat.totient (p + j) := by
  sorry
/-- Unconditional irrationality for fixed-resolution observables: if `m ≥ 2`, the letter map `f` vanishes at residue `0`, and some residue `r < m` with `r + 1` coprime to `m` has `f r ≠ 0`, then `∑_n f(φ(n) mod m) / 2 ^ n` is irrational. The object is the reduced word `φ(n) mod m` rather than `φ(n)` itself. -/
theorem irrational_totientObservable {m : ℕ} (hm : 2 ≤ m) (f : ℕ → ℤ) (hf0 : f 0 = 0)
    {r : ℕ} (hr : r < m) (hcop : Nat.Coprime (r + 1) m) (hfr : f r ≠ 0) :
    Irrational (totientObservableValue f m) := by
  sorry
/-- Dyadic resolution case: at resolution `m = 2 ^ k` with `k ≥ 1`, every integer-valued letter map that vanishes at residue `0` and is nonzero at some even residue `r < 2 ^ k` has irrational binary value. Every even residue qualifies because `r + 1` is then odd and hence coprime to `2 ^ k`. -/
theorem fixed_resolution_observable_irrational {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℤ)
    (hf0 : f 0 = 0) {r : ℕ} (hr : r < 2 ^ k) (hreven : r % 2 = 0) (hfr : f r ≠ 0) :
    Irrational (totientObservableValue f (2 ^ k)) := by
  sorry
/-- Headline unconditional consequence: for every `m ≥ 3` the least-residue totient series `A_m = ∑_n (φ(n) mod m) / 2 ^ n` is irrational. The excluded small cases are rational, `A_1 = 0` and `A_2 = 3 / 4`, a fact not formalised here. -/
theorem residue_series_irrational {m : ℕ} (hm : 3 ≤ m) :
    Irrational (totientResidueValue m) := by
  sorry
end PalomarCorpus.E249.ResidueClassTotientSeries

namespace PalomarCorpus.E249.TermwiseDyadicVacuous
/-- Route closure: whenever `t ≥ 1`, `N + t ≥ 2`, `v ≥ 1` and `2 ^ t` divides `φ(N + t)`, one has `2 ^ t ≤ v (N + t + 2)`. The termwise dyadic window therefore never beats the size budget and excludes no denominator, because `2 ^ t ∣ φ(N + t)` already forces `2 ^ t ≤ φ(N + t) < N + t`. -/
theorem termwise_dyadic_window_vacuous
    {N t v : ℕ} (ht : 1 ≤ t) (hNt : 2 ≤ N + t) (hv : 1 ≤ v)
    (hdvd : 2 ^ t ∣ Nat.totient (N + t)) :
    2 ^ t ≤ v * (N + t + 2) := by
  sorry
end PalomarCorpus.E249.TermwiseDyadicVacuous

namespace PalomarCorpus.E249.TotientAffineModeEscape
open scoped BigOperators
/-- The binary block of `H` consecutive totient values starting at `N + 1`, most significant weight first: `∑_{j < H} φ(N + 1 + j) 2 ^ (H - 1 - j)`, an integer. It equals `2 ^ H R_N - R_{N + H}` for the binary totient tail `R_N`, and is `0` when `H = 0`. -/
noncomputable def totientBlock (H N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range H,
    (Nat.totient (N + 1 + j) : ℤ) * 2 ^ (H - 1 - j)
/-- The signed endpoint error `E_H = totientBlock H c - k (2 ^ H - 1)` of the totient block at basepoint `c` against a fixed quotient `k`, on the pure dyadic axis where the odd part of the candidate denominator is `1`. -/
noncomputable def pureDyadicEndpointError (H c : ℕ) (k : ℤ) : ℤ :=
  totientBlock H c - k * ((2 : ℤ) ^ H - 1)
/-- The property that the endpoint error is eventually an affine function of the height: there are integers `A` and `B` and a threshold `H0` with `E_H = A H + B` for every `H ≥ H0`. -/
noncomputable def EventuallyAffinePureDyadicEndpointError (c : ℕ) (k : ℤ) : Prop :=
  ∃ A B : ℤ, ∃ H0 : ℕ, ∀ H, H0 ≤ H →
    pureDyadicEndpointError H c k = A * H + B
/-- Unconditional route closure: for every basepoint `c` and every fixed quotient `k`, the endpoint error is not eventually affine in the height. An affine tail would force the shifted totient letters onto one affine line, which fails at the exact points `(p, p - 1)`, `(q, q - 1)` and `(2 p, p - 1)` for arbitrarily late primes `2 < p < q`. This excludes one fixed endpoint-error mode; it does not exclude every mechanism by which the binary totient series could be rational. -/
theorem not_eventuallyAffine_pureDyadicEndpointError (c : ℕ) (k : ℤ) :
    ¬ EventuallyAffinePureDyadicEndpointError c k := by
  sorry
end PalomarCorpus.E249.TotientAffineModeEscape

namespace PalomarCorpus.E249.TotientRigidity
/-- The defect `g(n) - φ(n)` of a candidate integer coefficient sequence `g` against Euler's totient, taken in `ℤ`. -/
noncomputable def totientDefect (g : ℕ → ℤ) (n : ℕ) : ℤ := g n - (Nat.totient n : ℤ)
/-- Supporting identity: `φ(p n) = p φ(n)` for a prime `p` dividing `n`, stated over `ℤ`. -/
theorem totient_prime_mul_of_dvd {p n : ℕ} (hp : p.Prime) (h : p ∣ n) :
    (Nat.totient (p * n) : ℤ) = (p : ℤ) * (Nat.totient n : ℤ) := by
  sorry
/-- Supporting identity: `φ(p n) = (p - 1) φ(n)` for a prime `p` not dividing `n`, stated over `ℤ`. -/
theorem totient_prime_mul_of_not_dvd {p n : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) :
    (Nat.totient (p * n) : ℤ) = ((p : ℤ) - 1) * (Nat.totient n : ℤ) := by
  sorry
/-- Supporting identity: `φ(2 m) = φ(m)` for odd `m`, stated over `ℕ`. -/
theorem totient_two_mul_of_odd {m : ℕ} (hm : Odd m) :
    Nat.totient (2 * m) = Nat.totient m := by
  sorry
/-- Supporting identity: `φ(2 m) = 2 φ(m)` for even `m`, stated over `ℕ`; the degenerate case `m = 0` is included and both sides are `0`. -/
theorem totient_two_mul_of_even {m : ℕ} (hm : Even m) :
    Nat.totient (2 * m) = 2 * Nat.totient m := by
  sorry
/-- Rigidity route closure: let `p` be prime and let `g : ℕ → ℤ` obey the exact `p` laws `g(p n) = (p - 1) g(n)` when `p` does not divide `n` and `g(p n) = p g(n)` when `p` divides `n`, for every `n ≥ 1`, and suppose that for every `ε > 0` the bound `|g(n) - φ(n)| ≤ ε n` holds for all large `n`. Then `g(n) = φ(n)` for every `n ≥ 1`. One exact prime law with an `o(n)` error therefore leaves no rational control other than `φ` itself. -/
theorem one_prime_law_and_little_o_forces_totient
    {p : ℕ} (hp : p.Prime) {g : ℕ → ℤ}
    (hlaw_not_dvd : ∀ n : ℕ, 1 ≤ n → ¬ p ∣ n → g (p * n) = ((p : ℤ) - 1) * g n)
    (hlaw_dvd : ∀ n : ℕ, 1 ≤ n → p ∣ n → g (p * n) = (p : ℤ) * g n)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |(g n : ℝ) - (Nat.totient n : ℝ)| ≤ ε * (n : ℝ))
    {n : ℕ} (hn : 1 ≤ n) :
    g n = (Nat.totient n : ℤ) := by
  sorry
/-- Rigidity route closure: let `g : ℕ → ℤ` satisfy `g(2 m) = g(m)` for odd `m ≥ 1` and `g(2 m) = 2 g(m)` for even `m ≥ 2`, and suppose that for every `q ≥ 1` the congruence `q ∣ g(n) - φ(n)` holds for all sufficiently large `n`. Then `g(n) = φ(n)` for every `n ≥ 1`. No odd-prime law and no size bound are needed. -/
theorem even_law_and_eventual_congruence_forces_totient
    {g : ℕ → ℤ}
    (hodd : ∀ m : ℕ, Odd m → 1 ≤ m → g (2 * m) = g m)
    (heven : ∀ m : ℕ, Even m → 2 ≤ m → g (2 * m) = 2 * g m)
    (hcong : ∀ q : ℕ, 1 ≤ q → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (q : ℤ) ∣ totientDefect g n)
    {n : ℕ} (hn : 1 ≤ n) :
    g n = (Nat.totient n : ℤ) := by
  sorry
end PalomarCorpus.E249.TotientRigidity
