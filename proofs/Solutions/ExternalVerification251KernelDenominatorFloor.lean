/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos251.KernelDenominatorFloor

open scoped BigOperators

namespace Erdos249257.ExternalVerification251KernelDenominatorFloor

noncomputable def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n

noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)

noncomputable def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

noncomputable def noSmallDivisor (m : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, k =>
      if m < k * k then true
      else if m % k == 0 then false
      else noSmallDivisor m fuel (k + 1)

noncomputable def isPrimeTD (m : ℕ) : Bool := decide (2 ≤ m) && noSmallDivisor m m 2

noncomputable def primeSumLoop (B : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | m + 1 =>
      let s := primeSumLoop B m
      if isPrimeTD m then (s.1 + 1, s.2 + m * 2 ^ (B - s.1 - 1)) else s

noncomputable def certCheck (c u v u' v' X : ℕ) : Bool :=
  let s := primeSumLoop c X
  (s.1 == c) && decide (0 < v) && decide (0 < v') && (u' * v == u * v' + 1) &&
    decide (u * 2 ^ c < s.2 * v) &&
    decide ((2 * s.2 + 5000 * (c + 1) ^ 4) * v' < u' * 2 ^ (c + 1))

noncomputable def certX : ℕ := 10000

noncomputable def certC : ℕ := 1229

noncomputable def certU : ℕ :=
  8065641857152652932176019632186898003271162829171466334827308360779441527871744503350940785598890336998852555074615973558897922500842023448210201391609566636587897181681526620217

noncomputable def certV : ℕ :=
  2194945124413663232143970924541263312422069524635615360518424707735195822181683072018928990483166295508439269024868312162917239885377332351730406072544968385302138677814423351745

noncomputable def certU' : ℕ :=
  653943710149816262688241189247090522210826000856855544597530261633155217846686899097127598765624846200590981384174695232839888185316374272333277389611483117334000493867584923912

noncomputable def certV' : ℕ :=
  177961107578986655119842724162170963012013632328159817663784906052492297355019687649040361529707294916566508739385806203025466313389810291243786005499164537499383612081805160767

private theorem noSmallDivisor_eq_source (m : ℕ) :
    ∀ fuel k : ℕ,
      noSmallDivisor m fuel k = ErdosProblems.Erdos251.noSmallDivisor m fuel k := by
  intro fuel
  induction fuel with
  | zero => intro k; rfl
  | succ fuel ih =>
      intro k
      simp only [noSmallDivisor, ErdosProblems.Erdos251.noSmallDivisor, ih]

private theorem isPrimeTD_eq_source (m : ℕ) :
    isPrimeTD m = ErdosProblems.Erdos251.isPrimeTD m := by
  simp only [isPrimeTD, ErdosProblems.Erdos251.isPrimeTD, noSmallDivisor_eq_source]

private theorem primeSumLoop_eq_source (B : ℕ) :
    ∀ X : ℕ, primeSumLoop B X = ErdosProblems.Erdos251.primeSumLoop B X := by
  intro X
  induction X with
  | zero => rfl
  | succ X ih =>
      simp only [primeSumLoop, ErdosProblems.Erdos251.primeSumLoop, ih,
        isPrimeTD_eq_source]

private theorem certCheck_eq_source (c u v u' v' X : ℕ) :
    certCheck c u v u' v' X = ErdosProblems.Erdos251.certCheck c u v u' v' X := by
  simp only [certCheck, ErdosProblems.Erdos251.certCheck, primeSumLoop_eq_source]

private theorem certX_eq_source : certX = ErdosProblems.Erdos251.certX := rfl

private theorem certC_eq_source : certC = ErdosProblems.Erdos251.certC := rfl

private theorem certU_eq_source : certU = ErdosProblems.Erdos251.certU := rfl

private theorem certV_eq_source : certV = ErdosProblems.Erdos251.certV := rfl

private theorem certU'_eq_source : certU' = ErdosProblems.Erdos251.certU' := rfl

private theorem certV'_eq_source : certV' = ErdosProblems.Erdos251.certV' := rfl

/-- The kernel re-runs the `10^4` trial-division sieve and decides the six
conditions on the certificate literals. -/
theorem cert_10000 : certCheck certC certU certV certU' certV' certX = true := by
  rw [certCheck_eq_source, certC_eq_source, certU_eq_source, certV_eq_source,
    certU'_eq_source, certV'_eq_source, certX_eq_source]
  exact ErdosProblems.Erdos251.cert_10000

/-- A passing certificate at any truncation index `c ≥ 9` forces every rational
`a / b` equal to the prime series to satisfy `v + v' ≤ b`. -/
theorem den_bound_of_certCheck (c u v u' v' X : ℕ) (hc : 9 ≤ c)
    (h : certCheck c u v u' v' X = true) :
    ∀ (a : ℤ) (b : ℕ), 0 < b → (∑' n, primeDyadicTerm n) = a / b → v + v' ≤ b := by
  rw [certCheck_eq_source] at h
  exact ErdosProblems.Erdos251.den_bound_of_certCheck c u v u' v' X hc h

/-- Every rational `a / b` equal to `S` has `b ≥ 2^589 > 10^177`. -/
theorem kernel_denominator_floor (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b :=
  ErdosProblems.Erdos251.kernel_denominator_floor a b hb hS

/-- The same floor for the prime-gap series `S - 2` of Erdős #251. -/
theorem kernel_denominator_floor_primeGap (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeGapDyadicTerm n) = a / b) : (2 ^ 589 : ℕ) ≤ b :=
  ErdosProblems.Erdos251.kernel_denominator_floor_primeGap a b hb hS

end Erdos249257.ExternalVerification251KernelDenominatorFloor
