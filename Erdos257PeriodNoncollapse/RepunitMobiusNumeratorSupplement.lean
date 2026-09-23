import Erdos257PeriodNoncollapse.RadicalMobiusShadow
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Tactic
import Erdos257PeriodNoncollapse.RepunitMobiusNumerator

/-
The paper repository's copy of this module does not declare the results below; they were proved in
this corpus. A shim can only publish a name the library has, so this module keeps them, and keeps them
exactly as they were written: it is the corpus module with every declaration the library already carries
removed, and the shim imported in their place. No statement, hypothesis, proof or name is changed here.
-/

/-!
# The repunit Möbius numerator is a positive gcd word

This file proves the finite polynomial identity recorded as T1 in the private
Erdős #249 development.  On the intended boundary `Squarefree r`, the signed
repunit numerator

`∑ d ∣ r, μ(d) (r / d) (1 + X^d + ... + X^(r-d))`

is the gcd word whose coefficient at `X^k`, for `k < r`, is

`(r / gcd r k) * φ (gcd r k)`.

Thus every coefficient in the stated range is strictly positive and every
coefficient outside it is zero.  The squarefree hypothesis is kept explicit:
this module does not promote the formal development.s radical claim to a statement about
arbitrary nonsquarefree exponents.
-/

open scoped BigOperators ArithmeticFunction.Moebius Polynomial

namespace Erdos257PeriodNoncollapse.RepunitMobiusNumerator

private theorem moebius_prod_subset_primeFactors {r : ℕ}
    (hr : Squarefree r) {s : Finset ℕ} (hs : s ⊆ r.primeFactors) :
    ArithmeticFunction.moebius (s.prod id) = (-1 : ℤ) ^ s.card := by
  have hsprime : ∀ p ∈ s, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (hs hp)
  have hproddiv : s.prod id ∣ r := by
    calc
      s.prod id ∣ r.primeFactors.prod id :=
        Finset.prod_dvd_prod_of_subset s r.primeFactors id hs
      _ = r := Nat.prod_primeFactors_of_squarefree hr
  have hsq : Squarefree (s.prod id) := hr.squarefree_of_dvd hproddiv
  rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
  congr 1
  rw [ArithmeticFunction.cardFactors_apply]
  calc
    (s.prod id).primeFactorsList.length =
        (s.prod id).primeFactors.card := by
          exact (List.toFinset_card_of_nodup hsq.nodup_primeFactorsList).symm
    _ = s.card := by
      simpa [Function.id_def] using
        congrArg Finset.card (Nat.primeFactors_prod hsprime)

theorem divisor_mobiusNumerator_eq_subset {r : ℕ}
    (hr : Squarefree r) :
    (∑ d ∈ r.divisors,
        ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ)) *
          (((RadicalMobiusShadow.mersenne r /
            RadicalMobiusShadow.mersenne d : ℕ) : ℤ))) =
      RadicalMobiusShadow.mobiusNumerator r := by
  rw [← Nat.divisors_filter_squarefree_of_squarefree hr,
    Nat.sum_divisors_filter_squarefree hr.ne_zero, Nat.factors_eq]
  unfold RadicalMobiusShadow.mobiusNumerator
  apply Finset.sum_congr rfl
  intro s hs
  have hmobius :=
    moebius_prod_subset_primeFactors hr (Finset.mem_powerset.mp hs)
  rw [s.prod_val, Function.id_def]
  have hmobius' :
      ArithmeticFunction.moebius (∏ x ∈ s, x) = (-1 : ℤ) ^ s.card := by
    simpa [Function.id_def] using hmobius
  rw [hmobius']

end Erdos257PeriodNoncollapse.RepunitMobiusNumerator
