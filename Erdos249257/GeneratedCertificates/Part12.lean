-- Generated direct-prime emitted certificates, part 12 of 16 (12 certificates).
import Erdos249257.CertificateKernel
import Mathlib.Tactic.NormNum.Prime
import Erdos249257.GeneratedCertificates.Part00

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos249257

theorem concrete_generated_b2_F33_A14329_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (33 : Nat).factorization.support) :
    p = 3 ∨ p = 11 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 33 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 33 := Nat.le_of_dvd (by decide : 0 < 33) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact False.elim ((by decide : ¬ 2 ∣ 33) hp_dvd)
  · exact Or.inl rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)
  · exact False.elim ((by decide : ¬ 13 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 14) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 15) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 16) hp_prime)
  · exact False.elim ((by decide : ¬ 17 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 18) hp_prime)
  · exact False.elim ((by decide : ¬ 19 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 20) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 21) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 22) hp_prime)
  · exact False.elim ((by decide : ¬ 23 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 24) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 25) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 26) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 27) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 28) hp_prime)
  · exact False.elim ((by decide : ¬ 29 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 30) hp_prime)
  · exact False.elim ((by decide : ¬ 31 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 32) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 33) hp_prime)

theorem concrete_generated_b2_F33_A14329_p3_prime_witness :
    PrimeComponentWitness 33 14329 2 3 599479 := by
  have hquot : primeComponentQuotient 2 33 3 = 4196353 := by decide
  have hq : Nat.Prime 599479 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 599479 ∣ 14329)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F33_A14329_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 33 14329 2 3 := by
  exact Or.inr (Or.inr ⟨599479, concrete_generated_b2_F33_A14329_p3_prime_witness⟩)

theorem concrete_generated_b2_F33_A14329_p11_prime_witness :
    PrimeComponentWitness 33 14329 2 11 599479 := by
  have hquot : primeComponentQuotient 2 33 11 = 1227133513 := by decide
  have hq : Nat.Prime 599479 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 599479 ∣ 14329)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F33_A14329_p11_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 33 14329 2 11 := by
  exact Or.inr (Or.inr ⟨599479, concrete_generated_b2_F33_A14329_p11_prime_witness⟩)

def emittedCertificate_b2_L33_A14329 :
    EmittedCertificateTable 33 14329 2 where
  rows := ({3, 11} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F33_A14329_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F33_A14329_p3_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F33_A14329_p11_prime_witness

theorem orderOf_b2_mod599479_eq_33_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 2
      (by decide : Nat.Coprime 2 599479)) = 33 := by
  let hcop : Nat.Coprime 2 599479 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 33 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 33 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 599479)ˣ) : ZMod 599479) ^ 33) =
        (1 : ZMod 599479)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    33 14329 8589934591 599479 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L33_A14329

theorem concrete_lifted_b2_F33_A13788017_from_A23_mul599479_p3_prime_witness :
    PrimeComponentWitness 33 13788017 2 3 7 := by
  have hquot : primeComponentQuotient 2 33 3 = 4196353 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 13788017)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b2_F33_A13788017_from_A23_mul599479_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 33 13788017 2 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_lifted_b2_F33_A13788017_from_A23_mul599479_p3_prime_witness⟩)

theorem concrete_lifted_b2_F33_A13788017_from_A23_mul599479_p11_prime_witness :
    PrimeComponentWitness 33 13788017 2 11 89 := by
  have hquot : primeComponentQuotient 2 33 11 = 1227133513 := by decide
  have hq : Nat.Prime 89 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 89 ∣ 13788017)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b2_F33_A13788017_from_A23_mul599479_p11_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 33 13788017 2 11 := by
  exact Or.inr (Or.inr ⟨89, concrete_lifted_b2_F33_A13788017_from_A23_mul599479_p11_prime_witness⟩)

theorem concrete_generated_b4_F12_A51_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (12 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 12 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by decide : 0 < 12) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact False.elim ((by decide : ¬ 11 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)

set_option maxRecDepth 10000 in
theorem concrete_generated_b4_F12_A51_p2_prime_witness :
    PrimeComponentWitness 12 51 4 2 241 := by
  have hquot : primeComponentQuotient 4 12 2 = 4097 := by decide
  have hq : Nat.Prime 241 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 241 ∣ 51)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b4_F12_A51_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 51 4 2 := by
  exact Or.inr (Or.inr ⟨241, concrete_generated_b4_F12_A51_p2_prime_witness⟩)

theorem concrete_generated_b4_F12_A51_p3_prime_witness :
    PrimeComponentWitness 12 51 4 3 7 := by
  have hquot : primeComponentQuotient 4 12 3 = 65793 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 51)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b4_F12_A51_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 51 4 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b4_F12_A51_p3_prime_witness⟩)

def emittedCertificate_b4_L12_A51 :
    EmittedCertificateTable 12 51 4 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b4_F12_A51_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b4_F12_A51_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b4_F12_A51_p3_prime_witness

theorem orderOf_b4_mod328965_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 4
      (by decide : Nat.Coprime 4 328965)) = 12 := by
  let hcop : Nat.Coprime 4 328965 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 4 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 4 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 4 hcop : (ZMod 328965)ˣ) : ZMod 328965) ^ 12) =
        (1 : ZMod 328965)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 51 16777215 328965 4 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 4 hcop)) 4 (by decide))
    emittedCertificate_b4_L12_A51

theorem concrete_lifted_b6_F12_A65_from_A13_mul5_p2_prime_witness :
    PrimeComponentWitness 12 65 6 2 37 := by
  have hquot : primeComponentQuotient 6 12 2 = 46657 := by decide
  have hq : Nat.Prime 37 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 37 ∣ 65)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b6_F12_A65_from_A13_mul5_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 65 6 2 := by
  exact Or.inr (Or.inr ⟨37, concrete_lifted_b6_F12_A65_from_A13_mul5_p2_prime_witness⟩)

theorem concrete_lifted_b6_F12_A65_from_A13_mul5_p3_prime_witness :
    PrimeComponentWitness 12 65 6 3 31 := by
  have hquot : primeComponentQuotient 6 12 3 = 1680913 := by decide
  have hq : Nat.Prime 31 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 31 ∣ 65)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b6_F12_A65_from_A13_mul5_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 65 6 3 := by
  exact Or.inr (Or.inr ⟨31, concrete_lifted_b6_F12_A65_from_A13_mul5_p3_prime_witness⟩)

theorem concrete_generated_b10_F6_A231_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (6 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 6 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 6 := Nat.le_of_dvd (by decide : 0 < 6) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 6) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)

theorem concrete_generated_b10_F6_A231_p2_prime_witness :
    PrimeComponentWitness 6 231 10 2 13 := by
  have hquot : primeComponentQuotient 10 6 2 = 1001 := by decide
  have hq : Nat.Prime 13 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 13 ∣ 231)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b10_F6_A231_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 231 10 2 := by
  exact Or.inr (Or.inr ⟨13, concrete_generated_b10_F6_A231_p2_prime_witness⟩)

theorem concrete_generated_b10_F6_A231_p3_prime_witness :
    PrimeComponentWitness 6 231 10 3 13 := by
  have hquot : primeComponentQuotient 10 6 3 = 10101 := by decide
  have hq : Nat.Prime 13 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 13 ∣ 231)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b10_F6_A231_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 231 10 3 := by
  exact Or.inr (Or.inr ⟨13, concrete_generated_b10_F6_A231_p3_prime_witness⟩)

def emittedCertificate_b10_L6_A231 :
    EmittedCertificateTable 6 231 10 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b10_F6_A231_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b10_F6_A231_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b10_F6_A231_p3_prime_witness

theorem orderOf_b10_mod4329_eq_6_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 10
      (by decide : Nat.Coprime 10 4329)) = 6 := by
  let hcop : Nat.Coprime 10 4329 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 10 hcop) ∣ 6 := by
    have hpow_unit : (ZMod.unitOfCoprime 10 hcop) ^ 6 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 10 hcop : (ZMod 4329)ˣ) : ZMod 4329) ^ 6) =
        (1 : ZMod 4329)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    6 231 999999 4329 10 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 10 hcop)) 10 (by decide))
    emittedCertificate_b10_L6_A231

theorem concrete_generated_b12_F12_A145_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (12 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 12 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by decide : 0 < 12) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact False.elim ((by decide : ¬ 11 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)

theorem concrete_generated_b12_F12_A145_p2_prime_witness :
    PrimeComponentWitness 12 145 12 2 20593 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 145)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A145_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 145 12 2 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A145_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A145_p3_prime_witness :
    PrimeComponentWitness 12 145 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 145)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A145_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 145 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A145_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A145 :
    EmittedCertificateTable 12 145 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A145_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A145_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A145_p3_prime_witness

theorem orderOf_b12_mod61490347919_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 61490347919)) = 12 := by
  let hcop : Nat.Coprime 12 61490347919 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 61490347919)ˣ) :
          ZMod 61490347919) ^ 12) =
        (1 : ZMod 61490347919)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 145 8916100448255 61490347919 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A145

theorem concrete_generated_b12_F12_A1729_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (12 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 12 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by decide : 0 < 12) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact False.elim ((by decide : ¬ 11 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)

theorem concrete_generated_b12_F12_A1729_p2_prime_witness :
    PrimeComponentWitness 12 1729 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 1729)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1729_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1729 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A1729_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b12_F12_A1729_p3_prime_witness :
    PrimeComponentWitness 12 1729 12 3 157 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 157 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 157 ∣ 1729)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1729_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1729 12 3 := by
  exact Or.inr (Or.inr ⟨157, concrete_generated_b12_F12_A1729_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A1729 :
    EmittedCertificateTable 12 1729 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A1729_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1729_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1729_p3_prime_witness

theorem orderOf_b12_mod5156796095_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 5156796095)) = 12 := by
  let hcop : Nat.Coprime 12 5156796095 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 5156796095)ˣ) :
          ZMod 5156796095) ^ 12) =
        (1 : ZMod 5156796095)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 1729 8916100448255 5156796095 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A1729

theorem concrete_generated_b12_F12_A5005_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (12 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 12 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by decide : 0 < 12) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact False.elim ((by decide : ¬ 11 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)

theorem concrete_generated_b12_F12_A5005_p2_prime_witness :
    PrimeComponentWitness 12 5005 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 5005)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A5005_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 5005 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A5005_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A5005_p3_prime_witness :
    PrimeComponentWitness 12 5005 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 5005)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A5005_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 5005 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A5005_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A5005 :
    EmittedCertificateTable 12 5005 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A5005_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A5005_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A5005_p3_prime_witness

theorem orderOf_b12_mod1781438651_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 1781438651)) = 12 := by
  let hcop : Nat.Coprime 12 1781438651 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 1781438651)ˣ) :
          ZMod 1781438651) ^ 12) =
        (1 : ZMod 1781438651)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 5005 8916100448255 1781438651 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A5005

theorem concrete_generated_b12_F12_A35815_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (12 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 12 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by decide : 0 < 12) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact False.elim ((by decide : ¬ 11 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)

theorem concrete_generated_b12_F12_A35815_p2_prime_witness :
    PrimeComponentWitness 12 35815 12 2 20593 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 35815)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A35815_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 35815 12 2 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A35815_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A35815_p3_prime_witness :
    PrimeComponentWitness 12 35815 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 35815)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A35815_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 35815 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A35815_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A35815 :
    EmittedCertificateTable 12 35815 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A35815_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A35815_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A35815_p3_prime_witness

theorem orderOf_b12_mod248948777_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 248948777)) = 12 := by
  let hcop : Nat.Coprime 12 248948777 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 248948777)ˣ) :
          ZMod 248948777) ^ 12) =
        (1 : ZMod 248948777)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 35815 8916100448255 248948777 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A35815

theorem concrete_lifted_b12_F12_A144151_from_A7_mul20593_p2_prime_witness :
    PrimeComponentWitness 12 144151 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 144151)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b12_F12_A144151_from_A7_mul20593_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 144151 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_lifted_b12_F12_A144151_from_A7_mul20593_p2_prime_witness⟩)

theorem concrete_lifted_b12_F12_A144151_from_A7_mul20593_p3_prime_witness :
    PrimeComponentWitness 12 144151 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 144151)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b12_F12_A144151_from_A7_mul20593_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 144151 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_lifted_b12_F12_A144151_from_A7_mul20593_p3_prime_witness⟩)

theorem concrete_generated_b12_F12_A1357265_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (12 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 12 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by decide : 0 < 12) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact False.elim ((by decide : ¬ 11 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)

theorem concrete_generated_b12_F12_A1357265_p2_prime_witness :
    PrimeComponentWitness 12 1357265 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 1357265)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1357265_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1357265 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A1357265_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A1357265_p3_prime_witness :
    PrimeComponentWitness 12 1357265 12 3 20593 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 1357265)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1357265_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1357265 12 3 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A1357265_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A1357265 :
    EmittedCertificateTable 12 1357265 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A1357265_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1357265_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1357265_p3_prime_witness

theorem orderOf_b12_mod6569167_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 6569167)) = 12 := by
  let hcop : Nat.Coprime 12 6569167 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 6569167)ˣ) :
          ZMod 6569167) ^ 12) =
        (1 : ZMod 6569167)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 1357265 8916100448255 6569167 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A1357265

theorem concrete_generated_b12_F12_A178026485_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (12 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 12 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by decide : 0 < 12) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact False.elim ((by decide : ¬ 11 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)

theorem concrete_generated_b12_F12_A178026485_p2_prime_witness :
    PrimeComponentWitness 12 178026485 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 178026485)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A178026485_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 178026485 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A178026485_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b12_F12_A178026485_p3_prime_witness :
    PrimeComponentWitness 12 178026485 12 3 157 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 157 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 157 ∣ 178026485)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A178026485_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 178026485 12 3 := by
  exact Or.inr (Or.inr ⟨157, concrete_generated_b12_F12_A178026485_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A178026485 :
    EmittedCertificateTable 12 178026485 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A178026485_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A178026485_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A178026485_p3_prime_witness

theorem orderOf_b12_mod50083_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 50083)) = 12 := by
  let hcop : Nat.Coprime 12 50083 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 50083)ˣ) : ZMod 50083) ^ 12) =
        (1 : ZMod 50083)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 178026485 8916100448255 50083 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A178026485

end Erdos249257
