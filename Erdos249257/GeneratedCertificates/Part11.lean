-- Generated direct-prime emitted certificates, part 11 of 16 (12 certificates).
import Erdos249257.CertificateKernel
import Mathlib.Tactic.NormNum.Prime
import Erdos249257.GeneratedCertificates.Part00

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos249257

theorem concrete_generated_b2_F33_A2047_factorization_support_cases
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

theorem concrete_generated_b2_F33_A2047_p3_prime_witness :
    PrimeComponentWitness 33 2047 2 3 7 := by
  have hquot : primeComponentQuotient 2 33 3 = 4196353 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 2047)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F33_A2047_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 33 2047 2 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b2_F33_A2047_p3_prime_witness⟩)

theorem concrete_generated_b2_F33_A2047_p11_prime_witness :
    PrimeComponentWitness 33 2047 2 11 599479 := by
  have hquot : primeComponentQuotient 2 33 11 = 1227133513 := by decide
  have hq : Nat.Prime 599479 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 599479 ∣ 2047)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F33_A2047_p11_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 33 2047 2 11 := by
  exact Or.inr (Or.inr ⟨599479, concrete_generated_b2_F33_A2047_p11_prime_witness⟩)

def emittedCertificate_b2_L33_A2047 :
    EmittedCertificateTable 33 2047 2 where
  rows := ({3, 11} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F33_A2047_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F33_A2047_p3_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F33_A2047_p11_prime_witness

theorem orderOf_b2_mod4196353_eq_33_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 2
      (by decide : Nat.Coprime 2 4196353)) = 33 := by
  let hcop : Nat.Coprime 2 4196353 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 33 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 33 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 4196353)ˣ) :
          ZMod 4196353) ^ 33) =
        (1 : ZMod 4196353)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    33 2047 8589934591 4196353 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L33_A2047

theorem concrete_lifted_b2_F33_A599479_from_A89_factorization_le_p3_prime_witness :
    PrimeComponentWitness 33 599479 2 3 7 := by
  have hquot : primeComponentQuotient 2 33 3 = 4196353 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 599479)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b2_F33_A599479_from_A89_factorization_le_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 33 599479 2 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_lifted_b2_F33_A599479_from_A89_factorization_le_p3_prime_witness⟩)

theorem concrete_lifted_b2_F33_A599479_from_A89_factorization_le_p11_prime_witness :
    PrimeComponentWitness 33 599479 2 11 23 := by
  have hquot : primeComponentQuotient 2 33 11 = 1227133513 := by decide
  have hq : Nat.Prime 23 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 23 ∣ 599479)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b2_F33_A599479_from_A89_factorization_le_p11_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 33 599479 2 11 := by
  exact Or.inr (Or.inr ⟨23, concrete_lifted_b2_F33_A599479_from_A89_factorization_le_p11_prime_witness⟩)

theorem concrete_lifted_b4_F12_A1785_from_A357_mul5_p2_prime_witness :
    PrimeComponentWitness 12 1785 4 2 241 := by
  have hquot : primeComponentQuotient 4 12 2 = 4097 := by decide
  have hq : Nat.Prime 241 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 241 ∣ 1785)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b4_F12_A1785_from_A357_mul5_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1785 4 2 := by
  exact Or.inr (Or.inr ⟨241, concrete_lifted_b4_F12_A1785_from_A357_mul5_p2_prime_witness⟩)

theorem concrete_lifted_b4_F12_A1785_from_A357_mul5_p3_prime_witness :
    PrimeComponentWitness 12 1785 4 3 13 := by
  have hquot : primeComponentQuotient 4 12 3 = 65793 := by decide
  have hq : Nat.Prime 13 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 13 ∣ 1785)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b4_F12_A1785_from_A357_mul5_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1785 4 3 := by
  exact Or.inr (Or.inr ⟨13, concrete_lifted_b4_F12_A1785_from_A357_mul5_p3_prime_witness⟩)

theorem concrete_generated_b6_F12_A403_factorization_support_cases
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

theorem concrete_generated_b6_F12_A403_p2_prime_witness :
    PrimeComponentWitness 12 403 6 2 37 := by
  have hquot : primeComponentQuotient 6 12 2 = 46657 := by decide
  have hq : Nat.Prime 37 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 37 ∣ 403)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b6_F12_A403_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 403 6 2 := by
  exact Or.inr (Or.inr ⟨37, concrete_generated_b6_F12_A403_p2_prime_witness⟩)

theorem concrete_generated_b6_F12_A403_p3_prime_witness :
    PrimeComponentWitness 12 403 6 3 43 := by
  have hquot : primeComponentQuotient 6 12 3 = 1680913 := by decide
  have hq : Nat.Prime 43 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 43 ∣ 403)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b6_F12_A403_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 403 6 3 := by
  exact Or.inr (Or.inr ⟨43, concrete_generated_b6_F12_A403_p3_prime_witness⟩)

def emittedCertificate_b6_L12_A403 :
    EmittedCertificateTable 12 403 6 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b6_F12_A403_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b6_F12_A403_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b6_F12_A403_p3_prime_witness

theorem orderOf_b6_mod5401445_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 6
      (by decide : Nat.Coprime 6 5401445)) = 12 := by
  let hcop : Nat.Coprime 6 5401445 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 6 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 6 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 6 hcop : (ZMod 5401445)ˣ) :
          ZMod 5401445) ^ 12) =
        (1 : ZMod 5401445)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 403 2176782335 5401445 6 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 6 hcop)) 6 (by decide))
    emittedCertificate_b6_L12_A403

theorem concrete_generated_b6_F12_A14911_factorization_support_cases
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

theorem concrete_generated_b6_F12_A14911_p2_prime_witness :
    PrimeComponentWitness 12 14911 6 2 97 := by
  have hquot : primeComponentQuotient 6 12 2 = 46657 := by decide
  have hq : Nat.Prime 97 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 97 ∣ 14911)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b6_F12_A14911_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 14911 6 2 := by
  exact Or.inr (Or.inr ⟨97, concrete_generated_b6_F12_A14911_p2_prime_witness⟩)

theorem concrete_generated_b6_F12_A14911_p3_prime_witness :
    PrimeComponentWitness 12 14911 6 3 43 := by
  have hquot : primeComponentQuotient 6 12 3 = 1680913 := by decide
  have hq : Nat.Prime 43 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 43 ∣ 14911)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b6_F12_A14911_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 14911 6 3 := by
  exact Or.inr (Or.inr ⟨43, concrete_generated_b6_F12_A14911_p3_prime_witness⟩)

def emittedCertificate_b6_L12_A14911 :
    EmittedCertificateTable 12 14911 6 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b6_F12_A14911_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b6_F12_A14911_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b6_F12_A14911_p3_prime_witness

theorem orderOf_b6_mod145985_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 6
      (by decide : Nat.Coprime 6 145985)) = 12 := by
  let hcop : Nat.Coprime 6 145985 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 6 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 6 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 6 hcop : (ZMod 145985)ˣ) : ZMod 145985) ^ 12) =
        (1 : ZMod 145985)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 14911 2176782335 145985 6 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 6 hcop)) 6 (by decide))
    emittedCertificate_b6_L12_A14911

theorem concrete_generated_b10_F6_A77_factorization_support_cases
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

theorem concrete_generated_b10_F6_A77_p2_prime_witness :
    PrimeComponentWitness 6 77 10 2 13 := by
  have hquot : primeComponentQuotient 10 6 2 = 1001 := by decide
  have hq : Nat.Prime 13 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 13 ∣ 77)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b10_F6_A77_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 77 10 2 := by
  exact Or.inr (Or.inr ⟨13, concrete_generated_b10_F6_A77_p2_prime_witness⟩)

theorem concrete_generated_b10_F6_A77_p3_prime_witness :
    PrimeComponentWitness 6 77 10 3 3 := by
  have hquot : primeComponentQuotient 10 6 3 = 10101 := by decide
  have hq : Nat.Prime 3 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 77)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b10_F6_A77_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 77 10 3 := by
  exact Or.inr (Or.inr ⟨3, concrete_generated_b10_F6_A77_p3_prime_witness⟩)

def emittedCertificate_b10_L6_A77 :
    EmittedCertificateTable 6 77 10 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b10_F6_A77_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b10_F6_A77_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b10_F6_A77_p3_prime_witness

theorem orderOf_b10_mod12987_eq_6_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 10
      (by decide : Nat.Coprime 10 12987)) = 6 := by
  let hcop : Nat.Coprime 10 12987 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 10 hcop) ∣ 6 := by
    have hpow_unit : (ZMod.unitOfCoprime 10 hcop) ^ 6 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 10 hcop : (ZMod 12987)ˣ) : ZMod 12987) ^ 6) =
        (1 : ZMod 12987)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    6 77 999999 12987 10 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 10 hcop)) 10 (by decide))
    emittedCertificate_b10_L6_A77

theorem concrete_generated_b12_F12_A785_factorization_support_cases
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

theorem concrete_generated_b12_F12_A785_p2_prime_witness :
    PrimeComponentWitness 12 785 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 785)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A785_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 785 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A785_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A785_p3_prime_witness :
    PrimeComponentWitness 12 785 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 785)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A785_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 785 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A785_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A785 :
    EmittedCertificateTable 12 785 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A785_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A785_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A785_p3_prime_witness

theorem orderOf_b12_mod11358089743_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 11358089743)) = 12 := by
  let hcop : Nat.Coprime 12 11358089743 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 11358089743)ˣ) :
          ZMod 11358089743) ^ 12) =
        (1 : ZMod 11358089743)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 785 8916100448255 11358089743 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A785

theorem concrete_generated_b12_F12_A12089_factorization_support_cases
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

theorem concrete_generated_b12_F12_A12089_p2_prime_witness :
    PrimeComponentWitness 12 12089 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 12089)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A12089_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 12089 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A12089_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A12089_p3_prime_witness :
    PrimeComponentWitness 12 12089 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 12089)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A12089_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 12089 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A12089_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A12089 :
    EmittedCertificateTable 12 12089 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A12089_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A12089_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A12089_p3_prime_witness

theorem orderOf_b12_mod737538295_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 737538295)) = 12 := by
  let hcop : Nat.Coprime 12 737538295 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 737538295)ˣ) :
          ZMod 737538295) ^ 12) =
        (1 : ZMod 737538295)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 12089 8916100448255 737538295 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A12089

theorem concrete_generated_b12_F12_A19285_factorization_support_cases
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

theorem concrete_generated_b12_F12_A19285_p2_prime_witness :
    PrimeComponentWitness 12 19285 12 2 20593 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 19285)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A19285_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 19285 12 2 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A19285_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b12_F12_A19285_p3_prime_witness :
    PrimeComponentWitness 12 19285 12 3 157 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 157 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 157 ∣ 19285)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A19285_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 19285 12 3 := by
  exact Or.inr (Or.inr ⟨157, concrete_generated_b12_F12_A19285_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A19285 :
    EmittedCertificateTable 12 19285 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A19285_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A19285_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A19285_p3_prime_witness

theorem orderOf_b12_mod462333443_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 462333443)) = 12 := by
  let hcop : Nat.Coprime 12 462333443 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 462333443)ˣ) :
          ZMod 462333443) ^ 12) =
        (1 : ZMod 462333443)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 19285 8916100448255 462333443 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A19285

theorem concrete_lifted_b12_F12_A102965_from_A5_mul20593_p2_prime_witness :
    PrimeComponentWitness 12 102965 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 102965)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b12_F12_A102965_from_A5_mul20593_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 102965 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_lifted_b12_F12_A102965_from_A5_mul20593_p2_prime_witness⟩)

theorem concrete_lifted_b12_F12_A102965_from_A5_mul20593_p3_prime_witness :
    PrimeComponentWitness 12 102965 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 102965)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b12_F12_A102965_from_A5_mul20593_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 102965 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_lifted_b12_F12_A102965_from_A5_mul20593_p3_prime_witness⟩)

theorem concrete_generated_b12_F12_A159355_factorization_support_cases
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

theorem concrete_generated_b12_F12_A159355_p2_prime_witness :
    PrimeComponentWitness 12 159355 12 2 20593 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 159355)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A159355_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 159355 12 2 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A159355_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A159355_p3_prime_witness :
    PrimeComponentWitness 12 159355 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 159355)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A159355_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 159355 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A159355_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A159355 :
    EmittedCertificateTable 12 159355 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A159355_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A159355_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A159355_p3_prime_witness

theorem orderOf_b12_mod55951181_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 55951181)) = 12 := by
  let hcop : Nat.Coprime 12 55951181 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 55951181)ˣ) :
          ZMod 55951181) ^ 12) =
        (1 : ZMod 55951181)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 159355 8916100448255 55951181 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A159355

theorem concrete_generated_b12_F12_A3255395_factorization_support_cases
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

theorem concrete_generated_b12_F12_A3255395_p2_prime_witness :
    PrimeComponentWitness 12 3255395 12 2 20593 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 3255395)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A3255395_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 3255395 12 2 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A3255395_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A3255395_p3_prime_witness :
    PrimeComponentWitness 12 3255395 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 3255395)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A3255395_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 3255395 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A3255395_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A3255395 :
    EmittedCertificateTable 12 3255395 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A3255395_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A3255395_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A3255395_p3_prime_witness

theorem orderOf_b12_mod2738869_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 2738869)) = 12 := by
  let hcop : Nat.Coprime 12 2738869 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 2738869)ˣ) :
          ZMod 2738869) ^ 12) =
        (1 : ZMod 2738869)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 3255395 8916100448255 2738869 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A3255395

end Erdos249257
