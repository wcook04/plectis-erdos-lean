-- Generated direct-prime emitted certificates, part 14 of 16 (11 certificates).
import Erdos249257.CertificateKernel
import Mathlib.Tactic.NormNum.Prime
import Erdos249257.GeneratedCertificates.Part00

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos249257

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F30_A99_p2_prime_witness :
    PrimeComponentWitness 30 99 2 2 331 := by
  have hquot : primeComponentQuotient 2 30 2 = 32769 := by decide
  have hq : Nat.Prime 331 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 331 ∣ 99)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F30_A99_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 30 99 2 2 := by
  exact Or.inr (Or.inr ⟨331, concrete_generated_b2_F30_A99_p2_prime_witness⟩)

theorem concrete_generated_b2_F30_A99_p3_prime_witness :
    PrimeComponentWitness 30 99 2 3 7 := by
  have hquot : primeComponentQuotient 2 30 3 = 1049601 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 99)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F30_A99_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 30 99 2 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b2_F30_A99_p3_prime_witness⟩)

theorem concrete_generated_b2_F30_A99_p5_prime_witness :
    PrimeComponentWitness 30 99 2 5 31 := by
  have hquot : primeComponentQuotient 2 30 5 = 17043521 := by decide
  have hq : Nat.Prime 31 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 31 ∣ 99)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F30_A99_p5_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 30 99 2 5 := by
  exact Or.inr (Or.inr ⟨31, concrete_generated_b2_F30_A99_p5_prime_witness⟩)

def emittedCertificate_b2_L30_A99 :
    EmittedCertificateTable 30 99 2 where
  rows := ({2, 3, 5} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F30_factorization_support_cases hp with rfl | rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F30_A99_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F30_A99_p3_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F30_A99_p5_prime_witness

theorem orderOf_b2_mod10845877_eq_30_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 2
      (by decide : Nat.Coprime 2 10845877)) = 30 := by
  let hcop : Nat.Coprime 2 10845877 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 30 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 30 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 10845877)ˣ) :
          ZMod 10845877) ^ 30) =
        (1 : ZMod 10845877)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    30 99 1073741823 10845877 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L30_A99

theorem concrete_generated_b2_F105_A71_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (105 : Nat).factorization.support) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  have hsupport :
      (105 : Nat).factorization.support = ({3, 5, 7} : Finset Nat) := by
    rw [Nat.support_factorization]
    rw [show (105 : Nat) = 3 * (5 * (7)) by decide]
    rw [Nat.primeFactors_mul (by decide) (by decide)]
    rw [Nat.primeFactors_mul (by decide) (by decide)]
    rw [Nat.Prime.primeFactors (by decide : Nat.Prime 3)]
    rw [Nat.Prime.primeFactors (by decide : Nat.Prime 5)]
    rw [Nat.Prime.primeFactors (by decide : Nat.Prime 7)]
    rfl
  rw [hsupport] at hp
  simpa using hp

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F105_A71_p3_prime_witness :
    PrimeComponentWitness 105 71 2 3 7 := by
  have hquot : primeComponentQuotient 2 105 3 = 1180591620751771041793 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 71)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F105_A71_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 71 2 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b2_F105_A71_p3_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F105_A71_p5_prime_witness :
    PrimeComponentWitness 105 71 2 5 31 := by
  have hquot : primeComponentQuotient 2 105 5 = 19342822337210501698682881 := by decide
  have hq : Nat.Prime 31 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 31 ∣ 71)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F105_A71_p5_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 71 2 5 := by
  exact Or.inr (Or.inr ⟨31, concrete_generated_b2_F105_A71_p5_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F105_A71_p7_prime_witness :
    PrimeComponentWitness 105 71 2 7 7 := by
  have hquot : primeComponentQuotient 2 105 7 = 1237977819370199922113544193 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 71)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F105_A71_p7_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 71 2 7 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b2_F105_A71_p7_prime_witness⟩)

def emittedCertificate_b2_L105_A71 :
    EmittedCertificateTable 105 71 2 where
  rows := ({3, 5, 7} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F105_A71_factorization_support_cases hp with rfl | rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A71_p3_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A71_p5_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A71_p7_prime_witness

set_option maxRecDepth 10000 in
theorem orderOf_b2_mod571335481793004800674570458761_eq_105_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 2
      (by decide : Nat.Coprime 2 571335481793004800674570458761)) = 105 := by
  let hcop : Nat.Coprime 2 571335481793004800674570458761 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 105 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 105 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 571335481793004800674570458761)ˣ) :
          ZMod 571335481793004800674570458761) ^ 105) =
        (1 : ZMod 571335481793004800674570458761)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    105 71 40564819207303340847894502572031 571335481793004800674570458761 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L105_A71

theorem concrete_lifted_b2_F105_A279527_from_A2201_mul127_p3_prime_witness :
    PrimeComponentWitness 105 279527 2 3 7 := by
  have hquot : primeComponentQuotient 2 105 3 = 1180591620751771041793 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 279527)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b2_F105_A279527_from_A2201_mul127_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 279527 2 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_lifted_b2_F105_A279527_from_A2201_mul127_p3_prime_witness⟩)

theorem concrete_lifted_b2_F105_A279527_from_A2201_mul127_p5_prime_witness :
    PrimeComponentWitness 105 279527 2 5 151 := by
  have hquot : primeComponentQuotient 2 105 5 = 19342822337210501698682881 := by decide
  have hq : Nat.Prime 151 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 151 ∣ 279527)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b2_F105_A279527_from_A2201_mul127_p5_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 279527 2 5 := by
  exact Or.inr (Or.inr ⟨151, concrete_lifted_b2_F105_A279527_from_A2201_mul127_p5_prime_witness⟩)

theorem concrete_lifted_b2_F105_A279527_from_A2201_mul127_p7_prime_witness :
    PrimeComponentWitness 105 279527 2 7 7 := by
  have hquot : primeComponentQuotient 2 105 7 = 1237977819370199922113544193 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 279527)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b2_F105_A279527_from_A2201_mul127_p7_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 279527 2 7 := by
  exact Or.inr (Or.inr ⟨7, concrete_lifted_b2_F105_A279527_from_A2201_mul127_p7_prime_witness⟩)

theorem concrete_generated_b4_F12_A5_factorization_support_cases
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

theorem concrete_generated_b4_F12_A5_p2_prime_witness :
    PrimeComponentWitness 12 5 4 2 17 := by
  have hquot : primeComponentQuotient 4 12 2 = 4097 := by decide
  have hq : Nat.Prime 17 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 17 ∣ 5)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b4_F12_A5_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 5 4 2 := by
  exact Or.inr (Or.inr ⟨17, concrete_generated_b4_F12_A5_p2_prime_witness⟩)

theorem concrete_generated_b4_F12_A5_p3_prime_witness :
    PrimeComponentWitness 12 5 4 3 3 := by
  have hquot : primeComponentQuotient 4 12 3 = 65793 := by decide
  have hq : Nat.Prime 3 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 5)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b4_F12_A5_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 5 4 3 := by
  exact Or.inr (Or.inr ⟨3, concrete_generated_b4_F12_A5_p3_prime_witness⟩)

def emittedCertificate_b4_L12_A5 :
    EmittedCertificateTable 12 5 4 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b4_F12_A5_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b4_F12_A5_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b4_F12_A5_p3_prime_witness

theorem orderOf_b4_mod3355443_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 4
      (by decide : Nat.Coprime 4 3355443)) = 12 := by
  let hcop : Nat.Coprime 4 3355443 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 4 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 4 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 4 hcop : (ZMod 3355443)ˣ) :
          ZMod 3355443) ^ 12) =
        (1 : ZMod 3355443)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 5 16777215 3355443 4 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 4 hcop)) 4 (by decide))
    emittedCertificate_b4_L12_A5

theorem concrete_lifted_b10_F6_A2849_from_A77_mul37_p2_prime_witness :
    PrimeComponentWitness 6 2849 10 2 13 := by
  have hquot : primeComponentQuotient 10 6 2 = 1001 := by decide
  have hq : Nat.Prime 13 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 13 ∣ 2849)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b10_F6_A2849_from_A77_mul37_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 2849 10 2 := by
  exact Or.inr (Or.inr ⟨13, concrete_lifted_b10_F6_A2849_from_A77_mul37_p2_prime_witness⟩)

theorem concrete_lifted_b10_F6_A2849_from_A77_mul37_p3_prime_witness :
    PrimeComponentWitness 6 2849 10 3 3 := by
  have hquot : primeComponentQuotient 10 6 3 = 10101 := by decide
  have hq : Nat.Prime 3 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2849)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b10_F6_A2849_from_A77_mul37_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 2849 10 3 := by
  exact Or.inr (Or.inr ⟨3, concrete_lifted_b10_F6_A2849_from_A77_mul37_p3_prime_witness⟩)

theorem concrete_generated_b12_F12_A77_factorization_support_cases
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

theorem concrete_generated_b12_F12_A77_p2_prime_witness :
    PrimeComponentWitness 12 77 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 77)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A77_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 77 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A77_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A77_p3_prime_witness :
    PrimeComponentWitness 12 77 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 77)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A77_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 77 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A77_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A77 :
    EmittedCertificateTable 12 77 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A77_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A77_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A77_p3_prime_witness

theorem orderOf_b12_mod115793512315_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 115793512315)) = 12 := by
  let hcop : Nat.Coprime 12 115793512315 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 115793512315)ˣ) :
          ZMod 115793512315) ^ 12) =
        (1 : ZMod 115793512315)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 77 8916100448255 115793512315 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A77

theorem concrete_generated_b12_F12_A665_factorization_support_cases
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

theorem concrete_generated_b12_F12_A665_p2_prime_witness :
    PrimeComponentWitness 12 665 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 665)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A665_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 665 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A665_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b12_F12_A665_p3_prime_witness :
    PrimeComponentWitness 12 665 12 3 157 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 157 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 157 ∣ 665)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A665_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 665 12 3 := by
  exact Or.inr (Or.inr ⟨157, concrete_generated_b12_F12_A665_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A665 :
    EmittedCertificateTable 12 665 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A665_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A665_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A665_p3_prime_witness

theorem orderOf_b12_mod13407669847_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 13407669847)) = 12 := by
  let hcop : Nat.Coprime 12 13407669847 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 13407669847)ˣ) :
          ZMod 13407669847) ^ 12) =
        (1 : ZMod 13407669847)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 665 8916100448255 13407669847 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A665

theorem concrete_generated_b12_F12_A2233_factorization_support_cases
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

theorem concrete_generated_b12_F12_A2233_p2_prime_witness :
    PrimeComponentWitness 12 2233 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 2233)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A2233_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 2233 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A2233_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A2233_p3_prime_witness :
    PrimeComponentWitness 12 2233 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 2233)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A2233_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 2233 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A2233_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A2233 :
    EmittedCertificateTable 12 2233 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A2233_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A2233_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A2233_p3_prime_witness

theorem orderOf_b12_mod3992879735_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 3992879735)) = 12 := by
  let hcop : Nat.Coprime 12 3992879735 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 3992879735)ˣ) :
          ZMod 3992879735) ^ 12) =
        (1 : ZMod 3992879735)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 2233 8916100448255 3992879735 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A2233

theorem concrete_generated_b12_F12_A29029_factorization_support_cases
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

theorem concrete_generated_b12_F12_A29029_p2_prime_witness :
    PrimeComponentWitness 12 29029 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 29029)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A29029_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 29029 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A29029_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A29029_p3_prime_witness :
    PrimeComponentWitness 12 29029 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 29029)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A29029_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 29029 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A29029_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A29029 :
    EmittedCertificateTable 12 29029 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A29029_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A29029_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A29029_p3_prime_witness

theorem orderOf_b12_mod307144595_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 307144595)) = 12 := by
  let hcop : Nat.Coprime 12 307144595 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 307144595)ˣ) :
          ZMod 307144595) ^ 12) =
        (1 : ZMod 307144595)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 29029 8916100448255 307144595 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A29029

theorem concrete_generated_b12_F12_A720755_factorization_support_cases
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

theorem concrete_generated_b12_F12_A720755_p2_prime_witness :
    PrimeComponentWitness 12 720755 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 720755)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A720755_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 720755 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A720755_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A720755_p3_prime_witness :
    PrimeComponentWitness 12 720755 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 720755)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A720755_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 720755 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A720755_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A720755 :
    EmittedCertificateTable 12 720755 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A720755_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A720755_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A720755_p3_prime_witness

theorem orderOf_b12_mod12370501_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 12370501)) = 12 := by
  let hcop : Nat.Coprime 12 12370501 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 12370501)ˣ) :
          ZMod 12370501) ^ 12) =
        (1 : ZMod 12370501)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 720755 8916100448255 12370501 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A720755

theorem concrete_generated_b12_F12_A35605297_factorization_support_cases
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

theorem concrete_generated_b12_F12_A35605297_p2_prime_witness :
    PrimeComponentWitness 12 35605297 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 35605297)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A35605297_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 35605297 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A35605297_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b12_F12_A35605297_p3_prime_witness :
    PrimeComponentWitness 12 35605297 12 3 157 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 157 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 157 ∣ 35605297)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A35605297_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 35605297 12 3 := by
  exact Or.inr (Or.inr ⟨157, concrete_generated_b12_F12_A35605297_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A35605297 :
    EmittedCertificateTable 12 35605297 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A35605297_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A35605297_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A35605297_p3_prime_witness

theorem orderOf_b12_mod250415_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 250415)) = 12 := by
  let hcop : Nat.Coprime 12 250415 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 250415)ˣ) : ZMod 250415) ^ 12) =
        (1 : ZMod 250415)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 35605297 8916100448255 250415 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A35605297

end Erdos249257
