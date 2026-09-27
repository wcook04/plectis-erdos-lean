-- Generated direct-prime emitted certificates, part 4 of 16 (11 certificates).
import Erdos249257.CertificateKernel
import Mathlib.Tactic.NormNum.Prime
import Erdos249257.GeneratedCertificates.Part00

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos249257

theorem concrete_generated_b2_F12_A9_p2_prime_witness :
    PrimeComponentWitness 12 9 2 2 5 := by
  have hquot : primeComponentQuotient 2 12 2 = 65 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 9)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F12_A9_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 9 2 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b2_F12_A9_p2_prime_witness⟩)

theorem concrete_generated_b2_F12_A9_p3_prime_witness :
    PrimeComponentWitness 12 9 2 3 7 := by
  have hquot : primeComponentQuotient 2 12 3 = 273 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 9)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F12_A9_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 9 2 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b2_F12_A9_p3_prime_witness⟩)

def emittedCertificate_b2_L12_A9 :
    EmittedCertificateTable 12 9 2 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F12_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F12_A9_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F12_A9_p3_prime_witness

theorem orderOf_b2_mod455_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 2
      (by decide : Nat.Coprime 2 455)) = 12 := by
  let hcop : Nat.Coprime 2 455 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 455)ˣ) : ZMod 455) ^ 12) =
        (1 : ZMod 455)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 9 4095 455 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L12_A9

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F210_A21_p2_prime_witness :
    PrimeComponentWitness 210 21 2 2 3 := by
  refine ⟨(by decide : Nat.Prime 3), ?_, ?_⟩
  · have hquot : primeComponentQuotient 2 210 2 = 40564819207303340847894502572033 := by decide
    rw [hquot]
    decide
  · have hquot : primeComponentQuotient 2 210 2 = 40564819207303340847894502572033 := by decide
    rw [hquot]
    have hfactor : (40564819207303340847894502572033 : Nat).factorization 3 = 2 := by
      rw [show (40564819207303340847894502572033 : Nat) = 3 ^ 2 * 4507202134144815649766055841337 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      change (3 ^ 2 : Nat).factorization 3 + (4507202134144815649766055841337 : Nat).factorization 3 = 2
      have hleft : (3 ^ 2 : Nat).factorization 3 = 2 :=
        Nat.factorization_pow_self (by decide : Nat.Prime 3)
      have hright : (4507202134144815649766055841337 : Nat).factorization 3 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 4507202134144815649766055841337)
      rw [hleft, hright]
    rw [hfactor]
    have hA_factor : (21 : Nat).factorization 3 = 1 := by
      rw [show (21 : Nat) = 3 * 7 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 3),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 7),
      ]
    rw [hA_factor]
    decide

theorem concrete_generated_b2_F210_A21_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 210 21 2 2 := by
  exact Or.inr (Or.inr ⟨3, concrete_generated_b2_F210_A21_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F210_A21_p3_prime_witness :
    PrimeComponentWitness 210 21 2 3 7 := by
  refine ⟨(by decide : Nat.Prime 7), ?_, ?_⟩
  · have hquot : primeComponentQuotient 2 210 3 = 1393796574908163946347162983661240005427201 := by decide
    rw [hquot]
    decide
  · have hquot : primeComponentQuotient 2 210 3 = 1393796574908163946347162983661240005427201 := by decide
    rw [hquot]
    have hfactor : (1393796574908163946347162983661240005427201 : Nat).factorization 7 = 2 := by
      rw [show (1393796574908163946347162983661240005427201 : Nat) = 7 ^ 2 * 28444828059350284619329856809413061335249 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      change (7 ^ 2 : Nat).factorization 7 + (28444828059350284619329856809413061335249 : Nat).factorization 7 = 2
      have hleft : (7 ^ 2 : Nat).factorization 7 = 2 :=
        Nat.factorization_pow_self (by decide : Nat.Prime 7)
      have hright : (28444828059350284619329856809413061335249 : Nat).factorization 7 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 28444828059350284619329856809413061335249)
      rw [hleft, hright]
    rw [hfactor]
    have hA_factor : (21 : Nat).factorization 7 = 1 := by
      rw [show (21 : Nat) = 7 * 3 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 7),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 3),
      ]
    rw [hA_factor]
    decide

theorem concrete_generated_b2_F210_A21_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 210 21 2 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b2_F210_A21_p3_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F210_A21_p5_prime_witness :
    PrimeComponentWitness 210 21 2 5 11 := by
  have hquot : primeComponentQuotient 2 210 5 = 374144419156796217651873571134047410522241514864641 := by decide
  have hq : Nat.Prime 11 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 11 ∣ 21)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F210_A21_p5_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 210 21 2 5 := by
  exact Or.inr (Or.inr ⟨11, concrete_generated_b2_F210_A21_p5_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F210_A21_p7_prime_witness :
    PrimeComponentWitness 210 21 2 7 43 := by
  have hquot : primeComponentQuotient 2 210 7 = 1532495542293136552393534905231451066410343099426406401 := by decide
  have hq : Nat.Prime 43 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 43 ∣ 21)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F210_A21_p7_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 210 21 2 7 := by
  exact Or.inr (Or.inr ⟨43, concrete_generated_b2_F210_A21_p7_prime_witness⟩)

def emittedCertificate_b2_L210_A21 :
    EmittedCertificateTable 210 21 2 where
  rows := ({2, 3, 5, 7} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F210_factorization_support_cases hp with rfl | rfl | rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq | hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F210_A21_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F210_A21_p3_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F210_A21_p5_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F210_A21_p7_prime_witness

set_option maxRecDepth 10000 in
theorem orderOf_b2_mod78357359872438382959760437264635738332511231696837136349933763_eq_210_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 2
      (by decide : Nat.Coprime 2 78357359872438382959760437264635738332511231696837136349933763)) = 210 := by
  let hcop : Nat.Coprime 2 78357359872438382959760437264635738332511231696837136349933763 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 210 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 210 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 78357359872438382959760437264635738332511231696837136349933763)ˣ) :
          ZMod 78357359872438382959760437264635738332511231696837136349933763) ^ 210) =
        (1 : ZMod 78357359872438382959760437264635738332511231696837136349933763)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    210 21 1645504557321206042154969182557350504982735865633579863348609023 78357359872438382959760437264635738332511231696837136349933763 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L210_A21

theorem concrete_lifted_b4_F12_A255_from_A51_mul5_p2_prime_witness :
    PrimeComponentWitness 12 255 4 2 241 := by
  have hquot : primeComponentQuotient 4 12 2 = 4097 := by decide
  have hq : Nat.Prime 241 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 241 ∣ 255)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b4_F12_A255_from_A51_mul5_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 255 4 2 := by
  exact Or.inr (Or.inr ⟨241, concrete_lifted_b4_F12_A255_from_A51_mul5_p2_prime_witness⟩)

theorem concrete_lifted_b4_F12_A255_from_A51_mul5_p3_prime_witness :
    PrimeComponentWitness 12 255 4 3 7 := by
  have hquot : primeComponentQuotient 4 12 3 = 65793 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 255)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b4_F12_A255_from_A51_mul5_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 255 4 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_lifted_b4_F12_A255_from_A51_mul5_p3_prime_witness⟩)

theorem concrete_lifted_b10_F6_A8547_from_A231_mul37_p2_prime_witness :
    PrimeComponentWitness 6 8547 10 2 13 := by
  have hquot : primeComponentQuotient 10 6 2 = 1001 := by decide
  have hq : Nat.Prime 13 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 13 ∣ 8547)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b10_F6_A8547_from_A231_mul37_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 8547 10 2 := by
  exact Or.inr (Or.inr ⟨13, concrete_lifted_b10_F6_A8547_from_A231_mul37_p2_prime_witness⟩)

theorem concrete_lifted_b10_F6_A8547_from_A231_mul37_p3_prime_witness :
    PrimeComponentWitness 6 8547 10 3 13 := by
  have hquot : primeComponentQuotient 10 6 3 = 10101 := by decide
  have hq : Nat.Prime 13 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 13 ∣ 8547)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b10_F6_A8547_from_A231_mul37_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 8547 10 3 := by
  exact Or.inr (Or.inr ⟨13, concrete_lifted_b10_F6_A8547_from_A231_mul37_p3_prime_witness⟩)

theorem concrete_generated_b12_F12_A7_factorization_support_cases
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

theorem concrete_generated_b12_F12_A7_p2_prime_witness :
    PrimeComponentWitness 12 7 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 7)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A7_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 7 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A7_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A7_p3_prime_witness :
    PrimeComponentWitness 12 7 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 7)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A7_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 7 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A7_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A7 :
    EmittedCertificateTable 12 7 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A7_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A7_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A7_p3_prime_witness

theorem orderOf_b12_mod1273728635465_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 1273728635465)) = 12 := by
  let hcop : Nat.Coprime 12 1273728635465 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 1273728635465)ˣ) :
          ZMod 1273728635465) ^ 12) =
        (1 : ZMod 1273728635465)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 7 8916100448255 1273728635465 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A7

theorem concrete_generated_b12_F12_A1045_factorization_support_cases
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

theorem concrete_generated_b12_F12_A1045_p2_prime_witness :
    PrimeComponentWitness 12 1045 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 1045)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1045_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1045 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A1045_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A1045_p3_prime_witness :
    PrimeComponentWitness 12 1045 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 1045)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1045_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1045 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A1045_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A1045 :
    EmittedCertificateTable 12 1045 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A1045_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1045_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1045_p3_prime_witness

theorem orderOf_b12_mod8532153539_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 8532153539)) = 12 := by
  let hcop : Nat.Coprime 12 8532153539 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 8532153539)ˣ) :
          ZMod 8532153539) ^ 12) =
        (1 : ZMod 8532153539)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 1045 8916100448255 8532153539 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A1045

theorem concrete_generated_b12_F12_A14287_factorization_support_cases
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

theorem concrete_generated_b12_F12_A14287_p2_prime_witness :
    PrimeComponentWitness 12 14287 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 14287)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A14287_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 14287 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A14287_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A14287_p3_prime_witness :
    PrimeComponentWitness 12 14287 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 14287)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A14287_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 14287 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A14287_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A14287 :
    EmittedCertificateTable 12 14287 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A14287_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A14287_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A14287_p3_prime_witness

theorem orderOf_b12_mod624070865_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 624070865)) = 12 := by
  let hcop : Nat.Coprime 12 624070865 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 624070865)ˣ) :
          ZMod 624070865) ^ 12) =
        (1 : ZMod 624070865)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 14287 8916100448255 624070865 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A14287

theorem concrete_generated_b12_F12_A95095_factorization_support_cases
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

theorem concrete_generated_b12_F12_A95095_p2_prime_witness :
    PrimeComponentWitness 12 95095 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 95095)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A95095_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 95095 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A95095_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b12_F12_A95095_p3_prime_witness :
    PrimeComponentWitness 12 95095 12 3 157 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 157 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 157 ∣ 95095)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A95095_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 95095 12 3 := by
  exact Or.inr (Or.inr ⟨157, concrete_generated_b12_F12_A95095_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A95095 :
    EmittedCertificateTable 12 95095 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A95095_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A95095_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A95095_p3_prime_witness

theorem orderOf_b12_mod93759929_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 93759929)) = 12 := by
  let hcop : Nat.Coprime 12 93759929 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 93759929)ˣ) :
          ZMod 93759929) ^ 12) =
        (1 : ZMod 93759929)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 95095 8916100448255 93759929 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A95095

theorem concrete_generated_b12_F12_A271453_factorization_support_cases
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

theorem concrete_generated_b12_F12_A271453_p2_prime_witness :
    PrimeComponentWitness 12 271453 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 271453)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A271453_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 271453 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A271453_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A271453_p3_prime_witness :
    PrimeComponentWitness 12 271453 12 3 20593 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 271453)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A271453_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 271453 12 3 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A271453_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A271453 :
    EmittedCertificateTable 12 271453 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A271453_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A271453_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A271453_p3_prime_witness

theorem orderOf_b12_mod32845835_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 32845835)) = 12 := by
  let hcop : Nat.Coprime 12 32845835 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 32845835)ˣ) :
          ZMod 32845835) ^ 12) =
        (1 : ZMod 32845835)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 271453 8916100448255 32845835 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A271453

theorem concrete_generated_b12_F12_A6661039_factorization_support_cases
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

theorem concrete_generated_b12_F12_A6661039_p2_prime_witness :
    PrimeComponentWitness 12 6661039 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 6661039)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A6661039_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 6661039 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A6661039_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A6661039_p3_prime_witness :
    PrimeComponentWitness 12 6661039 12 3 20593 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 6661039)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A6661039_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 6661039 12 3 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A6661039_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A6661039 :
    EmittedCertificateTable 12 6661039 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A6661039_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A6661039_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A6661039_p3_prime_witness

theorem orderOf_b12_mod1338545_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 1338545)) = 12 := by
  let hcop : Nat.Coprime 12 1338545 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 1338545)ˣ) :
          ZMod 1338545) ^ 12) =
        (1 : ZMod 1338545)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 6661039 8916100448255 1338545 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A6661039

theorem concrete_generated_b12_F12_A9369815_factorization_support_cases
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

theorem concrete_generated_b12_F12_A9369815_p2_prime_witness :
    PrimeComponentWitness 12 9369815 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 9369815)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A9369815_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 9369815 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A9369815_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A9369815_p3_prime_witness :
    PrimeComponentWitness 12 9369815 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 9369815)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A9369815_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 9369815 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A9369815_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A9369815 :
    EmittedCertificateTable 12 9369815 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A9369815_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A9369815_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A9369815_p3_prime_witness

theorem orderOf_b12_mod951577_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 951577)) = 12 := by
  let hcop : Nat.Coprime 12 951577 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 951577)ˣ) : ZMod 951577) ^ 12) =
        (1 : ZMod 951577)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 9369815 8916100448255 951577 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A9369815

end Erdos249257
