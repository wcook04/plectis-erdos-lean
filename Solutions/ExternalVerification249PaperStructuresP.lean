/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.TotientMahlerDefect

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.TotientMahlerDefect`.
-/

open Module
open Matrix

namespace Erdos249257.ExternalVerification249PaperStructuresP

structure SeparatedMinorCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ℕ → ℚ) where
  rowIndex : ι → ℕ
  det_ne_zero :
    Matrix.det (fun i j : ι => family j (rowIndex i)) ≠ 0

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

/-- The copied structure `SeparatedMinorCertificate` and its source `Erdos249257.SeparatedMinorCertificate` carry the same
fields, so each converts into the other field by field. -/
def SeparatedMinorCertificate_transport_toSrc {ι : Type*} [Fintype ι] [DecidableEq ι] {family : ι → ℕ → ℚ} (x : @SeparatedMinorCertificate ι inferInstance inferInstance family) :
    @Erdos249257.SeparatedMinorCertificate ι inferInstance inferInstance family :=
  ⟨x.rowIndex, x.det_ne_zero⟩

/-- The inverse of `SeparatedMinorCertificate_transport_toSrc`. -/
def SeparatedMinorCertificate_transport_ofSrc {ι : Type*} [Fintype ι] [DecidableEq ι] {family : ι → ℕ → ℚ} (x : @Erdos249257.SeparatedMinorCertificate ι inferInstance inferInstance family) :
    @SeparatedMinorCertificate ι inferInstance inferInstance family :=
  ⟨x.rowIndex, x.det_ne_zero⟩

@[simp] theorem SeparatedMinorCertificate_transport_toSrc_rowIndex {ι : Type*} [Fintype ι] [DecidableEq ι] {family : ι → ℕ → ℚ}
    (x : @SeparatedMinorCertificate ι inferInstance inferInstance family) :
    (SeparatedMinorCertificate_transport_toSrc x).rowIndex = x.rowIndex := rfl

@[simp] theorem SeparatedMinorCertificate_transport_ofSrc_rowIndex {ι : Type*} [Fintype ι] [DecidableEq ι] {family : ι → ℕ → ℚ}
    (x : @Erdos249257.SeparatedMinorCertificate ι inferInstance inferInstance family) :
    (SeparatedMinorCertificate_transport_ofSrc x).rowIndex = x.rowIndex := rfl

theorem linearIndependent_of_separatedMinorCertificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] (family : ι → ℕ → ℚ)
    (cert : SeparatedMinorCertificate family) :
    LinearIndependent ℚ family := @Erdos249257.linearIndependent_of_separatedMinorCertificate ι inferInstance inferInstance family (SeparatedMinorCertificate_transport_toSrc cert)

end Erdos249257.ExternalVerification249PaperStructuresP
