/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.GenericTailOrbitRigidity`.
-/

open Filter
open Set

namespace Erdos249257.ExternalVerification257PaperStructuresCK

noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)

/-- States prop:local-void from the long record for Erdős problem #257. Transported from
Erdos249257.affineBinaryOrbit_sub in the substantive development, whose statement was
refereed against the paper in the coverage ledger. -/
theorem affineBinaryOrbit_sub (a : ℕ → ℤ) (u0 v0 : ℤ) :
    ∀ L : ℕ,
      affineBinaryOrbit a u0 L - affineBinaryOrbit a v0 L =
        (2 : ℤ) ^ L * (u0 - v0) := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresCK
