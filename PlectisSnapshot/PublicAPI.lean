/-
SPDX-FileCopyrightText: 2026 Will Cook
SPDX-License-Identifier: Apache-2.0

Generated public API adapter for the Plectis Lean snapshot.
It exposes stable metadata strings for consumers while the private frontier moves.
-/
import Erdos257PeriodNoncollapse
import Erdos257PeriodNoncollapse.CertificateKernel

namespace PlectisSnapshot

def publicApiContractSchema : String := "plectis_lean_public_api_contract_v0"
def publicApiContractVersion : String := "0.1.0-pre"
def sourceSnapshotSHA256 : String := "33e418aadb7a64865a828595697c414acb8a2c09a188cdbe2a78a5c077c98a09"
def sourceFileCount : Nat := 202
def plectisConsumptionMode : String := "pointer_only_until_public_tag"

def exposedDeclarationFamilies : List String :=
[
  "certificate_kernel",
  "generated_certificate_aggregate",
  "selected_certificate_shards",
  "target_runner_declarations",
  "non_claim_ids",
  "receipt_schema_ids",
]

def nonClaimIds : List String :=
[
  "not_erdos_257_solution",
  "not_erdos_249_solution",
  "not_publication_authority",
  "not_private_root_equivalence",
  "not_provider_proof_authority",
  "not_hidden_proof_body_authority",
]

end PlectisSnapshot
