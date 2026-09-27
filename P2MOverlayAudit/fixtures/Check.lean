import P2MOverlayAudit.ExprEquivalence
import P2MOverlayAudit.fixtures.OriginalFixture
import P2MOverlayAudit.fixtures.P2MFixture

open Lean P2MOverlayAudit

run_meta do
  let env ← getEnv
  let good : Array Pair := #[
    ⟨`Example.Carrier, `P2MFixture.Example.Carrier⟩,
    ⟨`Example.id, `P2MFixture.Example.id⟩]
  match checkTypes env `P2MOverlayAudit.fixtures.P2MFixture good with
  | .ok () => pure ()
  | .error e => throwError "positive mapping rejected: {e}"
  let missing : Array Pair := #[⟨`Example.id, `P2MFixture.Example.id⟩]
  match checkTypes env `P2MOverlayAudit.fixtures.P2MFixture missing with
  | .error e =>
      unless e.startsWith "unmapped overlay project constant" do
        throwError "wrong missing-constant failure: {e}"
  | .ok () => throwError "incomplete constant map accepted"
  let duplicate : Array Pair := #[good[0]!, good[0]!]
  match checkTypes env `P2MOverlayAudit.fixtures.P2MFixture duplicate with
  | .error e =>
      unless e.startsWith "constant map is not injective" do
        throwError "wrong duplicate failure: {e}"
  | .ok () => throwError "noninjective constant map accepted"
  let .ok mapping := prepareMap env good `P2MOverlayAudit.fixtures.P2MFixture
    | throwError "valid mapping rejected"
  let typeExpr := Expr.forallE `x (.const `P2MFixture.Example.Carrier [])
      (.sort (.succ .zero)) .default
  let expected := Expr.forallE `x (.const `Example.Carrier [])
      (.sort (.succ .zero)) .default
  match remapExpr env `P2MOverlayAudit.fixtures.P2MFixture mapping typeExpr with
  | .ok actual =>
      unless actual == expected do
        throwError "binder/universe-preserving remap failed"
  | .error e => throwError "positive remap rejected: {e}"
  let altered := Expr.forallE `x (.const `P2MFixture.Example.Carrier [])
      (.sort .zero) .default
  match remapExpr env `P2MOverlayAudit.fixtures.P2MFixture mapping altered with
  | .ok actual =>
      if actual == expected then throwError "universe difference was erased"
  | .error e => throwError "altered expression unexpectedly rejected: {e}"
