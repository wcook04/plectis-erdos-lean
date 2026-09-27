import Lean

/-!
Source-overlay type equivalence. Run only in an environment importing both the
original and freshly built overlay roots. This is additional evidence; it does
not replace the native staged type/axiom audit.

The caller supplies one complete, injective overlay -> original constant map
from independently extracted declaration graphs. An unlisted constant declared
in an overlay project module is an error, including private/generated names.
-/

namespace P2MOverlayAudit

open Lean Meta

structure Pair where
  original : Name
  overlay : Name
  deriving Inhabited, Repr

def declaringModule? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

def isOverlayConstant (env : Environment) (overlayModulePrefix n : Name) : Bool :=
  overlayModulePrefix.isPrefixOf n ||
  (privateToUserName? n).any (overlayModulePrefix.isPrefixOf ·) ||
  (declaringModule? env n).any (overlayModulePrefix.isPrefixOf ·)

def prepareMap (env : Environment) (pairs : Array Pair)
    (overlayModulePrefix : Name) : Except String (Std.HashMap Name Name) := Id.run do
  let mut forward : Std.HashMap Name Name := {}
  let mut reverse : Std.HashMap Name Name := {}
  for pair in pairs do
    if pair.original == pair.overlay then
      return .error s!"identity pair {pair.original} is not an overlay mapping"
    if forward.contains pair.overlay || reverse.contains pair.original then
      return .error s!"constant map is not injective at {pair.overlay} -> {pair.original}"
    if (env.find? pair.original).isNone || (env.find? pair.overlay).isNone then
      return .error s!"mapped constant is missing: {pair.overlay} -> {pair.original}"
    if !isOverlayConstant env overlayModulePrefix pair.overlay then
      return .error s!"mapped overlay constant has wrong declaring module: {pair.overlay}"
    if isOverlayConstant env overlayModulePrefix pair.original then
      return .error s!"original constant belongs to overlay module: {pair.original}"
    forward := forward.insert pair.overlay pair.original
    reverse := reverse.insert pair.original pair.overlay
  return .ok forward

def mapName (env : Environment) (overlayModulePrefix : Name)
    (mapping : Std.HashMap Name Name) (n : Name) : Except String Name :=
  match mapping[n]? with
  | some original => .ok original
  | none =>
    if isOverlayConstant env overlayModulePrefix n then
      .error s!"unmapped overlay project constant: {n}"
    else .ok n

partial def remapExpr (env : Environment) (overlayModulePrefix : Name)
    (mapping : Std.HashMap Name Name) : Expr → Except String Expr
  | .bvar i => .ok (.bvar i)
  | .fvar _ => .error "free variable in elaborated declaration type"
  | .mvar _ => .error "metavariable in elaborated declaration type"
  | .sort level => .ok (.sort level)
  | .const n levels => do
      let n' ← mapName env overlayModulePrefix mapping n
      return .const n' levels
  | .app fn arg => do
      let fn' ← remapExpr env overlayModulePrefix mapping fn
      let arg' ← remapExpr env overlayModulePrefix mapping arg
      return .app fn' arg'
  | .lam n ty body info => do
      let ty' ← remapExpr env overlayModulePrefix mapping ty
      let body' ← remapExpr env overlayModulePrefix mapping body
      return .lam n ty' body' info
  | .forallE n ty body info => do
      let ty' ← remapExpr env overlayModulePrefix mapping ty
      let body' ← remapExpr env overlayModulePrefix mapping body
      return .forallE n ty' body' info
  | .letE n ty val body nondep => do
      let ty' ← remapExpr env overlayModulePrefix mapping ty
      let val' ← remapExpr env overlayModulePrefix mapping val
      let body' ← remapExpr env overlayModulePrefix mapping body
      return .letE n ty' val' body' nondep
  | .lit literal => .ok (.lit literal)
  | .mdata data expr => do
      let expr' ← remapExpr env overlayModulePrefix mapping expr
      return .mdata data expr'
  | .proj structName idx expr => do
      let structName' ← mapName env overlayModulePrefix mapping structName
      let expr' ← remapExpr env overlayModulePrefix mapping expr
      return .proj structName' idx expr'

def checkTypePair (env : Environment) (overlayModulePrefix : Name)
    (mapping : Std.HashMap Name Name) (pair : Pair) : Except String Unit := do
  let some original := env.find? pair.original
    | .error s!"missing original declaration {pair.original}"
  let some overlay := env.find? pair.overlay
    | .error s!"missing overlay declaration {pair.overlay}"
  let transformed ← remapExpr env overlayModulePrefix mapping overlay.type
  if original.type == transformed then .ok ()
  else .error s!"elaborated type mismatch: {pair.overlay} -> {pair.original}"

def checkTypes (env : Environment) (overlayModulePrefix : Name)
    (pairs : Array Pair) : Except String Unit := do
  if pairs.isEmpty then .error "empty constant map"
  else
    let mapping ← prepareMap env pairs overlayModulePrefix
    for pair in pairs do
      checkTypePair env overlayModulePrefix mapping pair

end P2MOverlayAudit
