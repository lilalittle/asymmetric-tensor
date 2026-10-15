import Lean

/-!
Executable checks for this repository. This module uses Lean's transitive
`collectAxioms`, not a textual search or a warning count. It is verification
infrastructure, not part of the mathematical development.
-/

open Lean Elab Command

namespace ProofAudit

/-- Ordinary Lean logical axioms deliberately permitted by this project.
`Lean.ofReduceBool`, `sorryAx`, and arbitrary custom axioms are not included. -/
def logicalAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

private def names (xs : Array Name) : String :=
  String.intercalate ", " (xs.toList.map toString)

/-- Check the complete transitive dependency set of one named theorem.
The custom axiom list is exact; ordinary logical dependencies may be a subset. -/
def checkTheorem (decl : Name) (expectedCustom : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  match env.find? decl with
  | some (.thmInfo _) => pure ()
  | _ => throwError "PROOF_AUDIT_TARGET: {decl} is missing or is not a theorem"
  let actual ← collectAxioms decl
  if actual.contains `sorryAx then
    throwError "PROOF_AUDIT_INCOMPLETE: {decl} transitively depends on sorryAx"
  let custom := actual.filter fun ax => !logicalAxioms.contains ax
  let unexpected := custom.filter fun ax => !expectedCustom.contains ax
  let missing := expectedCustom.filter fun ax => !custom.contains ax
  unless unexpected.isEmpty && missing.isEmpty do
    throwError "PROOF_AUDIT_AXIOMS: {decl}; unexpected [{names unexpected}]; expected but absent [{names missing}]; actual [{names actual}]"
  logInfo m!"PROOF_AUDIT_OK: {decl}; axioms [{names actual}]"

/-- Check every declaration owned by selected modules, irrespective of namespace.
This includes private and generated declarations. Completeness is checked
transitively, while the inventory check concerns axioms declared by these modules.
The selective theorem check above additionally constrains imported custom axioms. -/
def checkModules (modules : Array Name) (allowedDeclared : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  for mod in modules do
    unless mod == env.mainModule || (env.getModuleIdx? mod).isSome do
      throwError "PROOF_AUDIT_MODULE: module {mod} was not imported"
  let moduleNames := env.header.moduleNames
  let mut checked := 0
  let mut declared : Array Name := #[]
  for (decl, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? decl with
      | some idx => moduleNames[idx.toNat]!
      | none => env.mainModule
    if modules.contains owner then
      checked := checked + 1
      let axioms ← collectAxioms decl
      if axioms.contains `sorryAx then
        throwError "PROOF_AUDIT_INCOMPLETE: {decl} in {owner} transitively depends on sorryAx"
      if info matches .axiomInfo _ then
        declared := declared.push decl
        unless allowedDeclared.contains decl do
          throwError "PROOF_AUDIT_INVENTORY: unexpected first-party axiom {decl} in {owner}"
  unless checked > 0 do
    throwError "PROOF_AUDIT_EMPTY: no first-party declarations were checked"
  let missing := allowedDeclared.filter fun ax => !declared.contains ax
  unless missing.isEmpty do
    throwError "PROOF_AUDIT_INVENTORY: declared axioms missing [{names missing}]"
  logInfo m!"PROOF_AUDIT_COMPLETE: {checked} declarations in [{names modules}]; declared axioms [{names (declared.qsort Name.lt)}]; no transitive sorryAx"

/-- Production root and all of its imported submodules. -/
def checkRoot (root : Name) (allowedDeclared : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let modules := env.header.moduleNames.filter fun mod => root.isPrefixOf mod
  unless modules.contains root do
    throwError "PROOF_AUDIT_MODULE: production root {root} was not imported"
  checkModules modules allowedDeclared

elab "#audit_theorem " decl:ident " custom " "[" axs:ident,* "]" : command => do
  checkTheorem decl.getId (axs.getElems.map (·.getId))

elab "#audit_root " root:ident " declared " "[" axs:ident,* "]" : command => do
  checkRoot root.getId (axs.getElems.map (·.getId))

-- Used by the mutation regressions; production checks imported modules above.
elab "#audit_current_module" " declared " "[" axs:ident,* "]" : command => do
  checkModules #[(← getEnv).mainModule] (axs.getElems.map (·.getId))

end ProofAudit
