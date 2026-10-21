import AsymmetricTensor
import Lean

/-! Machine-readable transitive dependencies for the current production source.
This log does not update the historical `docs/equation-coverage.json` ledger.
Its accepted six-axiom audit program is archived separately. Build first. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let root := `AsymmetricTensor
  let logical := #[`propext, `Classical.choice, `Quot.sound]
  -- The reviewed v5.7 source declares no custom axioms. Check every owned
  -- declaration, including opaque values and generated structure declarations,
  -- for transitive dependencies beyond the three logical axioms above.
  let permitted : Array Name := #[]
  let mut count := 0
  let mut declared : Array Name := #[]
  for (name, info) in env.constants.toList.mergeSort (fun a b => Name.lt a.1 b.1) do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    unless root.isPrefixOf owner do continue
    count := count + 1
    let axioms := (← collectAxioms name).qsort Name.lt
    let custom := axioms.filter fun a => !logical.contains a
    for ax in custom do
      unless permitted.contains ax do
        throwError "Unreviewed transitive axiom {ax} in {name}"
    if info matches .axiomInfo _ then declared := declared.push name
    let kind := match info with
      | .axiomInfo _ => "axiom"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .defnInfo _ => "definition"
      | _ => "generated"
    let signature ← liftTermElabM do
      return (← Meta.ppExpr info.type).pretty
    let json := Json.mkObj [
      ("name", toJson name.toString), ("module", toJson owner.toString),
      ("kind", toJson kind), ("type", toJson signature),
      ("axioms", toJson (axioms.map Name.toString)),
      ("custom_axioms", toJson (custom.map Name.toString))]
    logInfo m!"EQUATION_AXIOM {json.compress}"
  unless count > 0 do throwError "No production declarations found"
  unless declared.size == permitted.size && permitted.all declared.contains do
    throwError "Changed explicit axiom inventory: {declared}"
  logInfo m!"EQUATION_AXIOM_COUNT {count}"
