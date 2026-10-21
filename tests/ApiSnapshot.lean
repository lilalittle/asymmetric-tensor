import AsymmetricTensor
import Lean
open Lean Elab Command

/-!
Migration aid used by `scripts/check_public_api.py`. Compare fully elaborated
public types, preserving binder names/kinds, universes, and constant references.
Only generated hygiene scopes on binders and elaborator metadata are removed.
Every declaration in the public namespace is compared, including structure types,
constructors, recursors, projections and derived/explicit instances. Declaration
kinds are compared too; this does not compare compiled implementation bodies.
-/

private partial def normalizeBinders : Expr → Expr
  | .forallE n t b bi => .forallE n.eraseMacroScopes (normalizeBinders t) (normalizeBinders b) bi
  | .lam n t b bi => .lam n.eraseMacroScopes (normalizeBinders t) (normalizeBinders b) bi
  | .letE n t v b nd => .letE n.eraseMacroScopes (normalizeBinders t)
      (normalizeBinders v) (normalizeBinders b) nd
  | .app f a => .app (normalizeBinders f) (normalizeBinders a)
  | .mdata _ b => normalizeBinders b
  | .proj s i b => .proj s i (normalizeBinders b)
  | e => e
elab "#public_snapshot" : command => do
  let env ← getEnv
  for (name, info) in env.constants.toList.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    if (`AsymmetricTensor).isPrefixOf name then
      let kind := match info with
        | .axiomInfo _ => "axiom"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .defnInfo _ => "definition"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .quotInfo _ => "quotient"
      let ty := (reprStr (normalizeBinders info.type)).replace "\n" "\\n"
      logInfo m!"API|{name}|{kind}|{reprStr info.levelParams}|{ty}"
#public_snapshot
