module

public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command
public meta import Lean.OriginalConstKind

/-! Kernel axiom-closure checks for all theorem declarations in a namespace.
This command checks proof dependencies; source-statement correspondence is
enforced separately by the fixed comparator modules. -/

public meta section

open Lean Elab Command

private inductive AuditRoot where
  | checkedTheorem
  | actualAxiom
  | unknownKind

private def auditNamespace (namespaceName : Name) (aggregate : Bool) : CommandElabM Unit := do
  let env ← getEnv
  -- Preserve SMap.toList's cons-fold order, but allocate only matching audit roots.
  let roots := env.constants.fold (init := ([] : List (Name × AuditRoot))) fun roots name info =>
    if namespaceName.isPrefixOf name then
      match info with
      | .thmInfo _ => (name, .checkedTheorem) :: roots
      | .axiomInfo _ =>
        if !aggregate then roots else
          -- The module system exports theorem statements as opaque kernel axioms.
          -- Check their original kind before interpreting the pinned axiom closure.
          match Lean.getOriginalConstKind? env name with
          | some .thm => (name, .checkedTheorem) :: roots
          | some .axiom => (name, .actualAxiom) :: roots
          | some .defn | some .opaque => roots
          | _ => (name, .unknownKind) :: roots
      | _ => roots
    else
      roots
  let mut count : Nat := 0
  for (name, kind) in roots do
    match kind with
    | .unknownKind => throwError "{name}: cannot identify original audit declaration kind"
    | .actualAxiom =>
      let axioms ← Lean.collectAxioms name
      throwError "{name}: forbidden axiom declaration (reachable axioms {axioms.toList})"
    | .checkedTheorem =>
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "{name}: forbidden axiom dependency {ax}"
      logInfo m!"AXIOMS {name}: {axioms.toList}"
      count := count + 1
  if count == 0 then
    throwError "No theorem declarations found in namespace {namespaceName}"
  logInfo m!"AXIOM_AUDIT_PASS {namespaceName}: {count} theorems"

elab "#audit_namespace " ns:ident : command =>
  auditNamespace ns.getId false

/-- Audit original theorem kinds across the public aggregate's import boundary. -/
elab "#audit_aggregate_namespace " ns:ident : command =>
  auditNamespace ns.getId true
