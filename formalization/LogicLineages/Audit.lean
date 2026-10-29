module

public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command

/-! Kernel axiom-closure checks for all theorem declarations in a namespace.
This command checks proof dependencies; source-statement correspondence is
enforced separately by the fixed comparator modules. -/

public meta section

open Lean Elab Command

elab "#audit_namespace " ns:ident : command => do
  let namespaceName := ns.getId
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if namespaceName.isPrefixOf name then
      if let .thmInfo _ := info then
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "{name}: forbidden axiom dependency {ax}"
        logInfo m!"AXIOMS {name}: {axioms.toList}"
        count := count + 1
  if count == 0 then
    throwError "No theorem declarations found in namespace {namespaceName}"
  logInfo m!"AXIOM_AUDIT_PASS {namespaceName}: {count} theorems"
