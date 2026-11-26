module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source GroundEquivalence
open RawSourceDAG RawSourceDAG.Operations

def References : Prop :=
  (∀ (tail ss : List Spec) (s : Spec) (r : Ref ss s),
    referenceIndex (ScopedDAG.Ref.front tail r) = referenceIndex r) ∧
  (∀ (front ss : List Spec) (s : Spec) (r : Ref ss s),
    referenceIndex (ScopedDAG.Ref.back front r) = front.length + referenceIndex r) ∧
  (∀ (ss : List Spec) (s : Spec) (r : Ref ss s),
    referenceIndex (r.map insertSpec) = referenceIndex r) ∧
  (∀ (Γ Θ ps : List Ty) (r : Renaming Γ Θ) (τ : Ty) (x : Variable (ps++Γ) τ),
    variableIndex (ScopedDAG.prefixRename r ps x) = renameIndex ps.length (renamingCode r) (variableIndex x)) ∧
  (∀ (Γ ps : List Ty) (τ : Ty) (x : Variable (ps++Γ) τ),
    variableIndex (insertGround Γ ps x) = insertIndex ps.length (variableIndex x))

def Append : Prop :=
  (∀ (Γ : List Ty) (ss tt : List Spec) (a : DAG Γ ss) (b : DAG Γ tt),
    encodeGraph (ScopedDAG.append a b) = appendTable (encodeGraph a) (encodeGraph b)) ∧
  ∀ (a b : List Node), (appendTable a b).length = a.length+b.length

def Rename : Prop :=
  (∀ (Γ Θ : List Ty) (r : Renaming Γ Θ), (renamingCode r).length = Γ.length) ∧
  (∀ (Γ Θ : List Ty) (ss : List Spec) (r : Renaming Γ Θ) (g : DAG Γ ss),
    encodeGraph (ScopedDAG.rename r g) = renameTable (renamingCode r) (encodeGraph g)) ∧
  (∀ (Γ Θ : List Ty) (τ : Ty) (r : Renaming Γ Θ) (d : Input Γ τ),
    encode ⟨Θ,τ,ScopedDAG.renameInput r d⟩ =
      renameCode (Θ.map SyntaxCode.typeCode) (renamingCode r) (encode ⟨Γ,τ,d⟩)) ∧
  ∀ (ρ : List Nat) (as : List Node), (renameTable ρ as).length = as.length

def Insert : Prop :=
  (∀ (Γ : List Ty) (ss : List Spec) (g : DAG Γ ss),
    encodeGraph g.insert = insertTable (encodeGraph g)) ∧
  ∀ as : List Node, (insertTable as).length = as.length

/-- Computation of the literal structural routines on every raw input, not a checked wrapper. -/
def Primitive : Prop :=
  Primrec (fun p : List Node × List Node => appendTable p.1 p.2) ∧
  Primrec (fun p : List Nat × List Node => renameTable p.1 p.2) ∧
  Primrec insertTable ∧
  Primrec (fun p : List Nat × List Nat × Code => renameCode p.1 p.2.1 p.2.2)
end LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsTargets
