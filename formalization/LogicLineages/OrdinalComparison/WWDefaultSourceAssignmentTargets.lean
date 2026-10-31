module
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DefaultSourceAssignment.Targets
open SyntaxCode OrdinalSyntax

def AssignmentCorrect : Prop := ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
  assignmentCode (Γ.map typeCode) (encodeTerm t) =
    (AdmissibleAssignment.assignment defaultPolicy t).map vectorCode

def AssignmentChecked : Prop := ∀ Γ n v, assignmentCode Γ n = some v → ∃ τ, check Γ n = some τ

/-- Full raw-input correspondence, not only correctness on already-typed inputs. -/
def AssignmentSourceExact : Prop := ∀ (Γ : List Ty) n v,
  assignmentCode (Γ.map typeCode) n = some v ↔
    ∃ (τ : Ty) (t : OriginalTerm Γ τ) (w : OrdinalVector Γ τ.level),
      encodeTerm t = n ∧ AdmissibleAssignment.assignment defaultPolicy t = some w ∧ vectorCode w = v

def AssignmentPrimitiveRecursive : Prop :=
  Primrec (fun p : List Nat×Nat => assignmentCode p.1 p.2)

def AssignmentComputable : Prop :=
  Computable (fun p : List Nat×Nat => assignmentCode p.1 p.2)
end LogicLineages.OrdinalComparison.Source.DefaultSourceAssignment.Targets
