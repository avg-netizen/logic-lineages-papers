module
public import LogicLineages.StandardControlCurrent.PolicyAssignmentDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyAssignmentTargets
open OrdinalComparison Source Source.AdmissibleSum Source.SyntaxCode Source.OrdinalSyntax

def LiteralCalibration : Prop := ∀ (p : Policy) (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
  PolicyAssignment.assignmentCode p (Γ.map typeCode) (encodeTerm t) =
    (AdmissibleAssignment.assignment p t).map vectorCode

def SourceExact : Prop := ∀ (p : Policy) (Γ : List Ty) (n : Nat) (v : List Nat),
  PolicyAssignment.assignmentCode p (Γ.map typeCode) n = some v ↔
    ∃ (τ : Ty) (t : OriginalTerm Γ τ) (w : OrdinalVector Γ τ.level),
      encodeTerm t=n ∧ AdmissibleAssignment.assignment p t=some w ∧ vectorCode w=v

def TypedSuccess : Prop := ∀ (p : Policy) (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
  ∃ w : OrdinalVector Γ τ.level,
    AdmissibleAssignment.assignment p t=some w ∧
    PolicyAssignment.assignmentCode p (Γ.map typeCode) (encodeTerm t)=some (vectorCode w) ∧
    ∀ j, GeneratedOrdinalGrade Γ j.val (w j)

def Programs : Prop := ∀ p : Policy, PolicyShape.Effective p →
  Computable (fun x : Nat × Nat × Nat => PolicyAssignment.primeCode p x.1 x.2.1 x.2.2) ∧
  Computable (fun x : List Nat × Nat => PolicyAssignment.assignmentCode p x.1 x.2)

def Full : Prop := LiteralCalibration ∧ SourceExact ∧ TypedSuccess ∧ Programs
end LogicLineages.StandardControlCurrent.PolicyAssignmentTargets
