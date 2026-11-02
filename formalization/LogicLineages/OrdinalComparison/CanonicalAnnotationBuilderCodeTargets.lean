module
public import LogicLineages.OrdinalComparison.CanonicalAnnotationBuilderCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.CanonicalAnnotationBuilderCode.Targets
open ScalarAnnotationData

def PrimitiveRecursive : Prop :=
  Primrec (fun p : List Nat × Nat × Nat => buildCode p.1 p.2.1 p.2.2)

/-- Raw successful output retains the actual numeric full assignment and
passes genuine result-type and curried-ground arity checks. -/
def RawChecked : Prop := ∀ (Γ : List Nat) (tracked n : Nat) (u : List Nat) (d : Nat),
  buildCode Γ tracked n = some (u,d) →
  ∃ τ arity, SyntaxCode.check Γ n = some τ ∧
    TrackedSourceInspectionCode.arityCode τ = some arity ∧
    DefaultSourceAssignment.assignmentCode Γ n = some u

/-- Every unchanged complete grammar source succeeds, with genuine full
assignment and valid annotation semantics. No equality to the noncanonical
Expr-indexed Builder data is asserted. No supplied success/certificate premise. -/
def ActualSourceBuild : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (n : Nat) (e : TrackedSource.Expr k Γ F n),
  ∃ (u : OrdinalVector Γ (Ty.curriedGround n).level) (d : Tree k Γ F),
    buildCode (Γ.map SyntaxCode.typeCode) (SourceTypedPorts.variableIndex F)
      (SyntaxCode.encodeTerm (TrackedSource.erase e)) = some (OrdinalSyntax.vectorCode u,SourceAnnotationCode.code d) ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u ∧
    erase d = u 0 ∧ Valid d
end LogicLineages.OrdinalComparison.Source.CanonicalAnnotationBuilderCode.Targets
