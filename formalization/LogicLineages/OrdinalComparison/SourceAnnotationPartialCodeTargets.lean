module
public import LogicLineages.OrdinalComparison.SourceAnnotationPartialCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationPartialCode.Targets
open ScalarAnnotationData SourceAnnotationCode

def ExactPartialCode : Prop := ∀ (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (d : Tree k (.ground :: Γ) (.there F)),
  groundPartialCode (SourceTypedPorts.variableIndex (show Variable (.ground :: Γ) (Ty.curriedGround (k+1)) from .there F)) (code d) =
    (groundPartial d).map code

def PrimitiveRecursive : Prop := Primrec₂ groundPartialCode

/-- Success is derived only for independently Valid data. The generic exact
Option theorem above includes failure without strengthening its domain. -/
def ValidActualPartial : Prop := ∀ (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (d : Tree k (.ground :: Γ) (.there F)), Valid d →
  ∃ (out : Tree k Γ F) (v : OrdinalPartialVector Γ .ground),
    groundPartialCode (SourceTypedPorts.variableIndex (show Variable (.ground :: Γ) (Ty.curriedGround (k+1)) from .there F)) (code d) = some (code out) ∧
    groundPartial d = some out ∧
    AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (erase d) = some v ∧
    eraseCode (SourceTypedPorts.variableIndex F) (code out) = OrdinalSyntax.typedCode (v 0) ∧ Valid out
end LogicLineages.OrdinalComparison.Source.SourceAnnotationPartialCode.Targets
