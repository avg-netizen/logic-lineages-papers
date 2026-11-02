module
public import LogicLineages.OrdinalComparison.ScalarAnnotationDataDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarAnnotationData.Targets
open ActiveScalarAnnotation AdditiveHeadTree

def ExactCertificates : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (d : Tree k Γ F), Valid d →
  ScalarTrees F (erase d) ∧ Annotated OrdinalSyntax.defaultPolicy F (erase d)

def ExactGroundClosure : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (d : Tree k (.ground :: Γ) (.there F)),
  erase (closeTree d) = ordinalHeadClosure (erase d) ∧ (Valid d → Valid (closeTree d))

/-- Both deterministic producer success and actual partial success are derived.
The output is certified data for the derivative scalar, not an asserted source. -/
def ExactGroundPartial : Prop := ∀ (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (d : Tree k (.ground :: Γ) (.there F)),
  Valid d → ∃ (out : Tree k Γ F) (v : OrdinalPartialVector Γ .ground),
    groundPartial d = some out ∧ AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (erase d) = some v ∧
    erase out = v 0 ∧ Valid out
end LogicLineages.OrdinalComparison.Source.ScalarAnnotationData.Targets
