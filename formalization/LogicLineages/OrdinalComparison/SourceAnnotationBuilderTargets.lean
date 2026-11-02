module
public import LogicLineages.OrdinalComparison.SourceAnnotationBuilderDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationBuilder.Targets
open ScalarAnnotationData AdditiveHeadTree

def ExactRepeat : Prop := ∀ (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (n : Nat) (d : Tree k Γ F),
  erase (repeatTree n d) = AdmissibleAssignment.repeated OrdinalSyntax.defaultPolicy .scalarRepeat n (erase d) ∧
    (0 < n → Valid d → Valid (repeatTree n d))

/-- Every unchanged source grammar member is accepted, including arbitrary
opaque F-free internals and functional-result ground lambdas. No Valid,
assignment-success, annotation or child-construction premise is supplied. -/
def ActualSourceData : Prop := ∀ (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (n : Nat) (e : TrackedSource.Expr k Γ F n),
  ∃ (u : OrdinalVector Γ (Ty.curriedGround n).level) (d : Tree k Γ F),
    build e = some (u,d) ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u ∧
    erase d = u 0 ∧ Valid d

/-- Exact ORDERED selected-head trace, including duplicates, plus actual
stored source/vector and head-tree certificates for every emitted record. -/
def ExactSelectedOperators : Prop := ∀ (k : Nat) (Γ : List Ty)
    (d : Tree k (Ty.curriedGround (k+1) :: Γ) .here), Valid d →
  (selectedOperators d).map Operator.head = selectedHeads (erase d) ∧
  ∀ op ∈ selectedOperators d,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy op.source = some op.vector ∧
    HeadTree (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) op.head
end LogicLineages.OrdinalComparison.Source.SourceAnnotationBuilder.Targets
