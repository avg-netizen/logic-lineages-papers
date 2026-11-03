module
public import LogicLineages.OrdinalComparison.ActiveScalarAnnotationDefinitions
public import LogicLineages.OrdinalComparison.WWUnaryCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedHeadCarrier
open ActiveScalarAnnotation OriginalDomain

/-- A literal collapse occurrence reached in a tracked-active scalar branch.
The root collapse must actually contain the tracked name. Descent is through
scalar addition or collapse tails only, never into positive heads. Inactive
opaque pieces cannot generate selections. Occurrences are not collected or
quotiented, and this relation asserts no multiplicity accounting. -/
inductive Selected {k Γ} (F : Variable Γ (Ty.curriedGround (k+1))) :
    OrdinalExpression Γ → OrdinalExpression Γ → Prop where
  | here {h t} (active : Active F (.collapse h t)) : Selected F (.collapse h t) h
  | addLeft {a b h} (selected : Selected F a h) : Selected F (.add a b) h
  | addRight {a b h} (selected : Selected F b h) : Selected F (.add a b) h
  | tail {g t h} (selected : Selected F t h) : Selected F (.collapse g t) h

/-- An actual original operator, its actual full vector, literal fresh-name
saturation, and literal ground-closed carrier. The same common unit observation
is used on all functional names, including the fresh tracked name. -/
def HasActualCarrier {Γ : List Ty} {k : Nat}
    (h : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) : Prop :=
  ∃ (r : Nat)
    (t : OriginalTerm (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (r+1)))
    (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (r+1)).level)
    (w v : OrdinalVector (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ) 1),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some u ∧
    u (UnaryCarrier.headIndex r) = h ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy
      (UnaryCarrier.saturate r (t.rename UnaryCarrier.renameTracked)) = some w ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (UnaryCarrier.carrier t) = some v ∧
    v = GroundClosing.vector (UnaryCarrier.groundMap _) w ∧
    v 0 = GroundClosing.expression (UnaryCarrier.groundMap _) (w 0) ∧
    (∀ x : Variable (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ) .ground,
      (⟨Ty.ground,x⟩ : SourceFreeOccurrences.PackedVariable _) ∉
        SourceFreeOccurrences.freeOccurrences (UnaryCarrier.carrier t)) ∧
    ∀ (ρ : Variable (Ty.curriedGround (k+1) :: Γ) .ground → Nat)
      (μ : Variable (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ) .ground → Nat),
      expressionValue (UnitObservation.substitution μ) (v 1) =
        expressionValue (UnitObservation.substitution ρ) h
end LogicLineages.OrdinalComparison.Source.SelectedHeadCarrier
