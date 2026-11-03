module
public import LogicLineages.OrdinalComparison.ScalarAnnotationDataDefinitions
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DeterministicCarrierData
open ScalarAnnotationData

/-- Literal actual application to zero, repeated exactly the source arity.
All coordinates are retained; in particular the scalar is never reset. -/
def saturateVector {Γ : List Ty} : (r : Nat) →
    OrdinalVector Γ (Ty.curriedGround (r+1)).level → OrdinalVector Γ 1
  | 0, u => u
  | r+1, u => saturateVector r (AdmissibleAssignment.application
      (σ := .ground) (τ := Ty.curriedGround (r+1)) OrdinalSyntax.defaultPolicy u (fun _ => .one))

/-- Raw data, without eliminated existence proofs or choice. Source zero has
assignment one, so closing uses the actual GroundClosing vector map. -/
def carrierData {k Γ} (op : Operator (Ty.curriedGround (k+1) :: Γ)) :
    Operator (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ) :=
  ⟨0, UnaryCarrier.carrier op.source,
    GroundClosing.vector (UnaryCarrier.groundMap _)
      (saturateVector op.arity (SourceRenaming.renameVector UnaryCarrier.renameTracked op.vector))⟩

def carrierList {k Γ} (ops : List (Operator (Ty.curriedGround (k+1) :: Γ))) :=
  ops.map carrierData
end LogicLineages.OrdinalComparison.Source.DeterministicCarrierData
