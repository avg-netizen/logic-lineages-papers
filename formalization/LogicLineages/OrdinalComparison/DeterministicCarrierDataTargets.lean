module
public import LogicLineages.OrdinalComparison.DeterministicCarrierDataDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DeterministicCarrierData.Targets
open ScalarAnnotationData ScalarCarrierAccounting OriginalDomain SourceFreeOccurrences
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ExactSaturation : Prop := ∀ (Γ : List Ty) (r : Nat)
    (t : OriginalTerm Γ (Ty.curriedGround (r+1)))
    (u : OrdinalVector Γ (Ty.curriedGround (r+1)).level),
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some u →
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (UnaryCarrier.saturate r t) =
      some (saturateVector r u) ∧
  ∀ ν, denote ν (saturateVector r u 1) = denote ν (u (UnaryCarrier.headIndex r))

/-- Stored assignment suffices: no head-tree, nonfinite-head, or new source
existence premise is required. Actual positive grade is derived from source. -/
def ExactCarrierData : Prop := ∀ (k : Nat) (Γ : List Ty)
    (op : Operator (Ty.curriedGround (k+1) :: Γ)),
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy op.source = some op.vector →
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (carrierData op).source =
      some (carrierData op).vector ∧
  (∀ x : Variable (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ) .ground,
    (⟨Ty.ground,x⟩ : PackedVariable _) ∉ SourceFreeOccurrences.freeOccurrences (carrierData op).source) ∧
  unitValue (carrierData op).head = unitValue op.head ∧
  ∀ (ρ : Variable (Ty.curriedGround (k+1) :: Γ) .ground → Nat)
    (μ : Variable (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ) .ground → Nat),
    expressionValue (UnitObservation.substitution μ) (carrierData op).head =
      expressionValue (UnitObservation.substitution ρ) op.head

def ExactCarrierList : Prop := ∀ (k : Nat) (Γ : List Ty)
    (ops : List (Operator (Ty.curriedGround (k+1) :: Γ))),
  (∀ op ∈ ops, AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy op.source = some op.vector) →
  (carrierList ops).length = ops.length ∧
  (carrierList ops).map (fun op => unitValue op.head) = ops.map (fun op => unitValue op.head) ∧
  ∀ op ∈ carrierList ops,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy op.source = some op.vector ∧
    ∀ x : Variable (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ) .ground,
      (⟨Ty.ground,x⟩ : PackedVariable _) ∉ SourceFreeOccurrences.freeOccurrences op.source
end LogicLineages.OrdinalComparison.Source.DeterministicCarrierData.Targets
