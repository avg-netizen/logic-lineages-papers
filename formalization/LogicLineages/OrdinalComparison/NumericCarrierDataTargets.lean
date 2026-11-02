module
public import LogicLineages.OrdinalComparison.NumericCarrierDataDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericCarrierData.Targets
open ScalarAnnotationData ScalarCarrierAccounting

def ExactCarrierCode : Prop := ∀ (k : Nat) (Γ : List Ty)
    (op : Operator (Ty.curriedGround (k+1)::Γ)),
  carrierCode ((Ty.curriedGround (k+1)::Γ).map SyntaxCode.typeCode)
    (SourceAnnotationCode.operatorCode op) =
      SourceAnnotationCode.operatorCode (DeterministicCarrierData.carrierData op)

def PrimitiveRecursiveAlgorithms : Prop := Primrec freshOrdinal ∧ Primrec freshVector ∧
  Primrec₂ saturateSource ∧ Primrec₂ saturateVector ∧ Primrec₂ carrierCode

/-- Actual source assignment discharges the semantic hypotheses; the preceding
literal calibration requires no validity of the stored raw vector. -/
def ActualCarrierRecord : Prop := ∀ (k : Nat) (Γ : List Ty)
    (op : Operator (Ty.curriedGround (k+1)::Γ)),
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy op.source = some op.vector →
  let out := carrierCode ((Ty.curriedGround (k+1)::Γ).map SyntaxCode.typeCode)
    (SourceAnnotationCode.operatorCode op)
  DefaultSourceAssignment.assignmentCode
    ((Ty.curriedGround (k+1)::Ty.curriedGround (k+1)::Γ).map SyntaxCode.typeCode)
    (SourceAnnotationCode.operatorSource out) = some (SourceAnnotationCode.operatorVector out) ∧
  (∀ x : Variable (Ty.curriedGround (k+1)::Ty.curriedGround (k+1)::Γ) .ground,
    (⟨Ty.ground,x⟩ : SourceFreeOccurrences.PackedVariable _) ∉
      SourceFreeOccurrences.freeOccurrences (DeterministicCarrierData.carrierData op).source) ∧
  unitValue (DeterministicCarrierData.carrierData op).head = unitValue op.head ∧
  ∀ (ρ : Variable (Ty.curriedGround (k+1)::Γ) .ground → Nat)
    (μ : Variable (Ty.curriedGround (k+1)::Ty.curriedGround (k+1)::Γ) .ground → Nat),
    OriginalDomain.expressionValue (UnitObservation.substitution μ)
      (DeterministicCarrierData.carrierData op).head =
    OriginalDomain.expressionValue (UnitObservation.substitution ρ) op.head
end LogicLineages.OrdinalComparison.Source.NumericCarrierData.Targets
