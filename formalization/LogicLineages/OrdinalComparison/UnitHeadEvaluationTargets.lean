module
public import LogicLineages.OrdinalComparison.UnitHeadEvaluationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitHeadEvaluation.Targets
open ForwardTranslation ScalarAnnotationData OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def GeneratedPositiveEvaluation : Prop := ∀ (Γ : List Ty) (i : Nat)
    (q : OrdinalExpression Γ), GeneratedOrdinalGrade Γ i q → 0 < i →
  ∃ a : ClosedPositive, extractUnitHead q = some a ∧
    evaluateUnitHead q = some a.evaluate ∧ a.evaluate.1.repr = denote (fun _ => 1) q

/-- Every actual stored operator is evaluated and classified; no supplied
extraction success, normal notation, head tree or finite/nonfinite premise. -/
def ActualOperatorClassification : Prop := ∀ (Γ : List Ty) (op : Operator Γ),
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy op.source = some op.vector →
  ∃ a : ClosedPositive, extractUnitHead op.head = some a ∧
    evaluateUnitHead op.head = some a.evaluate ∧
    a.evaluate.1.repr = denote (fun _ => 1) op.head ∧
    (finiteCode (closedPositiveCode a) = true ↔ denote (fun _ => 1) op.head < Ordinal.omega0) ∧
    (finiteCode (closedPositiveCode a) = false ↔ Ordinal.omega0 ≤ denote (fun _ => 1) op.head) ∧
    (finiteCode (closedPositiveCode a) = true →
      (finiteValueCode (closedPositiveCode a) : Ordinal) = denote (fun _ => 1) op.head) ∧
    ∀ μ : Variable Γ .ground → Nat,
      a.evaluate.1.repr = expressionValue (UnitObservation.substitution μ) op.head

/-- Numeric normalization/classification is primitive recursive on the actual
closed-positive syntax code. This is not yet a raw-original-source codec. -/
def ExactNumericBridge : Prop :=
  Primrec normalCode ∧ Primrec finiteCode ∧ Primrec finiteValueCode ∧
  ∀ a : ClosedPositive,
    normalCode (closedPositiveCode a) = rawNoteEncode a.evaluate.1 ∧
    (finiteCode (closedPositiveCode a) = true ↔ a.evaluate.1.repr < Ordinal.omega0) ∧
    (finiteCode (closedPositiveCode a) = true →
      (finiteValueCode (closedPositiveCode a) : Ordinal) = a.evaluate.1.repr)
end LogicLineages.OrdinalComparison.Source.UnitHeadEvaluation.Targets
