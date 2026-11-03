module
public import LogicLineages.OrdinalComparison.UnitHeadCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitHeadCode.Targets
open ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ExactRawUnitExtraction : Prop := ∀ (Γ : List Ty) (q : OrdinalExpression Γ),
  unitCode (OrdinalSyntax.typedCode q) = OrdinalSyntax.typedCode (UnitHeadEvaluation.unitSyntax q) ∧
  positiveCode (OrdinalSyntax.typedCode q) =
    (UnitHeadEvaluation.extractUnitHead q).map closedPositiveCode

def PrimitiveRecursiveAlgorithms : Prop :=
  Primrec unitCode ∧ Primrec positiveCode ∧ Primrec classify

/-- Actual numeric ordinal syntax is the only evaluator input. Generated
positive grade guarantees success, exact normal code, and literal classification. -/
def ActualPositiveClassification : Prop := ∀ (Γ : List Ty) (i : Nat) (q : OrdinalExpression Γ),
  GeneratedOrdinalGrade Γ i q → 0 < i →
  ∃ (a : ClosedPositive) (finite : Bool) (value : Nat),
    positiveCode (OrdinalSyntax.typedCode q) = some (closedPositiveCode a) ∧
    classify (OrdinalSyntax.typedCode q) = some (rawNoteEncode a.evaluate.1,finite,value) ∧
    a.evaluate.1.repr = denote (fun _ => 1) q ∧
    (finite = true ↔ denote (fun _ => 1) q < Ordinal.omega0) ∧
    (finite = false ↔ Ordinal.omega0 ≤ denote (fun _ => 1) q) ∧
    (finite = true → (value : Ordinal) = denote (fun _ => 1) q)
end LogicLineages.OrdinalComparison.Source.UnitHeadCode.Targets
