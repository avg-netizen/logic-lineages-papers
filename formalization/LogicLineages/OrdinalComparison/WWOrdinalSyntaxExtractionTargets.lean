module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxExtractionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OrdinalSyntax ForwardTranslation

def OrdinalSyntaxExtractionCorrect : Prop :=
  ∀ (Γ : List Ty) (t : OrdinalExpression Γ),
    extraction (typedCode t) =
      ((extractPositive t).map closedPositiveCode,
       (compileScalar t).map (scalarSyntaxCode (fun c => SourceTypedPorts.variableIndex c.2.1)))

def OrdinalSyntaxExtractionPrimitiveRecursive : Prop := Primrec extraction
end LogicLineages.OrdinalComparison.Source.Targets
