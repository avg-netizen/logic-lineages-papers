module
public import LogicLineages.OrdinalComparison.SourceGammaAggregateCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaAggregateCode.Targets
open SourceCollisionCompletion SourceAggregateCompletion

def ExactLiteralCodes : Prop := ∀ (Γ : List Ty) (p q : OriginalTerm Γ .ground),
  eraserCode (SyntaxCode.encodeTerm p) (SyntaxCode.encodeTerm q)=SyntaxCode.encodeTerm (eraser p q) ∧
  leftCode (SyntaxCode.encodeTerm p) (SyntaxCode.encodeTerm q)=SyntaxCode.encodeTerm (detectorLeft p q) ∧
  rightCode (SyntaxCode.encodeTerm p) (SyntaxCode.encodeTerm q)=SyntaxCode.encodeTerm (detectorRight p q)

def ExactAggregateCode : Prop := ∀ (Γ : List Ty)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)),
  aggregateCode (es.map pairCode)=pairCode (aggregate es)

def UniformPrimitiveRecursive : Prop :=
  Primrec₂ eraserCode ∧ Primrec₂ leftCode ∧ Primrec₂ rightCode ∧ Primrec₂ step ∧ Primrec aggregateCode
end LogicLineages.OrdinalComparison.Source.SourceGammaAggregateCode.Targets
