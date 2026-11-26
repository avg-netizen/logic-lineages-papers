module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSingleBottomLeastDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSingleBottomLeastTargets
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedPrimarySubstitution

/-- Original scalar least-set membership is equivalent before and after erasing
one variable by bottom. This is a native semantic statement, not an ID1 derivation. -/
def ActualScalarLeastSingleBottom : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalarOld scalarNew : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    ∀ sigma : Ty,
    Calibrates scalarOld context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    Calibrates scalarNew context (encodedScalar n arity (sigma :: Gamma) context) (encodedR n arity (sigma :: Gamma) context) →
    ∀ q : Packed (Fin n) arity (sigma :: Gamma), InUniverse ctx.1.1 ctx.1.2 q.2 →
    (representativeCode ctx.1.1 ctx.1.2 q ∈ leastSet scalarNew context ↔
      representativeCode ctx.1.1 ctx.1.2 (substitutePacked (singleSubstitution (.bottom sigma)) q) ∈ leastSet scalarOld context)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSingleBottomLeastTargets
