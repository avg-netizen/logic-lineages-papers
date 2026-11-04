module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceWeakeningLeastDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceWeakeningLeastTargets
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedPrimaryWeakening

def ActualScalarLeastWeakening : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalarOld scalarNew : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    ∀ sigma : Ty,
    Calibrates scalarOld context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    Calibrates scalarNew context (encodedScalar n arity (sigma :: Gamma) context) (encodedR n arity (sigma :: Gamma) context) →
    ∀ q : Packed (Fin n) arity Gamma, InUniverse ctx.1.1 ctx.1.2 q.2 →
    (representativeCode ctx.1.1 ctx.1.2 q ∈ leastSet scalarOld context ↔
      representativeCode ctx.1.1 ctx.1.2 (renamePacked (Renaming.weaken Gamma sigma) q) ∈ leastSet scalarNew context)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceWeakeningLeastTargets
