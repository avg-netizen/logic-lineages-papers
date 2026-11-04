module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceNeutralExpansionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceNeutralExpansionTargets
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedPrimaryShapes

def ActualNeutralComputabilityExpansion : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    ∀ (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau),
    InUniverse ctx.1.1 ctx.1.2 q → isLambda q = false →
    (∀ y : Nat, encodedR n arity Gamma context (representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩) y →
      SourceComputabilityFormula.Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau y) →
    SourceComputabilityFormula.Computable n arity Gamma (fun x => x ∈ leastSet scalar context)
      context tau (representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceNeutralExpansionTargets
