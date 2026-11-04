module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConditionalLambdaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConditionalLambdaTargets
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths

def ActualConditionalLambdaComputability : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    ∀ (sigma tau : Ty) (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau),
    InUniverse ctx.1.1 ctx.1.2 (.lam body) →
    Acc (fun successor source => PositivePath
      (QuotientEdge n arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) (sigma :: Gamma)) source successor)
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,body⟩) →
    (∀ a : AuxTerm (Fin n) arity Gamma sigma, InUniverse ctx.1.1 ctx.1.2 a →
      SourceComputabilityFormula.Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context sigma
        (representativeCode ctx.1.1 ctx.1.2 ⟨sigma,a⟩) →
      SourceComputabilityFormula.Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau
        (representativeCode ctx.1.1 ctx.1.2 ⟨tau,substitute body (singleSubstitution a)⟩)) →
    SourceComputabilityFormula.Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context (.arrow sigma tau)
      (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,.lam body⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConditionalLambdaTargets
