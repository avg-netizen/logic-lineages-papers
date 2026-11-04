module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityDownwardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityDownwardTargets
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility

def ActualComputabilityDownward : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    ∀ (tau : Ty) (source successor : Nat),
    SourceComputabilityFormula.Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau source →
    encodedR n arity Gamma context source successor →
    SourceComputabilityFormula.Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau successor

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityDownwardTargets
