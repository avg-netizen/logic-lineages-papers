module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityLeastDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityLeastTargets
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility

def ActualComputabilityLeast : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    ∀ (tau : Ty) (value : Nat),
    SourceComputabilityFormula.Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau value →
    value ∈ leastSet scalar context

def ActualComputabilityAccessible : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    ∀ (tau : Ty) (value : Nat),
    SourceComputabilityFormula.Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau value →
    Acc (fun successor source => encodedR n arity Gamma context source successor) value

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityLeastTargets
