module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceScalarMultisetLeastDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceScalarMultisetLeastTargets
open OrdinaryArithmeticQuotient OrdinaryArithmeticDirect OrdinaryArithmeticCarrier
open PositiveArithmeticOperators PositiveArithmeticLeastSet PositiveArithmeticAccessibility

def ActualScalarMembersToMultiset : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Source.Ty), ∃ scalar multiset : Positive (Fin 2),
    (∀ context : Nat,
      Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) ∧
      Calibrates multiset context (encodedList n arity Gamma context) (encodedDirect n arity Gamma context)) ∧
    (∀ (context code : Nat) (ctx : Context n) (values : List Nat),
      Encodable.decode context = some ctx →
      SubtypeClosed (fun tau => tau ∈ ctx.1.2) →
      Encodable.decode code = some values →
      (∀ x ∈ values, x ∈ leastSet scalar context) →
      code ∈ leastSet multiset context)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceScalarMultisetLeastTargets
