module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceMultisetLeastMembershipDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceMultisetLeastMembershipTargets
open OrdinaryArithmeticQuotient OrdinaryArithmeticDirect OrdinaryArithmeticCarrier
open PositiveArithmeticOperators PositiveArithmeticLeastSet PositiveArithmeticAccessibility
open DirectMultisetAccessibleSubtype

def ActualConditionalLeastMembership : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Source.Ty), ∃ scalar multiset : Positive (Fin 2),
    (∀ context : Nat,
      Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) ∧
      Calibrates multiset context (encodedList n arity Gamma context) (encodedDirect n arity Gamma context)) ∧
    (∀ (context code : Nat) (ctx : Context n) (values : List Nat),
      Encodable.decode context = some ctx →
      SubtypeClosed (fun tau => tau ∈ ctx.1.2) →
      Encodable.decode code = some values →
      encodedList n arity Gamma context code →
      MembersAccessible (QuotientDominationCertificates.relation n arity ctx.1.1 ctx.1.2 Gamma ctx.2) values →
      code ∈ leastSet multiset context)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceMultisetLeastMembershipTargets
