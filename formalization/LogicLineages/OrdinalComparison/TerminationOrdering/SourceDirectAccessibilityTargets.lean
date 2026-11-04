module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceDirectAccessibilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceDirectAccessibilityTargets
open OrdinaryArithmeticQuotient OrdinaryArithmeticDirect DirectMultisetAccessibility
open DirectMultisetAccessibleSubtype

def ActualListAccessibility : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Source.Ty) (ctx : Context n) (values : List Nat),
    MembersAccessible (QuotientDominationCertificates.relation n arity ctx.1.1 ctx.1.2 Gamma ctx.2) values →
    Acc (ReverseDirect (QuotientDominationCertificates.relation n arity ctx.1.1 ctx.1.2 Gamma ctx.2)) values

def ActualDecodedAccessibility : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Source.Ty) (context code : Nat) (ctx : Context n) (values : List Nat),
    Encodable.decode context = some ctx → Encodable.decode code = some values →
    MembersAccessible (QuotientDominationCertificates.relation n arity ctx.1.1 ctx.1.2 Gamma ctx.2) values →
    Acc (fun successor source => encodedDirect n arity Gamma context source successor) code

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceDirectAccessibilityTargets
