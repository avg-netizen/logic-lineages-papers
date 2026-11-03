module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOccurrenceTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalAngleProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalTargetUnmarkedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationSimulation
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedOccurrenceTransport

def canonicalPacked {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (n : Nat) (q : OriginalPacked Symbol arity Gamma) : Packed Symbol arity Gamma := ⟨q.1,canonical n q.2⟩

def canonicalList {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (n : Nat) (qs : List (OriginalPacked Symbol arity Gamma)) : List (Packed Symbol arity Gamma) := qs.map (canonicalPacked n)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationSimulation
