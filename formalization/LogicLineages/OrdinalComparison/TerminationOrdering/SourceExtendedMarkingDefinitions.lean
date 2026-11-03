module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRelatedSubstitutionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMarking
open Source Source.SourceMarkedSyntax RecursiveComparison

/-- Total top marking: the ACTUAL lambda spine is retained. Already marked
heads and variables are unchanged; this does not mark arbitrary subterms. -/
def star {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty} :
    MarkedTerm Symbol arity Gamma tau → MarkedTerm Symbol arity Gamma tau
  | .var v => .var v
  | .lam body => .lam (star body)
  | .ordinary f base => .marked f (headResult f) base [] .nil
  | .marked f tau base types extras => .marked f tau base types extras

def starPacked {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (q : Packed Symbol arity Gamma) : Packed Symbol arity Gamma := ⟨q.1,star q.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMarking
