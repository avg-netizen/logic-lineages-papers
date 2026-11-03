module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedTargetDroppingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PrefixSourceComposition
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison

/-- Literal compiler environment image: a variable, or an ACTUAL typed
prefix copy of the specified whole source. No comparison oracle is present. -/
def PrefixImage {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma types) {tau : Ty} (q : MarkedTerm Symbol arity Gamma tau) : Prop :=
  (∃ v : Variable Gamma tau,q=.var v) ∨
  ∃ (preTypes : List Ty) (pre : Arguments Symbol arity Gamma preTypes),
    SourceExtendedComparison.Prefix pre extras ∧ q=.marked f tau base preTypes pre

end LogicLineages.OrdinalComparison.TerminationOrdering.PrefixSourceComposition
