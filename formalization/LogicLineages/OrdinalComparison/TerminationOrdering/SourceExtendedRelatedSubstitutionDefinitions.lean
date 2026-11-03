module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedSubstitutionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRelatedSubstitution
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison

/-- This is the literal hypothesis of the related-substitution lemma, using
actual auxiliary derivations on each pair of images, not an oracle relation. -/
def EnvironmentsRelated {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (above : Symbol → Symbol → Prop) (theta eta : MarkedSubstitution Symbol arity Gamma Delta) : Prop :=
  ∀ tau (v : Variable Gamma tau),SourceExtendedComparison.Weak Symbol arity above Delta ⟨tau,theta v⟩ ⟨tau,eta v⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedRelatedSubstitution
