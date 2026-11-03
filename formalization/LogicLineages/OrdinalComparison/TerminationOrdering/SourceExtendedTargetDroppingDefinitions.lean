module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMarkingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedTargetDropping
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison

/-- Source lemma5.30: drop a literal finite FINAL block of target extras.
The generic packed endpoint equality prevents hidden dependent-type casts. -/
def DropMeaning {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (s t : Packed Symbol arity Gamma) : Prop :=
  ∀ (g : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity g))
    (types moreTypes : List Ty) (extras : Arguments Symbol arity Gamma types)
    (more : Arguments Symbol arity Gamma moreTypes),
  t=⟨t.1,.marked g t.1 base (types++moreTypes) (appendArguments extras more)⟩ →
    SourceExtendedComparison.Weak Symbol arity above Gamma s ⟨t.1,.marked g t.1 base types extras⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedTargetDropping
