module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SubstitutionEnvironmentSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitution
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding FiniteObservationBits ConfinedStructuralInterpretation ConfinedSubstitution

def substituteSource {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ Δ : List Ty} {τ : Ty} (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (q : ConfinedTerm I Γ τ) : ConfinedTerm I Δ τ :=
  ⟨substituteTerm q.val s,ConfinedSubstitutionProof.substitutionClosure Symbol inferInstance arity I Γ Δ τ q.val s q.property hs⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitution
