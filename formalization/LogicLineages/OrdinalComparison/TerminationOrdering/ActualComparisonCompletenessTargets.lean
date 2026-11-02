module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessTargets
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice ConfinedStructuralInterpretation TypedObservationAccess RecursiveComparison SourceConstructorIteration ActualComparisonCompleteness

def WeakCompleteness : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (P : World I) (τ : Ty) (q : ConfinedTerm I (portTypes P.val++I.context) τ) (o : ObservationAt I τ P),
    Weak Symbol arity above (portTypes P.val++I.context) ⟨τ,q.val⟩ ⟨τ,observedTerm o⟩ →
    readBit false (interpret q (limit I above) P (identity I P)) o.val=true

def StrictCompleteness : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (P : World I) (τ : Ty) (q : ConfinedTerm I (portTypes P.val++I.context) τ) (o : ObservationAt I τ P),
    Strict Symbol arity above (portTypes P.val++I.context) ⟨τ,q.val⟩ ⟨τ,observedTerm o⟩ →
    readBit true (interpret q (limit I above) P (identity I P)) o.val=true

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessTargets
