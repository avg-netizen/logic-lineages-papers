module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedStructuralInterpretationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitInterpretationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitApplicationTargets
open Source Source.SourceSpecialApplication FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions ConfinedStructuralInterpretation SourceConstructorIteration

def FullApplication : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (Γ : List Ty) (σ : Ty) (q : ConfinedTerm I Γ σ) (P : World I) (ρ : Environment I Γ P) (types : List Ty) (τ : Ty) (args : Values I types P) (h : σ=arrows types τ),
  applyWith (interpret q (limit I above) P ρ) types τ args h = scan q (limit I above) P ρ (fun {_} _ => false) types τ args h

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitApplicationTargets
