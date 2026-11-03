module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplicationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LiteralSpecialApplicationValue
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions ConfinedStructuralInterpretation SourceConstructorIteration ActualOriginalApplication

def BottomApplications {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {P : World I} {σ : Ty} (a : Value I σ P) : Prop :=
  ∀ (types : List Ty) (τ : Ty) (args : Values I types P) (h : σ=arrows types τ),types≠[] →
    applyWith a types τ args h=ExecutableDomainBottom.bottomValue I τ P

def MaskAgreement {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {P : World I} (ρ : Environment I Γ P) (a b : Protected Γ) : Prop :=
  ∀ {τ} (v : Variable Γ τ),a v=b v ∨ BottomApplications (ρ v)

end LogicLineages.OrdinalComparison.TerminationOrdering.LiteralSpecialApplicationValue
