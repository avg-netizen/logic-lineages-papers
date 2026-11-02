module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplicationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplicationTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice FunctionalSpineActions ConfinedStructuralInterpretation ConfinedSubstitution SubstitutionEnvironmentSupport SourceConstructorIteration ActualOriginalApplication

def SuccessConfinement : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ Δ : List Ty) (σ : Ty) (q : ConfinedTerm I Γ σ) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s) (types : List Ty) (τ : Ty) (args : Arguments Symbol arity Δ types) (ha : ArgumentsConfined I args) (h : σ=arrows types τ),
    ∀ r,applyOriginalWith q.val s args h=some r → Confined I r

def SuccessInterpretation : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (Γ Δ : List Ty) (σ : Ty) (q : ConfinedTerm I Γ σ) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s) (types : List Ty) (τ : Ty) (args : Arguments Symbol arity Δ types) (ha : ArgumentsConfined I args) (h : σ=arrows types τ)
    (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P),
    Agreement (limit I above) s hs ρ η → ∀ (r : MarkedTerm Symbol arity Δ τ) (hr : Confined I r),
    applyOriginalWith q.val s args h=some r →
    interpret ⟨r,hr⟩ (limit I above) P η=
      scan q (limit I above) P ρ (fun {_} _ => true) types τ (argumentValues args ha (limit I above) P η) h

def FailureBottom : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (Γ Δ : List Ty) (σ : Ty) (q : ConfinedTerm I Γ σ) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s) (types : List Ty) (τ : Ty) (args : Arguments Symbol arity Δ types) (ha : ArgumentsConfined I args) (h : σ=arrows types τ)
    (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P),
    Agreement (limit I above) s hs ρ η → applyOriginalWith q.val s args h=none →
    scan q (limit I above) P ρ (fun {_} _ => true) types τ (argumentValues args ha (limit I above) P η) h=
      ExecutableDomainBottom.bottomValue I τ P

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplicationTargets
