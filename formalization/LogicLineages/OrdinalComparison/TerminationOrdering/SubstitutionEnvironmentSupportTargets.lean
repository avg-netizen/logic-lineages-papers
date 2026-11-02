module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SubstitutionEnvironmentSupportDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SubstitutionEnvironmentSupportTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions ConfinedStructuralInterpretation ConfinedSubstitution ComparisonFreeVariables SubstitutionEnvironmentSupport

def MaskLocality : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (τ : Ty) (q : ConfinedTerm I Γ τ) (M : Constructors I) (P : World I) (ρ : Environment I Γ P) (mask mask' : Protected Γ),Supported q.val (fun {_} v => mask v=mask' v) → ∀ (types : List Ty) (υ : Ty) (args : Values I types P) (h : τ=arrows types υ),scan q M P ρ mask types υ args h=scan q M P ρ mask' types υ args h

def AgreementRestriction : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ Δ : List Ty) (M : Constructors I) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s) (P Q : World I) (h : Extends P Q) (ρ : Environment I Γ P) (η : Environment I Δ P), Agreement M s hs ρ η → Agreement M s hs (restrict h ρ) (restrict h η)

def AgreementLift : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ Δ : List Ty) (σ : Ty) (M : Constructors I) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s) (P : World I) (a : Value I σ P) (ρ : Environment I Γ P) (η : Environment I Δ P),Agreement M s hs ρ η → Agreement M (liftSubstitution (τ := σ) s) (ConfinedSubstitutionProof.liftedRange Symbol inferInstance arity I Γ Δ σ s hs) (extend a ρ) (extend a η)

end LogicLineages.OrdinalComparison.TerminationOrdering.SubstitutionEnvironmentSupportTargets
