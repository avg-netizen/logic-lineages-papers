module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment
open FullListValueApplication CoherentConstructorLattice OriginalSpineActions ConfinedStructuralInterpretation
open ConfinedSubstitution SubstitutionEnvironmentSupport SourceConstructorIteration ActualLimitSubstitution Compatible
/-- Strengthened supporting law, not the original unconstrained-family claim. -/
def FullApplication : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (hcompat : CurrentTupleCompatible M) (Γ : List Ty) (σ : Ty) (q : ConfinedTerm I Γ σ) (P : World I) (ρ : Environment I Γ P) (types : List Ty) (τ : Ty) (args : Values I types P) (h : σ=arrows types τ),
  applyWith (interpret q M P ρ) types τ args h = scan q M P ρ (fun {_} _ => false) types τ args h

def InterpretationSubstitution : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (hcompat : CurrentTupleCompatible M) (Γ Δ : List Ty) (τ : Ty) (q : ConfinedTerm I Γ τ) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s) (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P) , Agreement M s hs ρ η → interpret (substituteSource s hs q) M P η=interpret q M P ρ

def ScannerSubstitution : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (hcompat : CurrentTupleCompatible M) (Γ Δ : List Ty) (τ : Ty) (q : ConfinedTerm I Γ τ) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s) (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P) (sourceMask : Protected Γ) (targetMask : Protected Δ),Agreement M s hs ρ η → ProtectedCompatible I s sourceMask targetMask → ∀ (types : List Ty) (υ : Ty) (args : Values I types P) (h : τ=arrows types υ),scan (substituteSource s hs q) M P η targetMask types υ args h=scan q M P ρ sourceMask types υ args h

/-- The existing actual fixed point satisfies the extra condition. -/
def FixedPointCompatible : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol)
  (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop)
  (_ : DecidableRel above), CurrentTupleCompatible (limit I above)
end LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleTargets
