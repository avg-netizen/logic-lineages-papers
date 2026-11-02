module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions ConfinedStructuralInterpretation ConfinedSubstitution SubstitutionEnvironmentSupport SourceConstructorIteration ActualLimitSubstitution

def InterpretationSubstitution : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (Γ Δ : List Ty) (τ : Ty) (q : ConfinedTerm I Γ τ) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s) (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P) , Agreement (limit I above) s hs ρ η → interpret (substituteSource s hs q) (limit I above) P η=interpret q (limit I above) P ρ

def ScannerSubstitution : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (Γ Δ : List Ty) (τ : Ty) (q : ConfinedTerm I Γ τ) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s) (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P) (sourceMask : Protected Γ) (targetMask : Protected Δ),Agreement (limit I above) s hs ρ η → ProtectedCompatible I s sourceMask targetMask → ∀ (types : List Ty) (υ : Ty) (args : Values I types P) (h : τ=arrows types υ),scan (substituteSource s hs q) (limit I above) P η targetMask types υ args h=scan q (limit I above) P ρ sourceMask types υ args h

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionTargets
