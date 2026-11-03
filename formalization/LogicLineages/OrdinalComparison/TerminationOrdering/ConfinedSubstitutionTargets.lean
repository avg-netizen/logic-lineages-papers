module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedSubstitutionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedSubstitutionTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding FiniteObservationBits OriginalSpineActions ConfinedStructuralInterpretation ComparisonFreeVariables ConfinedSubstitution

def SubstitutionClosure : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ Δ : List Ty) (τ : Ty) (q : MarkedTerm Symbol arity Γ τ) (s : MarkedSubstitution Symbol arity Γ Δ) , Confined I q → RangeConfined I s → Confined I (substituteTerm q s)

def ArgumentClosure : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ Δ : List Ty) (types : List Ty) (args : Arguments Symbol arity Γ types) (s : MarkedSubstitution Symbol arity Γ Δ) , ArgumentsConfined I args → RangeConfined I s → ArgumentsConfined I (substituteArguments args s)

def LiftedRange : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ Δ : List Ty) (σ : Ty) (s : MarkedSubstitution Symbol arity Γ Δ) , RangeConfined I s → RangeConfined I (liftSubstitution (τ := σ) s)

def InitiallyCompatible : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ Δ : List Ty) (s : MarkedSubstitution Symbol arity Γ Δ) , ProtectedCompatible I s (fun {_} _ => false) (fun {_} _ => false)

def LiftedCompatibility : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ Δ : List Ty) (σ : Ty) (s : MarkedSubstitution Symbol arity Γ Δ) (sourceMask : Protected Γ) (targetMask : Protected Δ), ProtectedCompatible I s sourceMask targetMask → ProtectedCompatible I (liftSubstitution (τ := σ) s) (LambdaSpineActions.protectExtend sourceMask) (LambdaSpineActions.protectExtend targetMask)

def LiteralLift : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ Δ : List Ty) (σ : Ty) (s : MarkedSubstitution Symbol arity Γ Δ) , liftSubstitution (τ := σ) s Variable.here=MarkedTerm.var Variable.here ∧ ∀ {τ} (v : Variable Γ τ),liftSubstitution (τ := σ) s (Variable.there v)=renameTerm (s v) (Renaming.weaken Δ σ)

end LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedSubstitutionTargets
