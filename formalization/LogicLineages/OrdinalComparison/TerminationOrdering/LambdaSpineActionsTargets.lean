module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LambdaSpineActionsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LambdaSpineActionsTargets
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions LambdaObservationMatching LambdaSpineActions

def BinderProtection : Prop := ∀ (Γ : List Ty) (σ : Ty) (mask : Protected Γ),protectExtend (σ := σ) mask Variable.here=true ∧ ∀ {τ} (v : Variable Γ τ),protectExtend (σ := σ) mask (Variable.there v)=mask v

def BinderConsumption : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ υ : Ty) (A : PairedAction I (σ::Γ) υ) (M : Constructors I) (P : World I) (ρ : Environment I Γ P) (mask : Protected Γ) (α : Ty) (rest : List Ty) (τ : Ty) (args : Values I (α::rest) P) (h : Ty.arrow σ υ=arrows (α::rest) τ),consume A M P ρ mask α rest τ args h=A.scan M P (extend (castValue (Ty.arrow.inj h).1.symm (args ⟨0,by simp⟩)) ρ) (protectExtend mask) rest τ (tailValues args) (Ty.arrow.inj h).2

def NaturalTables : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ υ : Ty) (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ) (M : Constructors I) (P : World I) (ρ : Environment I Γ P),NaturalTupleLayer.Good (lambdaRaw body A M P ρ)

def RawMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ υ : Ty) (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ) (M N : Constructors I) (P : World I) (ρ η : Environment I Γ P),M ≤ N → EnvLE ρ η → lambdaRaw body A M P ρ ≤ lambdaRaw body A N P η

def RawRestriction : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ υ : Ty) (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ) (M : Constructors I) (P Q : World I) (h : Extends P Q) (ρ : Environment I Γ P),rawWeaken h (lambdaRaw body A M P ρ)=lambdaRaw body A M Q (restrict h ρ)

def ActualLambdaAction : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ υ : Ty) (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ) , ∃ a : PairedAction I Γ (.arrow σ υ),(∀ M P (ρ : Environment I Γ P),(layerView I (.arrow σ υ) P (a.evaluate M P ρ)).val=lambdaRaw body A M P ρ) ∧ a.scan=lambdaScan A a.evaluate

end LogicLineages.OrdinalComparison.TerminationOrdering.LambdaSpineActionsTargets
