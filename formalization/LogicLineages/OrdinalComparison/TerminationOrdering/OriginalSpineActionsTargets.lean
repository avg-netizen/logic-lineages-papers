module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalSpineActionsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalSpineActionsTargets
open Source Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions

def VariableEquations : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ : Ty) (v : Variable Γ σ) (M : Constructors I) (P : World I) (ρ : Environment I Γ P) (mask : Protected Γ) (types : List Ty) (τ : Ty) (args : Values I types P) (h : σ=arrows types τ), variableEvaluate v M P ρ=ρ v ∧ (types=[] → variableScan v M P ρ mask types τ args h=applyWith (ρ v) types τ args h) ∧ (types≠[] → mask v=true → variableScan v M P ρ mask types τ args h=ExecutableDomainBottom.bottomValue I τ P) ∧ (mask v=false → variableScan v M P ρ mask types τ args h=applyWith (ρ v) types τ args h)

def VariableEvaluationMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ : Ty) (v : Variable Γ σ) , EvaluationMonotone (I := I) (variableEvaluate v)

def VariableEvaluationNatural : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ : Ty) (v : Variable Γ σ) , EvaluationNatural (I := I) (variableEvaluate v)

def VariableScanMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ : Ty) (v : Variable Γ σ) , ScanMonotone (I := I) (variableScan v)

def VariableScanNatural : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ : Ty) (v : Variable Γ σ) , ScanNatural (I := I) (variableScan v)

def ActualVariableAction : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ : Ty) (v : Variable Γ σ) , ∃ a : PairedAction I Γ σ,a.evaluate=variableEvaluate v ∧ a.scan=variableScan v

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalSpineActionsTargets
