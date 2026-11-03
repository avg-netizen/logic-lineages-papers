module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalSpineActionsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalSpineActionsTargets
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions TypedExtraDownsets FullTuplePacking OrdinaryFunctionalValue FunctionalSpineActions

def StateMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (f : HeadIndex I) (base : ArgumentActions I Γ (headArguments arity f.val)) (extraTypes : List Ty) (ht : ∀ τ ∈ extraTypes,τ ∈ TypedExtraDownsets.types I) (extras : ArgumentActions I Γ extraTypes) (M N : Constructors I) (P : World I) (ρ η : Environment I Γ P),M ≤ N → EnvLE ρ η → markedState f base extraTypes ht extras M P ρ ≤ markedState f base extraTypes ht extras N P η

def StateRestriction : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (f : HeadIndex I) (base : ArgumentActions I Γ (headArguments arity f.val)) (extraTypes : List Ty) (ht : ∀ τ ∈ extraTypes,τ ∈ TypedExtraDownsets.types I) (extras : ArgumentActions I Γ extraTypes) (M : Constructors I) (P Q : World I) (h : Extends P Q) (ρ : Environment I Γ P),(inputFamily I f).restrict h (markedState f base extraTypes ht extras M P ρ)=markedState f base extraTypes ht extras M Q (restrict h ρ)

def FullTupleScanEquation : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (f : HeadIndex I) (σ : TypeIndex I) (e : Evaluate I Γ σ.val) (state : (M : Constructors I) → (P : World I) → Environment I Γ P → Inputs I f P) (M : Constructors I) (P : World I) (ρ : Environment I Γ P) (mask : Protected Γ) (types : List Ty) (τ : Ty) (args : Values I types P) (h : σ.val=arrows types τ) (hne : types≠[]),functionalScan f σ e state M P ρ mask types τ args h=M.val f (resultTag I σ (sourceSuffix σ types τ h hne)) P (FunctionalTupleBuilder.appendInput (state M P ρ) (packTuple σ (sourceSuffix σ types τ h hne) args))

def EvaluationEquations : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (f : HeadIndex I) (σ : TypeIndex I) (base : ArgumentActions I Γ (headArguments arity f.val)) (extraTypes : List Ty) (ht : ∀ τ ∈ extraTypes,τ ∈ TypedExtraDownsets.types I) (extras : ArgumentActions I Γ extraTypes) (M : Constructors I) (P : World I) (ρ : Environment I Γ P),ordinaryEvaluate f base M P ρ=ordinaryValue M f (evaluateArguments base M P ρ) ∧ markedEvaluate f σ base extraTypes ht extras M P ρ=M.val f σ P (markedState f base extraTypes ht extras M P ρ)

def ActualOrdinaryAction : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (f : HeadIndex I) (base : ArgumentActions I Γ (headArguments arity f.val)) , ∃ a : PairedAction I Γ (headResult f.val),a.evaluate=ordinaryEvaluate f base ∧ a.scan=ordinaryScan f base

def ActualMarkedAction : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (f : HeadIndex I) (σ : TypeIndex I) (base : ArgumentActions I Γ (headArguments arity f.val)) (extraTypes : List Ty) (ht : ∀ τ ∈ extraTypes,τ ∈ TypedExtraDownsets.types I) (extras : ArgumentActions I Γ extraTypes) , ∃ a : PairedAction I Γ σ.val,a.evaluate=markedEvaluate f σ base extraTypes ht extras ∧ a.scan=markedScan f σ base extraTypes ht extras

end LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalSpineActionsTargets
