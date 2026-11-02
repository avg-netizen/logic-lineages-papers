module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedStructuralInterpretationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedStructuralInterpretationTargets
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions FunctionalSpineActions TypedExtraDownsets ConfinedStructuralInterpretation

def FrameConfinement : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (q : FiniteQueryPrimitives.Query Symbol arity I.context (budget I)),FiniteQueryPrimitives.Frame I.source I.target q → Confined I q.source.2

def SourceEquations : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) , (∀ (Γ : List Ty) (τ : Ty) (v : Variable Γ τ) (h : Confined I (.var v)), buildTerm I (.var v) h=OriginalSpineActionsProof.variableAction v) ∧
  (∀ (Γ : List Ty) (σ τ : Ty) (body : MarkedTerm Symbol arity (σ::Γ) τ) (h : Confined I (.lam body)),buildTerm I (.lam body) h=LambdaSpineActionsProof.lambdaAction body (buildTerm I body ⟨h.1.2.2,h.2⟩)) ∧
  (∀ (Γ : List Ty) (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f)) (h : Confined I (.ordinary f base)),buildTerm I (.ordinary f base) h=FunctionalSpineActionsProof.ordinaryAction ⟨f,h.2.1⟩ (buildArguments I base ⟨h.1.2,h.2.2⟩)) ∧
  (∀ (Γ : List Ty) (f : Head Symbol) (τ : Ty) (base : Arguments Symbol arity Γ (headArguments arity f)) (ts : List Ty) (extras : Arguments Symbol arity Γ ts) (h : Confined I (.marked f τ base ts extras)),buildTerm I (.marked f τ base ts extras) h=FunctionalSpineActionsProof.markedAction ⟨f,h.2.1⟩ ⟨τ,h.1.1⟩ (buildArguments I base ⟨h.1.2.1,h.2.2.1⟩) ts (argumentTypeList extras ⟨h.1.2.2,h.2.2.2⟩) (buildArguments I extras ⟨h.1.2.2,h.2.2.2⟩)) ∧
  (∀ (Γ ts : List Ty) (σ : Ty) (q : MarkedTerm Symbol arity Γ σ) (rest : Arguments Symbol arity Γ ts) (h : ArgumentsConfined I (.cons q rest)),buildArguments I (.cons q rest) h=fun i => Fin.cases (buildTerm I q ⟨h.1.1,h.2.1⟩) (buildArguments I rest ⟨h.1.2,h.2.2⟩) i)

def InterpretationMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (τ : Ty) (q : ConfinedTerm I Γ τ) , EvaluationMonotone (interpret q)

def InterpretationNatural : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (τ : Ty) (q : ConfinedTerm I Γ τ) , EvaluationNatural (interpret q)

def ScannerMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (τ : Ty) (q : ConfinedTerm I Γ τ) , ScanMonotone (scan q)

def ScannerNatural : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (τ : Ty) (q : ConfinedTerm I Γ τ) , ScanNatural (scan q)

def EmptyScanner : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (τ : Ty) (q : ConfinedTerm I Γ τ) (M : Constructors I) (P : World I) (ρ : Environment I Γ P) (mask : Protected Γ) (args : Values I [] P),scan q M P ρ mask [] τ args rfl=interpret q M P ρ

end LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedStructuralInterpretationTargets
