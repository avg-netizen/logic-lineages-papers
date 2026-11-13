module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralSpecialApplicationValueTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleSpecialTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts
open FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment
open FullListValueApplication CoherentConstructorLattice OriginalSpineActions ConfinedStructuralInterpretation
open ConfinedSubstitution SubstitutionEnvironmentSupport ActualOriginalApplication LiteralSpecialApplicationValue
/-- Explicitly strengthened original-spine and literal simultaneous-application
contracts. Original syntax, actual success/failure, confinement, environment
agreement and literal identity environment are unchanged. This does not assert
the unrestricted generic-family manuscript statement. -/
def SuccessInterpretation : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (hcompat : Compatible.CurrentTupleCompatible M) (Γ Δ : List Ty) (σ : Ty) (q : ConfinedTerm I Γ σ) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s) (types : List Ty) (τ : Ty) (args : Arguments Symbol arity Δ types) (ha : ArgumentsConfined I args) (h : σ=arrows types τ)
    (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P),
    Agreement M s hs ρ η → ∀ (r : MarkedTerm Symbol arity Δ τ) (hr : Confined I r),
    applyOriginalWith q.val s args h=some r →
    interpret ⟨r,hr⟩ M P η=
      scan q M P ρ (fun {_} _ => true) types τ (argumentValues args ha M P η) h

def FailureBottom : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (hcompat : Compatible.CurrentTupleCompatible M) (Γ Δ : List Ty) (σ : Ty) (q : ConfinedTerm I Γ σ) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s) (types : List Ty) (τ : Ty) (args : Arguments Symbol arity Δ types) (ha : ArgumentsConfined I args) (h : σ=arrows types τ)
    (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P),
    Agreement M s hs ρ η → applyOriginalWith q.val s args h=none →
    scan q M P ρ (fun {_} _ => true) types τ (argumentValues args ha M P η) h=
      ExecutableDomainBottom.bottomValue I τ P

def SpecialSuccess : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (hcompat : Compatible.CurrentTupleCompatible M) (P : World I) (types : List Ty) (τ : Ty) (q : ConfinedTerm I (portTypes P.val++I.context) (arrows types τ)) (args : Arguments Symbol arity (portTypes P.val++I.context) types) (ha : ArgumentsConfined I args)
    (r : MarkedTerm Symbol arity (portTypes P.val++I.context) τ) (hr : Confined I r),specialApply q.val args=some r →
    applyFull types τ (interpret q M P (identity I P)) (argumentValues args ha M P (identity I P))=
      interpret ⟨r,hr⟩ M P (identity I P)

def SpecialFailure : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (hcompat : Compatible.CurrentTupleCompatible M) (P : World I) (types : List Ty) (τ : Ty) (q : ConfinedTerm I (portTypes P.val++I.context) (arrows types τ)) (args : Arguments Symbol arity (portTypes P.val++I.context) types) (ha : ArgumentsConfined I args),specialApply q.val args=none →
    applyFull types τ (interpret q M P (identity I P)) (argumentValues args ha M P (identity I P))=
      ExecutableDomainBottom.bottomValue I τ P

end LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleSpecialTargets
