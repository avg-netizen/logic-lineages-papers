module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralSpecialApplicationValueDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LiteralSpecialApplicationValueTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions ConfinedStructuralInterpretation SourceConstructorIteration ActualOriginalApplication LiteralSpecialApplicationValue

def ScannerMaskAgreement : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ : Ty) (q : ConfinedTerm I Γ σ)
    (M : Constructors I) (P : World I) (ρ : Environment I Γ P) (a b : Protected Γ),MaskAgreement ρ a b →
    ∀ (types : List Ty) (τ : Ty) (args : Values I types P) (h : σ=arrows types τ),scan q M P ρ a types τ args h=scan q M P ρ b types τ args h

def LiteralIdentityMasks : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (P : World I) (σ : Ty) (q : ConfinedTerm I (portTypes P.val++I.context) σ)
    (M : Constructors I) (a b : Protected (portTypes P.val++I.context)) (types : List Ty) (τ : Ty) (args : Values I types P) (h : σ=arrows types τ),
    scan q M P (identity I P) a types τ args h=scan q M P (identity I P) b types τ args h

def SpecialSuccess : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (P : World I) (types : List Ty) (τ : Ty) (q : ConfinedTerm I (portTypes P.val++I.context) (arrows types τ)) (args : Arguments Symbol arity (portTypes P.val++I.context) types) (ha : ArgumentsConfined I args)
    (r : MarkedTerm Symbol arity (portTypes P.val++I.context) τ) (hr : Confined I r),specialApply q.val args=some r →
    applyFull types τ (interpret q (limit I above) P (identity I P)) (argumentValues args ha (limit I above) P (identity I P))=
      interpret ⟨r,hr⟩ (limit I above) P (identity I P)

def SpecialFailure : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (P : World I) (types : List Ty) (τ : Ty) (q : ConfinedTerm I (portTypes P.val++I.context) (arrows types τ)) (args : Arguments Symbol arity (portTypes P.val++I.context) types) (ha : ArgumentsConfined I args),specialApply q.val args=none →
    applyFull types τ (interpret q (limit I above) P (identity I P)) (argumentValues args ha (limit I above) P (identity I P))=
      ExecutableDomainBottom.bottomValue I τ P

end LogicLineages.OrdinalComparison.TerminationOrdering.LiteralSpecialApplicationValueTargets
