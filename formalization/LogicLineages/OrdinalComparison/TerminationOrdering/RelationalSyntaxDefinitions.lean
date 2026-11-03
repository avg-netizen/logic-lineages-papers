module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelatedEnvironmentsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedApplyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryLogicalRelationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntax
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourcePortContexts FiniteObservationBits RecursiveNaturalDomains TypedValueEnvironment
open CoherentConstructorLattice ConfinedStructuralInterpretation RelatedEnvironments ActualValueLogicalRelation

/-- Genuine evaluation under related environments, with the SAME literal
substitution on every occurrence of each old source name. -/
def EvaluationRelated {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (M : Constructors I)
    {Gamma : List Ty} {sigma : Ty} (q : ConfinedTerm I Gamma sigma) : Prop :=
  ∀ (P : World I) (rho : Environment I Gamma P)
    (s : MarkedSubstitution Symbol arity Gamma (portTypes P.val++I.context)),
    EnvironmentRelated I above P rho s →
      Related I above sigma P (interpret q M P rho) (substituteTerm q.val s)

/-- The all-mask induction invariant is stated against the EXPLICIT masked
syntax scanner, whose initial/original-prefix correspondence is already paid.
Protection is never erased, and an undefined result requires WHOLE bottom. -/
def ScannerRelated {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (M : Constructors I)
    {Gamma : List Ty} {sigma : Ty} (q : ConfinedTerm I Gamma sigma) : Prop :=
  ∀ (P : World I) (rho : Environment I Gamma P)
    (s : MarkedSubstitution Symbol arity Gamma (portTypes P.val++I.context))
    (mask : OriginalSpineActions.Protected Gamma),EnvironmentRelated I above P rho s →
    ∀ (types : List Ty) (tau : Ty) (values : FullListValueApplication.Values I types P)
    (args : Arguments Symbol arity (portTypes P.val++I.context) types) (h : sigma=arrows types tau),
    (∀ i,Related I above (types.get i) P (values i) (argumentAt args i)) →
    match ProtectedApply.applyWith q.val mask s args h with
    | none => scan q M P rho mask types tau values h=ExecutableDomainBottom.bottomValue I tau P
    | some result => Related I above tau P (scan q M P rho mask types tau values h) result

def ArgumentsRelated {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (M : Constructors I)
    {Gamma types : List Ty} (args : Arguments Symbol arity Gamma types)
    (ha : ArgumentsConfined I args) : Prop :=
  ∀ (P : World I) (rho : Environment I Gamma P)
    (s : MarkedSubstitution Symbol arity Gamma (portTypes P.val++I.context)),
    EnvironmentRelated I above P rho s →
    ∀ i,Related I above (types.get i) P (ActualOriginalApplication.argumentValues args ha M P rho i)
      (argumentAt (substituteArguments args s) i)

end LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntax
