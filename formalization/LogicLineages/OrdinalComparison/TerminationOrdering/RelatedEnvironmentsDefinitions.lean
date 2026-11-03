module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LogicalRelationWorldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.LambdaObservationMatchingDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RelatedEnvironments
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourcePortContexts FiniteObservationBits TypedValueEnvironment ActualValueLogicalRelation

/-- Pointwise actual value-to-literal-syntax relatedness. This is a relational
induction invariant, not equality with an interpretation of substituted syntax. -/
def EnvironmentRelated {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (above : Symbol → Symbol → Prop) {Γ : List Ty}
    (P : World I) (rho : Environment I Γ P)
    (s : MarkedSubstitution Symbol arity Γ (portTypes P.val++I.context)) : Prop :=
  ∀ {tau : Ty} (v : Variable Γ tau),Related I above tau P (rho v) (s v)

/-- Literal future-world substitution; the same source names remain shared. -/
def futureSubstitution {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {P Q : World I} (h : Extends P Q)
    (s : MarkedSubstitution Symbol arity Γ (portTypes P.val++I.context)) :
    MarkedSubstitution Symbol arity Γ (portTypes Q.val++I.context) :=
  fun v => futureSyntax h (s v)

end LogicLineages.OrdinalComparison.TerminationOrdering.RelatedEnvironments
