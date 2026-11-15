module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadMoveTransitivity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadMoveTransitivity.ClassProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadMoveTransitivity.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
theorem transitivity : Targets.InternalTransitivity := by
  intro n arity body alpha Delta sourceHead sourceBase middleHead middleBase targetHead targetBase symbols types hab hbc
  have ha := (OriginalHeadMove.InternalProof.internalAcceptance n arity body alpha Delta sourceHead sourceBase middleHead middleBase symbols types).mp hab
  have hb := (OriginalHeadMove.InternalProof.internalAcceptance n arity body alpha Delta middleHead middleBase targetHead targetBase symbols types).mp hbc
  have hwindow := andLeft (andLeft (andLeft ha))
  have hsource := andRight (andLeft (andLeft hb))
  have hclass := ClassProof.transitive sourceHead middleHead targetHead (andRight (andLeft ha)) (andRight (andLeft hb))
  have hperm := OriginalArgumentPermutationClosure.Proof.transitivity body alpha Delta sourceBase middleBase targetBase (andRight ha) (andRight hb)
  exact (OriginalHeadMove.InternalProof.internalAcceptance n arity body alpha Delta sourceHead sourceBase targetHead targetBase symbols types).mpr
    (andIntro (andIntro (andIntro hwindow hsource) hclass) hperm)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadMoveTransitivity.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadMoveTransitivity.Proof
