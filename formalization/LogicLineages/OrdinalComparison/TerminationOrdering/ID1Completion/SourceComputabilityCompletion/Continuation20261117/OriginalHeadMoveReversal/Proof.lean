module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.ClassSymmetryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.SourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.SourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem reversal : Targets.InternalReversal := by
  intro n arity body alpha Delta sourceHead sourceBase targetHead targetBase symbols types hv hc hm
  have ha := (OriginalHeadMove.InternalProof.internalAcceptance n arity body alpha Delta
    sourceHead sourceBase targetHead targetBase symbols types).mp hm
  have sourceWindow := andLeft (andLeft (andLeft ha))
  have targetMember := andRight (andLeft (andLeft ha))
  have sourceMember := andRight
    (OriginalGuardedHeadSourceCoverage.SourceProof.source n arity sourceHead symbols types hv sourceWindow hc)
  have targetWindow := HeadWindowBooleanRange.SourceProof.sourceWindow n arity body alpha Delta
    targetHead symbols types targetMember
  have hc' := ClassSymmetryProof.symmetric sourceHead targetHead (andRight (andLeft ha))
  have hp := OriginalArgumentPermutationClosure.Proof.symmetry body alpha Delta sourceBase targetBase (andRight ha)
  exact (OriginalHeadMove.InternalProof.internalAcceptance n arity body alpha Delta
    targetHead targetBase sourceHead sourceBase symbols types).mpr
    (andIntro (andIntro (andIntro targetWindow sourceMember) hc') hp)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.Proof
