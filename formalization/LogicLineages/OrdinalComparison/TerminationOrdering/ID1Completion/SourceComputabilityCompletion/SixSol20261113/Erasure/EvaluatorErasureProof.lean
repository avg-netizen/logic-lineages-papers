module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureObservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureRowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open GuardedSourceSyntaxProof (numeralRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualErasureCongruence : EvaluatorErasureTargets.ActualErasureCongruence := by
 intro R H G M W body alpha Delta left right erasedLeft erasedRight parameter erasedParameter c gamma deleted count cutoff d
   hpair hp hn hl hb hd hdel heL heR
 have hsL := andLeft hpair
 have hsR := andLeft (andRight hpair)
 apply EvaluatorErasureSyntax.sameCases R left right parameter _ (andRight (andRight hpair))
 intro beta j Theta common hinc hcommon
 have hsL' := renameInto hsL j Theta hinc
 have hsR' := renameInto hsR j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hn' := renameInto hn j Theta hinc
 have hl' := renameInto hl j Theta hinc
 have hb' := renameInto hb j Theta hinc
 have hd' := renameInto hd j Theta hinc
 have hdel' := renameInto hdel j Theta hinc
 have heL' := renameInto heL j Theta hinc
 have heR' := renameInto heR j Theta hinc
 simp only [graph1Rename,graph2Rename,graph3Rename,numeralRename,
   OriginalContextInsertionSyntaxProof.lengthRename,OriginalContextInsertion.Below,
   InternalOriginalOrderSyntaxProof.orderRename] at hsL' hsR' hp' hn' hl' hb' hd' hdel' heL' heR'
 rw [EvaluatorErasureSyntax.admittedRename]
 exact EvaluatorErasureQueries.atCommon R H G M W
   (left.relabel j) (right.relabel j) (erasedLeft.relabel j) (erasedRight.relabel j) (parameter.relabel j) (erasedParameter.relabel j) (c.relabel j) (gamma.relabel j) (deleted.relabel j) (count.relabel j) (cutoff.relabel j) (d.relabel j) common
   hsL' hsR' (andLeft hcommon) (andRight hcommon) hp' hn' hl' hb' hd' hdel' heL' heR'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureProof
