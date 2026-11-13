module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureCore
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureObservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureRowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureQueries
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
theorem atCommon (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right erasedLeft erasedRight parameter erasedParameter c gamma deleted count cutoff d common : OTerm alpha)
 (hsL : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hsR : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (hvL : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) common left parameter)))
 (hvR : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) common right parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedParameter c deleted)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count gamma)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)))
 (hd : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d cutoff gamma)))
 (hdel : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma)))
 (heL : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedLeft d cutoff left)))
 (heR : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedRight d cutoff right)))
 :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W erasedLeft erasedRight erasedParameter)) := by
 let baseP : Program 2 := leftOf (.projection 0)
 let innerP : Program 2 := rightOf (.projection 0)
 let recursiveP : Program 2 := leftOf innerP
 let rowP : Program 2 := rightOf innerP
 let cellP : Program 2 := .composition InternalRawListRecursion.lookup ![.projection 1,rowP]
 let qs : Fin 5 → Program 2 := ![baseP,innerP,recursiveP,rowP,cellP]
 let xs : Fin 2 → OTerm alpha := ![common,cutoff]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta ys hinc hg
 let xx : Fin 2 → OTerm beta := ![common.relabel j,cutoff.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hg
 have hsL' := renameInto hsL j Theta hinc
 have hsR' := renameInto hsR j Theta hinc
 have hvL' := renameInto hvL j Theta hinc
 have hvR' := renameInto hvR j Theta hinc
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
   InternalOriginalOrderSyntaxProof.orderRename] at hsL' hsR' hvL' hvR' hp' hn' hl' hb' hd' hdel' heL' heR'
 have hbase := unaryRecover InternalUnpair.left (.projection 0) (ys 0) (common.relabel j) xx (hg 0) (projectionValue 0 xx)
 have hinner := unaryRecover InternalUnpair.right (.projection 0) (ys 1) (common.relabel j) xx (hg 1) (projectionValue 0 xx)
 have hrecursive := unaryRecover InternalUnpair.left innerP (ys 2) (ys 1) xx (hg 2) (hg 1)
 have hrow := unaryRecover InternalUnpair.right innerP (ys 3) (ys 1) xx (hg 3) (hg 1)
 have houterPair := reconstructPair (common.relabel j) (ys 0) (ys 1) hbase hinner
 have hinnerPair := reconstructPair (ys 1) (ys 2) (ys 3) hrecursive hrow
 have hcell := binaryRecover InternalRawListRecursion.lookup (.projection 1) rowP
   (ys 4) (cutoff.relabel j) (ys 3) xx (hg 4) (projectionValue 1 xx) (hg 3)
 rw [EvaluatorErasureSyntax.admittedRename]
 exact EvaluatorErasureCore.atCoordinates R H G M W
   (left.relabel j) (right.relabel j) (erasedLeft.relabel j) (erasedRight.relabel j) (parameter.relabel j) (erasedParameter.relabel j) (c.relabel j) (gamma.relabel j) (deleted.relabel j) (count.relabel j) (cutoff.relabel j) (d.relabel j) (common.relabel j) (ys 1) (ys 0) (ys 2) (ys 3) (ys 4)
   hsL' hsR' hvL' hvR' hp' hn' hl' hb' hd' hdel' heL' heR' houterPair hinnerPair hcell
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureQueries
