module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureObservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureRowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureCore
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atCoordinates (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right erasedLeft erasedRight parameter erasedParameter c gamma deleted count cutoff d common inner rootBase rootRecursive row cell : OTerm alpha)
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
 (houter : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing common rootBase inner)))
 (hinner : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner rootRecursive row)))
 (hcell : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup cell cutoff row))) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W erasedLeft erasedRight erasedParameter)) := by
 let Q := OriginalHereditaryEvaluatorDefinitions.evaluator R
 have hrowL := EvaluatorErasureRowProof.rowAt R H G M W left parameter common inner rootBase rootRecursive row hsL hvL houter hinner
 have hrowR := EvaluatorErasureRowProof.rowAt R H G M W right parameter common inner rootBase rootRecursive row hsR hvR houter hinner
 have hobsL := EvaluatorErasureRowProof.cellAt Q left parameter c gamma count cutoff row cell hp hl hb hrowL hcell
 have hobsR := EvaluatorErasureRowProof.cellAt Q right parameter c gamma count cutoff row cell hp hl hb hrowR hcell
 have houtL := EvaluatorErasureObservationProof.actualCell Q left erasedLeft parameter erasedParameter c gamma deleted cutoff d cell
   hp hn hd hdel heL hobsL
 have houtR := EvaluatorErasureObservationProof.actualCell Q right erasedRight parameter erasedParameter c gamma deleted cutoff d cell
   hp hn hd hdel heR hobsR
 obtain ⟨hinsLaw⟩ := OriginalAllPositionContextDeleteInductionProof.actualDeletionInsertion body alpha Delta count gamma cutoff deleted d
 obtain ⟨hinsFields⟩ := andIntro hl (andIntro hb (andIntro hdel hd))
 have hins := Nonempty.intro (Derivation.implicationElimination hinsLaw hinsFields)
 have hsNewL := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta H G M W
   left erasedLeft d cutoff deleted gamma c parameter erasedParameter hins heL hp hn hsL
 have hsNewR := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta H G M W
   right erasedRight d cutoff deleted gamma c parameter erasedParameter hins heR hp hn hsR
 exact andIntro hsNewL (andIntro hsNewR
   (EvaluatorErasureSyntax.sameIntro R erasedLeft erasedRight erasedParameter cell (andIntro houtL houtR)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureCore
