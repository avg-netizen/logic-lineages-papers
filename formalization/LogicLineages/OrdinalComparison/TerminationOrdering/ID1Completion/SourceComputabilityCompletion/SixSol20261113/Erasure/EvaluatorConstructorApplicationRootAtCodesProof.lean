module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationRawQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootAtCodesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem actualRoot (Q : Program 2)
 (arrow d e fp ap fn arg parent parameter fv av fo ao obs td data candidate : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent)))
 (hf : Nonempty (Derivation body Delta (graph2 Q fv fn parameter)))
 (ha : Nonempty (Derivation body Delta (graph2 Q av arg parameter)))
 (hfo : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fo arrow fv)))
 (hao : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ao d av)))
 (hobs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing obs fo ao)))
 (htd : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing td e obs)))
 (hdata : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data d td)))
 (hcan : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate (numeral 2) data))) :
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) candidate parent parameter)) := by
 apply RankCalibrationApplicationRawQueries.actualCases arrow d e fp ap fn arg parent _ hc
 intro beta j Theta raw middle children hj hPacked hRaw hPayload hChildren
 rw [graph2Rename]
 have hc' := renameInto hc j Theta hj
 have hf' := renameInto hf j Theta hj
 have ha' := renameInto ha j Theta hj
 have hfo' := renameInto hfo j Theta hj
 have hao' := renameInto hao j Theta hj
 have hobs' := renameInto hobs j Theta hj
 have htd' := renameInto htd j Theta hj
 have hdata' := renameInto hdata j Theta hj
 have hcan' := renameInto hcan j Theta hj
 simp only [InternalApplicationValidityClosure.applicationConstructors,conjunctionRename,
  graph2Rename,graph4Rename,GuardedSourceSyntaxProof.numeralRename] at hc' hf' ha' hfo' hao' hobs' htd' hdata' hcan'
 exact OriginalRootObservationInternalProof.applicationLaw Q body beta Theta
  (parent.relabel j) (parameter.relabel j) (e.relabel j) raw (d.relabel j) children middle
  (fp.relabel j) (ap.relabel j) (arrow.relabel j) (fn.relabel j) (arg.relabel j)
  (fv.relabel j) (av.relabel j) (fo.relabel j) (ao.relabel j) (obs.relabel j)
  (td.relabel j) (data.relabel j) (candidate.relabel j)
  hPacked hRaw hPayload hChildren (andLeft hc') (andLeft (andRight hc'))
  (andLeft (andRight (andRight hc'))) hf' ha' hfo' hao' hobs' htd' hdata' hcan'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootAtCodesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootAtCodesProof
