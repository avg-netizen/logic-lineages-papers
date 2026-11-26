module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsConsCore
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.JobCompletionSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsConsQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Runtime ContentVisitsDefinitions ContentVisitsSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atCounts (R : Program 2) (job frame tagged tailTagged headCount value tailCount tailProduced forward tailForward produced : OTerm alpha)
 (hh : Nonempty (Derivation body Delta
   (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job headCount value)))
 (ht : Nonempty (Derivation body Delta
   (PrefixFrameDefinitions.PrefixFrame R tailTagged tailCount tailProduced)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame z job)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tagged frame tailTagged)))
 (hforward : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode forward value tailForward)))
 (hrt : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse tailProduced tailForward)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse produced forward))) :
 Nonempty (Derivation body Delta (Counted R tagged produced)) := by
 let zeroP : Program 3 := OriginalRawSyntaxTransport.constant 3 0
 let sf : Program 3 := consOf (.projection 0) zeroP
 let sv : Program 3 := consOf (.projection 1) zeroP
 let app : Program 3 := .composition InternalApplicationValidityStackAppend.append ![.projection 2,sv]
 let qs : Fin 3 → Program 3 := ![sf,sv,app]
 let xs : Fin 3 → OTerm alpha := ![frame,value,tailProduced]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta ys hinc hg
 let xx : Fin 3 → OTerm beta := ![frame.relabel j,value.relabel j,tailProduced.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hg
 have hh' := renameInto hh j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hc' := renameInto hc j Theta hinc
 have hforward' := renameInto hforward j Theta hinc
 have hrt' := renameInto hrt j Theta hinc
 have hr' := renameInto hr j Theta hinc
 simp only [JobFrameSyntax.frameRename,PrefixFrameSyntax.frameRename,graph1Rename,graph2Rename,zRelabel]
   at hh' ht' hf' hc' hforward' hrt' hr'
 have hz : Nonempty (Derivation body Theta (programGraph zeroP z xx)) :=
   OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx
 have hsf := binaryRecover InternalListCodec.consCode (.projection 0) zeroP
   (ys 0) (frame.relabel j) z xx (hg 0) (projectionValue 0 xx) hz
 have hsv := binaryRecover InternalListCodec.consCode (.projection 1) zeroP
   (ys 1) (value.relabel j) z xx (hg 1) (projectionValue 1 xx) hz
 have ha := binaryRecover InternalApplicationValidityStackAppend.append (.projection 2) sv
   (ys 2) (tailProduced.relabel j) (ys 1) xx (hg 2) (projectionValue 2 xx) (hg 1)
 rw [countedRename]
 exact ContentVisitsConsCore.atValues R
   (job.relabel j) (frame.relabel j) (tagged.relabel j) (tailTagged.relabel j) (headCount.relabel j) (value.relabel j) (tailCount.relabel j) (tailProduced.relabel j)
   (ys 0) (ys 1) (ys 2) (forward.relabel j) (tailForward.relabel j) (produced.relabel j)
   hh' ht' hf' hc' hsf hsv ha hforward' hrt' hr'
theorem assemble (R : Program 2) (job frame tagged tailTagged headCount value tailProduced forward tailForward produced : OTerm alpha)
 (hh : Nonempty (Derivation body Delta
   (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job headCount value)))
 (ht : Nonempty (Derivation body Delta
   (Counted R tailTagged tailProduced)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame z job)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tagged frame tailTagged)))
 (hforward : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode forward value tailForward)))
 (hrt : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse tailProduced tailForward)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse produced forward))) :
 Nonempty (Derivation body Delta (Counted R tagged produced)) := by
 apply countedCases R tailTagged tailProduced _ ht
 intro beta j Theta tailCount hinc htail
 have hh' := renameInto hh j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hc' := renameInto hc j Theta hinc
 have hforward' := renameInto hforward j Theta hinc
 have hrt' := renameInto hrt j Theta hinc
 have hr' := renameInto hr j Theta hinc
 simp only [JobFrameSyntax.frameRename,graph1Rename,graph2Rename,zRelabel]
   at hh' hf' hc' hforward' hrt' hr'
 rw [countedRename]
 exact atCounts R (job.relabel j) (frame.relabel j) (tagged.relabel j) (tailTagged.relabel j) (headCount.relabel j) (value.relabel j) tailCount (tailProduced.relabel j) (forward.relabel j) (tailForward.relabel j) (produced.relabel j) hh' htail hf' hc' hforward' hrt' hr'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsConsQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsConsQueries
