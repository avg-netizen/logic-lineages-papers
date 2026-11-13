module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnSupplierProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnGeometryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
attribute [local irreducible] programGraph
theorem fromGeometry (R Q : Program 2) (H : Program 1) (M W : Program 2) (job typed rawJob raw parameter gamma c children deletions counts payload frame produced value rawJobs annotatedPrefix childRow backwardChildren deletionPrefix : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed (numeral 0) rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (ha : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W (numeral 1) (numeral 0) raw gamma c)))
 (harity : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hf : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R frame produced value)))
 (hg : Nonempty (Derivation body Delta (ExpansionMapGeometryDefinitions.Geometry
   (SixSol20261113.Context.ChildContentDefinitions.observationFromJob Q) (numeral 1) (numeral 0) raw parameter children deletions produced rawJobs annotatedPrefix childRow backwardChildren deletionPrefix))) :
 Nonempty (Derivation body Delta (graph1 (SixSol20261113.Context.ChildContentDefinitions.observationFromJob Q) value job)) := by
 have he := andLeft (hg)
 have hscan := andLeft (andRight (hg))
 have hm := andLeft (andRight (andRight (hg)))
 have hlen := andLeft (andRight (andRight (andRight (hg))))
 have hrev := andLeft (andRight (andRight (andRight (andRight (hg)))))
 have hdel := andLeft (andRight (andRight (andRight (andRight (andRight (hg))))))
 have happend := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (hg)))))))
 have hfullLength := andRight (andRight (andRight (andRight (andRight (andRight (andRight (hg)))))))
 let zeroP : Program 3 := OriginalRawSyntaxTransport.constant 3 0
 let oneP : Program 3 := OriginalRawSyntaxTransport.constant 3 1
 let firstP : Program 3 := .composition InternalRawListRecursion.lookup ![zeroP,.projection 1]
 let secondP : Program 3 := .composition InternalRawListRecursion.lookup ![oneP,.projection 1]
 let rowP : Program 3 := .composition OriginalTypedArgumentObservations.reverse (fun _ : Fin 1 => .projection 2)
 let packedP : Program 3 := pairOf zeroP (.projection 0)
 let qs : Fin 6 → Program 3 := ![firstP,secondP,rowP,packedP,leftOf (.projection 0),rightOf (.projection 0)]
 let xs : Fin 3 → OTerm alpha := ![raw,childRow,deletionPrefix]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hi hq
 let xx : Fin 3 → OTerm beta := ![raw.relabel j,childRow.relabel j,deletionPrefix.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hq
 have hz : Nonempty (Derivation body Theta (programGraph zeroP (numeral 0) xx)) := OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx
 have hone : Nonempty (Derivation body Theta (programGraph oneP (numeral 1) xx)) := OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 1 xx
 have hfirst := binaryRecover InternalRawListRecursion.lookup zeroP (.projection 1) (ys 0) (numeral 0) (childRow.relabel j) xx (hq 0) hz (projectionValue 1 xx)
 have hsecond := binaryRecover InternalRawListRecursion.lookup oneP (.projection 1) (ys 1) (numeral 1) (childRow.relabel j) xx (hq 1) hone (projectionValue 1 xx)
 have hrow := unaryRecover OriginalTypedArgumentObservations.reverse (.projection 2) (ys 2) (deletionPrefix.relabel j) xx (hq 2) (projectionValue 2 xx)
 have hpacked := binaryRecover InternalPairing.pairing zeroP (.projection 0) (ys 3) (numeral 0) (raw.relabel j) xx (hq 3) hz (projectionValue 0 xx)
 have hleft := unaryRecover InternalUnpair.left (.projection 0) (ys 4) (raw.relabel j) xx (hq 4) (projectionValue 0 xx)
 have hright := unaryRecover InternalUnpair.right (.projection 0) (ys 5) (raw.relabel j) xx (hq 5) (projectionValue 0 xx)
 have htag := reconstructPair (raw.relabel j) (ys 4) (ys 5) hleft hright
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have ha' := renameInto ha j Theta hi
 have harity' := renameInto harity j Theta hi
 have hc' := renameInto hc j Theta hi
 have hp' := renameInto hp j Theta hi
 have hframe' := renameInto hframe j Theta hi
 have hf' := renameInto hf j Theta hi
 have he' := renameInto he j Theta hi
 have hscan' := renameInto hscan j Theta hi
 have hm' := renameInto hm j Theta hi
 have hlen' := renameInto hlen j Theta hi
 have hrev' := renameInto hrev j Theta hi
 have hdel' := renameInto hdel j Theta hi
 have happend' := renameInto happend j Theta hi
 have hfullLength' := renameInto hfullLength j Theta hi
 simp only [graph1Rename,graph2Rename,graph5Rename,numeralRename,UniformReturnSyntax.frameRename,OriginalInternalJobAdmissibleTransportSyntaxProof.admissibleRename,OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel] at hj' ht' hr' ha' harity' hc' hp' hframe' hf' he' hscan' hm' hlen' hrev' hdel' happend' hfullLength'
 have hs := ArgumentReturnSupplierProof.fromRows (raw.relabel j) (children.relabel j) (deletions.relabel j) (produced.relabel j) (childRow.relabel j) (backwardChildren.relabel j) (deletionPrefix.relabel j) (ys 0) (ys 1) (ys 2) harity' hfullLength' hlen' hrev' hdel' happend' hrow hfirst hsecond
 have hsemantic := ArgumentReturnDispatchProof.atSupplier R Q H M W (job.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (produced.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 5) (value.relabel j) (gamma.relabel j) (c.relabel j) (ys 4) (rawJobs.relabel j) (annotatedPrefix.relabel j) (childRow.relabel j) hj' ht' hr' hc' hp' hframe' hpacked hf' ha' htag he' hscan' hm' hlen' hfirst hsecond harity' hs
 rw [graph1Rename]
 exact ArgumentChildContentProof.observed Q (job.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (value.relabel j) hj' ht' hr' hsemantic

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnGeometryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnGeometryProof
