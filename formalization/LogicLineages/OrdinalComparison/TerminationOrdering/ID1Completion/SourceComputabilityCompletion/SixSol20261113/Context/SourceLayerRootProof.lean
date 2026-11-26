module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SourceLayerRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedAllChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentAllChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SourceLayerRootProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open InternalAdditionLawsProof (add)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedRename)
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261113.Runtime SixSol20261113.Erasure
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalApplicationCertificateConstructorsSupportProof
theorem fromRoot (R : Program 2) (H : Program 1) (M W : Program 2)
 (packed typ raw parameter c gamma job typed rawJob B weight out : OTerm alpha)
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (haccept : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W z typ raw gamma c)))
 (hjob : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hjobGraph : Nonempty (Derivation body Delta (graph2 OriginalHereditaryEvaluatorDefinitions.job job packed parameter)))
 (hweight : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 : Nonempty (Derivation body Delta ((graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out packed parameter).iff (graph2 (OriginalHereditaryObservationLayer.layer R (OriginalHereditaryEvaluatorDefinitions.evaluator R)) out packed parameter))) := by
 let childP : Program 3 := .composition (OriginalRawSyntaxTransport.arityOf (.projection 0)) (fun _ : Fin 1 => .projection 1)
 let deletionP : Program 3 := .composition OriginalContextInsertion.length (fun _ : Fin 1 => .projection 2)
 let countsP : Program 3 := pairOf childP deletionP
 let payloadP : Program 3 := pairOf (.projection 0) countsP
 let oneP : Program 3 := OriginalRawSyntaxTransport.constant 3 1
 let frameP : Program 3 := pairOf oneP payloadP
 let jobsP : Program 3 := .composition OriginalHereditaryAnnotatedExpansion.expansion (fun _ : Fin 1 => .projection 0)
 let taggedP : Program 3 := .composition OriginalHereditaryVisitScheduler.tagVisits (fun _ : Fin 1 => jobsP)
 let mapP : Program 1 := InternalListMap.map (k := 0) (ChildContentDefinitions.observationFromJob (OriginalHereditaryEvaluatorDefinitions.evaluator R))
 let forwardP : Program 3 := .composition mapP (fun _ : Fin 1 => jobsP)
 let producedP : Program 3 := .composition OriginalTypedArgumentObservations.reverse (fun _ : Fin 1 => forwardP)
 let sizeP : Program 3 := .composition OriginalContextInsertion.length (fun _ : Fin 1 => jobsP)
 let qs : Fin 10 → Program 3 := ![childP,deletionP,countsP,payloadP,frameP,jobsP,taggedP,forwardP,producedP,sizeP]
 let xs : Fin 3 → OTerm alpha := ![job,raw,gamma]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hi hq
 let xx : Fin 3 → OTerm beta := ![job.relabel j,raw.relabel j,gamma.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hq
 have hchildren := unaryRecover (OriginalRawSyntaxTransport.arityOf (.projection 0)) (.projection 1)
   (ys 0) (raw.relabel j) xx (hq 0) (projectionValue 1 xx)
 have hdeletions := unaryRecover OriginalContextInsertion.length (.projection 2)
   (ys 1) (gamma.relabel j) xx (hq 1) (projectionValue 2 xx)
 have hcounts := binaryRecover InternalPairing.pairing childP deletionP (ys 2) (ys 0) (ys 1) xx (hq 2) (hq 0) (hq 1)
 have hpayload := binaryRecover InternalPairing.pairing (.projection 0) countsP (ys 3) (job.relabel j) (ys 2) xx (hq 3) (projectionValue 0 xx) (hq 2)
 have hone : Nonempty (Derivation body Theta (programGraph oneP (numeral 1) xx)) := OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 1 xx
 have hframe := binaryRecover InternalPairing.pairing oneP payloadP (ys 4) (numeral 1) (ys 3) xx (hq 4) hone (hq 3)
 have hjobs := unaryRecover OriginalHereditaryAnnotatedExpansion.expansion (.projection 0) (ys 5) (job.relabel j) xx (hq 5) (projectionValue 0 xx)
 have htagged := unaryRecover OriginalHereditaryVisitScheduler.tagVisits jobsP (ys 6) (ys 5) xx (hq 6) (hq 5)
 have hforward := unaryRecover mapP jobsP (ys 7) (ys 5) xx (hq 7) (hq 5)
 have hproduced := unaryRecover OriginalTypedArgumentObservations.reverse forwardP (ys 8) (ys 7) xx (hq 8) (hq 7)
 have hsize := unaryRecover OriginalContextInsertion.length jobsP (ys 9) (ys 5) xx (hq 9) (hq 5)
 have hpacked' := renameInto hpacked j Theta hi
 have hp' := renameInto hp j Theta hi
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have haccept' := renameInto haccept j Theta hi
 have hadm' := renameInto hadm j Theta hi
 have hjob' := renameInto hjob j Theta hi
 have hjobGraph' := renameInto hjobGraph j Theta hi
 have hweight' := renameInto hweight j Theta hi
 simp only [graph1Rename,graph2Rename,zRelabel,numeralRename,termAcceptedRename,admissibleRename,OriginalHereditaryInternalAgendaSyntaxProof.jobRename] at hpacked' hp' hj' ht' hr' haccept' hadm' hjob' hjobGraph' hweight'
 have hbelowComplete := SourceFramedProof.actualBelowCompletion R H M W body beta Theta (c.relabel j) (B.relabel j) (weight.relabel j)
 have hall := SourceFramedAllChildrenProof.allChildren R H M W (c.relabel j) (B.relabel j) (job.relabel j) (weight.relabel j)
   (ys 5) (ys 9) hbelowComplete hjob' hweight' hjobs hsize
 have hbelowContent := FramedContentProof.actualBelowContent R H M W body beta Theta (c.relabel j) (B.relabel j) (weight.relabel j)
 have hcontent := FramedContentAllChildrenProof.allChildren R H M W (c.relabel j) (B.relabel j) (job.relabel j) (weight.relabel j)
   (ys 5) (ys 9) hbelowContent hjob' hweight' hjobs hsize
 simp only [OriginalTypedDecoderTransportLogicalProof.iffRename,graph2Rename]
 exact SourceLayerRowsProof.fromRows R H M W
   (packed.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (job.relabel j) (typed.relabel j) (rawJob.relabel j) (B.relabel j)
   (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (out.relabel j) (ys 9)
   hpacked' hp' hj' ht' hr' haccept' hadm' hjob' hjobGraph'
   hchildren hdeletions hcounts hpayload hframe hjobs htagged hforward hproduced hsize hall hcontent
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SourceLayerRootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SourceLayerRootProof
