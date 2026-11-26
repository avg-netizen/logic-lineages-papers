module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermQueries
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
attribute [local irreducible] programGraph
theorem evaluatorValue (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job packed parameter count value : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hgjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryEvaluatorDefinitions.job job packed parameter)))
 (hframe : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value))) :
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) value packed parameter)) := by
 let jobP : Program 2 := OriginalHereditaryEvaluatorDefinitions.job
 let zeroP : Program 2 := OriginalRawSyntaxTransport.constant 2 0
 let branchP : Program 2 := .composition OriginalHereditaryFuelProgram.branching (fun _ : Fin 1 => jobP)
 let visitP : Program 2 := pairOf zeroP jobP
 let workP : Program 2 := consOf visitP zeroP
 let qs : Fin 6 → Program 2 := ![branchP,OriginalHereditaryEvaluatorDefinitions.computedFuel,visitP,workP,OriginalHereditaryEvaluatorDefinitions.initial,OriginalHereditaryEvaluatorDefinitions.completed R]
 let xs : Fin 2 → OTerm alpha := ![packed,parameter]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hinc hg
 let xx : Fin 2 → OTerm beta := ![packed.relabel j,parameter.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hg
 have hj' := renameInto hj j Theta hinc
 have hgjob' := renameInto hgjob j Theta hinc
 have hframe' := renameInto hframe j Theta hinc
 rw [OriginalHereditaryInternalAgendaSyntaxProof.jobRename] at hj'
 rw [graph2Rename] at hgjob'
 rw [JobFrameSyntax.frameRename] at hframe'
 have hz : Nonempty (Derivation body Theta (programGraph zeroP (numeral 0) xx)) := OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx
 have hb := unaryRecover OriginalHereditaryFuelProgram.branching jobP (ys 0) (job.relabel j) xx (hg 0) hgjob'
 have hf := unaryRecover OriginalHereditaryFuelProgram.fuel jobP (ys 1) (job.relabel j) xx (hg 1) hgjob'
 have hv := binaryRecover InternalPairing.pairing zeroP jobP (ys 2) (numeral 0) (job.relabel j) xx (hg 2) hz hgjob'
 have hw := binaryRecover InternalListCodec.consCode visitP zeroP (ys 3) (ys 2) (numeral 0) xx (hg 3) (hg 2) hz
 have hi := binaryRecover InternalPairing.pairing workP zeroP (ys 4) (ys 3) (numeral 0) xx (hg 4) (hg 3) hz
 have hr := binaryRecover (OriginalHereditaryRuntimeIterationDefinitions.run R) OriginalHereditaryEvaluatorDefinitions.computedFuel OriginalHereditaryEvaluatorDefinitions.initial (ys 5) (ys 1) (ys 4) xx (hg 5) (hg 1) (hg 4)
 have he := FramedTermFuelProof.emptyAtFuel R H M W (c.relabel j) (B.relabel j) (job.relabel j) (ys 0) (ys 2) (ys 3) (ys 1) (ys 4) (ys 5) hj' hb hv hw hi hf hr
 rw [graph2Rename]
 exact FramedTermValueProof.fromFramed R (packed.relabel j) (parameter.relabel j) (job.relabel j) (ys 2) (ys 3) (ys 4) (count.relabel j) (value.relabel j) (ys 1) (ys 5) hv hw hi hframe' hr he (hg 5)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermQueries
