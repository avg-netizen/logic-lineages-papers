module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedValueTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackCore
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedValueAgreementProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem withStates (R : Program 2) (job first second left right frame work input ls rs lo ro : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job first left)))
 (hr : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job second right)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 0) job)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame (numeral 0))))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work (numeral 0))))
 (hls : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode ls left (numeral 0))))
 (hrs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rs right (numeral 0))))
 (hlo : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lo (numeral 0) ls)))
 (hro : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ro (numeral 0) rs))) :
 Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn left right)) := by
 have lr := JobFrameSyntax.frameApply R job first left (numeral 0) (numeral 0) frame work input ls lo hl
   (andIntro hf (andIntro hw (andIntro hi (andIntro hls hlo))))
 have rr := JobFrameSyntax.frameApply R job second right (numeral 0) (numeral 0) frame work input rs ro hr
   (andIntro hf (andIntro hw (andIntro hi (andIntro hrs hro))))
 have he := SixSol20261112.Runtime.CompletedAgreementProof.actualCompletedAgreement R body alpha Delta
   first second input lo ro lr (pairLeft lo (numeral 0) ls hlo) rr (pairLeft ro (numeral 0) rs hro)
 have hlo' := outputTransport InternalPairing.pairing lo ro (Fin.cons (numeral 0) (Fin.cons ls Fin.elim0)) he hlo
 have hs := valueUnique InternalUnpair.right ls rs (Fin.cons ro Fin.elim0)
   (pairRight ro (numeral 0) ls hlo') (pairRight ro (numeral 0) rs hro)
 have hls' := outputTransport InternalListCodec.consCode ls rs (Fin.cons left (Fin.cons (numeral 0) Fin.elim0)) hs hls
 exact valueUnique InternalListCodec.headCode left right (Fin.cons rs Fin.elim0)
   (InternalRawListRecursionSupportProof.consHead rs left (numeral 0) hls')
   (InternalRawListRecursionSupportProof.consHead rs right (numeral 0) hrs)
theorem actualFramedValueAgreement : FramedValueTargets.ActualFramedValueAgreement := by
 intro R body alpha Delta job first second left right hl hr
 let zeroP : Program 3 := OriginalRawSyntaxTransport.constant 3 0
 let frameP : Program 3 := pairOf zeroP (.projection 0)
 let workP : Program 3 := consOf frameP zeroP
 let inputP : Program 3 := pairOf workP zeroP
 let lsP : Program 3 := consOf (.projection 1) zeroP
 let rsP : Program 3 := consOf (.projection 2) zeroP
 let loP : Program 3 := pairOf zeroP lsP
 let roP : Program 3 := pairOf zeroP rsP
 let qs : Fin 7 → Program 3 := ![frameP,workP,inputP,lsP,rsP,loP,roP]
 let xs : Fin 3 → OTerm alpha := ![job,left,right]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hinc hg
 let xx : Fin 3 → OTerm beta := ![job.relabel j,left.relabel j,right.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hg
 have hz : Nonempty (Derivation body Theta (programGraph zeroP (numeral 0) xx)) :=
   OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx
 have hf := binaryRecover InternalPairing.pairing zeroP (.projection 0) (ys 0) (numeral 0) (job.relabel j) xx (hg 0) hz (projectionValue 0 xx)
 have hw := binaryRecover InternalListCodec.consCode frameP zeroP (ys 1) (ys 0) (numeral 0) xx (hg 1) (hg 0) hz
 have hi := binaryRecover InternalPairing.pairing workP zeroP (ys 2) (ys 1) (numeral 0) xx (hg 2) (hg 1) hz
 have hls := binaryRecover InternalListCodec.consCode (.projection 1) zeroP (ys 3) (left.relabel j) (numeral 0) xx (hg 3) (projectionValue 1 xx) hz
 have hrs := binaryRecover InternalListCodec.consCode (.projection 2) zeroP (ys 4) (right.relabel j) (numeral 0) xx (hg 4) (projectionValue 2 xx) hz
 have hlo := binaryRecover InternalPairing.pairing zeroP lsP (ys 5) (numeral 0) (ys 3) xx (hg 5) hz (hg 3)
 have hro := binaryRecover InternalPairing.pairing zeroP rsP (ys 6) (numeral 0) (ys 4) xx (hg 6) hz (hg 4)
 have hl' := renameInto hl j Theta hinc
 have hr' := renameInto hr j Theta hinc
 rw [JobFrameSyntax.frameRename] at hl' hr'
 rw [eqnRelabel]
 exact withStates R (job.relabel j) (first.relabel j) (second.relabel j) (left.relabel j) (right.relabel j)
   (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) hl' hr' hf hw hi hls hrs hlo hro
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedValueAgreementProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedValueAgreementProof
