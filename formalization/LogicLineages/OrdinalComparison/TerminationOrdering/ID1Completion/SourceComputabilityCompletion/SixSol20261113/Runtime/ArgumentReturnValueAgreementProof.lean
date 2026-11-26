module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedValueTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackCore
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AppendIdentityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnValueAgreementProof
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
theorem withStates (R : Program 2) (frame produced left right work input ls rs lo ro : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R frame produced left)))
 (hr : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R frame produced right)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame (numeral 0))))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work produced)))
 (hls : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode ls left (numeral 0))))
 (hrs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rs right (numeral 0))))
 (hlo : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lo (numeral 0) ls)))
 (hro : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ro (numeral 0) rs))) :
 Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn left right)) := by
 have ha := SixSol20261112.Context.AppendIdentityProof.actualRightZero body alpha Delta produced
 have lr := UniformReturnSyntax.frameApply R frame produced left (numeral 0) (numeral 0) work produced input ls lo hl
   (andIntro hw (andIntro ha (andIntro hi (andIntro hls hlo))))
 have rr := UniformReturnSyntax.frameApply R frame produced right (numeral 0) (numeral 0) work produced input rs ro hr
   (andIntro hw (andIntro ha (andIntro hi (andIntro hrs hro))))
 have he := SixSol20261112.Runtime.CompletedAgreementProof.actualCompletedAgreement R body alpha Delta
   (numeral 1) (numeral 1) input lo ro lr (pairLeft lo (numeral 0) ls hlo) rr (pairLeft ro (numeral 0) rs hro)
 have hlo' := outputTransport InternalPairing.pairing lo ro (Fin.cons (numeral 0) (Fin.cons ls Fin.elim0)) he hlo
 have hs := valueUnique InternalUnpair.right ls rs (Fin.cons ro Fin.elim0)
   (pairRight ro (numeral 0) ls hlo') (pairRight ro (numeral 0) rs hro)
 have hls' := outputTransport InternalListCodec.consCode ls rs (Fin.cons left (Fin.cons (numeral 0) Fin.elim0)) hs hls
 exact valueUnique InternalListCodec.headCode left right (Fin.cons rs Fin.elim0)
   (InternalRawListRecursionSupportProof.consHead rs left (numeral 0) hls')
   (InternalRawListRecursionSupportProof.consHead rs right (numeral 0) hrs)
theorem agreement (R : Program 2) (frame produced left right : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R frame produced left)))
 (hr : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R frame produced right))) :
 Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn left right)) := by
 let zeroP : Program 4 := OriginalRawSyntaxTransport.constant 4 0
 let workP : Program 4 := consOf (.projection 0) zeroP
 let inputP : Program 4 := pairOf workP (.projection 1)
 let lsP : Program 4 := consOf (.projection 2) zeroP
 let rsP : Program 4 := consOf (.projection 3) zeroP
 let loP : Program 4 := pairOf zeroP lsP
 let roP : Program 4 := pairOf zeroP rsP
 let qs : Fin 6 → Program 4 := ![workP,inputP,lsP,rsP,loP,roP]
 let xs : Fin 4 → OTerm alpha := ![frame,produced,left,right]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hinc hg
 let xx : Fin 4 → OTerm beta := ![frame.relabel j,produced.relabel j,left.relabel j,right.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
 rw [hx] at hg
 have hz : Nonempty (Derivation body Theta (programGraph zeroP (numeral 0) xx)) := OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx
 have hw := binaryRecover InternalListCodec.consCode (.projection 0) zeroP (ys 0) (frame.relabel j) (numeral 0) xx (hg 0) (projectionValue 0 xx) hz
 have hi := binaryRecover InternalPairing.pairing workP (.projection 1) (ys 1) (ys 0) (produced.relabel j) xx (hg 1) (hg 0) (projectionValue 1 xx)
 have hls := binaryRecover InternalListCodec.consCode (.projection 2) zeroP (ys 2) (left.relabel j) (numeral 0) xx (hg 2) (projectionValue 2 xx) hz
 have hrs := binaryRecover InternalListCodec.consCode (.projection 3) zeroP (ys 3) (right.relabel j) (numeral 0) xx (hg 3) (projectionValue 3 xx) hz
 have hlo := binaryRecover InternalPairing.pairing zeroP lsP (ys 4) (numeral 0) (ys 2) xx (hg 4) hz (hg 2)
 have hro := binaryRecover InternalPairing.pairing zeroP rsP (ys 5) (numeral 0) (ys 3) xx (hg 5) hz (hg 3)
 have hl' := renameInto hl j Theta hinc
 have hr' := renameInto hr j Theta hinc
 rw [UniformReturnSyntax.frameRename] at hl' hr'
 rw [eqnRelabel]
 exact withStates R (frame.relabel j) (produced.relabel j) (left.relabel j) (right.relabel j)
   (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) hl' hr' hw hi hls hrs hlo hro
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnValueAgreementProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnValueAgreementProof
