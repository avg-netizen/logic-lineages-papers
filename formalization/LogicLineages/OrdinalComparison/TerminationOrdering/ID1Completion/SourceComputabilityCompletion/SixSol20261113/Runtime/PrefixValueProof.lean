module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixValueTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AppendIdentityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CompletedAgreementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixValueProof
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
theorem withStates (R : Program 2) (tagged first second left right input lo ro : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R tagged first left)))
 (hr : Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R tagged second right)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input tagged (numeral 0))))
 (hlo : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lo (numeral 0) left)))
 (hro : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ro (numeral 0) right))) :
 Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn left right)) := by
 have ht := SixSol20261112.Context.AppendIdentityProof.actualRightZero body alpha Delta tagged
 have hleft := SixSol20261112.Context.AppendIdentityProof.actualRightZero body alpha Delta left
 have hright := SixSol20261112.Context.AppendIdentityProof.actualRightZero body alpha Delta right
 have lr := PrefixFrameSyntax.frameApply R tagged first left (numeral 0) (numeral 0) tagged input left lo hl
   (andIntro ht (andIntro hi (andIntro hleft hlo)))
 have rr := PrefixFrameSyntax.frameApply R tagged second right (numeral 0) (numeral 0) tagged input right ro hr
   (andIntro ht (andIntro hi (andIntro hright hro)))
 have he := SixSol20261112.Runtime.CompletedAgreementProof.actualCompletedAgreement R body alpha Delta
   first second input lo ro lr (pairLeft lo (numeral 0) left hlo) rr (pairLeft ro (numeral 0) right hro)
 have hlo' := outputTransport InternalPairing.pairing lo ro (Fin.cons (numeral 0) (Fin.cons left Fin.elim0)) he hlo
 exact valueUnique InternalUnpair.right left right (Fin.cons ro Fin.elim0)
   (pairRight ro (numeral 0) left hlo') (pairRight ro (numeral 0) right hro)
theorem actualProducedAgreement : PrefixValueTargets.ActualProducedAgreement := by
 intro R body alpha Delta tagged first second left right hl hr
 let zeroP : Program 3 := OriginalRawSyntaxTransport.constant 3 0
 let inputP : Program 3 := pairOf (.projection 0) zeroP
 let loP : Program 3 := pairOf zeroP (.projection 1)
 let roP : Program 3 := pairOf zeroP (.projection 2)
 let qs : Fin 3 → Program 3 := ![inputP,loP,roP]
 let xs : Fin 3 → OTerm alpha := ![tagged,left,right]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hinc hg
 let xx : Fin 3 → OTerm beta := ![tagged.relabel j,left.relabel j,right.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hg
 have hz : Nonempty (Derivation body Theta (programGraph zeroP (numeral 0) xx)) :=
   OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx
 have hi := binaryRecover InternalPairing.pairing (.projection 0) zeroP (ys 0) (tagged.relabel j) (numeral 0) xx (hg 0) (projectionValue 0 xx) hz
 have hlo := binaryRecover InternalPairing.pairing zeroP (.projection 1) (ys 1) (numeral 0) (left.relabel j) xx (hg 1) hz (projectionValue 1 xx)
 have hro := binaryRecover InternalPairing.pairing zeroP (.projection 2) (ys 2) (numeral 0) (right.relabel j) xx (hg 2) hz (projectionValue 2 xx)
 have hl' := renameInto hl j Theta hinc
 have hr' := renameInto hr j Theta hinc
 rw [PrefixFrameSyntax.frameRename] at hl' hr'
 rw [eqnRelabel]
 exact withStates R (tagged.relabel j) (first.relabel j) (second.relabel j) (left.relabel j) (right.relabel j)
   (ys 0) (ys 1) (ys 2) hl' hr' hi hlo hro
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixValueProof
