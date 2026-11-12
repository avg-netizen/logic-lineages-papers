module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalRawListRecursionProof InternalRawListRecursionSupportProof
open OriginalNumericListSort
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem baseValue (x singleton state : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton x z)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state z singleton))) :
 Nonempty (Derivation body Delta (graph1 insertBase state x)) := by
 let xs : Fin 1 → OTerm alpha := ![x]
 have hn := binaryValue InternalListCodec.consCode (.projection 0) InternalRawListRecursion.zero
   singleton x z xs hc (projectionValue 0 xs) (constantZero xs)
 exact binaryValue InternalPairing.pairing InternalRawListRecursion.zero
   (.composition InternalListCodec.consCode ![.projection 0,InternalRawListRecursion.zero])
   state z singleton xs hp (constantZero xs) hn

theorem insertNil (x singleton state : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton x z)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state z singleton))) :
 Nonempty (Derivation body Delta (graph2 insert singleton z x)) := by
 have hb := baseValue x singleton state hc hp
 have hs := nilValue insertBase insertStep state (Fin.cons x Fin.elim0) hb
 exact unaryValue InternalUnpair.right insertState singleton state ![z,x]
   (pairRight state z singleton hp) hs

theorem originalConsValue (head tail inserted previous code x : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing previous tail inserted)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail))) :
 Nonempty (Derivation body Delta (graph3 originalCons code head previous x)) := by
 let xs : Fin 3 → OTerm alpha := ![head,previous,x]
 have hl := unaryValue InternalUnpair.left (.projection (1 : Fin 3)) tail previous xs
   (pairLeft previous tail inserted hp) (projectionValue 1 xs)
 exact binaryValue InternalListCodec.consCode (.projection 0)
   (.composition InternalUnpair.left (fun _ : Fin 1 => .projection 1)) code head tail xs
   hc (projectionValue 0 xs) hl

theorem stepBefore (head tail inserted previous code x next state : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing previous tail inserted)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode next x code)))
 (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state code next)))
 (hlt : Nonempty (Derivation body Delta (graph2 InternalLessThan.ltTest z head x))) :
 Nonempty (Derivation body Delta (graph3 insertStep state head previous x)) := by
 let xs : Fin 3 → OTerm alpha := ![head,previous,x]
 have ho := originalConsValue head tail inserted previous code x hp hc
 have hb := binaryValue InternalListCodec.consCode (.projection 2) originalCons next x code xs
   hn (projectionValue 2 xs) ho
 have ht := binaryValue InternalLessThan.ltTest (.projection 0) (.projection 2) z head x xs
   hlt (projectionValue 0 xs) (projectionValue 2 xs)
 have hv := zeroBranchIntro (.composition InternalLessThan.ltTest ![.projection 0,.projection 2])
   beforeCons afterCons next xs ht hb
 exact binaryValue InternalPairing.pairing originalCons
   (InternalAcceptance.branch (.composition InternalLessThan.ltTest ![.projection 0,.projection 2]) beforeCons afterCons)
   state code next xs hpair ho hv

theorem stepAfter (head tail inserted previous code x next state k : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing previous tail inserted)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode next head inserted)))
 (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state code next)))
 (hlt : Nonempty (Derivation body Delta (graph2 InternalLessThan.ltTest (suc k) head x))) :
 Nonempty (Derivation body Delta (graph3 insertStep state head previous x)) := by
 let xs : Fin 3 → OTerm alpha := ![head,previous,x]
 have ho := originalConsValue head tail inserted previous code x hp hc
 have hr := unaryValue InternalUnpair.right (.projection (1 : Fin 3)) inserted previous xs
   (pairRight previous tail inserted hp) (projectionValue 1 xs)
 have hb := binaryValue InternalListCodec.consCode (.projection 0)
   (.composition InternalUnpair.right (fun _ : Fin 1 => .projection 1)) next head inserted xs
   hn (projectionValue 0 xs) hr
 have ht := binaryValue InternalLessThan.ltTest (.projection 0) (.projection 2) (suc k) head x xs
   hlt (projectionValue 0 xs) (projectionValue 2 xs)
 have hv := successorBranchIntro (.composition InternalLessThan.ltTest ![.projection 0,.projection 2])
   beforeCons afterCons next k xs ht hb
 exact binaryValue InternalPairing.pairing originalCons
   (InternalAcceptance.branch (.composition InternalLessThan.ltTest ![.projection 0,.projection 2]) beforeCons afterCons)
   state code next xs hpair ho hv

theorem insertFromState (code x state next : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 insertState state code x)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state code next))) :
 Nonempty (Derivation body Delta (graph2 insert next code x)) :=
 unaryValue InternalUnpair.right insertState next state ![code,x] (pairRight state code next hp) hs

theorem sortNil : Nonempty (Derivation body Delta (graph1 sort z z)) :=
 nilValue (InternalRawListRecursion.zero : Program 0) sortStep z Fin.elim0 (constantZero Fin.elim0)

theorem sortCons (code head tail sorted out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (hr : Nonempty (Derivation body Delta (graph1 sort sorted tail)))
 (hi : Nonempty (Derivation body Delta (graph2 insert out sorted head))) :
 Nonempty (Derivation body Delta (graph1 sort out code)) := by
 let xs : Fin 2 → OTerm alpha := ![head,sorted]
 have hs := binaryValue insert (.projection 1) (.projection 0) out sorted head xs
   hi (projectionValue 1 xs) (projectionValue 0 xs)
 exact consValue (InternalRawListRecursion.zero : Program 0) sortStep code head tail sorted out Fin.elim0 hc hr hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortValueProof
