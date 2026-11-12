module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyObserverWiringProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalGraphComposition InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalOriginalUniformVertexPathSupportProof (ternaryValue)
open OriginalClassContextAllPositionObserver
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal observer wiring at actual shared context/erasure coordinates. -/
theorem components (R : Program 2)
 (cutoff value parameter context gamma erasedType deleted erased erasedParam keyValue rank : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup erasedType cutoff gamma)))
 (hd : Nonempty (Derivation body Delta (graph2 deleteAt deleted cutoff gamma)))
 (he : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erased erasedType cutoff value)))
 (hep : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedParam context deleted)))
 (hk : Nonempty (Derivation body Delta (graph2 R keyValue erased erasedParam)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erased))) :
 let xs : Fin 3 → OTerm alpha := Fin.cons cutoff (Fin.cons value (Fin.cons parameter Fin.elim0))
 Nonempty (Derivation body Delta (programGraph (.composition R ![erasedPacked,erasedParameter]) keyValue xs)) ∧
 Nonempty (Derivation body Delta (programGraph
   (.composition OriginalRawSyntaxTransport.variableRankPackedRaw (fun _ : Fin 1 => erasedPacked)) rank xs)) := by
 let xs : Fin 3 → OTerm alpha := Fin.cons cutoff (Fin.cons value (Fin.cons parameter Fin.elim0))
 have hleft := unaryValue InternalUnpair.left (.projection 2) context parameter xs
   (pairLeft parameter context gamma hp) (projectionValue 2 xs)
 have hright := unaryValue InternalUnpair.right (.projection 2) gamma parameter xs
   (pairRight parameter context gamma hp) (projectionValue 2 xs)
 have hlookup := binaryValue InternalRawListRecursion.lookup (.projection 0) (rightOf (.projection 2))
   erasedType cutoff gamma xs hl (projectionValue 0 xs) hright
 have hdelete := binaryValue deleteAt (.projection 0) (rightOf (.projection 2))
   deleted cutoff gamma xs hd (projectionValue 0 xs) hright
 have herased := ternaryValue OriginalRawSyntaxTransport.erasePackedRaw
   (.composition InternalRawListRecursion.lookup ![.projection 0,rightOf (.projection 2)])
   (.projection 0) (.projection 1) erased erasedType cutoff value xs he hlookup
   (projectionValue 0 xs) (projectionValue 1 xs)
 have hparameter := binaryValue InternalPairing.pairing (leftOf (.projection 2))
   (.composition deleteAt ![.projection 0,rightOf (.projection 2)]) erasedParam context deleted xs hep hleft hdelete
 exact ⟨binaryValue R erasedPacked erasedParameter keyValue erased erasedParam xs hk herased hparameter,
   unaryValue OriginalRawSyntaxTransport.variableRankPackedRaw erasedPacked rank erased xs hr herased⟩

theorem positionForward (R : Program 2)
 (cutoff value parameter context gamma erasedType deleted erased erasedParam keyValue rank mark : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup erasedType cutoff gamma)))
 (hd : Nonempty (Derivation body Delta (graph2 deleteAt deleted cutoff gamma)))
 (he : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erased erasedType cutoff value)))
 (hep : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedParam context deleted)))
 (hk : Nonempty (Derivation body Delta (graph2 R keyValue erased erasedParam)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erased)))
 (h : Nonempty (Derivation body Delta (graph3 (positionObservation R) mark cutoff value parameter))) :
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark keyValue rank)) := by
 have hc := components R cutoff value parameter context gamma erasedType deleted erased erasedParam keyValue rank hp hl hd he hep hk hr
 exact binaryRecover InternalPairing.pairing (.composition R ![erasedPacked,erasedParameter])
   (.composition OriginalRawSyntaxTransport.variableRankPackedRaw (fun _ : Fin 1 => erasedPacked))
   mark keyValue rank (Fin.cons cutoff (Fin.cons value (Fin.cons parameter Fin.elim0))) h hc.1 hc.2

theorem positionBackward (R : Program 2)
 (cutoff value parameter context gamma erasedType deleted erased erasedParam keyValue rank mark : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup erasedType cutoff gamma)))
 (hd : Nonempty (Derivation body Delta (graph2 deleteAt deleted cutoff gamma)))
 (he : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erased erasedType cutoff value)))
 (hep : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedParam context deleted)))
 (hk : Nonempty (Derivation body Delta (graph2 R keyValue erased erasedParam)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erased)))
 (h : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark keyValue rank))) :
 Nonempty (Derivation body Delta (graph3 (positionObservation R) mark cutoff value parameter)) := by
 have hc := components R cutoff value parameter context gamma erasedType deleted erased erasedParam keyValue rank hp hl hd he hep hk hr
 exact binaryValue InternalPairing.pairing (.composition R ![erasedPacked,erasedParameter])
   (.composition OriginalRawSyntaxTransport.variableRankPackedRaw (fun _ : Fin 1 => erasedPacked))
   mark keyValue rank (Fin.cons cutoff (Fin.cons value (Fin.cons parameter Fin.elim0))) h hc.1 hc.2

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyObserverWiringProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyObserverWiringProof
