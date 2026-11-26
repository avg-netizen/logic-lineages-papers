module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsScanLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyObserverWiringProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalUniformVertexPathSupportProof (ternaryRecover ternaryValue)
open OriginalClassContextAllPositionObserver
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem ranges (i j count : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Below i (InternalTagArithmeticSyntaxProof.suc j))))
 (hj : Nonempty (Derivation body Delta (OriginalContextInsertion.Below (InternalTagArithmeticSyntaxProof.suc j) (InternalTagArithmeticSyntaxProof.suc count)))) :
 Nonempty (Derivation body Delta (OriginalContextInsertion.Below i count)) ∧
 Nonempty (Derivation body Delta (OriginalContextInsertion.Below j count)) := by
 have hb := OriginalContextInsertionBelowCoreProof.successorStrict j count hj
 exact ⟨InternalOriginalPairingOrderArithmeticProof.weakStrictTrans i j count hi hb,hb⟩

/-- Recover the literal unwrapped erasure from actual all-position selectors.
The lookup and deletion witnesses will be queried, not final target premises. -/
theorem selectorsRecover (cutoff input parameter c gamma typ deleted erased erasedParam : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup typ cutoff gamma)))
 (hd : Nonempty (Derivation body Delta (graph2 deleteAt deleted cutoff gamma)))
 (he : Nonempty (Derivation body Delta (graph3 erasedPacked erased cutoff input parameter)))
 (hep : Nonempty (Derivation body Delta (graph3 erasedParameter erasedParam cutoff input parameter))) :
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erased typ cutoff input)) ∧
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedParam c deleted)) := by
 let xs : Fin 3 → OTerm alpha := ![cutoff,input,parameter]
 have hleft := unaryValue InternalUnpair.left (.projection 2) c parameter xs
  (pairLeft parameter c gamma hp) (projectionValue 2 xs)
 have hright := unaryValue InternalUnpair.right (.projection 2) gamma parameter xs
  (pairRight parameter c gamma hp) (projectionValue 2 xs)
 have hlookup := binaryValue InternalRawListRecursion.lookup (.projection 0) (rightOf (.projection 2)) typ cutoff gamma xs hl (projectionValue 0 xs) hright
 have hdelete := binaryValue deleteAt (.projection 0) (rightOf (.projection 2)) deleted cutoff gamma xs hd (projectionValue 0 xs) hright
 have herase := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw
  (.composition InternalRawListRecursion.lookup ![.projection 0,rightOf (.projection 2)])
  (.projection 0) (.projection 1) erased typ cutoff input xs he hlookup (projectionValue 0 xs) (projectionValue 1 xs)
 have hparameter := binaryRecover InternalPairing.pairing (leftOf (.projection 2))
  (.composition deleteAt ![.projection 0,rightOf (.projection 2)]) erasedParam c deleted xs hep hleft hdelete
 exact ⟨herase,hparameter⟩

theorem selectorsIntro (cutoff input parameter c gamma typ deleted erased erasedParam : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup typ cutoff gamma)))
 (hd : Nonempty (Derivation body Delta (graph2 deleteAt deleted cutoff gamma)))
 (he : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erased typ cutoff input)))
 (hep : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedParam c deleted))) :
 Nonempty (Derivation body Delta (graph3 erasedPacked erased cutoff input parameter)) ∧
 Nonempty (Derivation body Delta (graph3 erasedParameter erasedParam cutoff input parameter)) := by
 let xs : Fin 3 → OTerm alpha := ![cutoff,input,parameter]
 have hleft := unaryValue InternalUnpair.left (.projection 2) c parameter xs
  (pairLeft parameter c gamma hp) (projectionValue 2 xs)
 have hright := unaryValue InternalUnpair.right (.projection 2) gamma parameter xs
  (pairRight parameter c gamma hp) (projectionValue 2 xs)
 have hlookup := binaryValue InternalRawListRecursion.lookup (.projection 0) (rightOf (.projection 2)) typ cutoff gamma xs hl (projectionValue 0 xs) hright
 have hdelete := binaryValue deleteAt (.projection 0) (rightOf (.projection 2)) deleted cutoff gamma xs hd (projectionValue 0 xs) hright
 have herase := ternaryValue OriginalRawSyntaxTransport.erasePackedRaw
  (.composition InternalRawListRecursion.lookup ![.projection 0,rightOf (.projection 2)])
  (.projection 0) (.projection 1) erased typ cutoff input xs he hlookup (projectionValue 0 xs) (projectionValue 1 xs)
 have hparameter := binaryValue InternalPairing.pairing (leftOf (.projection 2))
  (.composition deleteAt ![.projection 0,rightOf (.projection 2)]) erasedParam c deleted xs hep hleft hdelete
 exact ⟨herase,hparameter⟩

/-- A literal row lookup supplies its actual cell observation and row length. -/
theorem rowExpose (Q : Program 2) (count input parameter c gamma cutoff row value : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count gamma)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) row input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value cutoff row))) :
 Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation Q) value cutoff input parameter)) ∧
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count row)) := by
 have hs := OriginalHereditaryDeletionRowsBoundProof.scanFromRows Q input parameter gamma count row (pairRight parameter c gamma hp) hl hr
 obtain ⟨hi⟩ := OriginalHereditaryDeletionRowsIndexedProof.actualIndexed Q body alpha Delta count input parameter row cutoff value
 obtain ⟨hh⟩ := andIntro hb (andIntro hs hv)
 exact ⟨⟨Derivation.implicationElimination hi hh⟩, OriginalHereditaryDeletionRowsScanLengthProof.scanLength Q count input parameter row hs⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareSupportProof
