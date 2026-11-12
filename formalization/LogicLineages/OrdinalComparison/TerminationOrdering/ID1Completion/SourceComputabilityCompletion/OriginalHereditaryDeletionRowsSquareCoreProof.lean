module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof
open InternalOriginalUniformVertexPathSupportProof (ternaryRecover)
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open OriginalClassContextAllPositionObserver
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atCoordinates (Q : Program 2) (gamma count i j c parameter input upper upperParameter lower lowerParameter upperRow lowerRow upperValue lowerValue a b u l ul lu xl xr pl pr : OTerm alpha)
 (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (suc count) gamma)))
 (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Below i (suc j))))
 (hj : Nonempty (Derivation body Delta (OriginalContextInsertion.Below (suc j) (suc count))))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (heU : Nonempty (Derivation body Delta (graph3 erasedPacked upper (suc j) input parameter)))
 (hpU : Nonempty (Derivation body Delta (graph3 erasedParameter upperParameter (suc j) input parameter)))
 (heL : Nonempty (Derivation body Delta (graph3 erasedPacked lower i input parameter)))
 (hpL : Nonempty (Derivation body Delta (graph3 erasedParameter lowerParameter i input parameter)))
 (hrU : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) upperRow upper upperParameter)))
 (hrL : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) lowerRow lower lowerParameter)))
 (hvU : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup upperValue i upperRow)))
 (hvL : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup lowerValue j lowerRow)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup a i gamma)))
 (hb : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup b (suc j) gamma)))
 (hu : Nonempty (Derivation body Delta (graph2 deleteAt u (suc j) gamma)))
 (hl : Nonempty (Derivation body Delta (graph2 deleteAt l i gamma)))
 (hul : Nonempty (Derivation body Delta (graph2 deleteAt ul i u)))
 (hlu : Nonempty (Derivation body Delta (graph2 deleteAt lu j l)))
 (hxl : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw xl a i upper)))
 (hxr : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw xr b j lower)))
 (hpl : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pl c ul)))
 (hpr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pr c lu)))
 :
 Nonempty (Derivation body Delta (equal upperValue lowerValue ⊓ (OriginalContextInsertion.lengthGraph count upperRow ⊓ OriginalContextInsertion.lengthGraph count lowerRow))) := by
 have firstU := OriginalHereditaryDeletionRowsSquareSupportProof.selectorsRecover (suc j) input parameter c gamma b u upper upperParameter hp hb hu heU hpU
 have firstL := OriginalHereditaryDeletionRowsSquareSupportProof.selectorsRecover i input parameter c gamma a l lower lowerParameter hp ha hl heL hpL
 have hcontexts := andIntro hlen (andIntro hi (andIntro hj (andIntro ha (andIntro hb (andIntro hu (andIntro hul (andIntro hl hlu)))))))
 have hraw := andIntro firstU.1 (andIntro hxl (andIntro firstL.1 (andIntro hxr (andIntro hpl hpr))))
 have hfields := andIntro hcontexts hraw
 have sq := OriginalTwoDeletionParameterProof.inputSquare gamma (suc count) i j a b u l ul lu input upper lower xl xr c pl pr hfields
 have lookU := andLeft (andRight (andRight sq))
 have lookL := andRight (andRight (andRight sq))
 have bounds := OriginalHereditaryDeletionRowsSquareSupportProof.ranges i j count hi hj
 have originalI := InternalSquareRootArithmeticSupportProof.strictTrans i (suc j) (suc count) hi hj
 have lenU := OriginalAllPositionContextDeleteLengthProof.deleteLength gamma count (suc j) u hlen hj hu
 have lenL := OriginalAllPositionContextDeleteLengthProof.deleteLength gamma count i l hlen originalI hl
 have rowsU := OriginalHereditaryDeletionRowsSquareSupportProof.rowExpose Q count upper upperParameter c u i upperRow upperValue firstU.2 lenU bounds.1 hrU hvU
 have rowsL := OriginalHereditaryDeletionRowsSquareSupportProof.rowExpose Q count lower lowerParameter c l j lowerRow lowerValue firstL.2 lenL bounds.2 hrL hvL
 have secondU := OriginalHereditaryDeletionRowsSquareSupportProof.selectorsIntro i upper upperParameter c u a ul xl pl firstU.2 lookU hul hxl hpl
 have secondL := OriginalHereditaryDeletionRowsSquareSupportProof.selectorsIntro j lower lowerParameter c l b lu xr pr firstL.2 lookL hlu hxr hpr
 have qU := binaryRecover Q erasedPacked erasedParameter upperValue xl pl ![i,upper,upperParameter] rowsU.1 secondU.1 secondU.2
 have qL := binaryRecover Q erasedPacked erasedParameter lowerValue xr pr ![j,lower,lowerParameter] rowsL.1 secondL.1 secondL.2
 obtain ⟨ht⟩ := OriginalTwoDeletionParameterProof.actualObservationSquare Q body alpha Delta gamma (suc count) i j a b u l ul lu input upper lower xl xr c pl pr upperValue lowerValue
 obtain ⟨hh⟩ := andIntro hfields (andIntro qU qL)
 have hv : Nonempty (Derivation body Delta (equal upperValue lowerValue)) := ⟨Derivation.implicationElimination ht hh⟩
 exact andIntro hv (andIntro rowsU.2 rowsL.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsSquareCoreProof
