module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationEndpointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationSurvivorProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open UniformCertificateCompletion OriginalRawObjectTransport OriginalRawSyntaxTransport
open OriginalVariableObjectSupportProof (bottomObjectAccept)
open OriginalVariableObjectSyntaxProof (bottomGraphRename)
open OriginalVariableErasureCertificateRawProof (equalRefl bottomCodePair bottomObjectPair bottomObjectRank eraseObjectPair)
open OriginalRawSyntaxTransportInternalPackedProof (erasePackedBackward)
open OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof (variableBackward bottomBackward)
open OriginalRawSyntaxTransportInternalVariableSupportProof (variableActionBackward)
open OriginalRawSyntaxTransportInternalVariableEraseLeafProof (eraseLeafAboveBackwardAt)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawObjectTransportInternalSyntaxProof
open OriginalErasureCertificateContinuation OriginalErasureCertificateContinuationTargets
open OriginalErasureCertificateContinuationSyntaxProof
open OriginalErasureCertificateContinuationEndpointProof (targetBottom variableRank endpointAt)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal successor variable erasure, proved inside PA. -/
theorem eraseSuccessor (raw out domain index : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor raw (suc index))))
    (ho : Nonempty (Derivation body Delta (graph1 variableConstructor out index))) :
    Nonempty (Derivation body Delta (graph3 eraseRaw out domain (numeral 0) raw)) :=
  variableBackward .erase raw out domain (numeral 0) (suc index) hv
    (variableActionBackward .erase raw out domain (numeral 0) (suc index) hv
      (eraseLeafAboveBackwardAt raw out domain (numeral 0) (suc index) index hv
        ⟨InternalQuotientComparisonProof.zeroLessSuccessor index⟩
        (InternalEqualityTestPredecessorProof.predecessorSuccessor index) ho))

/-- Build the frozen Object constructor from actual original pair graphs. -/
theorem variableObjectBuild (object typ gamma index packed raw : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing object gamma packed)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor raw index))) :
    Nonempty (Derivation body Delta (graph3 variableObjectCode object typ gamma index)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons typ (Fin.cons gamma (Fin.cons index Fin.elim0))
  let vr : Program 3 := .composition variableConstructor (fun _ : Fin 1 => .projection 2)
  have hr := unaryValue variableConstructor (.projection 2) raw index xs hv (projectionValue 2 xs)
  have hpacked := binaryValue InternalPairing.pairing (.projection 0) vr packed typ raw xs hp
    (projectionValue 0 xs) hr
  exact binaryValue InternalPairing.pairing (.projection 1) (pairOf (.projection 0) vr)
    object gamma packed xs ho (projectionValue 1 xs) hpacked

/-- Actual erasure output pairs are recovered; neither survivor shape nor
bottom target nor erased rank is assumed. -/
theorem survivorAt (tau : Ty)
    (source target gamma extended packed raw domain index erasedSource erasedTarget
      variableRaw variablePacked bottomRaw bottomPacked : OTerm alpha)
    (hs : Nonempty (Derivation body Delta
      (Shape tau source gamma extended packed raw domain (suc index))))
    (hb : Nonempty (Derivation body Delta (ComputabilityLeast.bottomGraph target
      (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) extended)))
    (hes : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erasedSource source)))
    (het : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erasedTarget target)))
    (hvr : Nonempty (Derivation body Delta (graph1 variableConstructor variableRaw index)))
    (hvp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing variablePacked
      (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) variableRaw)))
    (hbr : Nonempty (Derivation body Delta (graph1 bottomConstructor bottomRaw
      (numeral (NumberedLeastCodeRepresentative.typeNumber tau)))))
    (hbp : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode bottomPacked
      (numeral (NumberedLeastCodeRepresentative.typeNumber tau))))) :
    Nonempty (Derivation body Delta
      (SurvivorResult tau source target gamma extended index erasedSource erasedTarget)) := by
  let typ : OTerm alpha := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  have hc := andLeft hs
  have hv := andLeft (andRight hs)
  have hp := andLeft (andRight (andRight hs))
  have hi := andRight (andRight (andRight hs))
  have bp := bottomCodePair bottomPacked bottomRaw typ hbr hbp
  have tp := bottomObjectPair target typ extended bottomPacked hbp hb
  have eraseS := erasePackedBackward packed variablePacked typ raw variableRaw domain (numeral 0)
    hp (eraseSuccessor raw variableRaw domain index hv hvr) hvp
  have eraseT := erasePackedBackward bottomPacked bottomPacked typ bottomRaw bottomRaw domain (numeral 0)
    bp (bottomBackward .erase bottomRaw bottomRaw domain (numeral 0) typ hbr (equalRefl bottomRaw)) bp
  have sp := eraseObjectPair domain source erasedSource gamma packed extended variablePacked hi hc eraseS hes
  have ep := eraseObjectPair domain target erasedTarget gamma bottomPacked extended bottomPacked tp hc eraseT het
  have hvar := variableObjectBuild erasedSource typ gamma index variablePacked variableRaw sp hvp hvr
  have hbottom := bottomObjectAccept erasedTarget gamma bottomPacked typ
    (pairLeft _ _ _ ep) (pairRight _ _ _ ep) hbp
  have sr := variableRank erasedSource gamma variablePacked variableRaw typ index sp hvp hvr
  have tr := bottomObjectRank erasedTarget gamma bottomPacked bottomRaw typ ep bp hbr
  have lt : Nonempty (Derivation body Delta (InternalLessThan.strictLess (numeral 0) (numeral 1))) :=
    ⟨InternalQuotientComparisonProof.zeroLessSuccessor z⟩
  have original := endpointAt tau source target gamma extended packed raw domain (suc index)
    bottomRaw bottomPacked hs hb hbr hbp
  exact andIntro original (andIntro hvar (andIntro hbottom (andIntro sr (andIntro tr lt))))

/-- These auxiliary queries only expose values of original constructors.
They have no dependency on the final selector or canonical representative. -/
def queries : Fin 4 → Program 2 :=
  ![.composition variableConstructor (fun _ : Fin 1 => .projection 1),
    pairOf (.projection 0) (.composition variableConstructor (fun _ : Fin 1 => .projection 1)),
    .composition bottomConstructor (fun _ : Fin 1 => .projection 0),
    .composition BottomRepresentative.bottomCode (fun _ : Fin 1 => .projection 0)]

theorem survivor (tau : Ty)
    (source target gamma extended packed raw domain index erasedSource erasedTarget : OTerm alpha)
    (hs : Nonempty (Derivation body Delta
      (Shape tau source gamma extended packed raw domain (suc index))))
    (hb : Nonempty (Derivation body Delta (ComputabilityLeast.bottomGraph target
      (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) extended)))
    (hes : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erasedSource source)))
    (het : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erasedTarget target))) :
    Nonempty (Derivation body Delta
      (SurvivorResult tau source target gamma extended index erasedSource erasedTarget)) := by
  let typ : OTerm alpha := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  apply queryCases queries (Fin.cons typ (Fin.cons index Fin.elim0)) _
  intro beta j ys Theta hj hq
  rw [survivorRename]
  have hs' := renameInto hs j Theta hj
  rw [shapeRename,sucRelabel] at hs'
  have hb' := renameInto hb j Theta hj
  rw [bottomGraphRename,numeralRename] at hb'
  have hes' := unaryRename eraseObjectRaw erasedSource source hes j Theta hj
  have het' := unaryRename eraseObjectRaw erasedTarget target het j Theta hj
  let typ' : OTerm beta := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  let xs : Fin 2 → OTerm beta := Fin.cons typ' (Fin.cons (index.relabel j) Fin.elim0)
  have hq' : ∀ i : Fin 4, Nonempty (Derivation body Theta
      (programGraph (queries i) (ys i) xs)) := by
    intro i
    simpa only [xs,typ',typ,numeralRename] using
      queryTwoRename (queries i) typ index j Theta (ys i) (hq i)
  have hvr := unaryRecover variableConstructor (.projection 1) (ys 0) (index.relabel j) xs
    (hq' 0) (projectionValue 1 xs)
  have hvp := binaryRecover InternalPairing.pairing (.projection 0)
    (.composition variableConstructor (fun _ : Fin 1 => .projection 1))
    (ys 1) typ' (ys 0) xs (hq' 1) (projectionValue 0 xs) (hq' 0)
  have hbr := unaryRecover bottomConstructor (.projection 0) (ys 2) typ' xs
    (hq' 2) (projectionValue 0 xs)
  have hbp := unaryRecover BottomRepresentative.bottomCode (.projection 0) (ys 3) typ' xs
    (hq' 3) (projectionValue 0 xs)
  exact survivorAt tau (source.relabel j) (target.relabel j) (gamma.relabel j)
    (extended.relabel j) (packed.relabel j) (raw.relabel j) (domain.relabel j)
    (index.relabel j) (erasedSource.relabel j) (erasedTarget.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) hs' hb' hes' het' hvr hvp hbr hbp

theorem actualOriginalSuccessorVariableErasure : ActualOriginalSuccessorVariableErasure := by
  intro p H G W body alpha Delta context tau source target witness gamma extended packed raw
    domain index erasedSource erasedTarget
  let A := Premise p H G W context tau source target witness gamma extended packed raw domain (suc index) ⊓
    (graph1 eraseObjectRaw erasedSource source ⊓ graph1 eraseObjectRaw erasedTarget target)
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have original := andLeft h
  obtain ⟨hout⟩ := survivor tau source target gamma extended packed raw domain index erasedSource erasedTarget
    (andLeft (andRight (andRight original)))
    (targetBottom p H G W context tau source target witness gamma extended packed raw domain (suc index) original)
    (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationSurvivorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationSurvivorProof
