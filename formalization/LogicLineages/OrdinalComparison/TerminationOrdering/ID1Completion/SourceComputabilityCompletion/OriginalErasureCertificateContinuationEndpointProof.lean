module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateRawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationEndpointProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight sameAccept queryCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open UniformCertificateCompletion OriginalRawObjectTransport OriginalRawSyntaxTransport
open OriginalVariableObject OriginalVariableObjectSyntaxProof
open OriginalVariableErasureCertificateSourceProof (beforeVariable certificateBottomWithWindow bottomAtKnownGamma)
open OriginalVariableErasureCertificateRawProof (equalRefl bottomCodePair bottomObjectPair bottomObjectRank)
open OriginalRawVariableRankSupportProof (rankPackedBackward)
open OriginalRawVariableRankLeafProof (rankVariableBackward)
open OriginalRawObjectRankTransportSupportProof (rankObjectBackward)
open OriginalRawObjectTransportInternalSyntaxProof
open OriginalErasureCertificateContinuation OriginalErasureCertificateContinuationTargets
open OriginalErasureCertificateContinuationSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal variable decoding does not depend on whether the index is zero. -/
theorem shapeVariable (tau : Ty) (source gamma extended packed raw domain index : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (Shape tau source gamma extended packed raw domain index))) :
    Nonempty (Derivation body Delta (variableObject source)) := by
  let typ : OTerm alpha := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  have hv := andLeft (andRight hs)
  have hp := andLeft (andRight (andRight hs))
  have ho := andRight (andRight (andRight hs))
  have htag := OriginalFinalVariableWeakeningSupportProof.packedVariableTag packed raw typ index hv hp
  have htest : Nonempty (Derivation body Delta
      (graph1 OriginalConstructorLeaf.variableTest (numeral 1) packed)) :=
    sameAccept OriginalLambdaConstructor.tag (InternalAcceptance.constantZero 1) z
      (Fin.cons packed Fin.elim0) htag (InternalLessThanSupportProof.zeroConstantValue _)
  exact unaryValue OriginalConstructorLeaf.variableTest InternalUnpair.right
    (numeral 1) packed (Fin.cons source Fin.elim0) htest (pairRight source extended packed ho)

theorem targetBottom (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw domain index : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (Premise p H G W context tau source target witness gamma extended packed raw domain index))) :
    Nonempty (Derivation body Delta
      (ComputabilityLeast.bottomGraph target
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) extended)) := by
  have hs := andLeft (andRight (andRight h))
  have hb := certificateBottomWithWindow (beforeVariable p H G W) context tau source target witness
    (andLeft h) (andLeft (andRight h))
    (shapeVariable tau source gamma extended packed raw domain index hs)
    (andRight (andRight (andRight h)))
  exact bottomAtKnownGamma tau source target extended
    (pairLeft source extended packed (andRight (andRight (andRight hs)))) hb

theorem variableRank (source gamma packed raw typ index : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source gamma packed)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor raw index))) :
    Nonempty (Derivation body Delta (graph1 variableRankObjectRaw (numeral 1) source)) :=
  rankObjectBackward source (numeral 1) gamma packed ho
    (rankPackedBackward packed (numeral 1) typ raw hp
      (rankVariableBackward raw (numeral 1) index hv (equalRefl (numeral 1))))

theorem endpointAt (tau : Ty)
    (source target gamma extended packed raw domain index bottomRaw bottomPacked : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (Shape tau source gamma extended packed raw domain index)))
    (hb : Nonempty (Derivation body Delta (ComputabilityLeast.bottomGraph target
      (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) extended)))
    (hbr : Nonempty (Derivation body Delta (graph1 bottomConstructor bottomRaw
      (numeral (NumberedLeastCodeRepresentative.typeNumber tau)))))
    (hbp : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode bottomPacked
      (numeral (NumberedLeastCodeRepresentative.typeNumber tau))))) :
    Nonempty (Derivation body Delta (EndpointResult tau source target extended)) := by
  let typ : OTerm alpha := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  have bp := bottomCodePair bottomPacked bottomRaw typ hbr hbp
  have tp := bottomObjectPair target typ extended bottomPacked hbp hb
  have sr := variableRank source extended packed raw typ index
    (andRight (andRight (andRight hs))) (andLeft (andRight (andRight hs))) (andLeft (andRight hs))
  have tr := bottomObjectRank target extended bottomPacked bottomRaw typ tp bp hbr
  have lt : Nonempty (Derivation body Delta (InternalLessThan.strictLess (numeral 0) (numeral 1))) :=
    ⟨InternalQuotientComparisonProof.zeroLessSuccessor z⟩
  exact andIntro hb (andIntro sr (andIntro tr lt))

theorem endpoint (tau : Ty)
    (source target gamma extended packed raw domain index : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (Shape tau source gamma extended packed raw domain index)))
    (hb : Nonempty (Derivation body Delta (ComputabilityLeast.bottomGraph target
      (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) extended))) :
    Nonempty (Derivation body Delta (EndpointResult tau source target extended)) := by
  let typ : OTerm alpha := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  apply queryCases (![bottomConstructor,BottomRepresentative.bottomCode] : Fin 2 → Program 1)
    (Fin.cons typ Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [endpointRename]
  have hs' := renameInto hs j Theta hj
  rw [shapeRename] at hs'
  have hb' := renameInto hb j Theta hj
  rw [bottomGraphRename,numeralRename] at hb'
  have hbr := queryOneRename bottomConstructor typ j Theta (ys 0) (hq 0)
  have hbp := queryOneRename BottomRepresentative.bottomCode typ j Theta (ys 1) (hq 1)
  simp only [typ,numeralRename] at hbr hbp
  exact endpointAt tau (source.relabel j) (target.relabel j) (gamma.relabel j)
    (extended.relabel j) (packed.relabel j) (raw.relabel j) (domain.relabel j)
    (index.relabel j) (ys 0) (ys 1) hs' hb' hbr hbp

theorem actualOriginalVariableCertificateEndpoint : ActualOriginalVariableCertificateEndpoint := by
  intro p H G W body alpha Delta context tau source target witness gamma extended packed raw domain index
  let A := Premise p H G W context tau source target witness gamma extended packed raw domain index
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hout⟩ := endpoint tau source target gamma extended packed raw domain index
    (andLeft (andRight (andRight h)))
    (targetBottom p H G W context tau source target witness gamma extended packed raw domain index h)
  exact ⟨Derivation.implicationIntroduction hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationEndpointProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationEndpointProof
