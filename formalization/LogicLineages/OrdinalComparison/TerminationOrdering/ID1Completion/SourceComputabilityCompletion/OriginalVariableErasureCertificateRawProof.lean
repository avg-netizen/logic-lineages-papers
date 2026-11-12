module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectRankTransportSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableEraseLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateRawProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof (refl)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalRawSyntaxTransport OriginalRawObjectTransport
open OriginalRawObjectTransportInternalSupportProof OriginalRawObjectTransportInternalSyntaxProof
open OriginalRawSyntaxTransportInternalPackedProof
open OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (variableActionBackward)
open OriginalRawSyntaxTransportInternalVariableEraseLeafProof (eraseLeafEqualBackward)
open OriginalRawVariableRankSupportProof (rankPackedBackward)
open OriginalRawVariableRankLeafProof (rankVariableBackward rankBottomBackward)
open OriginalRawObjectRankTransportSupportProof (rankObjectBackward)
open OriginalVariableObjectSupportProof (bottomObjectAccept)
open OriginalVariableObjectSyntaxProof (bottomGraphRename)
open OriginalVariableErasureCertificate OriginalVariableErasureCertificateSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem equalRefl (value : OTerm alpha) :
    Nonempty (Derivation body Delta (equal value value)) := by
  simpa only [equalEqn] using
    (show Nonempty (Derivation body Delta (eqn value value)) from ⟨refl value⟩)

/-- Expose the original packed bottom at its actual raw bottom payload.
Both occurrences of the type are the same supplied input. -/
theorem bottomCodePair (packed raw typ : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 bottomConstructor raw typ)))
    (hp : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode packed typ))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)) :=
  binaryRecover InternalPairing.pairing (.projection (0 : Fin 1)) bottomConstructor
    packed typ raw (Fin.cons typ Fin.elim0) hp (projectionValue 0 (Fin.cons typ Fin.elim0)) hr

/-- The actual bottom Object constructor exposes its literal Gamma and
packed bottom. No equality to a native code is used. -/
theorem bottomObjectPair (object typ gamma packed : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode packed typ)))
    (ho : Nonempty (Derivation body Delta (ComputabilityLeast.bottomGraph object typ gamma))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing object gamma packed)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons typ (Fin.cons gamma Fin.elim0)
  exact binaryRecover InternalPairing.pairing (.projection 1)
    (.composition BottomRepresentative.bottomCode (fun _ : Fin 1 => .projection 0))
    object gamma packed xs ho (projectionValue 1 xs)
    (unaryValue BottomRepresentative.bottomCode (.projection 0) packed typ xs hp (projectionValue 0 xs))

/-- Recover the output pairing of the literal Object eraser from a genuine
context cons and an independently constructed packed-erasure graph. -/
theorem eraseObjectPair (d input erased gamma packed extended erasedPacked : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input extended packed)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended d gamma)))
    (ht : Nonempty (Derivation body Delta (graph3 erasePackedRaw erasedPacked d (numeral 0) packed)))
    (he : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erased input))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erased gamma erasedPacked)) := by
  have hs := eraseComponents d input gamma packed extended hp hc
  let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
  have hq := compositionValue erasePackedRaw ![erasedDomain,constant 1 0,InternalUnpair.right]
    erasedPacked xs (Fin.cons d (Fin.cons (numeral 0) (Fin.cons packed Fin.elim0))) ht hs.2
  exact binaryRecover InternalPairing.pairing erasedContext erasedPayload
    erased gamma erasedPacked xs he hs.1 hq

/-- Cutoff zero matches the actual top variable. Its original traversal
returns the literal raw bottom of the erased context type. -/
theorem eraseVariableZero (raw bottomRaw typ : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor raw (numeral 0))))
    (hb : Nonempty (Derivation body Delta (graph1 bottomConstructor bottomRaw typ))) :
    Nonempty (Derivation body Delta (graph3 eraseRaw bottomRaw typ (numeral 0) raw)) :=
  variableBackward .erase raw bottomRaw typ (numeral 0) (numeral 0) hv
    (variableActionBackward .erase raw bottomRaw typ (numeral 0) (numeral 0) hv
      (eraseLeafEqualBackward raw bottomRaw typ (numeral 0) (numeral 0)
        hv (equalRefl (numeral 0)) hb))

/-- Original bottom syntax is unchanged by the same cutoff-zero traversal. -/
theorem eraseBottom (raw typ : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (graph1 bottomConstructor raw typ))) :
    Nonempty (Derivation body Delta (graph3 eraseRaw raw typ (numeral 0) raw)) :=
  bottomBackward .erase raw raw typ (numeral 0) typ hb (equalRefl raw)

theorem variableObjectRank (source gamma packed raw typ : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source gamma packed)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor raw (numeral 0)))) :
    Nonempty (Derivation body Delta (graph1 variableRankObjectRaw (numeral 1) source)) :=
  rankObjectBackward source (numeral 1) gamma packed ho
    (rankPackedBackward packed (numeral 1) typ raw hp
      (rankVariableBackward raw (numeral 1) (numeral 0) hv (equalRefl (numeral 1))))

theorem bottomObjectRank (target gamma packed raw typ : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target gamma packed)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
    (hb : Nonempty (Derivation body Delta (graph1 bottomConstructor raw typ))) :
    Nonempty (Derivation body Delta (graph1 variableRankObjectRaw (numeral 0) target)) :=
  rankObjectBackward target (numeral 0) gamma packed ho
    (rankPackedBackward packed (numeral 0) typ raw hp
      (rankBottomBackward raw (numeral 0) typ hb (equalRefl (numeral 0))))

/-- Both erasures use one actual bottom payload obtained independently of
the supplied erasure outputs. Constructor equations determine their output
pairs; pairing functionality gives collapse. The original rank drop follows
from the original variable/bottom rank leaves, without rank assumptions. -/
theorem rawResultAt (tau : Ty)
    (source target gamma extended packed raw erasedSource erasedTarget bottomRaw bottomPacked : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (TopVariableShape tau source gamma extended packed raw)))
    (hb : Nonempty (Derivation body Delta
      (ComputabilityLeast.bottomGraph target
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) extended)))
    (hes : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erasedSource source)))
    (het : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erasedTarget target)))
    (hbr : Nonempty (Derivation body Delta
      (graph1 bottomConstructor bottomRaw (numeral (NumberedLeastCodeRepresentative.typeNumber tau)))))
    (hbp : Nonempty (Derivation body Delta
      (graph1 BottomRepresentative.bottomCode bottomPacked
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau))))) :
    Nonempty (Derivation body Delta
      (RawResult tau source target gamma extended erasedSource erasedTarget)) := by
  let typ : OTerm alpha := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  have hc := andLeft hs
  have hv := andLeft (andRight hs)
  have hp := andLeft (andRight (andRight hs))
  have hi := andRight (andRight (andRight hs))
  have hbottomPair := bottomCodePair bottomPacked bottomRaw typ hbr hbp
  have htargetPair := bottomObjectPair target typ extended bottomPacked hbp hb
  have hsourceErase := erasePackedBackward packed bottomPacked typ raw bottomRaw typ (numeral 0)
    hp (eraseVariableZero raw bottomRaw typ hv hbr) hbottomPair
  have htargetErase := erasePackedBackward bottomPacked bottomPacked typ bottomRaw bottomRaw typ (numeral 0)
    hbottomPair (eraseBottom bottomRaw typ hbr) hbottomPair
  have hsourceOut := eraseObjectPair typ source erasedSource gamma packed extended bottomPacked
    hi hc hsourceErase hes
  have htargetOut := eraseObjectPair typ target erasedTarget gamma bottomPacked extended bottomPacked
    htargetPair hc htargetErase het
  have hsourceBottom := bottomObjectAccept erasedSource gamma bottomPacked typ
    (pairLeft _ _ _ hsourceOut) (pairRight _ _ _ hsourceOut) hbp
  have htargetBottom := bottomObjectAccept erasedTarget gamma bottomPacked typ
    (pairLeft _ _ _ htargetOut) (pairRight _ _ _ htargetOut) hbp
  have heq := valueUnique InternalPairing.pairing erasedSource erasedTarget
    (Fin.cons gamma (Fin.cons bottomPacked Fin.elim0)) hsourceOut htargetOut
  have he : Nonempty (Derivation body Delta (equal erasedSource erasedTarget)) := by
    simpa only [equalEqn] using heq
  have hsourceRank := variableObjectRank source extended packed raw typ hi hp hv
  have htargetRank := bottomObjectRank target extended bottomPacked bottomRaw typ htargetPair hbottomPair hbr
  have hstrict : Nonempty (Derivation body Delta
      (InternalLessThan.strictLess (numeral 0) (numeral 1))) :=
    ⟨InternalQuotientComparisonProof.zeroLessSuccessor z⟩
  exact andIntro hb (andIntro hsourceBottom (andIntro htargetBottom
    (andIntro he (andIntro hsourceRank (andIntro htargetRank hstrict)))))

/-- Original Program totality supplies the raw and packed bottom values
inside the arithmetic derivation. Neither value is a caller premise. -/
theorem rawResult (tau : Ty)
    (source target gamma extended packed raw erasedSource erasedTarget : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (TopVariableShape tau source gamma extended packed raw)))
    (hb : Nonempty (Derivation body Delta
      (ComputabilityLeast.bottomGraph target
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) extended)))
    (hes : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erasedSource source)))
    (het : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erasedTarget target))) :
    Nonempty (Derivation body Delta
      (RawResult tau source target gamma extended erasedSource erasedTarget)) := by
  let typ : OTerm alpha := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  apply queryCases (![bottomConstructor,BottomRepresentative.bottomCode] : Fin 2 → Program 1)
    (Fin.cons typ Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [rawResultRename]
  have hs' := renameInto hs j Theta hj
  rw [topVariableShapeRename] at hs'
  have hb' := renameInto hb j Theta hj
  rw [bottomGraphRename,numeralRename] at hb'
  have hes' := unaryRename eraseObjectRaw erasedSource source hes j Theta hj
  have het' := unaryRename eraseObjectRaw erasedTarget target het j Theta hj
  have hbr := queryOneRename bottomConstructor typ j Theta (ys 0) (hq 0)
  have hbp := queryOneRename BottomRepresentative.bottomCode typ j Theta (ys 1) (hq 1)
  simp only [typ,numeralRename] at hbr hbp
  exact rawResultAt tau (source.relabel j) (target.relabel j) (gamma.relabel j)
    (extended.relabel j) (packed.relabel j) (raw.relabel j)
    (erasedSource.relabel j) (erasedTarget.relabel j) (ys 0) (ys 1)
    hs' hb' hes' het' hbr hbp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateRawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateRawProof
