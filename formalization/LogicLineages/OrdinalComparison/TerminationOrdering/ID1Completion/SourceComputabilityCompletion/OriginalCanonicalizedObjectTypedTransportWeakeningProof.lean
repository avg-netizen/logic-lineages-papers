module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportWeakeningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open InternalParameterizedCanonicalResultFold (foldN foldGraph)
open InternalOriginalUniformDescentSelection (selectedTyped)
open OriginalRawObjectTransport OriginalRawSyntaxTransport
open OriginalRawObjectTransportInternalSyntaxProof
open OriginalTransparentDecoderValidatorCollapse UniformCertificateCompletion
open OriginalCanonicalizedObjectTypedTransportSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual shift exposure supplies every original Gamma/payload
coordinate. The canonical wrapper supplies its true fold output. -/
 theorem weakeningFromRecovered (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (context : Nat) (typ d input shifted out gamma raw extended shiftedRaw : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 (OriginalLambdaTraversalSelection.finalInputs (refined p H G W)).window
        (numeral 1) (numeral context))))
    (ht : Nonempty (Derivation body Delta
      (graph3 (GlobalSourcePackage.computability
        (OriginalLambdaTraversalSelection.finalInputs (refined p H G W))).typed
          (numeral 1) (numeral context) typ input)))
    (hr : Nonempty (Derivation body Delta
      (ShiftRecovered d input shifted gamma raw extended shiftedRaw)))
    (hk : Nonempty (Derivation body Delta
      (graph2 (OriginalFinalVariableObject.canonicalObjectProgram (refined p H G W))
        out (numeral context) shifted))) :
    Nonempty (Derivation body Delta
      (graph3 (GlobalSourcePackage.computability
        (OriginalLambdaTraversalSelection.finalInputs (refined p H G W))).typed
          (numeral 1) (numeral context) typ out)) := by
  let f := OriginalLambdaTraversalSelection.finalInputs (refined p H G W)
  apply parameterCases context gamma _
  intro beta j Theta hj parameter hp
  simp only [graph3Rename,numeralRename]
  have hr' := renameInto hr j Theta hj
  simp only [ShiftRecovered,conjunctionRename,graph2Rename,numeralRename] at hr'
  have hw' := windowRename f.window context hw j Theta hj
  have ht' := outerTypedRename (GlobalSourcePackage.computability f).typed context typ input ht j Theta hj
  have htyped := outerRecover p H G W context (typ.relabel j) (input.relabel j)
    (gamma.relabel j) (raw.relabel j) parameter hw' ht' (andLeft hr') hp
  have hk' := binaryRename (OriginalFinalVariableObject.canonicalObjectProgram (refined p H G W))
    out (numeral context) shifted hk j Theta hj
  simp only [numeralRename] at hk'
  apply canonicalCasesAtPair (refined p H G W) (numeral context) (shifted.relabel j)
    (out.relabel j) (extended.relabel j) (shiftedRaw.relabel j) _
    (andRight (andRight (andRight hr'))) hk'
  intro eta k Xi hk extendedParameter canonicalRaw hep hfold hout
  simp only [graph3Rename,numeralRename]
  simp only [numeralRename] at hep
  have hw'' := windowRename f.window context hw' k Xi hk
  have hp' := binaryRename InternalPairing.pairing parameter (numeral context)
    (gamma.relabel j) hp k Xi hk
  simp only [numeralRename] at hp'
  have hc := binaryRename InternalListCodec.consCode (extended.relabel j) (d.relabel j)
    (gamma.relabel j) (andLeft (andRight hr')) k Xi hk
  have hs := binaryRename shiftPackedRaw (shiftedRaw.relabel j) (numeral 0)
    (raw.relabel j) (andLeft (andRight (andRight hr'))) k Xi hk
  simp only [numeralRename] at hs
  have ht'' := renameInto htyped k Xi hk
  simp only [graph3Rename,numeralRename] at ht''
  have hi := OriginalContextInsertionZeroProof.zeroBackward
    ((d.relabel j).relabel k) ((gamma.relabel j).relabel k)
    ((extended.relabel j).relabel k) hc
  have hcanonical := OriginalCanonicalizedTypedTransportPackedProof.weakeningAt p H G W
    ((d.relabel j).relabel k) (numeral 0) ((gamma.relabel j).relabel k)
    ((extended.relabel j).relabel k) (numeral context) (parameter.relabel k) extendedParameter
    ((raw.relabel j).relabel k) ((shiftedRaw.relabel j).relabel k) canonicalRaw
    ((typ.relabel j).relabel k) hi hp' hep hs ht'' hfold
  exact outerAccept p H G W context ((typ.relabel j).relabel k)
    ((out.relabel j).relabel k) ((extended.relabel j).relabel k) canonicalRaw
    extendedParameter hw'' hout hep hcanonical

 theorem weakeningAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (context : Nat) (typ d input shifted out : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 (OriginalLambdaTraversalSelection.finalInputs (refined p H G W)).window
        (numeral 1) (numeral context))))
    (ht : Nonempty (Derivation body Delta
      (graph3 (GlobalSourcePackage.computability
        (OriginalLambdaTraversalSelection.finalInputs (refined p H G W))).typed
          (numeral 1) (numeral context) typ input)))
    (hs : Nonempty (Derivation body Delta (graph2 shiftObjectRaw shifted d input)))
    (hk : Nonempty (Derivation body Delta
      (graph2 (OriginalFinalVariableObject.canonicalObjectProgram (refined p H G W))
        out (numeral context) shifted))) :
    Nonempty (Derivation body Delta
      (graph3 (GlobalSourcePackage.computability
        (OriginalLambdaTraversalSelection.finalInputs (refined p H G W))).typed
          (numeral 1) (numeral context) typ out)) := by
  let f := OriginalLambdaTraversalSelection.finalInputs (refined p H G W)
  apply OriginalRawObjectTransportInternalExposureProof.actualRawObjectInternalShiftExposure
    body alpha Delta d input shifted _ hs
  intro beta j Theta hj gamma raw extended shiftedRaw hr
  simp only [graph3Rename,numeralRename]
  have hw' := windowRename f.window context hw j Theta hj
  have ht' := outerTypedRename (GlobalSourcePackage.computability f).typed context typ input ht j Theta hj
  have hk' := binaryRename (OriginalFinalVariableObject.canonicalObjectProgram (refined p H G W))
    out (numeral context) shifted hk j Theta hj
  simp only [numeralRename] at hk'
  exact weakeningFromRecovered p H G W context (typ.relabel j) (d.relabel j)
    (input.relabel j) (shifted.relabel j) (out.relabel j) gamma raw extended shiftedRaw
    hw' ht' hr hk'

 theorem actualOriginalCanonicalizedObjectTypedWeakening :
    OriginalCanonicalizedObjectTypedTransportTargets.ActualOriginalCanonicalizedObjectTypedWeakening := by
  intro p H G W body alpha Delta context typ d input shifted out
  let f := OriginalLambdaTraversalSelection.finalInputs (refined p H G W)
  let comp := GlobalSourcePackage.computability f
  let K := OriginalFinalVariableObject.canonicalObjectProgram (refined p H G W)
  let A := graph1 f.window (numeral 1) (numeral context) ⊓
    (graph3 comp.typed (numeral 1) (numeral context) typ input ⊓
      (graph2 shiftObjectRaw shifted d input ⊓ graph2 K out (numeral context) shifted))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hout⟩ := weakeningAt p H G W context typ d input shifted out
    (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andRight (andRight (andRight h)))
  exact ⟨Derivation.implicationIntroduction hout⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportWeakeningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportWeakeningProof
