module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportErasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
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

/-- The exact nonempty context and actual erasure exposure are retained.
The SAME original outer typed input pays all membership; K pays fixedness. -/
 theorem erasureFromRecovered (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (context : Nat) (typ d input erased out gamma raw extended erasedRaw : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 (OriginalLambdaTraversalSelection.finalInputs (refined p H G W)).window
        (numeral 1) (numeral context))))
    (ht : Nonempty (Derivation body Delta
      (graph3 (GlobalSourcePackage.computability
        (OriginalLambdaTraversalSelection.finalInputs (refined p H G W))).typed
          (numeral 1) (numeral context) typ input)))
    (hr : Nonempty (Derivation body Delta
      (EraseRecovered d input erased gamma raw extended erasedRaw)))
    (hk : Nonempty (Derivation body Delta
      (graph2 (OriginalFinalVariableObject.canonicalObjectProgram (refined p H G W))
        out (numeral context) erased))) :
    Nonempty (Derivation body Delta
      (graph3 (GlobalSourcePackage.computability
        (OriginalLambdaTraversalSelection.finalInputs (refined p H G W))).typed
          (numeral 1) (numeral context) typ out)) := by
  let f := OriginalLambdaTraversalSelection.finalInputs (refined p H G W)
  apply parameterCases context extended _
  intro beta j Theta hj extendedParameter hep
  simp only [graph3Rename,numeralRename]
  have hr' := renameInto hr j Theta hj
  simp only [EraseRecovered,conjunctionRename,graph2Rename,graph3Rename,numeralRename] at hr'
  have hw' := windowRename f.window context hw j Theta hj
  have ht' := outerTypedRename (GlobalSourcePackage.computability f).typed context typ input ht j Theta hj
  have htyped := outerRecover p H G W context (typ.relabel j) (input.relabel j)
    (extended.relabel j) (raw.relabel j) extendedParameter hw' ht' (andLeft hr') hep
  have hk' := binaryRename (OriginalFinalVariableObject.canonicalObjectProgram (refined p H G W))
    out (numeral context) erased hk j Theta hj
  simp only [numeralRename] at hk'
  apply canonicalCasesAtPair (refined p H G W) (numeral context) (erased.relabel j)
    (out.relabel j) (gamma.relabel j) (erasedRaw.relabel j) _
    (andRight (andRight (andRight hr'))) hk'
  intro eta k Xi hk parameter canonicalRaw hp hfold hout
  simp only [graph3Rename,numeralRename]
  simp only [numeralRename] at hp
  have hw'' := windowRename f.window context hw' k Xi hk
  have hep' := binaryRename InternalPairing.pairing extendedParameter (numeral context)
    (extended.relabel j) hep k Xi hk
  simp only [numeralRename] at hep'
  have hc := binaryRename InternalListCodec.consCode (extended.relabel j) (d.relabel j)
    (gamma.relabel j) (andLeft (andRight hr')) k Xi hk
  have he := renameInto (andLeft (andRight (andRight hr'))) k Xi hk
  simp only [graph3Rename,numeralRename] at he
  have ht'' := renameInto htyped k Xi hk
  simp only [graph3Rename,numeralRename] at ht''
  have hi := OriginalContextInsertionZeroProof.zeroBackward
    ((d.relabel j).relabel k) ((gamma.relabel j).relabel k)
    ((extended.relabel j).relabel k) hc
  have hcanonical := OriginalCanonicalizedTypedTransportPackedProof.erasureAt p H G W
    ((d.relabel j).relabel k) (numeral 0) ((gamma.relabel j).relabel k)
    ((extended.relabel j).relabel k) (numeral context) parameter (extendedParameter.relabel k)
    ((raw.relabel j).relabel k) ((erasedRaw.relabel j).relabel k) canonicalRaw
    ((typ.relabel j).relabel k) hi hp hep' he ht'' hfold
  exact outerAccept p H G W context ((typ.relabel j).relabel k)
    ((out.relabel j).relabel k) ((gamma.relabel j).relabel k) canonicalRaw
    parameter hw'' hout hp hcanonical

/-- Recover the raw payload internally, keeping the supplied actual left
coordinate and cons witness, before opening the actual erasure Program. -/
 theorem erasureAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (context : Nat) (typ d gamma extended input erased out : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 (OriginalLambdaTraversalSelection.finalInputs (refined p H G W)).window
        (numeral 1) (numeral context))))
    (ht : Nonempty (Derivation body Delta
      (graph3 (GlobalSourcePackage.computability
        (OriginalLambdaTraversalSelection.finalInputs (refined p H G W))).typed
          (numeral 1) (numeral context) typ input)))
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left extended input)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended d gamma)))
    (he : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erased input)))
    (hk : Nonempty (Derivation body Delta
      (graph2 (OriginalFinalVariableObject.canonicalObjectProgram (refined p H G W))
        out (numeral context) erased))) :
    Nonempty (Derivation body Delta
      (graph3 (GlobalSourcePackage.computability
        (OriginalLambdaTraversalSelection.finalInputs (refined p H G W))).typed
          (numeral 1) (numeral context) typ out)) := by
  let f := OriginalLambdaTraversalSelection.finalInputs (refined p H G W)
  apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
  intro beta j Theta raw hj hright
  simp only [graph3Rename,numeralRename]
  simp only [consTermRename,emptyRename] at hright
  have hl' := unaryRename InternalUnpair.left extended input hl j Theta hj
  have hp := reconstructPair (input.relabel j) (extended.relabel j) raw hl' hright
  have hc' := binaryRename InternalListCodec.consCode extended d gamma hc j Theta hj
  have he' := unaryRename eraseObjectRaw erased input he j Theta hj
  have hw' := windowRename f.window context hw j Theta hj
  have ht' := outerTypedRename (GlobalSourcePackage.computability f).typed context typ input ht j Theta hj
  have hk' := binaryRename (OriginalFinalVariableObject.canonicalObjectProgram (refined p H G W))
    out (numeral context) erased hk j Theta hj
  simp only [numeralRename] at hk'
  apply OriginalRawObjectTransportInternalExposureProof.actualRawObjectInternalEraseExposure
    body beta Theta (d.relabel j) (input.relabel j) (erased.relabel j)
    (gamma.relabel j) raw (extended.relabel j) _ hp hc' he'
  intro eta k Xi hk erasedRaw hr
  simp only [graph3Rename,numeralRename]
  have hw'' := windowRename f.window context hw' k Xi hk
  have ht'' := outerTypedRename (GlobalSourcePackage.computability f).typed context
    (typ.relabel j) (input.relabel j) ht' k Xi hk
  have hk'' := binaryRename (OriginalFinalVariableObject.canonicalObjectProgram (refined p H G W))
    (out.relabel j) (numeral context) (erased.relabel j) hk' k Xi hk
  simp only [numeralRename] at hk''
  exact erasureFromRecovered p H G W context ((typ.relabel j).relabel k)
    ((d.relabel j).relabel k) ((input.relabel j).relabel k) ((erased.relabel j).relabel k)
    ((out.relabel j).relabel k) ((gamma.relabel j).relabel k) (raw.relabel k)
    ((extended.relabel j).relabel k) erasedRaw hw'' ht'' hr hk''

 theorem actualOriginalCanonicalizedObjectTypedErasure :
    OriginalCanonicalizedObjectTypedTransportTargets.ActualOriginalCanonicalizedObjectTypedErasure := by
  intro p H G W body alpha Delta context typ d gamma extended input erased out
  let f := OriginalLambdaTraversalSelection.finalInputs (refined p H G W)
  let comp := GlobalSourcePackage.computability f
  let K := OriginalFinalVariableObject.canonicalObjectProgram (refined p H G W)
  let A := graph1 f.window (numeral 1) (numeral context) ⊓
    (graph3 comp.typed (numeral 1) (numeral context) typ input ⊓
      (graph1 InternalUnpair.left extended input ⊓
        (graph2 InternalListCodec.consCode extended d gamma ⊓
          (graph1 eraseObjectRaw erased input ⊓ graph2 K out (numeral context) erased))))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hout⟩ := erasureAt p H G W context typ d gamma extended input erased out
    (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andLeft (andRight (andRight (andRight h))))
    (andLeft (andRight (andRight (andRight (andRight h)))))
    (andRight (andRight (andRight (andRight (andRight h)))))
  exact ⟨Derivation.implicationIntroduction hout⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportErasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportErasureProof
