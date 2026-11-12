module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransportSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransportWeakeningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalTypedDecoderTransportLogicalProof (iffRename)
open OriginalRawObjectTransport OriginalRawSyntaxTransport
open OriginalRawObjectTransportInternalSyntaxProof
open OriginalCanonicalizedObjectTypedTransportSupportProof
open OriginalCanonicalizedObjectRankTransportSupportProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual shift supplies its context and packed coordinates. Source
transport pays the final fold's premises before canonical rank is applied. -/
theorem weakeningCanonicalRankFromRecovered
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (context : Nat) (typ d input shifted out gamma raw extended shiftedRaw rank : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 (finalInputs p H G W).window (numeral 1) (numeral context))))
    (ht : Nonempty (Derivation body Delta
      (graph3 (GlobalSourcePackage.computability (finalInputs p H G W)).typed
        (numeral 1) (numeral context) typ input)))
    (hr : Nonempty (Derivation body Delta
      (ShiftRecovered d input shifted gamma raw extended shiftedRaw)))
    (hk : Nonempty (Derivation body Delta
      (graph2 (OriginalFinalVariableObject.canonicalObjectProgram
        (OriginalFinalGuardedRank.refined p H G W)) out (numeral context) shifted))) :
    Nonempty (Derivation body Delta
      ((graph1 variableRankObjectRaw rank out).iff
        (graph1 variableRankObjectRaw rank shifted))) := by
  let f := finalInputs p H G W
  let r := OriginalFinalGuardedRank.refined p H G W
  apply parameterCases context gamma _
  intro beta j Theta hj parameter hp
  simp only [iffRename,graph1Rename]
  have hr' := renameInto hr j Theta hj
  simp only [ShiftRecovered,conjunctionRename,graph2Rename,numeralRename] at hr'
  have hw' := windowRename f.window context hw j Theta hj
  have ht' := outerTypedRename (GlobalSourcePackage.computability f).typed context typ input ht j Theta hj
  have htyped := outerRecover (guarded p H G W) H G W context
    (typ.relabel j) (input.relabel j) (gamma.relabel j) (raw.relabel j)
    parameter hw' ht' (andLeft hr') hp
  have hk' := binaryRename (OriginalFinalVariableObject.canonicalObjectProgram r)
    out (numeral context) shifted hk j Theta hj
  simp only [numeralRename] at hk'
  apply canonicalCasesAtPair r (numeral context) (shifted.relabel j)
    (out.relabel j) (extended.relabel j) (shiftedRaw.relabel j) _
    (andRight (andRight (andRight hr'))) hk'
  intro eta k Xi hscope extendedParameter canonicalRaw hep hfold hout
  simp only [iffRename,graph1Rename]
  simp only [numeralRename] at hep
  have hw'' := windowRename f.window context hw' k Xi hscope
  have hp' := binaryRename InternalPairing.pairing parameter (numeral context)
    (gamma.relabel j) hp k Xi hscope
  simp only [numeralRename] at hp'
  have hc := binaryRename InternalListCodec.consCode (extended.relabel j) (d.relabel j)
    (gamma.relabel j) (andLeft (andRight hr')) k Xi hscope
  have hs := binaryRename shiftPackedRaw (shiftedRaw.relabel j) (numeral 0)
    (raw.relabel j) (andLeft (andRight (andRight hr'))) k Xi hscope
  simp only [numeralRename] at hs
  have ht'' := renameInto htyped k Xi hscope
  simp only [graph3Rename,numeralRename] at ht''
  have hi := OriginalContextInsertionZeroProof.zeroBackward
    ((d.relabel j).relabel k) ((gamma.relabel j).relabel k)
    ((extended.relabel j).relabel k) hc
  have hcanonical := weakeningPackedRank p H G W
    ((d.relabel j).relabel k) (numeral 0) ((gamma.relabel j).relabel k)
    ((extended.relabel j).relabel k) (numeral context) (parameter.relabel k) extendedParameter
    ((raw.relabel j).relabel k) ((shiftedRaw.relabel j).relabel k) canonicalRaw
    ((typ.relabel j).relabel k) ((rank.relabel j).relabel k)
    hw'' hi hp' hep hs ht'' hfold
  have hshifted := binaryRename InternalPairing.pairing (shifted.relabel j)
    (extended.relabel j) (shiftedRaw.relabel j)
    (andRight (andRight (andRight hr'))) k Xi hscope
  exact objectRankOfPackedRank ((shifted.relabel j).relabel k)
    ((out.relabel j).relabel k) ((extended.relabel j).relabel k)
    ((shiftedRaw.relabel j).relabel k) canonicalRaw ((rank.relabel j).relabel k)
    hshifted hout hcanonical

/-- Recover all raw Object coordinates internally, retaining only the original
outer typed input and the actual raw-shift/canonical-output graphs. -/
theorem weakeningCanonicalRank
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (context : Nat) (typ d input shifted out rank : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 (finalInputs p H G W).window (numeral 1) (numeral context))))
    (ht : Nonempty (Derivation body Delta
      (graph3 (GlobalSourcePackage.computability (finalInputs p H G W)).typed
        (numeral 1) (numeral context) typ input)))
    (hs : Nonempty (Derivation body Delta (graph2 shiftObjectRaw shifted d input)))
    (hk : Nonempty (Derivation body Delta
      (graph2 (OriginalFinalVariableObject.canonicalObjectProgram
        (OriginalFinalGuardedRank.refined p H G W)) out (numeral context) shifted))) :
    Nonempty (Derivation body Delta
      ((graph1 variableRankObjectRaw rank out).iff
        (graph1 variableRankObjectRaw rank shifted))) := by
  let f := finalInputs p H G W
  let r := OriginalFinalGuardedRank.refined p H G W
  apply OriginalRawObjectTransportInternalExposureProof.actualRawObjectInternalShiftExposure
    body alpha Delta d input shifted _ hs
  intro beta j Theta hj gamma raw extended shiftedRaw hr
  simp only [iffRename,graph1Rename]
  have hw' := windowRename f.window context hw j Theta hj
  have ht' := outerTypedRename (GlobalSourcePackage.computability f).typed context typ input ht j Theta hj
  have hk' := binaryRename (OriginalFinalVariableObject.canonicalObjectProgram r)
    out (numeral context) shifted hk j Theta hj
  simp only [numeralRename] at hk'
  exact weakeningCanonicalRankFromRecovered p H G W context (typ.relabel j) (d.relabel j)
    (input.relabel j) (shifted.relabel j) (out.relabel j) gamma raw extended shiftedRaw
    (rank.relabel j) hw' ht' hr hk'

theorem actualOriginalCanonicalizedObjectWeakeningRank :
    OriginalCanonicalizedObjectRankTransportTargets.ActualOriginalCanonicalizedObjectWeakeningRank := by
  intro p H G W positive alpha Delta context typ d input shifted out rank
  let f := finalInputs p H G W
  let K := OriginalFinalVariableObject.canonicalObjectProgram (OriginalFinalGuardedRank.refined p H G W)
  let A := graph1 f.window (numeral 1) (numeral context) ⊓
    (graph3 (GlobalSourcePackage.computability f).typed (numeral 1) (numeral context) typ input ⊓
      (graph2 shiftObjectRaw shifted d input ⊓ graph2 K out (numeral context) shifted))
  have h : Nonempty (Derivation positive (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := andLeft (andRight (andRight h))
  have hcanonical := weakeningCanonicalRank p H G W context typ d input shifted out rank
    (andLeft h) (andLeft (andRight h)) hs (andRight (andRight (andRight h)))
  have hraw := OriginalCanonicalizedTypedTransportFoldProof.impApply
    (OriginalRawObjectRankTransportProof.actualOriginalRawObjectShiftRank
      positive alpha (A :: Delta) d input shifted rank) hs
  obtain ⟨hout⟩ := OriginalLambdaTraversalFinalLambdaProof.composeIff _ _ _ hcanonical hraw
  exact ⟨Derivation.implicationIntroduction hout⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransportWeakeningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransportWeakeningProof
