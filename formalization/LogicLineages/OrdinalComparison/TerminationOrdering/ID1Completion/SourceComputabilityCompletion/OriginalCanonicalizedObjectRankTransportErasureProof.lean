module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransportSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransportErasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalTypedDecoderTransportLogicalProof (iffRename)
open OriginalRawObjectTransport OriginalRawSyntaxTransport
open OriginalRawObjectTransportInternalSyntaxProof
open OriginalCanonicalizedObjectTypedTransportSupportProof
open OriginalCanonicalizedObjectRankTransportSupportProof
open OriginalRawVariableRank UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The genuine cons witness pays source erasure at the actual original
parameter. Canonical rank is obtained from final source premises, without
assuming selected typing or fixedness of the raw erased Object. -/
theorem erasureCanonicalRankFromRecovered
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (context : Nat) (typ d input erased out gamma raw extended erasedRaw rank : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 (finalInputs p H G W).window (numeral 1) (numeral context))))
    (ht : Nonempty (Derivation body Delta
      (graph3 (GlobalSourcePackage.computability (finalInputs p H G W)).typed
        (numeral 1) (numeral context) typ input)))
    (hr : Nonempty (Derivation body Delta
      (EraseRecovered d input erased gamma raw extended erasedRaw)))
    (hk : Nonempty (Derivation body Delta
      (graph2 (OriginalFinalVariableObject.canonicalObjectProgram
        (OriginalFinalGuardedRank.refined p H G W)) out (numeral context) erased))) :
    Nonempty (Derivation body Delta
      ((graph1 variableRankObjectRaw rank out).iff
        (graph1 variableRankObjectRaw rank erased))) := by
  let f := finalInputs p H G W
  let r := OriginalFinalGuardedRank.refined p H G W
  apply parameterCases context extended _
  intro beta j Theta hj extendedParameter hep
  simp only [iffRename,graph1Rename]
  have hr' := renameInto hr j Theta hj
  simp only [EraseRecovered,conjunctionRename,graph2Rename,graph3Rename,numeralRename] at hr'
  have hw' := windowRename f.window context hw j Theta hj
  have ht' := outerTypedRename (GlobalSourcePackage.computability f).typed context typ input ht j Theta hj
  have htyped := outerRecover (guarded p H G W) H G W context
    (typ.relabel j) (input.relabel j) (extended.relabel j) (raw.relabel j)
    extendedParameter hw' ht' (andLeft hr') hep
  have hk' := binaryRename (OriginalFinalVariableObject.canonicalObjectProgram r)
    out (numeral context) erased hk j Theta hj
  simp only [numeralRename] at hk'
  apply canonicalCasesAtPair r (numeral context) (erased.relabel j)
    (out.relabel j) (gamma.relabel j) (erasedRaw.relabel j) _
    (andRight (andRight (andRight hr'))) hk'
  intro eta k Xi hscope parameter canonicalRaw hp hfold hout
  simp only [iffRename,graph1Rename]
  simp only [numeralRename] at hp
  have hw'' := windowRename f.window context hw' k Xi hscope
  have hep' := binaryRename InternalPairing.pairing extendedParameter (numeral context)
    (extended.relabel j) hep k Xi hscope
  simp only [numeralRename] at hep'
  have hc := binaryRename InternalListCodec.consCode (extended.relabel j) (d.relabel j)
    (gamma.relabel j) (andLeft (andRight hr')) k Xi hscope
  have he := renameInto (andLeft (andRight (andRight hr'))) k Xi hscope
  simp only [graph3Rename,numeralRename] at he
  have ht'' := renameInto htyped k Xi hscope
  simp only [graph3Rename,numeralRename] at ht''
  have hi := OriginalContextInsertionZeroProof.zeroBackward
    ((d.relabel j).relabel k) ((gamma.relabel j).relabel k)
    ((extended.relabel j).relabel k) hc
  have hcanonical := erasurePackedRank p H G W
    ((d.relabel j).relabel k) (numeral 0) ((gamma.relabel j).relabel k)
    ((extended.relabel j).relabel k) (numeral context) parameter (extendedParameter.relabel k)
    ((raw.relabel j).relabel k) ((erasedRaw.relabel j).relabel k) canonicalRaw
    ((typ.relabel j).relabel k) ((rank.relabel j).relabel k)
    hw'' hi hp hep' he ht'' hfold
  have herased := binaryRename InternalPairing.pairing (erased.relabel j)
    (gamma.relabel j) (erasedRaw.relabel j)
    (andRight (andRight (andRight hr'))) k Xi hscope
  exact objectRankOfPackedRank ((erased.relabel j).relabel k)
    ((out.relabel j).relabel k) ((gamma.relabel j).relabel k)
    ((erasedRaw.relabel j).relabel k) canonicalRaw ((rank.relabel j).relabel k)
    herased hout hcanonical

/-- Recover the input payload internally while retaining the original left
coordinate and cons witnesses. The final canonicalization preserves the rank
of that actual raw erased Object. -/
theorem erasureCanonicalRank
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (context : Nat) (typ d gamma extended input erased out rank : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 (finalInputs p H G W).window (numeral 1) (numeral context))))
    (ht : Nonempty (Derivation body Delta
      (graph3 (GlobalSourcePackage.computability (finalInputs p H G W)).typed
        (numeral 1) (numeral context) typ input)))
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left extended input)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended d gamma)))
    (he : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erased input)))
    (hk : Nonempty (Derivation body Delta
      (graph2 (OriginalFinalVariableObject.canonicalObjectProgram
        (OriginalFinalGuardedRank.refined p H G W)) out (numeral context) erased))) :
    Nonempty (Derivation body Delta
      ((graph1 variableRankObjectRaw rank out).iff
        (graph1 variableRankObjectRaw rank erased))) := by
  let f := finalInputs p H G W
  let r := OriginalFinalGuardedRank.refined p H G W
  apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
  intro beta j Theta raw hj hright
  simp only [iffRename,graph1Rename]
  simp only [consTermRename,emptyRename] at hright
  have hl' := unaryRename InternalUnpair.left extended input hl j Theta hj
  have hp := reconstructPair (input.relabel j) (extended.relabel j) raw hl' hright
  have hc' := binaryRename InternalListCodec.consCode extended d gamma hc j Theta hj
  have he' := unaryRename eraseObjectRaw erased input he j Theta hj
  have hw' := windowRename f.window context hw j Theta hj
  have ht' := outerTypedRename (GlobalSourcePackage.computability f).typed context typ input ht j Theta hj
  have hk' := binaryRename (OriginalFinalVariableObject.canonicalObjectProgram r)
    out (numeral context) erased hk j Theta hj
  simp only [numeralRename] at hk'
  apply OriginalRawObjectTransportInternalExposureProof.actualRawObjectInternalEraseExposure
    body beta Theta (d.relabel j) (input.relabel j) (erased.relabel j)
    (gamma.relabel j) raw (extended.relabel j) _ hp hc' he'
  intro eta k Xi hscope erasedRaw hr
  simp only [iffRename,graph1Rename]
  have hw'' := windowRename f.window context hw' k Xi hscope
  have ht'' := outerTypedRename (GlobalSourcePackage.computability f).typed context
    (typ.relabel j) (input.relabel j) ht' k Xi hscope
  have hk'' := binaryRename (OriginalFinalVariableObject.canonicalObjectProgram r)
    (out.relabel j) (numeral context) (erased.relabel j) hk' k Xi hscope
  simp only [numeralRename] at hk''
  exact erasureCanonicalRankFromRecovered p H G W context ((typ.relabel j).relabel k)
    ((d.relabel j).relabel k) ((input.relabel j).relabel k) ((erased.relabel j).relabel k)
    ((out.relabel j).relabel k) ((gamma.relabel j).relabel k) (raw.relabel k)
    ((extended.relabel j).relabel k) erasedRaw ((rank.relabel j).relabel k)
    hw'' ht'' hr hk''

theorem actualOriginalCanonicalizedObjectErasureRank :
    OriginalCanonicalizedObjectRankTransportTargets.ActualOriginalCanonicalizedObjectErasureRank := by
  intro p H G W positive alpha Delta context typ d gamma extended input erased out before after
  let f := finalInputs p H G W
  let K := OriginalFinalVariableObject.canonicalObjectProgram (OriginalFinalGuardedRank.refined p H G W)
  let B := graph1 f.window (numeral 1) (numeral context) ⊓
    (graph3 (GlobalSourcePackage.computability f).typed (numeral 1) (numeral context) typ input ⊓
      (graph1 InternalUnpair.left extended input ⊓
        (graph2 InternalListCodec.consCode extended d gamma ⊓
          (graph1 eraseObjectRaw erased input ⊓ graph2 K out (numeral context) erased))))
  let A := B ⊓
    (graph1 variableRankObjectRaw before input ⊓ graph1 variableRankObjectRaw after out)
  have h : Nonempty (Derivation positive (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hi := andLeft h
  have he := andLeft (andRight (andRight (andRight (andRight hi))))
  obtain ⟨hcanonical⟩ := erasureCanonicalRank p H G W context typ d gamma extended input erased out after
    (andLeft hi) (andLeft (andRight hi)) (andLeft (andRight (andRight hi)))
    (andLeft (andRight (andRight (andRight hi)))) he
    (andRight (andRight (andRight (andRight (andRight hi)))))
  obtain ⟨ha⟩ := andRight (andRight h)
  have herased : Nonempty (Derivation positive (A :: Delta)
      (graph1 variableRankObjectRaw after erased)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hcanonical) ha⟩
  obtain ⟨hout⟩ := OriginalRawObjectRankTransportProof.rankEraseObjectNonincrease
    input erased before after he (andLeft (andRight h)) herased
  exact ⟨Derivation.implicationIntroduction hout⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransportErasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransportErasureProof
