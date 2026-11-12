module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankCompletionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectRankTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransportSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalUniformDescentSelection (selectedTyped validity)
open InternalOriginalUniformDescentSelectionInternalProof (typedRecover)
open InternalParameterizedCanonicalResultFold (foldGraph)
open OriginalCanonicalizedTypedTransportFoldProof (impApply)
open OriginalCanonicalizedTypedTransportOuterTypeProof (shiftedLeft erasedLeft)
open OriginalTransparentDecoderFinalTransportProof
open OriginalContextInsertion OriginalRawSyntaxTransport OriginalRawObjectTransport
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The transparent transport API is instantiated AFTER the single original
rank guard. Its refined tuple is definitionally the final-rank tuple. -/
abbrev guarded (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
  OriginalRankGuardedRepresentative.guardedInputs H G W p

abbrev finalInputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
  OriginalLambdaTraversalSelection.finalInputs (OriginalFinalGuardedRank.refined p H G W)

abbrev finalData (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
  OriginalLambdaTraversalSelection.finalData (OriginalFinalGuardedRank.refined p H G W)

/-- Recover the actual window argument from its original context/Gamma pair.
The packed payload does not alter the outer context sent to the window. -/
theorem windowAtParameter (window : Program 1) (c gamma parameter input : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph1 window (numeral 1) c)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma))) :
    Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph window input parameter)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  have hc := unaryValue InternalUnpair.left (.projection 1) c parameter xs
    (pairLeft parameter c gamma hp) (projectionValue 1 xs)
  exact unaryValue window (leftOf (.projection 1)) (numeral 1) c xs hw hc

/-- Apply the accepted SAME-final fold rank law to genuine source premises,
without requiring transition fixedness or selected typing of its input. -/
theorem foldRankAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (c gamma parameter input out typ rank : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 (finalInputs p H G W).window (numeral 1) c)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (validity (finalData p H G W)) (numeral 1) input parameter)))
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input)))
    (hn : Nonempty (Derivation body Delta
      (foldGraph (finalData p H G W) out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph1 variableRankPackedRaw rank out).iff
        (graph1 variableRankPackedRaw rank input))) := by
  obtain ⟨hlaw⟩ :=
    OriginalFinalGuardedRankCompletionProof.actualOriginalFinalGuardedFoldRank
      p H G W body alpha Delta out input typ parameter rank
  obtain ⟨hargs⟩ := andIntro
    (windowAtParameter (finalInputs p H G W).window c gamma parameter input hw hp)
    (andIntro (andIntro hv hl) hn)
  exact ⟨Derivation.implicationElimination hlaw hargs⟩

/-- Transport original source validity and the outer type to the shifted
payload, then invoke rank preservation by its actual final fold output. -/
theorem weakeningPackedRank (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (d cutoff gamma extended c parameter extendedParameter input shifted out typ rank : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 (finalInputs p H G W).window (numeral 1) c)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma)))
    (hq : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing extendedParameter c extended)))
    (hs : Nonempty (Derivation body Delta (graph2 shiftPackedRaw shifted cutoff input)))
    (ht : Nonempty (Derivation body Delta
      (graph3 (selectedTyped (finalData p H G W)) (numeral 1) input typ parameter)))
    (hn : Nonempty (Derivation body Delta
      (foldGraph (finalData p H G W) out shifted extendedParameter))) :
    Nonempty (Derivation body Delta
      ((graph1 variableRankPackedRaw rank out).iff
        (graph1 variableRankPackedRaw rank shifted))) := by
  let D := finalData p H G W
  have hf := typedRecover D.oldRepresentative (validity D) D.member input typ parameter ht
  have hv := impApply
    (actualOriginalTransparentDecoderFinalSourceWeakening (guarded p H G W) H G W
      body alpha Delta d cutoff gamma extended c parameter extendedParameter input shifted)
    (andIntro hi (andIntro hp (andIntro hq (andIntro hs (andLeft (andRight hf))))))
  have hl := shiftedLeft input shifted typ cutoff hs (andLeft (andRight (andRight hf)))
  exact foldRankAt p H G W c extended extendedParameter shifted out typ rank hw hq hv hl hn

/-- Retain the genuine context insertion in source erasure, then apply the
same fold law to the erased payload. Raw erased selectedTyped is not used. -/
theorem erasurePackedRank (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (d cutoff gamma extended c parameter extendedParameter input erased out typ rank : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 (finalInputs p H G W).window (numeral 1) c)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma)))
    (hq : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing extendedParameter c extended)))
    (he : Nonempty (Derivation body Delta (graph3 erasePackedRaw erased d cutoff input)))
    (ht : Nonempty (Derivation body Delta
      (graph3 (selectedTyped (finalData p H G W)) (numeral 1) input typ extendedParameter)))
    (hn : Nonempty (Derivation body Delta
      (foldGraph (finalData p H G W) out erased parameter))) :
    Nonempty (Derivation body Delta
      ((graph1 variableRankPackedRaw rank out).iff
        (graph1 variableRankPackedRaw rank erased))) := by
  let D := finalData p H G W
  have hf := typedRecover D.oldRepresentative (validity D) D.member
    input typ extendedParameter ht
  have hv := impApply
    (actualOriginalTransparentDecoderFinalSourceErasure (guarded p H G W) H G W
      body alpha Delta d cutoff gamma extended c parameter extendedParameter input erased)
    (andIntro hi (andIntro hp (andIntro hq (andIntro he (andLeft (andRight hf))))))
  have hl := erasedLeft input erased typ d cutoff he (andLeft (andRight (andRight hf)))
  exact foldRankAt p H G W c gamma parameter erased out typ rank hw hp hv hl hn

/-- Reassemble rank equivalence for the original Object wrappers at their
actual pair coordinates. Both Object values carry the same context code. -/
theorem objectRankOfPackedRank (input out gamma raw canonicalRaw rank : OTerm alpha)
    (hi : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing input gamma raw)))
    (ho : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing out gamma canonicalRaw)))
    (hr : Nonempty (Derivation body Delta
      ((graph1 variableRankPackedRaw rank canonicalRaw).iff
        (graph1 variableRankPackedRaw rank raw)))) :
    Nonempty (Derivation body Delta
      ((graph1 variableRankObjectRaw rank out).iff
        (graph1 variableRankObjectRaw rank input))) := by
  have hout := OriginalFinalGuardedRankObjectProof.objectRankAtPair rank out gamma canonicalRaw ho
  obtain ⟨hin⟩ := OriginalFinalGuardedRankObjectProof.objectRankAtPair rank input gamma raw hi
  have hinReverse : Nonempty (Derivation body Delta
      ((graph1 variableRankPackedRaw rank raw).iff
        (graph1 variableRankObjectRaw rank input))) :=
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionRight hin)
      (Derivation.conjunctionLeft hin)⟩
  exact OriginalLambdaTraversalFinalLambdaProof.composeIff _ _ _
    (OriginalLambdaTraversalFinalLambdaProof.composeIff _ _ _ hout hr) hinReverse

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransportSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransportSupportProof
