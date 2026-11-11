module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportExposureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportSourceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open OriginalTransparentDecoderValidatorCollapsePackedProof
open OriginalTransparentDecoderFinalTransport OriginalTransparentDecoderFinalTransportExposureProof
open OriginalTypedDecoderTransportLogicalProof (closedApply)
open OriginalContextInsertion
open OriginalContextInsertionSyntaxProof (insertRename)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Original packed source acceptance, transported through the actual
shifted payload and literal parameter pairs. The context guard is retained. -/
theorem sourceWeakeningAt (H G : Program 1) (M W : Program 2)
    (d cutoff gamma extended c parameter extendedParameter packed shifted : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hc : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma)))
    (hce : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing extendedParameter c extended)))
    (ht : Nonempty (Derivation body Delta (graph2 shiftPackedRaw shifted cutoff packed)))
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) shifted extendedParameter)) := by
  apply shiftPackedCases packed shifted cutoff _ ht
  intro beta j Theta typ raw transformed hj hp hraw hout
  simp only [graph2Rename,numeralRename]
  have hi' := renameInto hi j Theta hj
  simp only [insertRename] at hi'
  have hc' := renameInto hc j Theta hj
  simp only [graph2Rename] at hc'
  have hce' := renameInto hce j Theta hj
  simp only [graph2Rename] at hce'
  have ha' := renameInto ha j Theta hj
  simp only [graph2Rename,numeralRename] at ha'
  have hf := sourceFieldsElim H G M W (packed.relabel j) (parameter.relabel j)
    typ raw (c.relabel j) (gamma.relabel j) hp hc' ha'
  have moved := closedApply
    (OriginalUniverseDecoderTransportProof.actualOriginalUniverseInternalTermWeakening body H M W beta
      (d.relabel j) (cutoff.relabel j) (gamma.relabel j) (extended.relabel j)
      typ raw transformed (c.relabel j))
    (OriginalLambdaConstructorGraphSyntaxProof.andIntro hi' (OriginalLambdaConstructorGraphSyntaxProof.andIntro hraw (OriginalLambdaConstructorGraphSyntaxProof.andRight hf)))
  exact sourceFieldsIntro H G M W (shifted.relabel j) (extendedParameter.relabel j)
    typ transformed (c.relabel j) (extended.relabel j) hout hce' (OriginalLambdaConstructorGraphSyntaxProof.andLeft hf) moved

/-- Concrete original checker transport, with all coordinates arbitrary. -/
theorem sourceWeakening (H G : Program 1) (M W : Program 2) :
    PackedWeakening (OriginalUniverseDecoder.source H G M W) := by
  intro body alpha Delta d cutoff gamma extended c parameter extendedParameter packed shifted
  let A := Insert d cutoff gamma extended ⊓
    (graph2 InternalPairing.pairing parameter c gamma ⊓
      (graph2 InternalPairing.pairing extendedParameter c extended ⊓
        (graph2 shiftPackedRaw shifted cutoff packed ⊓
          graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)))
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨out⟩ := sourceWeakeningAt H G M W
    d cutoff gamma extended c parameter extendedParameter packed shifted
    (OriginalLambdaConstructorGraphSyntaxProof.andLeft h) (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight h)) (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight h)))
    (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight h))))
    (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight h))))
  exact ⟨Derivation.implicationIntroduction out⟩

/-- Original packed source acceptance, transported through the actual
erased payload and literal parameter pairs. The context guard is retained. -/
theorem sourceErasureAt (H G : Program 1) (M W : Program 2)
    (d cutoff gamma extended c parameter extendedParameter packed erased : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hc : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma)))
    (hce : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing extendedParameter c extended)))
    (ht : Nonempty (Derivation body Delta (graph3 erasePackedRaw erased d cutoff packed)))
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed extendedParameter))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) erased parameter)) := by
  apply erasePackedCases packed erased d cutoff _ ht
  intro beta j Theta typ raw transformed hj hp hraw hout
  simp only [graph2Rename,numeralRename]
  have hi' := renameInto hi j Theta hj
  simp only [insertRename] at hi'
  have hc' := renameInto hc j Theta hj
  simp only [graph2Rename] at hc'
  have hce' := renameInto hce j Theta hj
  simp only [graph2Rename] at hce'
  have ha' := renameInto ha j Theta hj
  simp only [graph2Rename,numeralRename] at ha'
  have hf := sourceFieldsElim H G M W (packed.relabel j) (extendedParameter.relabel j)
    typ raw (c.relabel j) (extended.relabel j) hp hce' ha'
  have moved := closedApply
    (OriginalUniverseDecoderTransportProof.actualOriginalUniverseInternalTermErasure body H M W beta
      (d.relabel j) (cutoff.relabel j) (gamma.relabel j) (extended.relabel j)
      typ raw transformed (c.relabel j))
    (OriginalLambdaConstructorGraphSyntaxProof.andIntro hi' (OriginalLambdaConstructorGraphSyntaxProof.andIntro hraw (OriginalLambdaConstructorGraphSyntaxProof.andRight hf)))
  exact sourceFieldsIntro H G M W (erased.relabel j) (parameter.relabel j)
    typ transformed (c.relabel j) (gamma.relabel j) hout hc' (OriginalLambdaConstructorGraphSyntaxProof.andLeft hf) moved

/-- Concrete original checker transport, with all coordinates arbitrary. -/
theorem sourceErasure (H G : Program 1) (M W : Program 2) :
    PackedErasure (OriginalUniverseDecoder.source H G M W) := by
  intro body alpha Delta d cutoff gamma extended c parameter extendedParameter packed erased
  let A := Insert d cutoff gamma extended ⊓
    (graph2 InternalPairing.pairing parameter c gamma ⊓
      (graph2 InternalPairing.pairing extendedParameter c extended ⊓
        (graph3 erasePackedRaw erased d cutoff packed ⊓
          graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed extendedParameter)))
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨out⟩ := sourceErasureAt H G M W
    d cutoff gamma extended c parameter extendedParameter packed erased
    (OriginalLambdaConstructorGraphSyntaxProof.andLeft h) (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight h)) (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight h)))
    (OriginalLambdaConstructorGraphSyntaxProof.andLeft (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight h))))
    (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight (OriginalLambdaConstructorGraphSyntaxProof.andRight h))))
  exact ⟨Derivation.implicationIntroduction out⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportSourceProof
