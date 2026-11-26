module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportVariableProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof
open OriginalContextInsertion OriginalRawSyntaxTransport
open OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open OriginalTypedDecoderTransport (selectedMode sourceContext targetContext)
open OriginalTypedDecoderTransportLogicalProof OriginalUniverseDecoderTransportLeafAcceptanceProof
open OriginalTypedDecoderTransportShapeProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual accepted variable branch. The boundary erasure case obtains
the requested bottom type from original V and insertion, not from a window. -/
theorem variableBranch (H : Program 1) (M W : Program 2) (erasing : Bool)
    (raw out d cutoff gamma extended typ index c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H M W false typ raw (sourceContext erasing gamma extended) c))) :
    Nonempty (Derivation body Delta
      (Accepted H M W false typ out (targetContext erasing gamma extended) c)) := by
  have hv := iffForward (variableIff H M W raw index typ (sourceContext erasing gamma extended) c hc) ha
  have hact := OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof.variableForward
    (selectedMode erasing) raw out d cutoff index hc ho
  apply OriginalTypedDecoderTransportVariableProof.variableTransport erasing out d cutoff typ index gamma extended _ hi (andRight hv) hact
  · intro beta j Theta targetIndex hj hcon hv'
    rw [acceptedRename]
    have hm := renameInto (andLeft hv) j Theta hj
    simp only [graph2Rename,SourceComputabilityFormulaSupportProof.numeral,
      InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hm
    exact iffBackward
      (variableIff H M W (out.relabel j) targetIndex (typ.relabel j)
        ((targetContext erasing gamma extended).relabel j) (c.relabel j) hcon)
      (andIntro hm hv')
  · intro beta j Theta hj hcon
    rw [acceptedRename]
    have hm := renameInto (andLeft hv) j Theta hj
    simp only [graph2Rename,SourceComputabilityFormulaSupportProof.numeral,
      InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hm
    exact iffBackward
      (bottomIff H M W (out.relabel j) (typ.relabel j) (typ.relabel j)
        ((targetContext erasing gamma extended).relabel j) (c.relabel j) hcon)
      (andIntro hm (equalReflexive (typ.relabel j)))

theorem bottomBranch (H : Program 1) (M W : Program 2) (erasing : Bool)
    (raw out d cutoff gamma extended typ recorded c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 bottomConstructor raw recorded)))
    (ho : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H M W false typ raw (sourceContext erasing gamma extended) c))) :
    Nonempty (Derivation body Delta
      (Accepted H M W false typ out (targetContext erasing gamma extended) c)) := by
  obtain ⟨he⟩ := bottomUnchanged erasing raw out d cutoff recorded hc ho
  rw [equalEqn] at he
  have hcon := outputTransport bottomConstructor raw out (Fin.cons recorded Fin.elim0) ⟨symm he⟩ hc
  exact iffBackward (bottomIff H M W out recorded typ (targetContext erasing gamma extended) c hcon)
    (iffForward (bottomIff H M W raw recorded typ (sourceContext erasing gamma extended) c hc) ha)

theorem nilBranch (H : Program 1) (M W : Program 2) (erasing : Bool)
    (raw out d cutoff gamma extended types c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0)))
    (ho : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H M W true types raw (sourceContext erasing gamma extended) c))) :
    Nonempty (Derivation body Delta
      (Accepted H M W true types out (targetContext erasing gamma extended) c)) := by
  obtain ⟨he⟩ := nilUnchanged erasing raw out d cutoff hc ho
  rw [equalEqn] at he
  have hcon := outputTransport nilConstructor raw out Fin.elim0 ⟨symm he⟩ hc
  exact iffBackward (nilIff H M W out types (targetContext erasing gamma extended) c hcon)
    (iffForward (nilIff H M W raw types (sourceContext erasing gamma extended) c hc) ha)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafProof
