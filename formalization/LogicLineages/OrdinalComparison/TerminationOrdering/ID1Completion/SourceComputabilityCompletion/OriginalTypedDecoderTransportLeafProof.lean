module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLeafAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportVariableProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof
open OriginalContextInsertion OriginalRawSyntaxTransport
open OriginalTypedDecoderTransport OriginalTypedDecoderTransportSyntaxProof
open OriginalTypedDecoderTransportLogicalProof OriginalTypedDecoderTransportLeafAcceptanceProof
open OriginalTypedDecoderTransportShapeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual accepted variable branch. The boundary erasure case obtains
the requested bottom type from original V and insertion, not from a window. -/
theorem variableBranch (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended typ index : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H false typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta
      (Accepted H false typ out (targetContext erasing gamma extended))) := by
  have hv := iffForward (variableIff H raw index typ (sourceContext erasing gamma extended) hc) ha
  have hact := OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof.variableForward
    (selectedMode erasing) raw out d cutoff index hc ho
  apply OriginalTypedDecoderTransportVariableProof.variableTransport erasing out d cutoff typ index gamma extended _ hi hv hact
  · intro beta j Theta targetIndex hj hcon hv'
    rw [acceptedRename]
    exact iffBackward
      (variableIff H (out.relabel j) targetIndex (typ.relabel j)
        ((targetContext erasing gamma extended).relabel j) hcon) hv'
  · intro beta j Theta hj hcon
    rw [acceptedRename]
    exact iffBackward
      (bottomIff H (out.relabel j) (typ.relabel j) (typ.relabel j)
        ((targetContext erasing gamma extended).relabel j) hcon)
      (equalReflexive (typ.relabel j))

theorem bottomBranch (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended typ recorded : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 bottomConstructor raw recorded)))
    (ho : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H false typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta
      (Accepted H false typ out (targetContext erasing gamma extended))) := by
  obtain ⟨he⟩ := bottomUnchanged erasing raw out d cutoff recorded hc ho
  rw [equalEqn] at he
  have hcon := outputTransport bottomConstructor raw out (Fin.cons recorded Fin.elim0) ⟨symm he⟩ hc
  exact iffBackward (bottomIff H out recorded typ (targetContext erasing gamma extended) hcon)
    (iffForward (bottomIff H raw recorded typ (sourceContext erasing gamma extended) hc) ha)

theorem nilBranch (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended types : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0)))
    (ho : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H true types raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta
      (Accepted H true types out (targetContext erasing gamma extended))) := by
  obtain ⟨he⟩ := nilUnchanged erasing raw out d cutoff hc ho
  rw [equalEqn] at he
  have hcon := outputTransport nilConstructor raw out Fin.elim0 ⟨symm he⟩ hc
  exact iffBackward (nilIff H out types (targetContext erasing gamma extended) hcon)
    (iffForward (nilIff H raw types (sourceContext erasing gamma extended) hc) ha)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLeafProof
