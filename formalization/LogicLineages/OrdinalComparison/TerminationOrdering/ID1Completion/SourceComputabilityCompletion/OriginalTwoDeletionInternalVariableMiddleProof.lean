module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableMiddleProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn suc sucRelabel)
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalSquareRootArithmeticSupportProof
open InternalOriginalPairingOrderArithmeticProof (withHyp weakStrictTrans)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open OriginalTwoDeletionInternalVariableArithmeticProof OriginalTwoDeletionInternalVariableRegionsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem middle (raw a b i j x upper lower left right : InternalGraphComposition.OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor raw x)))
    (hi : Nonempty (Derivation body Delta (ltF i x)))
    (hj : Nonempty (Derivation body Delta (ltF x (suc j))))
    (hu : Nonempty (Derivation body Delta (graph3 eraseRaw upper b (suc j) raw)))
    (hl : Nonempty (Derivation body Delta (graph3 eraseRaw left a i upper)))
    (hd : Nonempty (Derivation body Delta (graph3 eraseRaw lower a i raw)))
    (hr : Nonempty (Derivation body Delta (graph3 eraseRaw right b j lower))) : Nonempty (Derivation body Delta (equal left right)) := by
  apply positiveCases i x _ hi
  intro beta r Theta y hh he
  simp only [equalEqn, InternalTagArithmeticSyntaxProof.eqnRelabel]
  have hv' := renameInto hv r Theta hh
  have hi' := renameInto hi r Theta hh
  have hj' := renameInto hj r Theta hh
  have hu' := renameInto hu r Theta hh
  have hl' := renameInto hl r Theta hh
  have hd' := renameInto hd r Theta hh
  have hr' := renameInto hr r Theta hh
  simp only [graph1Rename, graph3Rename, orderRename, sucRelabel] at hv' hi' hj' hu' hl' hd' hr'
  obtain ⟨he⟩ := he
  obtain ⟨hi'⟩ := hi'
  obtain ⟨hj'⟩ := hj'
  have hvy := headTransport variableConstructor (raw.relabel r) (x.relabel r) (suc y) Fin.elim0 ⟨he⟩ hv'
  have hiy := orderRight (i.relabel r) he hi'
  have hyj := orderLeft (suc (j.relabel r)) he hj'
  simpa only [equalEqn] using between (raw.relabel r) (a.relabel r) (b.relabel r) (i.relabel r) (j.relabel r) y
    (upper.relabel r) (lower.relabel r) (left.relabel r) (right.relabel r)
    hvy ⟨hiy⟩ ⟨hyj⟩ (OriginalContextInsertionBelowCoreProof.successorStrict y (j.relabel r) ⟨hyj⟩)
    hu' hl' hd' hr'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableMiddleProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableMiddleProof
