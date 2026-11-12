module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableAboveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableUpperProof
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
open OriginalTwoDeletionInternalVariableAboveProof
 theorem upperRegion (raw a b i j x upper lower left right : InternalGraphComposition.OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor raw x)))
    (ho : Nonempty (Derivation body Delta (ltF i (suc j))))
    (hx : Nonempty (Derivation body Delta (ltF (suc j) x)))
    (hu : Nonempty (Derivation body Delta (graph3 eraseRaw upper b (suc j) raw)))
    (hl : Nonempty (Derivation body Delta (graph3 eraseRaw left a i upper)))
    (hd : Nonempty (Derivation body Delta (graph3 eraseRaw lower a i raw)))
    (hr : Nonempty (Derivation body Delta (graph3 eraseRaw right b j lower))) : Nonempty (Derivation body Delta (equal left right)) := by
  apply positiveCases (suc j) x _ hx
  intro beta r Theta y hh he
  simp only [equalEqn, InternalTagArithmeticSyntaxProof.eqnRelabel]
  have hv' := renameInto hv r Theta hh
  have ho' := renameInto ho r Theta hh
  have hx' := renameInto hx r Theta hh
  have hu' := renameInto hu r Theta hh
  have hl' := renameInto hl r Theta hh
  have hd' := renameInto hd r Theta hh
  have hr' := renameInto hr r Theta hh
  simp only [graph1Rename, graph3Rename, orderRename, sucRelabel] at hv' ho' hx' hu' hl' hd' hr'
  obtain ⟨he⟩ := he
  obtain ⟨hx'⟩ := hx'
  have hvy := headTransport variableConstructor (raw.relabel r) (x.relabel r) (suc y) Fin.elim0 ⟨he⟩ hv'
  have hjy := orderRight (suc (j.relabel r)) he hx'
  simpa only [equalEqn] using aboveSuccessorCase (raw.relabel r) (a.relabel r) (b.relabel r) (i.relabel r) (j.relabel r) y
    (upper.relabel r) (lower.relabel r) (left.relabel r) (right.relabel r)
    hvy ho' ⟨hjy⟩ (OriginalContextInsertionBelowCoreProof.successorStrict (j.relabel r) y ⟨hjy⟩)
    hu' hl' hd' hr'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableUpperProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableUpperProof
