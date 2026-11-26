module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableMiddleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableAboveProof
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
theorem aboveSuccessorCase (raw a b i j x upper lower left right : InternalGraphComposition.OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor raw (suc x))))
    (ho : Nonempty (Derivation body Delta (ltF i (suc j))))
    (hjx : Nonempty (Derivation body Delta (ltF (suc j) (suc x))))
    (hx : Nonempty (Derivation body Delta (ltF j x)))
    (hu : Nonempty (Derivation body Delta (graph3 eraseRaw upper b (suc j) raw)))
    (hl : Nonempty (Derivation body Delta (graph3 eraseRaw left a i upper)))
    (hd : Nonempty (Derivation body Delta (graph3 eraseRaw lower a i raw)))
    (hr : Nonempty (Derivation body Delta (graph3 eraseRaw right b j lower))) : Nonempty (Derivation body Delta (equal left right)) := by
  apply positiveCases j x _ hx
  intro beta r Theta y hh he
  simp only [equalEqn, InternalTagArithmeticSyntaxProof.eqnRelabel]
  have hv' := renameInto hv r Theta hh
  have ho' := renameInto ho r Theta hh
  have hjx' := renameInto hjx r Theta hh
  have hx' := renameInto hx r Theta hh
  have hu' := renameInto hu r Theta hh
  have hl' := renameInto hl r Theta hh
  have hd' := renameInto hd r Theta hh
  have hr' := renameInto hr r Theta hh
  simp only [graph1Rename, graph3Rename, orderRename, sucRelabel] at hv' ho' hjx' hx' hu' hl' hd' hr'
  obtain ⟨he⟩ := he
  obtain ⟨hx'⟩ := hx'
  obtain ⟨ho'⟩ := ho'
  have hxy := orderRight (j.relabel r) he hx'
  have hvy := headTransport variableConstructor (raw.relabel r) (suc (x.relabel r)) (suc (suc y)) Fin.elim0 ⟨congSuc he⟩ hv'
  have hiy := weakStrictTrans (i.relabel r) (j.relabel r) (suc y) ⟨ho'⟩ ⟨hxy⟩
  obtain ⟨hjx'⟩ := hjx'
  have hjyy := orderRight (suc (j.relabel r)) (congSuc he) hjx'
  simpa only [equalEqn] using aboveBoth (raw.relabel r) (a.relabel r) (b.relabel r) (i.relabel r) (j.relabel r) y
    (upper.relabel r) (lower.relabel r) (left.relabel r) (right.relabel r)
    hvy (rightSuccessor _ _ hiy) ⟨hjyy⟩ hiy ⟨hxy⟩ hu' hl' hd' hr'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableAboveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableAboveProof
