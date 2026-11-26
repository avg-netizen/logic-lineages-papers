module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverSelectionOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailWiringProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalClassContextObserver
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal composition exposure, independent of any minimum or key law. -/
theorem wires (seed parameter context extended gamma tailParameter obj erasedObj erased : OTerm alpha)
    (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context extended)))
    (hobj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing obj extended seed)))
    (he : Nonempty (Derivation body Delta (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedObj obj)))
    (hparts : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedObj gamma erased)))
    (htail : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tailParameter context gamma))) :
    Nonempty (Derivation body Delta
      (graph2 (rightOf erasedObject) erased seed parameter ⊓
        graph2 parentParameter tailParameter seed parameter)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons seed (Fin.cons parameter Fin.elim0)
  have hpRight := unaryValue InternalUnpair.right (.projection 1) extended parameter xs
    (pairRight parameter context extended hparam) (projectionValue 1 xs)
  have hpLeft := unaryValue InternalUnpair.left (.projection 1) context parameter xs
    (pairLeft parameter context extended hparam) (projectionValue 1 xs)
  have hpack := binaryValue InternalPairing.pairing (rightOf (.projection 1)) (.projection 0)
    obj extended seed xs hobj hpRight (projectionValue 0 xs)
  have herased := unaryValue OriginalRawObjectTransport.eraseObjectRaw
    (pairOf (rightOf (.projection 1)) (.projection 0)) erasedObj obj xs he hpack
  have hright := unaryValue InternalUnpair.right erasedObject erased erasedObj xs
    (pairRight erasedObj gamma erased hparts) herased
  have hleft := unaryValue InternalUnpair.left erasedObject gamma erasedObj xs
    (pairLeft erasedObj gamma erased hparts) herased
  exact andIntro hright (binaryValue InternalPairing.pairing
    (leftOf (.projection 1)) (leftOf erasedObject) tailParameter context gamma xs htail hpLeft hleft)

theorem keyForward (R : Program 2) (seed parameter erased tailParameter key : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (rightOf erasedObject) erased seed parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 parentParameter tailParameter seed parameter)))
    (hk : Nonempty (Derivation body Delta (graph2 R key erased tailParameter))) :
    Nonempty (Derivation body Delta (graph2 (erasedKey R) key seed parameter)) := by
  exact binaryValue R (rightOf erasedObject) parentParameter key erased tailParameter
    (Fin.cons seed (Fin.cons parameter Fin.elim0)) hk hr hp

theorem keyBackward (R : Program 2) (seed parameter erased tailParameter key : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (rightOf erasedObject) erased seed parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 parentParameter tailParameter seed parameter)))
    (hk : Nonempty (Derivation body Delta (graph2 (erasedKey R) key seed parameter))) :
    Nonempty (Derivation body Delta (graph2 R key erased tailParameter)) := by
  exact binaryRecover R (rightOf erasedObject) parentParameter key erased tailParameter
    (Fin.cons seed (Fin.cons parameter Fin.elim0)) hk hr hp

theorem rankForward (seed parameter erased rank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (rightOf erasedObject) erased seed parameter)))
    (hk : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erased))) :
    Nonempty (Derivation body Delta (graph2 erasedRank rank seed parameter)) := by
  exact unaryValue OriginalRawSyntaxTransport.variableRankPackedRaw (rightOf erasedObject) rank erased
    (Fin.cons seed (Fin.cons parameter Fin.elim0)) hk hr

theorem rankBackward (seed parameter erased rank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (rightOf erasedObject) erased seed parameter)))
    (hk : Nonempty (Derivation body Delta (graph2 erasedRank rank seed parameter))) :
    Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erased)) := by
  exact unaryRecover OriginalRawSyntaxTransport.variableRankPackedRaw (rightOf erasedObject) rank erased
    (Fin.cons seed (Fin.cons parameter Fin.elim0)) hk hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailWiringProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailWiringProof
