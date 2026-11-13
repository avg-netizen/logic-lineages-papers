module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentDirectProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z eqn)
open InternalTagArithmeticSupportProof (symm)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalAdditionLawsProof (add leftSuccessor)
open InternalOriginalOrderSyntaxProof (ltF)
open InternalSquareRootArithmeticSupportProof (orderRight strictWeakTrans)
open InternalUnpairReverseBoundsArithmeticProof (rightWeakAdd weakTrans)
open InternalOriginalPairingOrderArithmeticProof (weakStrictTrans)
open InternalRecursionClosureLogicProof (closedApply)
open InternalPairingSumBounds (weakBound)
open ObservationDescentDefinitions ObservationDescentPairProof ObservationDescentSelectorProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem positivePayload (tag payload root : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing root (suc tag) payload))) :
 Nonempty (Derivation body Delta (ltF payload root)) := by
 obtain ⟨h⟩ := rightWeakAdd (body := body) (Gamma := Delta) tag payload
 have hl : Nonempty (Derivation body Delta (ltF payload (add (suc tag) payload))) :=
   ⟨orderRight payload (symm (leftSuccessor tag payload)) h⟩
 exact strictWeakTrans payload (add (suc tag) payload) root hl
   (closedApply (InternalPairingSumBoundsProof.actualOriginalPairingSumBound body alpha root (suc tag) payload) hp)

theorem slotPayload (slot : DirectSlot) (payload root : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing root (numeral (directTag slot)) payload))) :
 Nonempty (Derivation body Delta (ltF payload root)) := by
 cases slot with
 | lambdaBody => exact positivePayload z payload root hp
 | function => exact positivePayload (suc z) payload root hp
 | argument => exact positivePayload (suc z) payload root hp

theorem actualDirectChildDescent : ObservationDescentTargets.ActualDirectChildDescent := by
 intro slot body alpha Delta out base inner recursive rows payload typed typ child ho hi hr hs ht
 have htp := actualSelectorBound (directPath slot) body alpha Delta payload typed hs
 have hcp := weakTrans child typed payload (pairRightBound typed typ child ht) htp
 have hcr := weakStrictTrans child payload recursive hcp (slotPayload slot payload recursive hr)
 exact strictWeakTrans child recursive out hcr (envelope out base inner recursive rows ho hi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentDirectProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentDirectProof
