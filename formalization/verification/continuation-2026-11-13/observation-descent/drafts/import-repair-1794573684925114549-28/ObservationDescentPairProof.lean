module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentPairProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionClosureLogicProof (closedApply)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (suc z eqn)
open InternalOriginalOrderSyntaxProof (ltF orderRename sucRelabel)
open InternalUnpairReverseBoundsArithmeticProof (weakTrans)
open InternalRecursionGraphStepSyntaxProof
open InternalRawListRecursionSyntaxProof (consTermRename emptyRename)
open InternalPairingSumBounds (weakBound)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem pairLeftBound (pair left right : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair left right))) :
 Nonempty (Derivation body Delta (weakBound left pair)) :=
 andLeft (closedApply (InternalUnpairReverseBoundsProof.actualOriginalPairingCoordinateBounds body alpha pair left right) hp)

theorem pairRightBound (pair left right : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair left right))) :
 Nonempty (Derivation body Delta (weakBound right pair)) :=
 andRight (closedApply (InternalUnpairReverseBoundsProof.actualOriginalPairingCoordinateBounds body alpha pair left right) hp)

theorem leftBound (input selected : OTerm alpha)
 (h : Nonempty (Derivation body Delta (graph1 InternalUnpair.left selected input))) :
 Nonempty (Derivation body Delta (weakBound selected input)) := by
 apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
 intro beta j Theta other hj ho
 simp only [weakBound,orderRename,sucRelabel]
 simp only [consTermRename,emptyRename] at ho
 have h' := renameInto h j Theta hj
 simp only [graph1,programRename,consTermRename,emptyRename] at h'
 exact andLeft (closedApply
   (InternalUnpairReverseBoundsProof.actualOriginalUnpairCoordinateBounds body beta
     (input.relabel j) (selected.relabel j) other) (andIntro h' ho))

theorem rightBound (input selected : OTerm alpha)
 (h : Nonempty (Derivation body Delta (graph1 InternalUnpair.right selected input))) :
 Nonempty (Derivation body Delta (weakBound selected input)) := by
 apply programCases InternalUnpair.left (Fin.cons input Fin.elim0) _
 intro beta j Theta other hj ho
 simp only [weakBound,orderRename,sucRelabel]
 simp only [consTermRename,emptyRename] at ho
 have h' := renameInto h j Theta hj
 simp only [graph1,programRename,consTermRename,emptyRename] at h'
 exact andRight (closedApply
   (InternalUnpairReverseBoundsProof.actualOriginalUnpairCoordinateBounds body beta
     (input.relabel j) other (selected.relabel j)) (andIntro ho h'))

theorem envelope (out base inner recursive rows : OTerm alpha)
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner recursive rows))) :
 Nonempty (Derivation body Delta (weakBound recursive out)) :=
 weakTrans recursive inner out (pairLeftBound inner recursive rows hi) (pairRightBound out base inner ho)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentPairProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentPairProof
