module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import Mathlib.Tactic.FinCases
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksNonvariableProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andIntro)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorOtherObserverTargets EvaluatorOtherMarksLogicalProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem tagSuccessor (i : Fin 3) : tag i.succ = i.val + 3 := by
 fin_cases i <;> rfl
theorem atValues (H G : Program 1) (M W : Program 2) (i : Fin 3)
 (left right parameter mark shape spine : OTerm alpha)
 (hsl : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hsr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (htl : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral (i.val+3)) left)))
 (htr : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral (i.val+3)) right)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing shape (numeral (i.val+3)) (numeral 0))))
 (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing spine (numeral (bottomFlag i.succ)) (numeral 0)))) :
 Nonempty (Derivation body Delta (OriginalLambdaTraversalObserver.observations left right mark)) := by
 have htl' : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral (tag i.succ)) left)) := by simpa only [tagSuccessor] using htl
 have htr' : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral (tag i.succ)) right)) := by simpa only [tagSuccessor] using htr
 have hp' : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing shape (numeral (tag i.succ)) (numeral 0))) := by simpa only [tagSuccessor] using hp
 exact andIntro
   (commonValue _ left right shape mark
     (EvaluatorOtherObserverProof.actualShape H G M W body alpha Delta i.succ left parameter shape hsl htl' hp')
     (EvaluatorOtherObserverProof.actualShape H G M W body alpha Delta i.succ right parameter shape hsr htr' hp'))
   (andIntro (commonValue _ left right (numeral 0) mark
     (EvaluatorOtherObserverProof.actualNonvariableMark body alpha Delta i left htl)
     (EvaluatorOtherObserverProof.actualNonvariableMark body alpha Delta i right htr))
   (andIntro (commonValue _ left right (numeral 0) mark
     (EvaluatorOtherObserverProof.actualNeutrality H G M W body alpha Delta i.succ left parameter hsl htl')
     (EvaluatorOtherObserverProof.actualNeutrality H G M W body alpha Delta i.succ right parameter hsr htr'))
   (andIntro (commonValue _ left right spine mark
     (EvaluatorOtherObserverProof.actualSpine H G M W body alpha Delta i.succ left parameter spine hsl htl' hq)
     (EvaluatorOtherObserverProof.actualSpine H G M W body alpha Delta i.succ right parameter spine hsr htr' hq))
   (commonValue _ left right (numeral (bottomFlag i.succ)) mark
     (EvaluatorOtherObserverProof.actualBottom H G M W body alpha Delta i.succ left parameter hsl htl')
     (EvaluatorOtherObserverProof.actualBottom H G M W body alpha Delta i.succ right parameter hsr htr')))))

theorem actualNonvariable (H G : Program 1) (M W : Program 2) (i : Fin 3)
 (left right parameter mark : OTerm alpha)
 (hsl : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hsr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (htl : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral (i.val+3)) left)))
 (htr : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral (i.val+3)) right))) :
 Nonempty (Derivation body Delta (OriginalLambdaTraversalObserver.observations left right mark)) := by
 let qs : Fin 2 → Program 3 := ![pairOf (.projection 0) (.projection 2),pairOf (.projection 1) (.projection 2)]
 let xs : Fin 3 → OTerm alpha := ![numeral (i.val+3),numeral (bottomFlag i.succ),numeral 0]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 have hx : (fun a => (xs a).relabel j) = (![numeral (i.val+3),numeral (bottomFlag i.succ),numeral 0] : Fin 3 → OTerm beta) := by
   funext a
   refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) a <;>
     exact GuardedSourceSyntaxProof.numeralRename _ j
 rw [hx] at hq
 let xx : Fin 3 → OTerm beta := ![numeral (i.val+3),numeral (bottomFlag i.succ),numeral 0]
 have hp := binaryRecover InternalPairing.pairing (.projection 0) (.projection 2) (ys 0) (numeral (i.val+3)) (numeral 0)
   xx (hq 0) (projectionValue 0 xx) (projectionValue 2 xx)
 have hb := binaryRecover InternalPairing.pairing (.projection 1) (.projection 2) (ys 1) (numeral (bottomFlag i.succ)) (numeral 0)
   xx (hq 1) (projectionValue 1 xx) (projectionValue 2 xx)
 have hsl' := renameInto hsl j Theta hj
 have hsr' := renameInto hsr j Theta hj
 have htl' := renameInto htl j Theta hj
 have htr' := renameInto htr j Theta hj
 simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hsr' htl' htr'
 rw [OriginalLambdaTraversalObserverSyntaxProof.observationsRename]
 exact atValues H G M W i (left.relabel j) (right.relabel j) (parameter.relabel j) (mark.relabel j)
   (ys 0) (ys 1) hsl' hsr' htl' htr' hp hb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksNonvariableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksNonvariableProof
