module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionChoiceSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedFactorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionLocalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof
open OriginalHereditaryLambda (atState)
open OriginalHereditaryLambdaChildControlProof (nonzeroBranchElim nonzeroBranchIntro)
open OriginalLambdaGuardLeafInternalProof (projectLeft projectRight)
open OriginalLambdaGuardLeafInternalChildProof (fourTuple)
open OriginalMixedClosedRecognitionStateSupportProof
open OriginalMixedClosedRecognitionChoiceSupportProof
open OriginalMixedDirectBottomTraceDescentProof (choice)
open OriginalMixedDirectBottomTrace
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (sucNeZero)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The checked literal four-input factor, expressed with its original input
vector. All wrapper suppliers are discharged by the inherited proof. -/
theorem rawFactor (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (window : Program 1)
 (xs : Fin 4 → OTerm alpha)
 (h : Nonempty (Derivation body Delta (programGraph
  (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) (suc z) xs))) :
 Nonempty (Derivation body Delta (programGraph
  (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (suc z) xs)) := by
 rw [← fourTuple xs] at h ⊢
 exact OriginalMixedClosedFactorProof.actualRawFactor H G M W oldStep window body alpha Delta
  (xs 0) (xs 1) (xs 2) (xs 3) h

/-- Terminal provenance retains its original source and direct-bottom
checks while the actual closed leaf is factored at the same input vector. -/
theorem terminalFactor (source : Program 2) (H G : Program 1) (M W : Program 2)
 (oldStep : Program 4) (window : Program 1) (xs : Fin 4 → OTerm alpha)
 (h : Nonempty (Derivation body Delta (programGraph
  (terminal source (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)) (suc z) xs))) :
 Nonempty (Derivation body Delta (programGraph
  (terminal source (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) (suc z) xs)) := by
 let C := OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window
 let L := OriginalTransparentMixedDirectBottom.leaf H G M W oldStep
 have hp := conjunctionRecover (OriginalTransparentVariableStep.sourceAt source)
  (InternalAcceptance.conjunction C OriginalTransparentDirectBottom.active) xs h
 have hinner := conjunctionRecover C OriginalTransparentDirectBottom.active xs (projectRight hp)
 exact conjunctionAccept (OriginalTransparentVariableStep.sourceAt source)
  (InternalAcceptance.conjunction L OriginalTransparentDirectBottom.active) xs (projectLeft hp)
  (conjunctionAccept L OriginalTransparentDirectBottom.active xs
   (rawFactor H G M W oldStep window xs (projectLeft hinner)) (projectRight hinner))

theorem finishFactor : OriginalMixedClosedRecognitionTargets.FinishFactor := by
 intro source H G M W oldStep window body alpha Delta out hf
 let C := OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window
 let L := OriginalTransparentMixedDirectBottom.leaf H G M W oldStep
 have hn := nonzeroInput (finish source C) (suc z) out
  (OriginalMixedDirectBottomTraceProof.rejectZero source C body alpha Delta).2 hf ⟨sucNeZero z⟩
 have ht := nonzeroBranchElim (.projection 0) (InternalAcceptance.constantZero 1)
  (atState (terminal source C)) (suc z) out (Fin.cons out Fin.elim0)
  (projectionValue 0 (Fin.cons out Fin.elim0)) hn hf
 have ht' := atStateFactor (terminal source C) (terminal source L)
  (fun beta Theta xs h => terminalFactor source H G M W oldStep window xs h) out ht
 exact nonzeroBranchIntro (.projection 0) (InternalAcceptance.constantZero 1)
  (atState (terminal source L)) (suc z) out (Fin.cons out Fin.elim0)
  (projectionValue 0 (Fin.cons out Fin.elim0)) hn ht'

theorem acceptedStep : OriginalMixedClosedRecognitionTargets.AcceptedStep := by
 intro source H G M W oldStep window body alpha Delta state next ht hn
 let C := OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window
 let L := OriginalTransparentMixedDirectBottom.leaf H G M W oldStep
 let a1 := atState OriginalHereditaryLambda.childLive
 let a2 := atState OriginalTransparentApplicationFunctionDefinitions.childLive
 let activeC := choice (atState (lambdaHop source C)) (atState (applicationHop source C)) a1 a2
 let activeL := choice (atState (lambdaHop source L)) (atState (applicationHop source L)) a1 a2
 have hs := nonzeroInput (transition source C) next state
  (OriginalMixedDirectBottomTraceProof.rejectZero source C body alpha Delta).1 ht hn
 have ha : Nonempty (Derivation body Delta (graph1 activeC next state)) :=
  nonzeroBranchElim (.projection 0) (InternalAcceptance.constantZero 1) activeC
   next state (Fin.cons state Fin.elim0) (projectionValue 0 (Fin.cons state Fin.elim0)) hs ht
 have hb : Nonempty (Derivation body Delta (graph1 activeL next state)) :=
  choiceFactor (OriginalTransparentLambdaStep.hopGuard source)
   (OriginalTransparentApplicationFunctionDefinitions.hopGuard source) C L a1 a2
   (fun beta Theta s h => atStateFactor C L
    (fun gamma Xi xs hx => rawFactor H G M W oldStep window xs hx) s h)
   state next hn ha
 exact nonzeroBranchIntro (.projection 0) (InternalAcceptance.constantZero 1) activeL
  next state (Fin.cons state Fin.elim0) (projectionValue 0 (Fin.cons state Fin.elim0)) hs hb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionLocalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionLocalProof
