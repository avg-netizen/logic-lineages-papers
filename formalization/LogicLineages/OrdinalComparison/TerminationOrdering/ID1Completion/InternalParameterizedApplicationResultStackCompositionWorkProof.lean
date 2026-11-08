module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionWorkProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedApplicationResultStackComposition InternalApplicationCertificateConstructors
open InternalApplicationResultStackComposition (liveState)
open InternalApplicationValidityStackAppend (append)
open InternalParameterizedApplicationResultStackCompositionSyntaxProof InternalApplicationResultStackCompositionStateProof
open InternalParameterizedApplicationResultStackCompositionRunProof InternalParameterizedApplicationResultStackCompositionBasicProof
open InternalParameterizedApplicationResultStackCompositionStepProof InternalParameterizedApplicationResultStackCompositionFrameProof
open InternalParameterizedApplicationResultStackCompositionInductionSyntaxProof InternalParameterizedApplicationResultStackCompositionInductionCoreProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem nonemptyAtStates (guard leaf : Program 2) (combine : Program 5) (parameter : OTerm α)
    (count second frontWork suffix joined initialResults middleResults finalResults state joinedState : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (workRow guard leaf combine parameter count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma
      (run guard leaf combine parameter (suc count) frontWork initialResults middleResults)))
    (hs : Nonempty (Derivation body Gamma
      (run guard leaf combine parameter second suffix middleResults finalResults)))
    (hn : Nonempty (Derivation body Gamma (eqn frontWork z).not))
    (hstate : Nonempty (Derivation body Gamma (graph2 liveState state frontWork initialResults)))
    (hjoined : Nonempty (Derivation body Gamma (graph2 liveState joinedState joined initialResults))) :
    Nonempty (Derivation body Gamma
      (run guard leaf combine parameter (add (suc count) second) joined initialResults finalResults)) := by
  apply workFrameCases guard leaf combine parameter frontWork suffix joined initialResults state joinedState _ hn ha hstate hjoined
  · intro β j Delta hj ht
    have hf' := renameInto hf j Delta hj
    have hstate' := renameInto hstate j Delta hj
    simp only [actualRunRename,sucRelabel] at hf'
    rw [graph2Rename] at hstate'
    obtain ⟨hbot⟩ := runCannotFail guard leaf combine (parameter.relabel j) (count.relabel j) (frontWork.relabel j)
      (initialResults.relabel j) (middleResults.relabel j) (state.relabel j) hstate' ht hf'
    exact ⟨Derivation.explosion hbot⟩
  · intro β j Delta nextWork joinedNext nextResults nextState joinedNextState hj haNext hnState hjnState ht hjt
    simp only [actualRunRename,addRelabel,sucRelabel]
    have hf' := renameInto hf j Delta hj
    have hs' := renameInto hs j Delta hj
    have hrow' := renameInto hrow j Delta hj
    have hstate' := renameInto hstate j Delta hj
    have hjoined' := renameInto hjoined j Delta hj
    simp only [actualRunRename,sucRelabel] at hf'
    rw [actualRunRename] at hs'
    rw [workRowRename] at hrow'
    rw [graph2Rename] at hstate' hjoined'
    have hnext := runFrontForward guard leaf combine (parameter.relabel j) (count.relabel j) (frontWork.relabel j)
      (initialResults.relabel j) (middleResults.relabel j) (state.relabel j)
      nextWork nextResults nextState hstate' hnState ht hf'
    have hcombined := workRowApply guard leaf combine (parameter.relabel j) (count.relabel j) (second.relabel j)
      nextWork (suffix.relabel j) joinedNext nextResults (middleResults.relabel j)
      (finalResults.relabel j) hrow' haNext hnext hs'
    have hback := runFrontBackward guard leaf combine (parameter.relabel j) (add (count.relabel j) (second.relabel j))
      (joined.relabel j) (initialResults.relabel j) (finalResults.relabel j)
      (joinedState.relabel j) joinedNext nextResults joinedNextState hjoined' hjnState hjt hcombined
    exact countTransport guard leaf combine (parameter.relabel j) (suc (add (count.relabel j) (second.relabel j)))
      (add (suc (count.relabel j)) (second.relabel j)) (joined.relabel j)
      (initialResults.relabel j) (finalResults.relabel j)
      ⟨symm (leftSuccessor (count.relabel j) (second.relabel j))⟩ hback

def stateQueries : Fin 2 → Program 3 :=
  fun i => .composition liveState (Fin.cons (.projection i.castSucc) (Fin.cons (.projection 2) Fin.elim0))

theorem nonemptyCore (guard leaf : Program 2) (combine : Program 5) (parameter : OTerm α)
    (count second frontWork suffix joined initialResults middleResults finalResults : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (workRow guard leaf combine parameter count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma
      (run guard leaf combine parameter (suc count) frontWork initialResults middleResults)))
    (hs : Nonempty (Derivation body Gamma
      (run guard leaf combine parameter second suffix middleResults finalResults)))
    (hn : Nonempty (Derivation body Gamma (eqn frontWork z).not)) :
    Nonempty (Derivation body Gamma
      (run guard leaf combine parameter (add (suc count) second) joined initialResults finalResults)) := by
  apply queryCases stateQueries (Fin.cons frontWork (Fin.cons joined (Fin.cons initialResults Fin.elim0))) _
  intro β j ys Delta hj hq
  simp only [actualRunRename,addRelabel,sucRelabel]
  simp only [consTermRename,emptyRename] at hq
  have hrow' := renameInto hrow j Delta hj
  have ha' := renameInto ha j Delta hj
  have hf' := renameInto hf j Delta hj
  have hs' := renameInto hs j Delta hj
  have hn' := renameInto hn j Delta hj
  rw [workRowRename] at hrow'
  rw [graph2Rename] at ha'
  simp only [actualRunRename,sucRelabel] at hf'
  rw [actualRunRename] at hs'
  simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
  let xs : Fin 3 → OTerm β := Fin.cons (frontWork.relabel j)
    (Fin.cons (joined.relabel j) (Fin.cons (initialResults.relabel j) Fin.elim0))
  have hp := binaryRecover liveState (.projection 0) (.projection 2)
    (ys 0) (frontWork.relabel j) (initialResults.relabel j) xs (hq 0)
    (projectionValue 0 xs) (projectionValue 2 xs)
  have hjp := binaryRecover liveState (.projection 1) (.projection 2)
    (ys 1) (joined.relabel j) (initialResults.relabel j) xs (hq 1)
    (projectionValue 1 xs) (projectionValue 2 xs)
  exact nonemptyAtStates guard leaf combine (parameter.relabel j) (count.relabel j) (second.relabel j)
    (frontWork.relabel j) (suffix.relabel j) (joined.relabel j) (initialResults.relabel j)
    (middleResults.relabel j) (finalResults.relabel j) (ys 0) (ys 1) hrow' ha' hf' hs' hn' hp hjp

theorem succCore (guard leaf : Program 2) (combine : Program 5) (parameter : OTerm α)
    (count second frontWork suffix joined initialResults middleResults finalResults : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (workRow guard leaf combine parameter count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma
      (run guard leaf combine parameter (suc count) frontWork initialResults middleResults)))
    (hs : Nonempty (Derivation body Gamma
      (run guard leaf combine parameter second suffix middleResults finalResults))) :
    Nonempty (Derivation body Gamma
      (run guard leaf combine parameter (add (suc count) second) joined initialResults finalResults)) := by
  apply formulaCases (eqn frontWork z)
  · exact workEmptyCore guard leaf combine parameter (suc count) second frontWork suffix joined
      initialResults middleResults finalResults ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp ha _) (withHyp hf _) (withHyp hs _)
  · exact nonemptyCore guard leaf combine parameter count second frontWork suffix joined
      initialResults middleResults finalResults (withHyp hrow _) (withHyp ha _) (withHyp hf _) (withHyp hs _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem succRow (guard leaf : Program 2) (combine : Program 5) (parameter : OTerm α) (count : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (workRow guard leaf combine parameter count))) :
    Nonempty (Derivation body Gamma (workRow guard leaf combine parameter (suc count))) := by
  unfold workRow
  apply actualFiniteUniversalIntroduction body α 7 Gamma
  let second : OTerm (α ⊕ Fin 7) := .var (.inr 0)
  let frontWork : OTerm (α ⊕ Fin 7) := .var (.inr 1)
  let suffix : OTerm (α ⊕ Fin 7) := .var (.inr 2)
  let joined : OTerm (α ⊕ Fin 7) := .var (.inr 3)
  let initialResults : OTerm (α ⊕ Fin 7) := .var (.inr 4)
  let middleResults : OTerm (α ⊕ Fin 7) := .var (.inr 5)
  let finalResults : OTerm (α ⊕ Fin 7) := .var (.inr 6)
  let p := parameter.relabel (Sum.inl : α → α ⊕ Fin 7)
  let n := count.relabel (Sum.inl : α → α ⊕ Fin 7)
  let A := graph2 append joined frontWork suffix ⊓
    (run guard leaf combine p (suc n) frontWork initialResults middleResults ⊓
      run guard leaf combine p second suffix middleResults finalResults)
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 7))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [workRowRename] at hrow'
  obtain ⟨d⟩ := succCore guard leaf combine p n second frontWork suffix joined initialResults middleResults finalResults hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [workBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem allRows (guard leaf : Program 2) (combine : Program 5) (parameter : OTerm α) (count : OTerm α) :
    Nonempty (Derivation body Gamma (workRow guard leaf combine parameter count)) := by
  let theta : Formula (α ⊕ Fin 1) := workRow guard leaf combine (parameter.relabel Sum.inl) (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,workInstantiate,varBind,liftBind] using
      (workZeroRow (body := body) (Gamma := Gamma) guard leaf combine parameter)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Gamma := theta :: Gamma.map weaken)
      guard leaf combine (parameter.relabel Sum.inl) (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,workSuccessor,InternalAdditionLawsProof.liftNext,InternalAdditionLawsProof.varNext] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,workInstantiate,varBind,liftBind] using (Nonempty.intro h)

theorem actualOriginalParameterizedResultStackWorkAppend :
    InternalParameterizedApplicationResultStackCompositionTargets.ActualOriginalParameterizedResultStackWorkAppend := by
  intro body guard leaf combine α Gamma first second frontWork suffix joined initialResults middleResults finalResults parameter
  let A := graph2 append joined frontWork suffix ⊓
    (run guard leaf combine parameter first frontWork initialResults middleResults ⊓
      run guard leaf combine parameter second suffix middleResults finalResults)
  have h : Nonempty (Derivation body (A :: Gamma) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := workRowApply guard leaf combine parameter first second frontWork suffix joined initialResults middleResults finalResults
    (allRows guard leaf combine parameter first) (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionWorkProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionWorkProof
