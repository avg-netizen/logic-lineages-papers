module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionResultProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedApplicationResultStackComposition InternalApplicationCertificateConstructors
open InternalApplicationResultStackComposition (liveState)
open InternalApplicationValidityStackAppend (append)
open InternalParameterizedApplicationResultStackCompositionSyntaxProof InternalApplicationResultStackCompositionStateProof
open InternalParameterizedApplicationResultStackCompositionRunProof InternalParameterizedApplicationResultStackCompositionBasicProof
open InternalParameterizedApplicationResultStackCompositionStepProof InternalParameterizedApplicationResultStackCompositionFrameProof
open InternalParameterizedApplicationResultStackCompositionInductionSyntaxProof InternalParameterizedApplicationResultStackCompositionInductionCoreProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem successorAtStates (guard leaf : Program 2) (combine : Program 5) (parameter : OTerm α)
    (count work initialResults finalResults background framedInitial framedFinal state framedState : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (resultRow guard leaf combine parameter count)))
    (hr : Nonempty (Derivation body Gamma
      (run guard leaf combine parameter (suc count) work initialResults finalResults)))
    (hi : Nonempty (Derivation body Gamma (graph2 append framedInitial initialResults background)))
    (hf : Nonempty (Derivation body Gamma (graph2 append framedFinal finalResults background)))
    (hstate : Nonempty (Derivation body Gamma (graph2 liveState state work initialResults)))
    (hframed : Nonempty (Derivation body Gamma (graph2 liveState framedState work framedInitial))) :
    Nonempty (Derivation body Gamma
      (run guard leaf combine parameter (suc count) work framedInitial framedFinal)) := by
  apply resultFrameCases guard leaf combine parameter work initialResults background framedInitial state framedState _ hi hstate hframed
  · intro β j Delta hj ht
    have hr' := renameInto hr j Delta hj
    have hstate' := renameInto hstate j Delta hj
    simp only [actualRunRename,sucRelabel] at hr'
    rw [graph2Rename] at hstate'
    obtain ⟨hbot⟩ := runCannotFail guard leaf combine (parameter.relabel j) (count.relabel j) (work.relabel j)
      (initialResults.relabel j) (finalResults.relabel j) (state.relabel j) hstate' ht hr'
    exact ⟨Derivation.explosion hbot⟩
  · intro β j Delta nextWork nextResults framedNextResults nextState framedNextState hj haNext hnState hfnState ht hft
    simp only [actualRunRename,sucRelabel]
    have hr' := renameInto hr j Delta hj
    have hf' := renameInto hf j Delta hj
    have hrow' := renameInto hrow j Delta hj
    have hstate' := renameInto hstate j Delta hj
    have hframed' := renameInto hframed j Delta hj
    simp only [actualRunRename,sucRelabel] at hr'
    rw [graph2Rename] at hf' hstate' hframed'
    rw [resultRowRename] at hrow'
    have hnext := runFrontForward guard leaf combine (parameter.relabel j) (count.relabel j) (work.relabel j)
      (initialResults.relabel j) (finalResults.relabel j) (state.relabel j)
      nextWork nextResults nextState hstate' hnState ht hr'
    have hframe := resultRowApply guard leaf combine (parameter.relabel j) (count.relabel j) nextWork nextResults
      (finalResults.relabel j) (background.relabel j) framedNextResults (framedFinal.relabel j)
      hrow' hnext haNext hf'
    exact runFrontBackward guard leaf combine (parameter.relabel j) (count.relabel j) (work.relabel j)
      (framedInitial.relabel j) (framedFinal.relabel j) (framedState.relabel j)
      nextWork framedNextResults framedNextState hframed' hfnState hft hframe

def stateQueries : Fin 2 → Program 3 :=
  fun i => .composition liveState (Fin.cons (.projection 0) (Fin.cons (.projection i.succ) Fin.elim0))

theorem succCore (guard leaf : Program 2) (combine : Program 5) (parameter : OTerm α)
    (count work initialResults finalResults background framedInitial framedFinal : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (resultRow guard leaf combine parameter count)))
    (hr : Nonempty (Derivation body Gamma
      (run guard leaf combine parameter (suc count) work initialResults finalResults)))
    (hi : Nonempty (Derivation body Gamma (graph2 append framedInitial initialResults background)))
    (hf : Nonempty (Derivation body Gamma (graph2 append framedFinal finalResults background))) :
    Nonempty (Derivation body Gamma
      (run guard leaf combine parameter (suc count) work framedInitial framedFinal)) := by
  apply queryCases stateQueries (Fin.cons work (Fin.cons initialResults (Fin.cons framedInitial Fin.elim0))) _
  intro β j ys Delta hj hq
  simp only [actualRunRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hq
  have hrow' := renameInto hrow j Delta hj
  have hr' := renameInto hr j Delta hj
  have hi' := renameInto hi j Delta hj
  have hf' := renameInto hf j Delta hj
  rw [resultRowRename] at hrow'
  simp only [actualRunRename,sucRelabel] at hr'
  rw [graph2Rename] at hi' hf'
  let xs : Fin 3 → OTerm β := Fin.cons (work.relabel j)
    (Fin.cons (initialResults.relabel j) (Fin.cons (framedInitial.relabel j) Fin.elim0))
  have hp := binaryRecover liveState (.projection 0) (.projection 1)
    (ys 0) (work.relabel j) (initialResults.relabel j) xs (hq 0)
    (projectionValue 0 xs) (projectionValue 1 xs)
  have hfp := binaryRecover liveState (.projection 0) (.projection 2)
    (ys 1) (work.relabel j) (framedInitial.relabel j) xs (hq 1)
    (projectionValue 0 xs) (projectionValue 2 xs)
  exact successorAtStates guard leaf combine (parameter.relabel j) (count.relabel j) (work.relabel j)
    (initialResults.relabel j) (finalResults.relabel j) (background.relabel j)
    (framedInitial.relabel j) (framedFinal.relabel j) (ys 0) (ys 1) hrow' hr' hi' hf' hp hfp

theorem succRow (guard leaf : Program 2) (combine : Program 5) (parameter : OTerm α) (count : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (resultRow guard leaf combine parameter count))) :
    Nonempty (Derivation body Gamma (resultRow guard leaf combine parameter (suc count))) := by
  unfold resultRow
  apply actualFiniteUniversalIntroduction body α 6 Gamma
  let work : OTerm (α ⊕ Fin 6) := .var (.inr 0)
  let initialResults : OTerm (α ⊕ Fin 6) := .var (.inr 1)
  let finalResults : OTerm (α ⊕ Fin 6) := .var (.inr 2)
  let background : OTerm (α ⊕ Fin 6) := .var (.inr 3)
  let framedInitial : OTerm (α ⊕ Fin 6) := .var (.inr 4)
  let framedFinal : OTerm (α ⊕ Fin 6) := .var (.inr 5)
  let p := parameter.relabel (Sum.inl : α → α ⊕ Fin 6)
  let n := count.relabel (Sum.inl : α → α ⊕ Fin 6)
  let A := run guard leaf combine p (suc n) work initialResults finalResults ⊓
    (graph2 append framedInitial initialResults background ⊓ graph2 append framedFinal finalResults background)
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 6))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [resultRowRename] at hrow'
  obtain ⟨d⟩ := succCore guard leaf combine p n work initialResults finalResults background framedInitial framedFinal hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [resultBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem allRows (guard leaf : Program 2) (combine : Program 5) (parameter : OTerm α) (count : OTerm α) :
    Nonempty (Derivation body Gamma (resultRow guard leaf combine parameter count)) := by
  let theta : Formula (α ⊕ Fin 1) := resultRow guard leaf combine (parameter.relabel Sum.inl) (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,resultInstantiate,varBind,liftBind] using
      (resultZeroRow (body := body) (Gamma := Gamma) guard leaf combine parameter)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Gamma := theta :: Gamma.map weaken)
      guard leaf combine (parameter.relabel Sum.inl) (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,resultSuccessor,InternalAdditionLawsProof.liftNext,InternalAdditionLawsProof.varNext] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,resultInstantiate,varBind,liftBind] using (Nonempty.intro h)

theorem actualOriginalParameterizedResultStackResultSuffixFrame :
    InternalParameterizedApplicationResultStackCompositionTargets.ActualOriginalParameterizedResultStackResultSuffixFrame := by
  intro body guard leaf combine α Gamma count work initialResults finalResults background framedInitial framedFinal parameter
  let A := run guard leaf combine parameter count work initialResults finalResults ⊓
    (graph2 append framedInitial initialResults background ⊓ graph2 append framedFinal finalResults background)
  have h : Nonempty (Derivation body (A :: Gamma) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := resultRowApply guard leaf combine parameter count work initialResults finalResults background framedInitial framedFinal
    (allRows guard leaf combine parameter count) (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionResultProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionResultProof
