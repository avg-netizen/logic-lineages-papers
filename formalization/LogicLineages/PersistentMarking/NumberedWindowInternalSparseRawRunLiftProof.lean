module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShiftProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue headTransport)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (orderCases)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb eqn bindEmbedding nextEmbedding liftBind varBind zSubst zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction symm trans addZero addSucc)
open ID1Completion.InternalAdditionLawsProof (add addSubst liftNext varNext)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseRawTick (chosenTick stateFrame performLive)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickOpenScratchProof (frameRead)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename stateSubst)
open NumberedWindowInternalSparseRawRun (iterateState)
open NumberedWindowInternalSparseRawRunShapeMotiveProof (pairRename pairSubst)
open NumberedWindowInternalSparseRawRunShiftProof (runSuccessor shiftLate)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The #689 terminal tick in an arbitrary context. -/
theorem terminalTick (p other : Program 3) (flag : OTerm α) :
    Nonempty (Derivation body Γ
      (programGraph (chosenTick p other) (stateTerm flag z) ![stateTerm flag z])) :=
  zeroBranchIntro stateFrame (.projection 0) (performLive p other) (stateTerm flag z)
    ![stateTerm flag z] (frameRead flag z) (projectionValue 0 ![stateTerm flag z])

/-- One more unit of fuel at a reached terminal scratch. The reached
output is fed as the prior result; the original start stays in the
recursor's input slot and is unrelated to it. -/
theorem terminalOneMore (p other : Program 3) (flag start fuel : OTerm α)
    (h : Nonempty (Derivation body Γ
      (programGraph (iterateState p other) (stateTerm flag z) ![fuel,start]))) :
    Nonempty (Derivation body Γ
      (programGraph (iterateState p other) (stateTerm flag z) ![suc fuel,start])) :=
  runSuccessor p other (stateTerm flag z) (stateTerm flag z) fuel start h
    (terminalTick p other flag)

private theorem fuelSubst {α β : Type} (p other : Program 3) (t fuel gap start : OTerm α)
    (ts : α → OTerm β) :
    (programGraph (iterateState p other) t ![add fuel gap,start]).subst (fun a => emb (ts a)) =
      programGraph (iterateState p other) (t.subst ts)
        ![add (fuel.subst ts) (gap.subst ts),start.subst ts] := by
  rw [programSubst,pairSubst,addSubst]

/-- Object induction on the gap, with the original addition axioms. -/
theorem terminalExtra (p other : Program 3) (flag start fuel gap : OTerm α)
    (h : Nonempty (Derivation body Γ
      (programGraph (iterateState p other) (stateTerm flag z) ![fuel,start]))) :
    Nonempty (Derivation body Γ
      (programGraph (iterateState p other) (stateTerm flag z) ![add fuel gap,start])) := by
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let j : α → α ⊕ Fin 1 := Sum.inl
  let flag' : OTerm (α ⊕ Fin 1) := flag.relabel j
  let fuel' : OTerm (α ⊕ Fin 1) := fuel.relabel j
  let start' : OTerm (α ⊕ Fin 1) := start.relabel j
  let theta : Formula (α ⊕ Fin 1) :=
    programGraph (iterateState p other) (stateTerm flag' z) ![add fuel' v,start']
  have inst (t : OTerm α) : instantiate theta (emb t) =
      programGraph (iterateState p other) (stateTerm flag z) ![add fuel t,start] := by
    simp only [theta,instantiate,bindEmbedding,fuelSubst,stateSubst,zSubst,flag',fuel',start',
      j,v,liftBind,varBind]
  have next : successorInstance theta =
      programGraph (iterateState p other) (stateTerm flag' z) ![add fuel' (suc v),start'] := by
    simp only [theta,successorInstance,nextEmbedding,fuelSubst,stateSubst,zSubst,flag',fuel',
      start',j,v,liftNext,varNext]
  obtain ⟨base⟩ := headTransport (iterateState p other) (stateTerm flag z) fuel (add fuel z)
    ![start] ⟨symm (addZero fuel)⟩ h
  have ih : Nonempty (Derivation body (theta :: Γ.map weaken) theta) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have more := terminalOneMore p other flag' start' (add fuel' v) ih
  obtain ⟨stepd⟩ := headTransport (iterateState p other) (stateTerm flag' z)
    (suc (add fuel' v)) (add fuel' (suc v)) ![start'] ⟨symm (addSucc fuel' v)⟩ more
  have result := Derivation.universalElimination (emb gap)
    (natInduction theta (by rw [inst]; exact base) (by rw [next]; exact stepd))
  rw [inst] at result
  exact ⟨result⟩

/-- Extra fuel related by the original object order. -/
theorem terminalLater (p other : Program 3) (flag start fuel more : OTerm α)
    (hlt : Nonempty (Derivation body Γ (ltF fuel more)))
    (h : Nonempty (Derivation body Γ
      (programGraph (iterateState p other) (stateTerm flag z) ![fuel,start]))) :
    Nonempty (Derivation body Γ
      (programGraph (iterateState p other) (stateTerm flag z) ![more,start])) := by
  apply orderCases Γ fuel more _ hlt
  intro β j Δ w hj he
  rw [programRename,pairRename,stateRename,zRelabel]
  have h' := renameInto h j Δ hj
  rw [programRename,pairRename,stateRename,zRelabel] at h'
  have extra := terminalExtra p other (flag.relabel j) (start.relabel j) (fuel.relabel j)
    (suc w) h'
  exact headTransport (iterateState p other) (stateTerm (flag.relabel j) z)
    (add (fuel.relabel j) (suc w)) (more.relabel j) ![start.relabel j] he extra

/-- Extra fuel on the next scratch, then one first-tick shift. -/
theorem runLift (p other : Program 3) (flag start next fuel more : OTerm α)
    (ht : Nonempty (Derivation body Γ (programGraph (chosenTick p other) next ![start])))
    (hlt : Nonempty (Derivation body Γ (ltF fuel more)))
    (h : Nonempty (Derivation body Γ
      (programGraph (iterateState p other) (stateTerm flag z) ![fuel,next]))) :
    Nonempty (Derivation body Γ
      (programGraph (iterateState p other) (stateTerm flag z) ![more,start])) := by
  apply orderCases Γ fuel more _ hlt
  intro β j Δ w hj he
  rw [programRename,pairRename,stateRename,zRelabel]
  have h' := renameInto h j Δ hj
  rw [programRename,pairRename,stateRename,zRelabel] at h'
  have ht' := renameInto ht j Δ hj
  rw [programRename,inputsRename] at ht'
  have extra := terminalExtra p other (flag.relabel j) (next.relabel j) (fuel.relabel j) w h'
  have late := shiftLate p other (start.relabel j) (next.relabel j)
    (add (fuel.relabel j) w) (stateTerm (flag.relabel j) z) ht' extra
  obtain ⟨de⟩ := he
  exact headTransport (iterateState p other) (stateTerm (flag.relabel j) z)
    (suc (add (fuel.relabel j) w)) (more.relabel j) ![start.relabel j]
    ⟨trans (symm (addSucc (fuel.relabel j) w)) de⟩ late

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftProof
