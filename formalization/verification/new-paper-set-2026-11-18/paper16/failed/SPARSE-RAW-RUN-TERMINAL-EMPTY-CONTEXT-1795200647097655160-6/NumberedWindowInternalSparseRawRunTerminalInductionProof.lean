module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTerminalComponentsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTerminalInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding nextEmbedding liftBind varBind)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open ID1Completion.InternalAdditionLawsProof (liftNext varNext)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseRawTick (chosenTick)
open NumberedWindowInternalSparseRawRunTerminalComponentsProof   (loopArgs loopGraph zeroLoopGraph nextLoopGraph)

private theorem argsSubst {α β : Type} (fuel st : OTerm α) (ts : α → OTerm β) :
    (fun i => (loopArgs fuel st i).subst ts) = loopArgs (fuel.subst ts) (st.subst ts) := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;> rfl

private theorem loopSubst {α β : Type} (p other : Program 3) (st fuel : OTerm α)
    (ts : α → OTerm β) :
    (loopGraph p other st fuel).subst (fun a => emb (ts a)) =
      loopGraph p other (st.subst ts) (fuel.subst ts) := by
  simp only [loopGraph,programSubst,argsSubst]

/-- Intermediate syntactic cut for the actual chosen tick; discharged from
its proved terminal graph in the single frozen endpoint. -/
theorem deriveTerminalLoop {body : Positive (Fin 1)} {α : Type}
    (p other : Program 3) (st fuel : OTerm α)
    (fixed : Nonempty (Derivation body [] (programGraph (chosenTick p other) st ![st]))) :
    Nonempty (Derivation body [] (loopGraph p other st fuel)) := by
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let j : α → α ⊕ Fin 1 := Sum.inl
  let theta : Formula (α ⊕ Fin 1) := loopGraph p other (st.relabel j) v
  obtain ⟨atZero⟩ := zeroLoopGraph (body := body) (Γ := []) p other st
  have base : Derivation body [] (instantiate theta (emb z)) := by
    simpa only [theta,instantiate,bindEmbedding,loopSubst,j,v,liftBind,varBind] using atZero
  have ih : Nonempty (Derivation body [theta] theta) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have moved := renameInto fixed j [theta] (fun _ h => by cases h)
  rw [programRename,inputsRename] at moved
  obtain ⟨atNext⟩ := nextLoopGraph p other (st.relabel j) v ih moved
  have stepProof : Derivation body (theta :: ([] : List (Formula α)).map weaken)
      (successorInstance theta) := by
    simpa only [theta,successorInstance,nextEmbedding,loopSubst,j,v,liftNext,varNext] using atNext
  have result := Derivation.universalElimination (emb fuel) (natInduction theta base stepProof)
  simpa only [theta,instantiate,bindEmbedding,loopSubst,j,v,liftBind,varBind] using
    (Nonempty.intro result)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTerminalInductionProof
