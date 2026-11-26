module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickIterationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeMotiveProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickIterationFixedProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename recursionZeroValue projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding nextEmbedding liftBind varBind)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open ID1Completion.InternalAdditionLawsProof (liftNext varNext)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseRawRunShapeMotiveProof (pairSubst)
open NumberedWindowInternalLiteralTickIterationMotiveProof (tickLoop tickStep)
open NumberedWindowInternalLiteralTickIterationProof (runSuccessor)

private theorem fixedSubst {α β : Type} (step : Program 1) (st fuel : OTerm α) (ts : α → OTerm β) :
    (programGraph (tickLoop step) st ![fuel,st]).subst (fun a => emb (ts a)) =
      programGraph (tickLoop step) (st.subst ts) ![fuel.subst ts,st.subst ts] := by
  rw [programSubst,pairSubst]

/-- A literal fixed tick stays fixed at every fuel in the original
arithmetic, with no numerical or closed-input assumption on the state. -/
theorem exact_OpenTickIterationFixed {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (step : Program 1) (st fuel : OTerm α)
    (fixed : Nonempty (Derivation body Γ (programGraph step st ![st]))) :
    Nonempty (Derivation body Γ (programGraph (tickLoop step) st ![fuel,st])) := by
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let j : α → α ⊕ Fin 1 := Sum.inl
  let theta : Formula (α ⊕ Fin 1) := programGraph (tickLoop step) (st.relabel j) ![v,st.relabel j]
  have atZero : Nonempty (Derivation body Γ (programGraph (tickLoop step) st ![z,st])) :=
    recursionZeroValue (.projection 0) (tickStep step) st ![st] (projectionValue 0 ![st])
  obtain ⟨atz⟩ := atZero
  have base : Derivation body Γ (instantiate theta (emb z)) := by
    simpa only [theta,instantiate,bindEmbedding,fixedSubst,j,v,liftBind,varBind] using atz
  let Δ := theta :: Γ.map weaken
  have moved := renameInto fixed j Δ
    (fun f h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩))
  rw [programRename,inputsRename] at moved
  obtain ⟨atNext⟩ := runSuccessor (Γ := Δ) step (st.relabel j) (st.relabel j) v (st.relabel j)
    ⟨Derivation.hypothesis List.mem_cons_self⟩ moved
  have stepProof : Derivation body Δ (successorInstance theta) := by
    simpa only [theta,successorInstance,nextEmbedding,fixedSubst,j,v,liftNext,varNext] using atNext
  have result := Derivation.universalElimination (emb fuel) (natInduction theta base stepProof)
  simpa only [theta,instantiate,bindEmbedding,fixedSubst,j,v,liftBind,varBind] using
    (Nonempty.intro result)

#print axioms exact_OpenTickIterationFixed
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickIterationFixedProof
