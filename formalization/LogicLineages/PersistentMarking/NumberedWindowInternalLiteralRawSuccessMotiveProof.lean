module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRawSuccessorCasesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinderTransportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRawSuccessMotiveProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (programSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst liftNext varNext)
open ID1Completion.InternalBetaExtensionSyntaxProof (impRename)
open ID1Completion.InternalBinderTransportSyntaxProof
  (formulaRelabel renameSubst formulaSubstVar termRelabelSubst termSubstVar)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding bindTerm liftBind varBind nextEmbedding nextTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparseRawRun (iterateState)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)

/-- Induct on the real fuel only. The start, requested successful
scratch output, and the caller's object conclusion are fixed. -/
def successMotive {α : Type} (p other : Program 3)
    (fuel start out : OTerm α) (goal : Formula α) : Formula α :=
  (programGraph (iterateState p other) out ![fuel,start]).imp goal

theorem successMotiveRename {α β : Type} (p other : Program 3) (fuel start out : OTerm α)
    (goal : Formula α) (j : α → β) :
    (successMotive p other fuel start out goal).relabel j =
      successMotive p other (fuel.relabel j) (start.relabel j) (out.relabel j) (goal.relabel j) := by
  have pair : (fun i : Fin 2 => ((![fuel,start] : Fin 2 → OTerm α) i).relabel j) =
      ![fuel.relabel j,start.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun l => Fin.elim0 l)) i
  rw [successMotive,impRename,programRename,pair]
  rfl

theorem successMotiveSubst {α β : Type} (p other : Program 3) (fuel start out : OTerm α)
    (goal : Formula α) (ts : α → OTerm β) :
    (successMotive p other fuel start out goal).subst (fun a => emb (ts a)) =
      successMotive p other (fuel.subst ts) (start.subst ts) (out.subst ts)
        (goal.subst (fun a => emb (ts a))) := by
  have pair : (fun i : Fin 2 => ((![fuel,start] : Fin 2 → OTerm α) i).subst ts) =
      ![fuel.subst ts,start.subst ts] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun l => Fin.elim0 l)) i
  rw [successMotive,impSubst,programSubst,pair]
  rfl

theorem successMotiveInstantiate {α : Type} (p other : Program 3) (start out fuel : OTerm α)
    (goal : Formula α) :
    let j : α → α ⊕ Fin 1 := Sum.inl
    let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
    instantiate (successMotive p other v (start.relabel j) (out.relabel j) (goal.relabel j))
      (emb fuel) = successMotive p other fuel start out goal := by
  intro j v
  have keepGoal : (goal.relabel j).subst (fun a => emb (bindTerm fuel a)) = goal := by
    rw [formulaRelabel,renameSubst]
    exact formulaSubstVar goal
  simp only [instantiate,bindEmbedding,successMotiveSubst,j,v,liftBind,varBind,keepGoal]

theorem successMotiveNext {α : Type} (p other : Program 3) (start out : OTerm α)
    (goal : Formula α) :
    let j : α → α ⊕ Fin 1 := Sum.inl
    let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
    successorInstance (successMotive p other v (start.relabel j) (out.relabel j) (goal.relabel j)) =
      successMotive p other (suc v) (start.relabel j) (out.relabel j) (goal.relabel j) := by
  intro j v
  have keepGoal : (goal.relabel j).subst (fun a => emb (nextTerm a)) = goal.relabel j := by
    rw [formulaRelabel,renameSubst]
    change goal.subst (Term.var ∘ j) = _
    rw [← renameSubst goal j Term.var,formulaSubstVar]
  simp only [successorInstance,nextEmbedding,successMotiveSubst,j,v,liftNext,varNext]
  exact congrArg (successMotive p other (suc v) (start.relabel j) (out.relabel j)) keepGoal

#print axioms successMotiveRename
#print axioms successMotiveSubst
#print axioms successMotiveInstantiate
#print axioms successMotiveNext
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRawSuccessMotiveProof
