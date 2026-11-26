module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsFinishCompareProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsStateProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsFinishProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph)
open NumberedWindowInternalSparsePositiveOutputTargets (equivalent)
open NumberedWindowInternalSparsePositiveOutputStateProof (loopOfState)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (moveLoop)
open NumberedWindowInternalSparsePositiveTerminalityChecks (exact_OpenChosenFuelTerminal)
open NumberedWindowInternalSparsePositiveTerminalScratchCasesProof (terminalCases)
open NumberedWindowInternalSparsePositiveChosenConsTargets
open NumberedWindowInternalSparsePositiveChosenConsSyntaxProof
open NumberedWindowInternalSparsePositiveChosenConsStateProof (backward)
open NumberedWindowInternalSparsePositiveChosenConsFinishCompareProof (finishAtPair)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem sameState (raw : Program 5) (least : Program 3)
    (out state ctx ty current cert next tl : OTerm α)
    (old : Nonempty (Derivation body Γ (loopGraph raw least state cert ctx ty current cert)))
    (new : Nonempty (Derivation body Γ (loopGraph raw least state tl ctx ty next tl))) :
    Nonempty (Derivation body Γ (equivalent (finishGraph raw least out ctx ty current cert)
      (finishGraph raw least out ctx ty next tl))) := by
  let wanted := equivalent (finishGraph raw least out ctx ty current cert)
    (finishGraph raw least out ctx ty next tl)
  have ht := closedApply (exact_OpenChosenFuelTerminal body raw least α state ctx ty next tl) new
  apply terminalCases state wanted ht
  intro β j Δ res hJ done
  unfold wanted
  rw [finishEquivalenceRename]
  have l := moveLoop j Δ hJ raw least state cert ctx ty current cert old
  have r := moveLoop j Δ hJ raw least state tl ctx ty next tl new
  exact finishAtPair raw least (out.relabel j) (state.relabel j) res (ctx.relabel j) (ty.relabel j)
    (current.relabel j) (cert.relabel j) (next.relabel j) (tl.relabel j) l r done

private theorem compareFinish (raw : Program 5) (least : Program 3)
    (out ctx ty current cert hd tl next : OTerm α)
    (fact : Nonempty (Derivation body Γ (genuineHead raw least ctx ty current cert hd tl next))) :
    Nonempty (Derivation body Γ (equivalent (finishGraph raw least out ctx ty current cert)
      (finishGraph raw least out ctx ty next tl))) := by
  let wanted := equivalent (finishGraph raw least out ctx ty current cert)
    (finishGraph raw least out ctx ty next tl)
  apply chosenCases raw least ctx ty next tl wanted
  intro β j Δ state hJ new
  unfold wanted
  rw [finishEquivalenceRename]
  have h := renameInto fact j Δ hJ
  rw [headRename] at h
  have old := backward raw least state (ctx.relabel j) (ty.relabel j) (current.relabel j)
    (cert.relabel j) (hd.relabel j) (tl.relabel j) (next.relabel j) h new
  have l := loopOfState raw least state (ctx.relabel j) (ty.relabel j) (current.relabel j) (cert.relabel j) old
  have r := loopOfState raw least state (ctx.relabel j) (ty.relabel j) (next.relabel j) (tl.relabel j) new
  exact sameState raw least (out.relabel j) state (ctx.relabel j) (ty.relabel j) (current.relabel j)
    (cert.relabel j) (next.relabel j) (tl.relabel j) l r

theorem finishCons : OpenFinishCons := by
  intro body raw least α out ctx ty current cert hd tl next
  let h := genuineHead raw least ctx ty current cert hd tl next
  obtain ⟨done⟩ := compareFinish (body := body) (Γ := [h]) raw least out ctx ty current cert hd tl next
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction done⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsFinishProof
