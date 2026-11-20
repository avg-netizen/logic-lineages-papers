module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGateProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceSelectorCasesProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets
open NumberedWindowInternalSparsePathSuccessfulAdvanceSyntaxProof (acceptsRename reportRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof (supply reportCases)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGateProof (obtainCalls acceptCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceSelectorCasesProof (chooseSelectors)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem forward (raw : Program 5) (least : Program 3) (ctx ty current hop target : OTerm α)
    (accepted : Nonempty (Derivation body Γ (selectedGraph raw least (suc target) ctx ty (suc current) hop))) :
    Nonempty (Derivation body Γ (someHopCalls raw least ctx ty current hop target)) := by
  apply chooseSelectors hop (someHopCalls raw least ctx ty current hop target)
  intro β j Δ q w r hJ a b c
  rw [reportRename]
  have yes := renameInto accepted j Δ hJ
  rw [acceptsRename] at yes
  exact supply (ctx.relabel j) (ty.relabel j) (current.relabel j) (hop.relabel j) (target.relabel j) q w r
    (obtainCalls raw least (ctx.relabel j) (ty.relabel j) (current.relabel j) (hop.relabel j)
      (target.relabel j) q w r yes a b c)

private theorem backward (raw : Program 5) (least : Program 3) (ctx ty current hop target : OTerm α)
    (reported : Nonempty (Derivation body Γ (someHopCalls raw least ctx ty current hop target))) :
    Nonempty (Derivation body Γ (selectedGraph raw least (suc target) ctx ty (suc current) hop)) := by
  apply reportCases raw least ctx ty current hop target
    (selectedGraph raw least (suc target) ctx ty (suc current) hop) reported
  intro β j Δ q w r _ facts
  rw [acceptsRename]
  exact acceptCalls raw least (ctx.relabel j) (ty.relabel j) (current.relabel j) (hop.relabel j)
    (target.relabel j) q w r facts

theorem exact_OpenSuccessfulAdvanceCalls : OpenSuccessfulAdvanceCalls := by
  intro body raw least α ctx ty current hop target
  let a := selectedGraph raw least (suc target) ctx ty (suc current) hop
  let b := someHopCalls raw least ctx ty current hop target
  obtain ⟨x⟩ := forward (body := body) (Γ := [a]) raw least ctx ty current hop target
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨y⟩ := backward (body := body) (Γ := [b]) raw least ctx ty current hop target
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction x)
    (Derivation.implicationIntroduction y)⟩

#print axioms exact_OpenSuccessfulAdvanceCalls
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceChecks
