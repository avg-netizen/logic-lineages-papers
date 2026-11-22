module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedValidityCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchLeavesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchArgsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchRecursiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverSelectedValidityTargets (layout)
open NumberedWindowInternalCoverRefinedValidityCasesProof (exact_OpenCoverRefinedValidityCases)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (packRow renameRow)
open NumberedWindowInternalCoverRefinedInductionDispatchLeavesProof (atNamed atTypeLeaf)
open NumberedWindowInternalCoverRefinedInductionDispatchArgsProof (atOrdinary atNumbered)
open NumberedWindowInternalCoverRefinedInductionDispatchRecursiveProof (atLambda atAux)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets

theorem exact_OpenCoverRefinedInductionDispatch : ExactOpenCoverRefinedInductionDispatch := by
  intro V TV M B TW s body α Γ raw p vertices ctx result P need row
  apply exact_OpenCoverRefinedValidityCases V TV body α Γ raw _ row.parent.valid
  intro tag arity hit β j Δ fields keep len ordered same header accepted
  rw [graphRename]
  let raw' := raw.relabel j
  let p' := p.relabel j
  let vertices' := vertices.relabel j
  let ctx' := ctx.relabel j
  let result' := result.relabel j
  have physical := renameRow P s j keep row
  have actual : ParentRow P s body Δ raw' p' vertices' ctx' result' :=
    { physical with parent := { physical.parent with valid := accepted } }
  simp only [layout,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hit
  rcases hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rcases fields with _ | ⟨ty,_ | ⟨i,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
    exact atNamed P s false raw' p' vertices' ctx' result' ty i need
      (packRow P s actual ordered same header)
  · rcases fields with _ | ⟨ty,_ | ⟨i,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
    exact atNamed P s true raw' p' vertices' ctx' result' ty i need
      (packRow P s actual ordered same header)
  · rcases fields with _ | ⟨ty,_ | ⟨q,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
    exact atLambda V TV M B TW s raw' p' vertices' ctx' result' ty q need
      (packRow P s actual ordered same header)
  · rcases fields with _ | ⟨ty,_ | ⟨extra,rest⟩⟩ <;> simp at len
    exact atTypeLeaf P s raw' p' vertices' ctx' result' ty need
      (packRow P s actual ordered same header)
  · rcases fields with _ | ⟨h,_ | ⟨a,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
    exact atOrdinary P s raw' p' vertices' ctx' result' h a need
      (packRow P s actual ordered same header)
  · rcases fields with _ | ⟨h,_ | ⟨ty,_ | ⟨k,_ | ⟨l,_ | ⟨r,_ | ⟨extra,rest⟩⟩⟩⟩⟩⟩ <;> simp at len
    exact atNumbered P s raw' p' vertices' ctx' result' h ty k l r need
      (packRow P s actual ordered same header)
  · rcases fields with _ | ⟨dom,_ | ⟨cod,_ | ⟨fn,_ | ⟨arg,_ | ⟨extra,rest⟩⟩⟩⟩⟩ <;> simp at len
    exact atAux V TV M B TW s raw' p' vertices' ctx' result' dom cod fn arg need
      (packRow P s actual ordered same header)

#print axioms exact_OpenCoverRefinedInductionDispatch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchProof
