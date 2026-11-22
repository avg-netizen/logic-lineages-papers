module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedStepTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedStepLeavesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedOwnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedValidityCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverSelectedValidityTargets (layout headerAt)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverRefinedValidityCasesProof (exact_OpenCoverRefinedValidityCases)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (packRow renameRow moveMemberKey)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (Programs ParentRow PackedRow)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedOwnProof
  (exact_OpenCoverCombinedRestrictedLambdaOwn exact_OpenCoverCombinedRestrictedOrdinaryOwn
    exact_OpenCoverCombinedRestrictedNumberedOwn)
open NumberedWindowInternalCoverCombinedRestrictedStepLeavesProof (combinedAtNamed combinedAtType combinedAtAux)
open NumberedWindowInternalCoverCombinedRestrictedStepTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem finishPacked (P : Programs) (s : Settings)
    {raw key p vertices ctx result : OTerm α} {tag : Nat} {fields : List (OTerm α)}
    (row : ParentRow P s body Γ raw p vertices ctx result)
    (ordered : Reports body Γ raw cellTail fields)
    (same : Nonempty (Derivation body Γ (eqn raw key)))
    (shape : Nonempty (Derivation body Γ (headerAt tag fields.length raw)))
    (atKey : PackedRow P s body Γ raw key p vertices ctx result tag fields →
      Nonempty (Derivation body Γ (memberGraph vertices key))) :
    Nonempty (Derivation body Γ (memberGraph vertices raw)) := by
  have literal := atKey (packRow P s row ordered same shape)
  obtain ⟨same⟩ := same
  exact moveMemberKey vertices key raw (symm same) literal

theorem exact_OpenCoverCombinedRestrictedBoundedStep : ExactOpenCoverCombinedRestrictedBoundedStep := by
  intro V TV M M0 B T s body α Γ raw p vertices ctx result row
  let P := combinedPrograms s V TV M M0 B T
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
    exact finishPacked P s (key := namedTerm 0 ty i) actual ordered same header
      (fun row => combinedAtNamed s V TV M M0 B T false p' vertices' ctx' result' ty i row.data)
  · rcases fields with _ | ⟨ty,_ | ⟨i,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
    exact finishPacked P s (key := namedTerm 1 ty i) actual ordered same header
      (fun row => combinedAtNamed s V TV M M0 B T true p' vertices' ctx' result' ty i row.data)
  · rcases fields with _ | ⟨ty,_ | ⟨q,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
    exact finishPacked P s (key := lambdaTerm ty q) actual ordered same header
      (fun row => exact_OpenCoverCombinedRestrictedLambdaOwn V TV M M0 B T s body β Δ
        ty q p' vertices' ctx' result' row.data)
  · rcases fields with _ | ⟨ty,_ | ⟨extra,rest⟩⟩ <;> simp at len
    exact finishPacked P s (key := typeLeafTerm ty) actual ordered same header
      (fun row => combinedAtType s V TV M M0 B T p' vertices' ctx' result' ty row.data)
  · rcases fields with _ | ⟨h,_ | ⟨a,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
    exact finishPacked P s (key := ordinaryKey h a) actual ordered same header
      (fun row => exact_OpenCoverCombinedRestrictedOrdinaryOwn V TV M M0 B T s body β Δ
        h a p' vertices' ctx' result' row.data)
  · rcases fields with _ | ⟨h,_ | ⟨ty,_ | ⟨k,_ | ⟨l,_ | ⟨r,_ | ⟨extra,rest⟩⟩⟩⟩⟩⟩ <;> simp at len
    exact finishPacked P s (key := numberedTerm h ty k l r) actual ordered same header
      (fun row => exact_OpenCoverCombinedRestrictedNumberedOwn V TV M M0 B T s body β Δ
        h ty k l r p' vertices' ctx' result' row.data)
  · rcases fields with _ | ⟨dom,_ | ⟨cod,_ | ⟨fn,_ | ⟨arg,_ | ⟨extra,rest⟩⟩⟩⟩⟩ <;> simp at len
    exact finishPacked P s (key := auxiliaryTerm dom cod fn arg) actual ordered same header
      (fun row => combinedAtAux s V TV M M0 B T raw' p' vertices' ctx' result' dom cod fn arg row)

#print axioms exact_OpenCoverCombinedRestrictedBoundedStep

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedStepProof
