module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationReductionRootProof
open NumberedWindowAtomicApplicationTargets NumberedWindowAtomicApplicationReductionTargets
open NumberedWindowAtomicApplicationTableProof (auxView)
open NumberedWindowAtomicRawStep
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowConcreteCheckers (root)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowMarkRootAlgorithm (guarded)
open NumberedWindowRootDispatchAlgorithm (fixed parts check)
open NumberedWindowAnnotationAlgorithm (annotations)

private theorem onlyBottom (xs : Entries) (s : Settings) (dom cod fn arg y tag : Nat)
    (ws : List Nat) (fnTag : Nat) (fnFields : List Nat)
    (fnView : unpackNode fn = some (fnTag,fnFields)) (notLambda : fnTag ≠ 2) :
    parts (fixed xs s.window.2) (auxRaw dom cod fn arg) y tag ws =
      if tag = 7 ∧ ws = [] then NumberedWindowMarkRootAlgorithm.bottom (auxRaw dom cod fn arg) y
      else false := by
  let q := auxRaw dom cod fn arg
  have view : unpackNode q = some (6,[dom,cod,fn,arg]) := auxView dom cod fn arg
  have hmark (k : Nat) : NumberedWindowMarkRootAlgorithm.mark k q y = false := by
    simp [NumberedWindowMarkRootAlgorithm.mark,guarded,view,NumberedWindowMarkRootAlgorithm.markBody]
  have hlower : NumberedWindowMarkRootAlgorithm.lower q y = false := by
    simp [NumberedWindowMarkRootAlgorithm.lower,guarded,view,NumberedWindowMarkRootAlgorithm.lowerBody]
  have hselect (extra : Bool) (i : Nat) (ds : List Nat) :
      NumberedWindowSelectAlgorithm.select extra i ds q y = false := by
    simp [NumberedWindowSelectAlgorithm.select,guarded,view,NumberedWindowSelectAlgorithm.body]
  have hcopy : NumberedWindowCopyAlgorithm.copy xs s.window.2 q y = false := by
    cases hy : unpackNode y <;>
      simp [NumberedWindowCopyAlgorithm.copy,guarded,view,hy,NumberedWindowCopyAlgorithm.copyRows]
  have hstat (part : Nat) : NumberedWindowStatRootAlgorithm.stat xs s.window.2 part q y = false := by
    cases hy : unpackNode y <;>
      simp [NumberedWindowStatRootAlgorithm.stat,guarded,view,hy,NumberedWindowStatRootAlgorithm.rows]
  have hfabs : NumberedWindowBinderRootAlgorithm.fabs q y = false := by
    simp [NumberedWindowBinderRootAlgorithm.fabs,guarded,view,NumberedWindowBinderRootAlgorithm.fabsRow]
  have hbeta : NumberedWindowBinderRootAlgorithm.beta q y = false := by
    simp [NumberedWindowBinderRootAlgorithm.beta,guarded,view,
      NumberedWindowBinderRootAlgorithm.betaRows,fnView,List.getD_eq_getElem?_getD,notLambda]
  change parts (fixed xs s.window.2) q y tag ws =
    if tag = 7 ∧ ws = [] then NumberedWindowMarkRootAlgorithm.bottom q y else false
  rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | tag <;>
    rcases ws with _ | ⟨w,_ | ⟨u,_ | ⟨v,_ | ⟨r,rs⟩⟩⟩⟩ <;>
    simp [parts,fixed,hmark,hlower,hselect,hcopy,hstat,hfabs,hbeta]

private theorem annotation (dom cod fn arg : Nat) : (annotations (auxRaw dom cod fn arg)).1 = cod := by
  simp [annotations,NumberedWindowAnnotationAlgorithm.termNext,auxView,
    NumberedWindowAnnotationAlgorithm.termParts,List.getD_eq_getElem?_getD]

/-- An original root with any physically parsed non-lambda function can
only bottom the entire exact auxiliary at its original codomain. -/
theorem exact_OriginalNonLambdaAuxRoot (xs : Entries) (s : Settings)
    (dom cod fn arg cert y fnTag : Nat) (fnFields : List Nat)
    (fnView : unpackNode fn = some (fnTag,fnFields)) (notLambda : fnTag ≠ 2)
    (accepted : root xs s (auxRaw dom cod fn arg) cert y = true) :
    y = bottomRaw cod ∧ cert = bottomRoot := by
  cases hw : unpackNode cert with
  | none => simp [root,check,hw] at accepted
  | some node =>
    rcases node with ⟨tag,ws⟩
    have tested : parts (fixed xs s.window.2) (auxRaw dom cod fn arg) y tag ws = true := by
      simpa [root,check,hw] using accepted
    rw [onlyBottom xs s dom cod fn arg y tag ws fnTag fnFields fnView notLambda] at tested
    by_cases valid : tag = 7 ∧ ws = []
    · have retained : unpackNode cert = some (7,[]) := by rw [hw,valid.1,valid.2]
      have bottom : NumberedWindowMarkRootAlgorithm.bottom (auxRaw dom cod fn arg) y = true :=
        by simpa only [if_pos valid] using tested
      unfold NumberedWindowMarkRootAlgorithm.bottom guarded at bottom
      rw [annotation, ← bottomRaw] at bottom
      simp only [Bool.and_eq_true,beq_iff_eq,bne_iff_ne,and_assoc] at bottom
      exact ⟨bottom.2.2.2.symm,codeOfNode retained⟩
    · simp [valid] at tested

/-- In particular, the outer original root at an application-headed
auxiliary cannot beta regardless of either application's raw fields. -/
theorem exact_OriginalNestedAuxRoot (xs : Entries) (s : Settings)
    (dom cod leftDom leftCod leftFn leftArg arg cert y : Nat)
    (accepted : root xs s (auxRaw dom cod (auxRaw leftDom leftCod leftFn leftArg) arg) cert y = true) :
    y = bottomRaw cod ∧ cert = bottomRoot :=
  exact_OriginalNonLambdaAuxRoot xs s dom cod (auxRaw leftDom leftCod leftFn leftArg) arg cert y
    6 [leftDom,leftCod,leftFn,leftArg] (auxView leftDom leftCod leftFn leftArg) (by decide) accepted

#print axioms exact_OriginalNonLambdaAuxRoot
#print axioms exact_OriginalNestedAuxRoot

end LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationReductionRootProof
