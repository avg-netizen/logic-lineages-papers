module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionRootProof
open NumberedWindowAtomicApplicationTargets NumberedWindowAtomicApplicationReductionTargets
open NumberedWindowAtomicApplicationTableProof (auxView)
open NumberedWindowAtomicRawStep
open NumberedWindowAtomicRawStepFieldProof (freeView bottomView codeOfNode)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowConcreteCheckers (root)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowMarkRootAlgorithm (guarded)
open NumberedWindowRootDispatchAlgorithm (fixed parts check)
open NumberedWindowAnnotationAlgorithm (annotations)

private theorem onlyBottom (xs : Entries) (s : Settings) (dom cod fn arg y tag : Nat)
    (ws : List Nat) (h : AtomHead fn) :
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
    cases h with
    | free t n =>
      simp [NumberedWindowBinderRootAlgorithm.beta,guarded,view,
        NumberedWindowBinderRootAlgorithm.betaRows,freeView,List.getD_eq_getElem?_getD]
    | bottom t =>
      simp [NumberedWindowBinderRootAlgorithm.beta,guarded,view,
        NumberedWindowBinderRootAlgorithm.betaRows,bottomView,List.getD_eq_getElem?_getD]
  change parts (fixed xs s.window.2) q y tag ws =
    if tag = 7 ∧ ws = [] then NumberedWindowMarkRootAlgorithm.bottom q y else false
  rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | tag <;>
    rcases ws with _ | ⟨w,_ | ⟨u,_ | ⟨v,_ | ⟨r,rs⟩⟩⟩⟩ <;>
    simp [parts,fixed,hmark,hlower,hselect,hcopy,hstat,hfabs,hbeta]

private theorem annotation (dom cod fn arg : Nat) : (annotations (auxRaw dom cod fn arg)).1 = cod := by
  simp [annotations,NumberedWindowAnnotationAlgorithm.termNext,auxView,
    NumberedWindowAnnotationAlgorithm.termParts,List.getD_eq_getElem?_getD]

theorem auxRoot : ExactAtomicAuxRootReduction := by
  intro xs s dom cod fn arg cert y atom accepted
  cases hw : unpackNode cert with
  | none => simp [root,check,hw] at accepted
  | some node =>
    rcases node with ⟨tag,ws⟩
    have tested : parts (fixed xs s.window.2) (auxRaw dom cod fn arg) y tag ws = true := by
      simpa [root,check,hw] using accepted
    rw [onlyBottom xs s dom cod fn arg y tag ws atom] at tested
    by_cases valid : tag = 7 ∧ ws = []
    · have retained : unpackNode cert = some (7,[]) := by rw [hw,valid.1,valid.2]
      have bottom : NumberedWindowMarkRootAlgorithm.bottom (auxRaw dom cod fn arg) y = true :=
        by simpa only [if_pos valid] using tested
      simp only [NumberedWindowMarkRootAlgorithm.bottom,guarded,annotation,← bottomRaw,
        Bool.and_eq_true,beq_iff_eq,bne_iff_ne,and_assoc] at bottom
      exact ⟨bottom.2.2.2.symm,codeOfNode retained⟩
    · simp [valid] at tested

end LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionRootProof
