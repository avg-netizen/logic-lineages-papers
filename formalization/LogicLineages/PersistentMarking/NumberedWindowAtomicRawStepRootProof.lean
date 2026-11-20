module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepRootProof
open NumberedWindowAtomicRawStep NumberedWindowAtomicRawStepTargets
open NumberedWindowAtomicRawStepFieldProof
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowAddressAlgorithm (contextView)
open NumberedWindowConcreteCheckers (root)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowMarkRootAlgorithm (guarded)
open NumberedWindowRootDispatchAlgorithm (fixed parts check flagView)

private theorem atomicParts (xs : Entries) (s : Settings) (q y tag : Nat) (ws : List Nat)
    (sourceTag : Nat) (sourceFields : List Nat)
    (view : unpackNode q = some (sourceTag,sourceFields))
    (leaf : sourceTag = 0 ∨ sourceTag = 3) :
    parts (fixed xs s.window.2) q y tag ws =
      if tag = 7 ∧ ws = [] then NumberedWindowMarkRootAlgorithm.bottom q y else false := by
  have hmark (k : Nat) : NumberedWindowMarkRootAlgorithm.mark k q y = false := by
    rcases leaf with rfl | rfl <;>
      simp [NumberedWindowMarkRootAlgorithm.mark,guarded,view,NumberedWindowMarkRootAlgorithm.markBody]
  have hlower : NumberedWindowMarkRootAlgorithm.lower q y = false := by
    rcases leaf with rfl | rfl <;>
      simp [NumberedWindowMarkRootAlgorithm.lower,guarded,view,NumberedWindowMarkRootAlgorithm.lowerBody]
  have hselect (extra : Bool) (i : Nat) (ds : List Nat) : NumberedWindowSelectAlgorithm.select extra i ds q y = false := by
    rcases leaf with rfl | rfl <;>
      simp [NumberedWindowSelectAlgorithm.select,guarded,view,NumberedWindowSelectAlgorithm.body]
  have hcopy : NumberedWindowCopyAlgorithm.copy xs s.window.2 q y = false := by
    cases hy : unpackNode y <;> rcases leaf with rfl | rfl <;>
      simp [NumberedWindowCopyAlgorithm.copy,guarded,view,hy,NumberedWindowCopyAlgorithm.copyRows]
  have hstat (part : Nat) : NumberedWindowStatRootAlgorithm.stat xs s.window.2 part q y = false := by
    cases hy : unpackNode y <;> rcases leaf with rfl | rfl <;>
      simp [NumberedWindowStatRootAlgorithm.stat,guarded,view,hy,NumberedWindowStatRootAlgorithm.rows]
  have hfabs : NumberedWindowBinderRootAlgorithm.fabs q y = false := by
    rcases leaf with rfl | rfl <;>
      simp [NumberedWindowBinderRootAlgorithm.fabs,guarded,view,NumberedWindowBinderRootAlgorithm.fabsRow]
  have hbeta : NumberedWindowBinderRootAlgorithm.beta q y = false := by
    cases hy : unpackNode (sourceFields.getD 2 0) <;> rcases leaf with rfl | rfl <;>
      simp [NumberedWindowBinderRootAlgorithm.beta,guarded,view,hy,NumberedWindowBinderRootAlgorithm.betaRows]
  rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | tag <;>
    rcases ws with _ | ⟨w,_ | ⟨u,_ | ⟨v,_ | ⟨r,rs⟩⟩⟩⟩ <;>
    simp [parts,fixed,hmark,hlower,hselect,hcopy,hstat,hfabs,hbeta]

private theorem rootAtomic (xs : Entries) (s : Settings) (q w y tag : Nat) (fs : List Nat)
    (view : unpackNode q = some (tag,fs)) (leaf : tag = 0 ∨ tag = 3)
    (accepted : root xs s q w y = true) :
    w = bottomRoot ∧ NumberedWindowMarkRootAlgorithm.bottom q y = true := by
  cases hw : unpackNode w with
  | none => simp [root,check,hw] at accepted
  | some node =>
    rcases node with ⟨k,ws⟩
    have tested : parts (fixed xs s.window.2) q y k ws = true := by simpa [root,check,hw] using accepted
    rw [atomicParts xs s q y k ws tag fs view leaf] at tested
    by_cases right : k = 7 ∧ ws = []
    · have exactNode : unpackNode w = some (7,[]) := by rw [hw,right.1,right.2]
      exact ⟨codeOfNode exactNode,by simpa only [if_pos right] using tested⟩
    · simp [right] at tested

private theorem bottomTarget {q y t : Nat} (hTy : (NumberedWindowAnnotationAlgorithm.annotations q).1 = t)
    (h : NumberedWindowMarkRootAlgorithm.bottom q y = true) :
    y = bottomRaw t ∧ q ≠ bottomRaw t := by
  unfold NumberedWindowMarkRootAlgorithm.bottom guarded at h
  rw [hTy,← bottomRaw] at h
  simp only [Bool.and_eq_true,beq_iff_eq,bne_iff_ne,and_assoc] at h
  exact ⟨h.2.2.2.symm,h.2.2.1⟩

theorem atomicRoots : ExactConcreteAtomicRoot := by
  constructor
  · intro xs s t n w y h
    obtain ⟨certificate,step⟩ := rootAtomic xs s (freeRaw t n) w y 0 [t,n] (freeView t n)
      (Or.inl rfl) h
    exact ⟨(bottomTarget (freeAnnotation t n) step).1,certificate⟩
  · intro xs s t w y
    cases accepted : root xs s (bottomRaw t) w y with
    | false => rfl
    | true =>
      obtain ⟨_,step⟩ := rootAtomic xs s (bottomRaw t) w y 3 [t] (bottomView t) (Or.inr rfl) accepted
      exact False.elim ((bottomTarget (bottomAnnotation t) step).2 rfl)

end LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepRootProof
