module

public import LogicLineages.NativeModule.PersistentMarking.CutStrictWeakSupport
public import LogicLineages.NativeModule.PersistentMarking.CutWeakStrictProof
public import LogicLineages.NativeModule.PersistentMarking.CutSplitSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.CutStrictStrictSupport
open Spine ExtendedMeasure

theorem coverageAtBound {S : Signature} {owners targets : Args} {i : Nat} {q : Expr}
    (h : ExtendedCoverageTree S owners targets) (ha : At targets i q) :
    ∃ p j, At owners j p ∧ ∃ edge : ExtendedStrictTree S p q, treeSize edge < treeSize h := by
  cases ha with
  | here =>
    cases h with
    | coverageCons hp edge rest =>
      refine ⟨_,_,hp,edge,?_⟩
      change treeSize edge < 1 + treeSize edge + treeSize rest
      omega
  | there ha =>
    cases h with
    | coverageCons hp edge rest =>
      obtain ⟨p,j,hp',found,hbound⟩ := coverageAtBound rest ha
      refine ⟨p,j,hp',found,?_⟩
      change treeSize found < 1 + treeSize edge + treeSize rest
      omega
termination_by sizeOf targets
end LogicLineages.PersistentMarking.CutStrictStrictSupport
