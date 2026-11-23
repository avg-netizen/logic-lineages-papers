module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadConeTargets
import Init.Data.List.Lemmas

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadConeNumericProof
open NumberedWindowCopyAlgorithm
open NumberedWindowMarkRootAlgorithm (guarded)
open NumberedWindowInternalCopyHeadConeTargets

theorem rankCone (entries : Entries) (f g : Nat)
    (accepted : compareRanks true entries f g = true) :
    ∃ rankSrc rankDst, rank entries f = some rankSrc ∧
      rank entries g = some rankDst ∧ rankDst < rankSrc := by
  cases a : rank entries f with
  | none => simp [compareRanks,a] at accepted
  | some m =>
    cases b : rank entries g with
    | none => simp [compareRanks,a,b] at accepted
    | some n =>
      refine ⟨m,n,rfl,rfl,?_⟩
      simpa [compareRanks,a,b] using accepted

theorem exact_OriginalCopyHeadCone : ExactOriginalCopyHeadCone := by
  intro entries heads src dst f result label base extras g args srcView dstView accepted
  unfold copy guarded at accepted
  have steps := (Bool.and_eq_true_iff.mp accepted).2
  rw [srcView,dstView] at steps
  change copyRows entries heads (5,[f,result,label,base,extras]) (4,[g,args]) = true at steps
  have cond := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp steps).2).1
  change allowedTarget true entries heads result f g = true at cond
  obtain ⟨observed,member⟩ := Bool.and_eq_true_iff.mp cond
  obtain ⟨ty,cmp⟩ := Bool.and_eq_true_iff.mp observed
  exact ⟨List.contains_iff_mem.mp member,beq_iff_eq.mp ty,rankCone entries f g cmp⟩

#print axioms exact_OriginalCopyHeadCone

end LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadConeNumericProof
