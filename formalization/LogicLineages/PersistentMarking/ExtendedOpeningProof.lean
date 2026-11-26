import LogicLineages.PersistentMarking.ExtendedOpeningTargets
import LogicLineages.PersistentMarking.ExtendedRenamingProof
import LogicLineages.PersistentMarking.RefinementOpeningProof
namespace LogicLineages.PersistentMarking.ExtendedOpeningProof
open Spine NameBridge RefinementRenamingTargets RefinementRenameSupport RefinementOpeningProof ExtendedRenamingTargets

theorem absSynchronize : ExtendedOpeningTargets.AbsSynchronize := by
  intro S σ x y s t hxs hxt hys hyt h
  obtain ⟨h0,he0⟩ := ExtendedRenamingProof.tree S (swap σ x y) (swapInjective σ x y) _ h
  have he : renameJudgment (swap σ x y) (.weak (openBody σ x s) (openBody σ x t)) = .weak (openBody σ y s) (openBody σ y t) := by
    simp only [renameJudgment,opened σ x y s hxs hys,opened σ x y t hxt hyt]
  obtain ⟨out,he1⟩ := ExtendedRenameSupport.transport he h0
  exact ⟨out,he1.trans he0⟩

theorem fabsSynchronize : ExtendedOpeningTargets.FAbsSynchronize := by
  intro S f σ τ base extras body x y hxo hxb hyo hyb h
  have hx : freeOccursArgs (σ,x) base = false ∧ freeOccursArgs (σ,x) extras = false := by
    simpa only [freeOccurs,Bool.or_eq_false_iff] using hxo
  have hy : freeOccursArgs (σ,y) base = false ∧ freeOccursArgs (σ,y) extras = false := by
    simpa only [freeOccurs,Bool.or_eq_false_iff] using hyo
  have hbase := absentArgs σ x y base hx.1 hy.1
  have hextras := absentArgs σ x y extras hx.2 hy.2
  obtain ⟨h0,he0⟩ := ExtendedRenamingProof.tree S (swap σ x y) (swapInjective σ x y) _ h
  have he : renameJudgment (swap σ x y) (.weak (.marked f τ base (extras.append (.cons (.free σ x) .nil))) (openBody σ x body)) =
      .weak (.marked f τ base (extras.append (.cons (.free σ y) .nil))) (openBody σ y body) := by
    simp only [renameJudgment,renameMarked,ExtendedRenameSupport.append,renameCons,RefinementRenameSupport.renameFree,renameNil,swapName,hbase,hextras,opened σ x y body hxb hyb]
  obtain ⟨out,he1⟩ := ExtendedRenameSupport.transport he h0
  exact ⟨out,he1.trans he0⟩
end LogicLineages.PersistentMarking.ExtendedOpeningProof
