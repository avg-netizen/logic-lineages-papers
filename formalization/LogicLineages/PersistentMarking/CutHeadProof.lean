import LogicLineages.PersistentMarking.CutCoreSupport
namespace LogicLineages.PersistentMarking.CutHeadProof
open Spine ExtendedMeasure CutCoreSupport

theorem put (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (s : Expr) (g : Head) (base : Args) (u : Expr) (left : ExtendedWeak S s (.head g base))
    (right : ExtendedWeakTree S (.marked g g.result base .nil) u)
    (hc : treeSize right < n) (ho : Ordinary u) : ExtendedWeak S s u := by
  have hm := ExtendedMarkingProof.forward S s (.head g base) left
  have hcut := below (headmark s) _ u right hc ho hm
  exact ExtendedUnmarkProof.removeSource S s u hcut

theorem funFun (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (f g h : Head) (ss ts us : Args)
    (hp : PaperTerm S (.head f ss) f.result) (hu : PaperTerm S (.head h us) h.result)
    (hfg : Equivalent S f g) (hgh : Equivalent S g h)
    (htfg : f.result = g.result) (htgh : g.result = h.result)
    (left : ExtendedMatchingTree S ss ts) (right : ExtendedMatchingTree S ts us)
    (hc : treeSize right < n) (ho : OrdinaryArgs us) : ExtendedWeak S (.head f ss) (.head h us) := by
  obtain ⟨hm⟩ := CutMatchingProof.weakWeak S n below ss ts us ⟨left⟩ right hc ho
  exact ⟨.funHead hp hu (equivTrans hfg hgh) (htfg.trans htgh) hm⟩

theorem copyFun (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (f g h : Head) (ss es ts us : Args)
    (hp : PaperTerm S (.marked f g.result ss es) g.result) (hu : PaperTerm S (.head h us) h.result)
    (hfg : Precedes S f g) (hgh : Equivalent S g h) (htgh : g.result = h.result)
    (left : ExtendedWholeTree S f ss es ts) (right : ExtendedMatchingTree S ts us)
    (hc : treeSize right < n) (ho : OrdinaryArgs us) : ExtendedWeak S (.marked f g.result ss es) (.head h us) := by
  obtain ⟨hw⟩ := wholeMatching S n below f ss es ts us left right hc ho
  have hp' : PaperTerm S (.marked f h.result ss es) h.result := AuxiliaryReflexivityProof.retypePaper S f g.result h.result ss es hp
  have he : Expr.marked f g.result ss es = .marked f h.result ss es := by rw [htgh]
  rw [he]
  exact ⟨.copy hp' hu (precedeEquiv hfg hgh) hw⟩

theorem statFun (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (f g h : Head) (ss es ts us : Args)
    (hp : PaperTerm S (.marked f g.result ss es) g.result) (hu : PaperTerm S (.head h us) h.result)
    (hfg : Equivalent S f g) (hgh : Equivalent S g h) (htgh : g.result = h.result)
    (left : ExtendedMultisetTree S ss ts) (whole : ExtendedWholeTree S f ss es ts)
    (right : ExtendedMatchingTree S ts us) (hc : treeSize right < n) (ho : OrdinaryArgs us) :
    ExtendedWeak S (.marked f g.result ss es) (.head h us) := by
  obtain ⟨hm⟩ := CutStrictWeakProof.strictWeak S n below ss ts us ⟨left⟩ right hc ho
  obtain ⟨hw⟩ := wholeMatching S n below f ss es ts us whole right hc ho
  have hp' : PaperTerm S (.marked f h.result ss es) h.result := AuxiliaryReflexivityProof.retypePaper S f g.result h.result ss es hp
  have he : Expr.marked f g.result ss es = .marked f h.result ss es := by rw [htgh]
  rw [he]
  exact ⟨.stat hp' hu (equivTrans hfg hgh) hm hw⟩
end LogicLineages.PersistentMarking.CutHeadProof
