import LogicLineages.PersistentMarking.CutBinderProof
import LogicLineages.PersistentMarking.CutHeadProof
namespace LogicLineages.PersistentMarking.CutLeftCoreProof
open Spine NameBridge ExtendedMeasure

theorem types {S : Signature} {q : Expr} {σ τ : Ty} (h : PaperTerm S q σ) (k : PaperTerm S q τ) : σ = τ :=
  (SpineShiftProof.annotationExact _ _ _ h.1).symm.trans (SpineShiftProof.annotationExact _ _ _ k.1)

theorem abstraction (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (σ τ : Ty) (s t u : Expr) (x : Nat)
    (hp : PaperTerm S (.lam σ s) (.arrow σ τ)) (ht : PaperTerm S (.lam σ t) (.arrow σ τ))
    (hxs : freeOccurs (σ,x) s = false) (hxt : freeOccurs (σ,x) t = false)
    (left : ExtendedWeakTree S (openBody σ x s) (openBody σ x t))
    (right : ExtendedWeakTree S (.lam σ t) u) (hc : treeSize right = n) (ho : Ordinary u) :
    ExtendedWeak S (.lam σ s) u := by
  cases right with
  | @abs _ _ ρ body y hm hu hyt hyu child =>
    have he : τ = ρ := (Ty.arrow.inj (types ht hm)).2
    subst ρ
    exact CutBinderProof.abstractions S n below σ τ s t body x y hp hu hxs hxt hyt hyu left child
      (by change 1 + treeSize child = n at hc; omega) ho

theorem functional (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (f : Head) (σ τ : Ty) (base extras : Args) (body u : Expr) (x : Nat)
    (hp : PaperTerm S (.marked f (.arrow σ τ) base extras) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ body) (.arrow σ τ))
    (hxs : freeOccurs (σ,x) (.marked f (.arrow σ τ) base extras) = false) (hxt : freeOccurs (σ,x) body = false)
    (left : ExtendedWeakTree S (.marked f τ base (extras.append (.cons (.free σ x) .nil))) (openBody σ x body))
    (right : ExtendedWeakTree S (.lam σ body) u) (hc : treeSize right = n) (ho : Ordinary u) :
    ExtendedWeak S (.marked f (.arrow σ τ) base extras) u := by
  cases right with
  | @abs _ _ ρ target y hm hu hyt hyu child =>
    have he : τ = ρ := (Ty.arrow.inj (types ht hm)).2
    subst ρ
    exact CutBinderProof.functionalAbstraction S n below f base extras σ τ body target x y hp hu hxs hxt hyt hyu left child
      (by change 1 + treeSize child = n at hc; omega) ho

theorem functionalHead (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (f g : Head) (ss ts : Args) (u : Expr)
    (hp : PaperTerm S (.head f ss) f.result) (ht : PaperTerm S (.head g ts) g.result)
    (heq : Equivalent S f g) (htype : f.result = g.result) (left : ExtendedMatchingTree S ss ts)
    (right : ExtendedWeakTree S (.head g ts) u) (hc : treeSize right = n) (ho : Ordinary u) :
    ExtendedWeak S (.head f ss) u := by
  cases right with
  | funHead hm hu heq' htype' child =>
    exact CutHeadProof.funFun S n below _ _ _ _ _ _ hp hu heq heq' htype htype' left child
      (by change 1 + treeSize child = n at hc; omega) ho
  | put hm hu child =>
    exact CutHeadProof.put S n below _ _ _ _ ⟨.funHead hp ht heq htype left⟩ child
      (by change 1 + treeSize child = n at hc; omega) ho

theorem copyHead (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (f g : Head) (ss es ts : Args) (u : Expr)
    (hp : PaperTerm S (.marked f g.result ss es) g.result) (ht : PaperTerm S (.head g ts) g.result)
    (hprec : Precedes S f g) (left : ExtendedWholeTree S f ss es ts)
    (right : ExtendedWeakTree S (.head g ts) u) (hc : treeSize right = n) (ho : Ordinary u) :
    ExtendedWeak S (.marked f g.result ss es) u := by
  cases right with
  | funHead hm hu heq' htype' child =>
    exact CutHeadProof.copyFun S n below _ _ _ _ _ _ _ hp hu hprec heq' htype' left child
      (by change 1 + treeSize child = n at hc; omega) ho
  | put hm hu child =>
    exact CutHeadProof.put S n below _ _ _ _ ⟨.copy hp ht hprec left⟩ child
      (by change 1 + treeSize child = n at hc; omega) ho

theorem statHead (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (f g : Head) (ss es ts : Args) (u : Expr)
    (hp : PaperTerm S (.marked f g.result ss es) g.result) (ht : PaperTerm S (.head g ts) g.result)
    (heq : Equivalent S f g) (left : ExtendedMultisetTree S ss ts) (whole : ExtendedWholeTree S f ss es ts)
    (right : ExtendedWeakTree S (.head g ts) u) (hc : treeSize right = n) (ho : Ordinary u) :
    ExtendedWeak S (.marked f g.result ss es) u := by
  cases right with
  | funHead hm hu heq' htype' child =>
    exact CutHeadProof.statFun S n below _ _ _ _ _ _ _ hp hu heq heq' htype' left whole child
      (by change 1 + treeSize child = n at hc; omega) ho
  | put hm hu child =>
    exact CutHeadProof.put S n below _ _ _ _ ⟨.stat hp ht heq left whole⟩ child
      (by change 1 + treeSize child = n at hc; omega) ho
end LogicLineages.PersistentMarking.CutLeftCoreProof
