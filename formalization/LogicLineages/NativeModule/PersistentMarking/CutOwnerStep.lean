module

public import LogicLineages.NativeModule.PersistentMarking.CutOwnerHeadProof
public import LogicLineages.NativeModule.PersistentMarking.CutBinderProof
public import LogicLineages.NativeModule.PersistentMarking.CutSelectionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.CutOwnerStep
open Spine NameBridge ExtendedMeasure

theorem owner (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (f g : Head) (sb se tb te : Args) (τ : Ty) (u : Expr)
    (root : CutOwnerSyntax.Root S f sb se g tb te)
    (hp : PaperTerm S (.marked f τ sb se) τ) (ht : PaperTerm S (.marked g τ tb te) τ)
    (right : ExtendedWeakTree S (.marked g τ tb te) u) (hc : treeSize right = n) (ho : Ordinary u) :
    ExtendedWeak S (.marked f τ sb se) u := by
  cases right with
  | select hq hu ha harg hcall cont =>
    apply CutSelectionProof.selection S n below f sb se _ _ _ _ _ _ _ _ _ _ root hp ht hu ha harg
      (ConservativeOwnerSupport.wholeTuple _ _ _ _) hcall cont
    · change 1 + treeSize cont = n at hc; omega
    · exact ho
  | @fabs g σ τ tb te body x hq hu hxo hxb cont =>
    apply CutBinderProof.ownerFunctional S n below f g sb se tb te σ τ body x root hp ht hu hxo hxb cont
    · change 1 + treeSize cont = n at hc; omega
    · exact ho
  | copy hq hu hprec whole =>
    apply CutOwnerHeadProof.copy S n below _ _ _ _ _ _ _ _ root hp ht hu hprec whole
    · change 1 + treeSize whole = n at hc; omega
    · exact ho
  | stat hq hu heq multi whole =>
    apply CutOwnerHeadProof.stat S n below _ _ _ _ _ _ _ _ root hp ht hu heq multi whole
    · change 1 + treeSize multi + treeSize whole = n at hc; omega
    · change 1 + treeSize multi + treeSize whole = n at hc; omega
    · exact ho
  | inHead _ _ _ _ _ => exact False.elim ho
  | marked1 _ _ _ _ _ => exact False.elim ho
  | marked2 _ _ _ _ _ _ => exact False.elim ho
  | @drop g τ base u extras added hq hu cont =>
    have left := CutOwnerProof.retyped S f sb se g tb (extras.append added) τ root hp ht
    have hnew := TargetExtrasProof.suffixRemoval S _ g τ tb extras added left
    exact below _ _ u cont (by change 1 + treeSize cont = n at hc; omega) ho hnew
  | @perm g τ base extras u reordered hq hu hperm cont =>
    have left := CutOwnerProof.retyped S f sb se g tb te τ root hp ht
    have hnew := TargetExtrasProof.targetPermutation S _ g τ tb te reordered left hperm
    exact below _ _ u cont (by change 1 + treeSize cont = n at hc; omega) ho hnew
  | @copies g τ base extras u copies hq hu hcopies cont =>
    have left := CutOwnerProof.retyped S f sb se g tb te τ root hp ht
    have hnew := TargetExtrasProof.copyAddition S _ g τ tb te copies left hcopies
    exact below _ _ u cont (by change 1 + treeSize cont = n at hc; omega) ho hnew
  | pselect hq hu ha harg htuple hcall cont =>
    apply CutSelectionProof.selection S n below f sb se _ _ _ _ _ _ _ _ _ _ root hp ht hu ha harg htuple hcall cont
    · change 1 + treeSize cont = n at hc; omega
    · exact ho
end LogicLineages.PersistentMarking.CutOwnerStep
