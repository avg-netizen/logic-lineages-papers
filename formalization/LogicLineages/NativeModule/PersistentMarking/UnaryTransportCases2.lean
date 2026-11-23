module

public import LogicLineages.NativeModule.PersistentMarking.UnaryRootSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.UnaryTransportCases
open Spine NameBridge UnaryTransportSupport UnaryPermutationSupport UnaryTransportResults UnaryRootSupport ExtendedMeasure

theorem case_fabs (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f (.arrow σ τ) ss es) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ body) (.arrow σ τ))
    (hxo : freeOccurs (σ,x) (.marked f (.arrow σ τ) ss es) = false)
    (hxb : freeOccurs (σ,x) body = false)
    (hc : ExtendedTree S (.weak (.marked f τ ss (es.append (.cons (.free σ x) .nil))) (openBody σ x body)))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f (.arrow σ τ) ss es) (.lam σ body)) := by
  exact UnaryBinderProof.functional S f σ τ ss es body x hxo hxb hc

theorem case_copy (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f g.result ss es) g.result)
    (ht : PaperTerm S (.head g ts) g.result)
    (hpref : Precedes S f g)
    (hw : ExtendedTree S (.whole f ss es ts))
    (hn : 1 + treeSize hw = n) : Result S (.weak (.marked f g.result ss es) (.head g ts)) := by
  intro a b outTy result hab hqa hsb hright
  have hf := argumentFacts hab
  have he : Expr.marked g outTy ts (.cons b .nil) = result := Option.some.inj ((headCall hsb).symm.trans hright)
  subst result
  have hpnew : PaperTerm S (.marked f outTy ss (es.append (.cons a .nil))) outTy := markedPaper hp hf.1
  obtain ⟨hbase⟩ := wholeDrop hpnew hw
  obtain ⟨hextra⟩ := wholeNewExtra hpnew (ExtendedTree.wholeNil (S := S) (f := f) (base := ss) (extras := es)) hab
  refine ⟨_,markedCall hqa,?_⟩
  exact ⟨.marked1 hpnew (headPaper ht hf.2) hpref hbase hextra⟩

theorem case_stat (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f g.result ss es) g.result)
    (ht : PaperTerm S (.head g ts) g.result)
    (heq : Equivalent S f g)
    (hm : ExtendedTree S (.multiset ss ts))
    (hw : ExtendedTree S (.whole f ss es ts))
    (hn : 1 + treeSize hm + treeSize hw = n) : Result S (.weak (.marked f g.result ss es) (.head g ts)) := by
  intro a b outTy result hab hqa hsb hright
  have hf := argumentFacts hab
  have he : Expr.marked g outTy ts (.cons b .nil) = result := Option.some.inj ((headCall hsb).symm.trans hright)
  subst result
  have hpnew : PaperTerm S (.marked f outTy ss (es.append (.cons a .nil))) outTy := markedPaper hp hf.1
  obtain ⟨hbase⟩ := wholeDrop hpnew hw
  obtain ⟨hextra⟩ := wholeNewExtra hpnew (ExtendedTree.wholeNil (S := S) (f := f) (base := ss) (extras := es)) hab
  refine ⟨_,markedCall hqa,?_⟩
  exact ⟨.marked2 hpnew (headPaper ht hf.2) heq hm hbase hextra⟩

theorem case_inHead (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S (.marked g τ ts ds) τ)
    (heq : Equivalent S f g)
    (hm : ExtendedTree S (.matching ss ts))
    (ho : ExtendedTree S (.ordered es ds))
    (hn : 1 + treeSize hm + treeSize ho = n) : Result S (.weak (.marked f τ ss es) (.marked g τ ts ds)) := by
  intro a b outTy result hab hqa hsb hright
  have hf := argumentFacts hab
  have he : Expr.marked g outTy ts (ds.append (.cons b .nil)) = result := Option.some.inj ((markedCall hsb).symm.trans hright)
  subst result
  obtain ⟨hab⟩ := hab
  obtain ⟨hordered⟩ := appendOrdered ho (.orderedCons hab .orderedNil)
  refine ⟨_,markedCall hqa,?_⟩
  exact ⟨.inHead (markedPaper hp hf.1) (markedPaper ht hf.2) heq hm hordered⟩

theorem case_marked1 (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S (.marked g τ ts ds) τ)
    (hpref : Precedes S f g)
    (hb : ExtendedTree S (.whole f ss es ts))
    (he : ExtendedTree S (.whole f ss es ds))
    (hn : 1 + treeSize hb + treeSize he = n) : Result S (.weak (.marked f τ ss es) (.marked g τ ts ds)) := by
  intro a b outTy result hab hqa hsb hright
  have hf := argumentFacts hab
  have heq : Expr.marked g outTy ts (ds.append (.cons b .nil)) = result := Option.some.inj ((markedCall hsb).symm.trans hright)
  subst result
  have hpnew : PaperTerm S (.marked f outTy ss (es.append (.cons a .nil))) outTy := markedPaper hp hf.1
  obtain ⟨hbase⟩ := wholeDrop hpnew hb
  obtain ⟨hextra⟩ := wholeNewExtra hpnew he hab
  refine ⟨_,markedCall hqa,?_⟩
  exact ⟨.marked1 hpnew (markedPaper ht hf.2) hpref hbase hextra⟩
end LogicLineages.PersistentMarking.UnaryTransportCases
