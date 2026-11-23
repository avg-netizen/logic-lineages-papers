module

public import LogicLineages.NativeModule.PersistentMarking.UnaryRootSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.UnaryTransportCases
open Spine NameBridge UnaryTransportSupport UnaryPermutationSupport UnaryTransportResults UnaryRootSupport ExtendedMeasure

theorem case_marked2 (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S (.marked g τ ts ds) τ)
    (heq : Equivalent S f g)
    (hm : ExtendedTree S (.multiset ss ts))
    (hb : ExtendedTree S (.whole f ss es ts))
    (he : ExtendedTree S (.whole f ss es ds))
    (hn : 1 + treeSize hm + treeSize hb + treeSize he = n) : Result S (.weak (.marked f τ ss es) (.marked g τ ts ds)) := by
  intro a b outTy result hab hqa hsb hright
  have hf := argumentFacts hab
  have hout : Expr.marked g outTy ts (ds.append (.cons b .nil)) = result := Option.some.inj ((markedCall hsb).symm.trans hright)
  subst result
  have hpnew : PaperTerm S (.marked f outTy ss (es.append (.cons a .nil))) outTy := markedPaper hp hf.1
  obtain ⟨hbase⟩ := wholeDrop hpnew hb
  obtain ⟨hextra⟩ := wholeNewExtra hpnew he hab
  refine ⟨_,markedCall hqa,?_⟩
  exact ⟨.marked2 hpnew (markedPaper ht hf.2) heq hm hbase hextra⟩

theorem case_drop (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base (extras.append added)) τ)
    (ht : PaperTerm S t τ)
    (hc : ExtendedTree S (.weak (.marked f τ base extras) t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f τ base (extras.append added)) t) := by
  intro a b outTy result hab hqa hsb hright
  obtain ⟨p,hpCall,hE⟩ := small _ hc (by omega) a b outTy result hab hqa hsb hright
  have hpEq : Expr.marked f outTy base (extras.append (.cons a .nil)) = p :=
    Option.some.inj ((markedCall (f := f) (base := base) (extras := extras) hqa).symm.trans hpCall)
  subst p
  have hf := argumentFacts hab
  have hpnew : PaperTerm S (.marked f outTy base ((extras.append added).append (.cons a .nil))) outTy := markedPaper hp hf.1
  have htarget := resultPaper ht hsb hright hE
  have hperm := swapSuffix extras added (.cons a .nil)
  obtain ⟨href⟩ := OwnerRefinementProof.permutation S f outTy base _ _ hpnew hperm
  have hmid := (RefinementSubstitutionSupport.endpoints href).2
  obtain ⟨hE⟩ := hE
  refine ⟨_,markedCall hqa,?_⟩
  exact ⟨.perm hpnew htarget hperm (.drop hmid htarget hE)⟩

theorem case_perm (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base es) τ)
    (ht : PaperTerm S t τ)
    (hperm : Permutation es ds)
    (hc : ExtendedTree S (.weak (.marked f τ base ds) t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f τ base es) t) := by
  intro a b outTy result hab hqa hsb hright
  obtain ⟨p,hpCall,hE⟩ := small _ hc (by omega) a b outTy result hab hqa hsb hright
  have hpEq : Expr.marked f outTy base (ds.append (.cons a .nil)) = p :=
    Option.some.inj ((markedCall (f := f) (base := base) (extras := ds) hqa).symm.trans hpCall)
  subst p
  have hf := argumentFacts hab
  have hpnew : PaperTerm S (.marked f outTy base (es.append (.cons a .nil))) outTy := markedPaper hp hf.1
  have htarget := resultPaper ht hsb hright hE
  obtain ⟨hE⟩ := hE
  refine ⟨_,markedCall hqa,?_⟩
  exact ⟨.perm hpnew htarget (permutationAppend hperm (.cons a .nil)) hE⟩

theorem case_copies (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base extras) τ)
    (ht : PaperTerm S t τ)
    (hcopies : PrefixCopies f base extras ps)
    (hc : ExtendedTree S (.weak (.marked f τ base (extras.append ps)) t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f τ base extras) t) := by
  intro a b outTy result hab hqa hsb hright
  obtain ⟨p,hpCall,hE⟩ := small _ hc (by omega) a b outTy result hab hqa hsb hright
  have hpEq : Expr.marked f outTy base ((extras.append ps).append (.cons a .nil)) = p :=
    Option.some.inj ((markedCall (f := f) (base := base) (extras := extras.append ps) hqa).symm.trans hpCall)
  subst p
  have hf := argumentFacts hab
  have hpnew : PaperTerm S (.marked f outTy base (extras.append (.cons a .nil))) outTy := markedPaper hp hf.1
  have htarget := resultPaper ht hsb hright hE
  have hcopies' := copiesExtend hcopies (.cons a .nil)
  obtain ⟨href⟩ := OwnerRefinementProof.prefixExpansion S f outTy base _ ps hpnew hcopies'
  have hmid := (RefinementSubstitutionSupport.endpoints href).2
  obtain ⟨hE⟩ := hE
  refine ⟨_,markedCall hqa,?_⟩
  exact ⟨.copies hpnew htarget hcopies' (.perm hmid htarget (swapSuffix extras (.cons a .nil) ps) hE)⟩

theorem case_pselect (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base extras) τ)
    (ht : PaperTerm S t τ)
    (ha : (At base i q ∨ At extras i q))
    (hq : Typed EmptyContext q (ArrowPrefix domains τ))
    (htuple : PrefixTuple f base extras domains args)
    (hcall : apply q args = some r)
    (hc : ExtendedTree S (.weak r t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f τ base extras) t) := by
  exact UnarySelectionProof.selectCase S f τ base extras t q r domains args hp ht ha hq htuple hcall hc (small _ hc (by omega))
end LogicLineages.PersistentMarking.UnaryTransportCases
