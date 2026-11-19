import LogicLineages.PersistentMarking.LiteralDerivationLocalityTargets

namespace LogicLineages.PersistentMarking.LiteralDerivationBuilderProof
open Spine NameBridge LiteralDerivationTree

abbrev Witness (S : Signature) (J : Judgment) := _root_.Nonempty (Tree S J)

theorem BVar (S : Signature) (σ : Ty) (x : Nat) : Witness S (.weak (.free σ x) (.free σ x)) :=
  ⟨.var σ x⟩

theorem BAbs (S : Signature) (σ : Ty) (s : Expr) (τ : Ty) (t : Expr) (x : Nat)
    (hp : PaperTerm S (.lam σ s) (.arrow σ τ)) (hq : PaperTerm S (.lam σ t) (.arrow σ τ))
    (hf : freeOccurs (σ,x) s = false) (hg : freeOccurs (σ,x) t = false)
    (_ : Weak S (openBody σ x s) (openBody σ x t))
    (ih : Witness S (.weak (openBody σ x s) (openBody σ x t))) :
    Witness S (.weak (.lam σ s) (.lam σ t)) := by
  obtain ⟨tr⟩ := ih
  exact ⟨.abs σ τ s t x hp hq hf hg tr⟩

theorem BFun (S : Signature) (f : Head) (ss : Args) (g : Head) (ts : Args)
    (hp : PaperTerm S (.head f ss) f.result) (hq : PaperTerm S (.head g ts) g.result)
    (he : Equivalent S f g) (ht : f.result = g.result) (_ : Matching S ss ts)
    (ih : Witness S (.matching ss ts)) : Witness S (.weak (.head f ss) (.head g ts)) := by
  obtain ⟨tr⟩ := ih
  exact ⟨.funHead f g ss ts hp hq he ht tr⟩

theorem BPut (S : Signature) (f : Head) (ss : Args) (t : Expr)
    (hp : PaperTerm S (.head f ss) f.result) (hq : PaperTerm S t f.result)
    (_ : Weak S (.marked f f.result ss .nil) t)
    (ih : Witness S (.weak (.marked f f.result ss .nil) t)) :
    Witness S (.weak (.head f ss) t) := by
  obtain ⟨tr⟩ := ih
  exact ⟨.put f ss t hp hq tr⟩

theorem BSelect (S : Signature) (f : Head) (τ : Ty) (ss es : Args) (t : Expr) (i : Nat)
    (q : Expr) (domains : List Ty) (r : Expr)
    (hp : PaperTerm S (.marked f τ ss es) τ) (hq : PaperTerm S t τ)
    (ho : At ss i q ∨ At es i q) (ht : Typed EmptyContext q (ArrowPrefix domains τ))
    (ha : apply q (ownerCopies f ss es domains) = some r) (_ : Weak S r t)
    (ih : Witness S (.weak r t)) : Witness S (.weak (.marked f τ ss es) t) := by
  obtain ⟨tr⟩ := ih
  exact ⟨.select f τ ss es t i q domains r hp hq ho ht ha tr⟩

theorem BFAbs (S : Signature) (f : Head) (σ τ : Ty) (ss es : Args) (body : Expr) (x : Nat)
    (hp : PaperTerm S (.marked f (.arrow σ τ) ss es) (.arrow σ τ))
    (hq : PaperTerm S (.lam σ body) (.arrow σ τ))
    (hf : freeOccurs (σ,x) (.marked f (.arrow σ τ) ss es) = false) (hg : freeOccurs (σ,x) body = false)
    (_ : Weak S (.marked f τ ss (es.append (.cons (.free σ x) .nil))) (openBody σ x body))
    (ih : Witness S (.weak (.marked f τ ss (es.append (.cons (.free σ x) .nil))) (openBody σ x body))) :
    Witness S (.weak (.marked f (.arrow σ τ) ss es) (.lam σ body)) := by
  obtain ⟨tr⟩ := ih
  exact ⟨.fabs f σ τ ss es body x hp hq hf hg tr⟩

theorem BCopy (S : Signature) (f : Head) (ss es : Args) (g : Head) (ts : Args)
    (hp : PaperTerm S (.marked f g.result ss es) g.result) (hq : PaperTerm S (.head g ts) g.result)
    (hf : Precedes S f g) (_ : Whole S f ss es ts)
    (ih : Witness S (.whole f ss es ts)) :
    Witness S (.weak (.marked f g.result ss es) (.head g ts)) := by
  obtain ⟨tr⟩ := ih
  exact ⟨.copy f g ss es ts hp hq hf tr⟩

theorem BStat (S : Signature) (f : Head) (ss es : Args) (g : Head) (ts : Args)
    (hp : PaperTerm S (.marked f g.result ss es) g.result) (hq : PaperTerm S (.head g ts) g.result)
    (hf : Equivalent S f g) (_ : Multiset S ss ts) (_ : Whole S f ss es ts)
    (ihm : Witness S (.multiset ss ts)) (ihw : Witness S (.whole f ss es ts)) :
    Witness S (.weak (.marked f g.result ss es) (.head g ts)) := by
  obtain ⟨m⟩ := ihm
  obtain ⟨w⟩ := ihw
  exact ⟨.stat f g ss es ts hp hq hf m w⟩

theorem BStrict (S : Signature) (q : Expr) (σ : Ty) (t r : Expr)
    (hp : PaperTerm S q σ) (hq : PaperTerm S t σ) (hm : mark q = some r)
    (_ : Weak S r t) (ih : Witness S (.weak r t)) : Witness S (.strict q t) := by
  obtain ⟨tr⟩ := ih
  exact ⟨.strictIntro q t r σ hp hq hm tr⟩

theorem BMatchNil (S : Signature) : Witness S (.matching .nil .nil) := ⟨.matchingNil⟩

theorem BMatchCons (S : Signature) (targets : Args) (y : Expr) (rest : Args) (x : Expr) (xs : Args)
    (hr : Remove targets y rest) (_ : Weak S x y) (_ : Matching S xs rest)
    (ihw : Witness S (.weak x y)) (ihm : Witness S (.matching xs rest)) :
    Witness S (.matching (.cons x xs) targets) := by
  obtain ⟨w⟩ := ihw
  obtain ⟨m⟩ := ihm
  exact ⟨.matchingCons x y xs targets rest hr w m⟩

theorem BMultiset (S : Signature) (source kept removed target matched added : Args)
    (hs : Split source kept removed) (ht : Split target matched added) (hn : Nonempty removed)
    (_ : Matching S kept matched) (_ : Coverage S removed added)
    (ihm : Witness S (.matching kept matched)) (ihc : Witness S (.coverage removed added)) :
    Witness S (.multiset source target) := by
  obtain ⟨m⟩ := ihm
  obtain ⟨c⟩ := ihc
  exact ⟨.multisetReplace source kept removed target matched added hs ht hn m c⟩

theorem BCoverNil (S : Signature) (owners : Args) : Witness S (.coverage owners .nil) :=
  ⟨.coverageNil owners⟩

theorem BCoverCons (S : Signature) (owners : Args) (i : Nat) (q x : Expr) (xs : Args)
    (ho : At owners i q) (_ : Strict S q x) (_ : Coverage S owners xs)
    (ihs : Witness S (.strict q x)) (ihc : Witness S (.coverage owners xs)) :
    Witness S (.coverage owners (.cons x xs)) := by
  obtain ⟨st⟩ := ihs
  obtain ⟨cs⟩ := ihc
  exact ⟨.coverageCons owners i q x xs ho st cs⟩

theorem BWholeNil (S : Signature) (f : Head) (base extras : Args) :
    Witness S (.whole f base extras .nil) := ⟨.wholeNil f base extras⟩

theorem BWholeCons (S : Signature) (f : Head) (base extras : Args) (q : Expr) (qs : Args)
    (_ : Weak S (.marked f q.type base extras) q) (_ : Whole S f base extras qs)
    (ihw : Witness S (.weak (.marked f q.type base extras) q))
    (ihs : Witness S (.whole f base extras qs)) : Witness S (.whole f base extras (.cons q qs)) := by
  obtain ⟨w⟩ := ihw
  obtain ⟨more⟩ := ihs
  exact ⟨.wholeCons f q base extras qs w more⟩

end LogicLineages.PersistentMarking.LiteralDerivationBuilderProof
