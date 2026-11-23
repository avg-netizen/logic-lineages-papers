module

public import LogicLineages.NativeModule.PersistentMarking.UnaryRootSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.UnaryTransportCases
open Spine NameBridge UnaryTransportSupport UnaryPermutationSupport UnaryTransportResults UnaryRootSupport ExtendedMeasure

theorem case_var (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : Result S (.weak (.free σ x) (.free σ x)) := by
  intro a b outTy result hab hqa hsb hright
  simp [apply,applyAux] at hright

theorem case_abs (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.lam σ s) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ t) (.arrow σ τ))
    (hxs : freeOccurs (σ,x) s = false)
    (hxt : freeOccurs (σ,x) t = false)
    (hc : ExtendedTree S (.weak (openBody σ x s) (openBody σ x t)))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.lam σ s) (.lam σ t)) := by
  exact UnaryBinderProof.abstraction S σ s t x hxs hxt hc

theorem case_funHead (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.head f ss) f.result)
    (ht : PaperTerm S (.head g ts) g.result)
    (heq : Equivalent S f g)
    (htype : f.result = g.result)
    (hm : ExtendedTree S (.matching ss ts))
    (hn : 1 + treeSize hm = n) : Result S (.weak (.head f ss) (.head g ts)) := by
  intro a b outTy result hab hqa hsb hright
  have hf := argumentFacts hab
  have he : Expr.marked g outTy ts (.cons b .nil) = result := Option.some.inj ((headCall hsb).symm.trans hright)
  subst result
  refine ⟨_,headCall hqa,?_⟩
  obtain ⟨hab⟩ := hab
  exact ⟨.inHead (headPaper hp hf.1) (headPaper ht hf.2) heq hm (.orderedCons hab .orderedNil)⟩

theorem case_put (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.head f ss) f.result)
    (ht : PaperTerm S t f.result)
    (hc : ExtendedTree S (.weak (.marked f f.result ss .nil) t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.head f ss) t) := by
  intro a b outTy result hab hqa hsb hright
  obtain ⟨p,hpCall,hE⟩ := small _ hc (by omega) a b outTy result hab hqa hsb hright
  have he : apply (.head f ss) (.cons a .nil) = apply (.marked f f.result ss .nil) (.cons a .nil) := by
    simp only [apply,applyAux,SubstitutionProof.emptyArgsSubstitution,Args.append]
  exact ⟨p,he.trans hpCall,hE⟩

theorem case_select (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S t τ)
    (ha : (At ss i q ∨ At es i q))
    (hq : Typed EmptyContext q (ArrowPrefix domains τ))
    (hcall : apply q (ownerCopies f ss es domains) = some r)
    (hc : ExtendedTree S (.weak r t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f τ ss es) t) := by
  exact UnarySelectionProof.selectCase S f τ ss es t q r domains (ownerCopies f ss es domains) hp ht ha hq (ConservativeOwnerSupport.wholeTuple f ss es domains) hcall hc (small _ hc (by omega))
end LogicLineages.PersistentMarking.UnaryTransportCases
