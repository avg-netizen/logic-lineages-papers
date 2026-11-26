module

public import LogicLineages.NativeModule.PersistentMarking.ConservativeBinderProof
public import LogicLineages.NativeModule.PersistentMarking.RefinementMarkProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ConservativeCases
open Spine NameBridge ConservativeResults ConservativeListSupport ConservativeOwnerSupport
open ExtendedMeasure

theorem case_marked2 (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S (.marked g τ ts ds) τ)
    (heq : Equivalent S f g)
    (hm : ExtendedTree S (.multiset ss ts))
    (hb : ExtendedTree S (.whole f ss es ts))
    (he : ExtendedTree S (.whole f ss es ds))
    (hn : 1 + treeSize hm + treeSize hb + treeSize he = n) : Result S (.weak (.marked f τ ss es) (.marked g τ ts ds)) := by
  intro q hq ho
  exact False.elim ho

theorem case_drop (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base (extras.append added)) τ)
    (ht : PaperTerm S t τ)
    (hc : ExtendedTree S (.weak (.marked f τ base extras) t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f τ base (extras.append added)) t) := by
  intro q hq ho
  have howner := OwnerRefinementProof.prefixOmission S f τ base (extras.append added) extras hp (prefixAppend extras added)
  obtain ⟨hcomp⟩ := RefinementTransitivityProof.transitive S _ _ _ ⟨hq⟩ howner
  exact small _ hc (by omega) q hcomp ho

theorem case_perm (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base es) τ)
    (ht : PaperTerm S t τ)
    (hperm : Permutation es ds)
    (hc : ExtendedTree S (.weak (.marked f τ base ds) t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f τ base es) t) := by
  intro q hq ho
  have howner := OwnerRefinementProof.permutation S f τ base es ds hp hperm
  obtain ⟨hcomp⟩ := RefinementTransitivityProof.transitive S _ _ _ ⟨hq⟩ howner
  exact small _ hc (by omega) q hcomp ho

theorem case_copies (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base extras) τ)
    (ht : PaperTerm S t τ)
    (hcopies : PrefixCopies f base extras ps)
    (hc : ExtendedTree S (.weak (.marked f τ base (extras.append ps)) t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f τ base extras) t) := by
  intro q hq ho
  have howner := OwnerRefinementProof.prefixExpansion S f τ base extras ps hp hcopies
  obtain ⟨hcomp⟩ := RefinementTransitivityProof.transitive S _ _ _ ⟨hq⟩ howner
  exact small _ hc (by omega) q hcomp ho

theorem case_pselect (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base extras) τ)
    (ht : PaperTerm S t τ)
    (ha : (At base i q ∨ At extras i q))
    (hq : Typed EmptyContext q (ArrowPrefix domains τ))
    (htuple : PrefixTuple f base extras domains args)
    (hcall : apply q args = some r)
    (hc : ExtendedTree S (.weak r t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f τ base extras) t) := by
  intro p href ho
  cases href with
  | @marked _ _ qb qe _ _ hpp hps hb he =>
    exact ConservativeSelectionProof.selectCase S f τ base extras qb qe t q r domains args hp ht (.marked hpp hps hb he) ha hq htuple hcall
      (fun p hr => by obtain ⟨hr⟩ := hr; exact small _ hc (by omega) p hr ho)
end LogicLineages.PersistentMarking.ConservativeCases
