import LogicLineages.PersistentMarking.ConservativeBinderProof
import LogicLineages.PersistentMarking.RefinementMarkProof
namespace LogicLineages.PersistentMarking.ConservativeCases
open Spine NameBridge ConservativeResults ConservativeListSupport ConservativeOwnerSupport
open ExtendedMeasure

theorem case_fabs (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f (.arrow σ τ) ss es) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ body) (.arrow σ τ))
    (hxo : freeOccurs (σ,x) (.marked f (.arrow σ τ) ss es) = false)
    (hxb : freeOccurs (σ,x) body = false)
    (hc : ExtendedTree S (.weak (.marked f τ ss (es.append (.cons (.free σ x) .nil))) (openBody σ x body)))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f (.arrow σ τ) ss es) (.lam σ body)) := by
  exact ConservativeBinderProof.functional S n small f σ τ ss es body x hp ht hxo hxb hc (by omega)

theorem case_copy (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f g.result ss es) g.result)
    (ht : PaperTerm S (.head g ts) g.result)
    (hpref : Precedes S f g)
    (hw : ExtendedTree S (.whole f ss es ts))
    (hn : 1 + treeSize hw = n) : Result S (.weak (.marked f g.result ss es) (.head g ts)) := by
  intro q hq ho
  cases hq with
  | marked hqp hsp hb he =>
    exact .copy hqp ht hpref (small _ hw (by omega) _ _ _ (.marked hqp hsp hb he) ho)

theorem case_stat (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f g.result ss es) g.result)
    (ht : PaperTerm S (.head g ts) g.result)
    (heq : Equivalent S f g)
    (hm : ExtendedTree S (.multiset ss ts))
    (hw : ExtendedTree S (.whole f ss es ts))
    (hn : 1 + treeSize hm + treeSize hw = n) : Result S (.weak (.marked f g.result ss es) (.head g ts)) := by
  intro q hq ho
  cases hq with
  | marked hqp hsp hb he =>
    exact .stat hqp ht heq (small _ hm (by omega) _ hb ho) (small _ hw (by omega) _ _ _ (.marked hqp hsp hb he) ho)

theorem case_inHead (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S (.marked g τ ts ds) τ)
    (heq : Equivalent S f g)
    (hm : ExtendedTree S (.matching ss ts))
    (ho : ExtendedTree S (.ordered es ds))
    (hn : 1 + treeSize hm + treeSize ho = n) : Result S (.weak (.marked f τ ss es) (.marked g τ ts ds)) := by
  intro q hq hordinary
  exact False.elim hordinary

theorem case_marked1 (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S (.marked g τ ts ds) τ)
    (hpref : Precedes S f g)
    (hb : ExtendedTree S (.whole f ss es ts))
    (he : ExtendedTree S (.whole f ss es ds))
    (hn : 1 + treeSize hb + treeSize he = n) : Result S (.weak (.marked f τ ss es) (.marked g τ ts ds)) := by
  intro q hq ho
  exact False.elim ho
end LogicLineages.PersistentMarking.ConservativeCases
