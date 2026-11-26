import LogicLineages.PersistentMarking.SharpBinderProof
import LogicLineages.PersistentMarking.RefinementMarkProof
import LogicLineages.PersistentMarking.ExtraCompressionProof
import LogicLineages.PersistentMarking.ExtendedEndpointProof
namespace LogicLineages.PersistentMarking.SharpCases
open Spine NameBridge SharpResults ConservativeListSupport ConservativeOwnerSupport
open ExtendedMeasure

theorem case_fabs (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f (.arrow σ τ) ss es) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ body) (.arrow σ τ))
    (hxo : freeOccurs (σ,x) (.marked f (.arrow σ τ) ss es) = false)
    (hxb : freeOccurs (σ,x) body = false)
    (hc : ExtendedTree S (.weak (.marked f τ ss (es.append (.cons (.free σ x) .nil))) (openBody σ x body)))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f (.arrow σ τ) ss es) (.lam σ body)) := by
  exact SharpBinderProof.functional S n small f σ τ ss es body x hp ht hxo hxb hc (by omega)

theorem case_copy (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f g.result ss es) g.result)
    (ht : PaperTerm S (.head g ts) g.result)
    (hpref : Precedes S f g)
    (hw : ExtendedTree S (.whole f ss es ts))
    (hn : 1 + treeSize hw = n) : Result S (.weak (.marked f g.result ss es) (.head g ts)) := by
  intro q hq
  cases hq with
  | marked hqp hsp hb he =>
    obtain ⟨hw'⟩ := small _ hw (by omega) _ _ _ (.marked hqp hsp hb he)
    exact ⟨.copy hqp ht hpref hw'⟩

theorem case_stat (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f g.result ss es) g.result)
    (ht : PaperTerm S (.head g ts) g.result)
    (heq : Equivalent S f g)
    (hm : ExtendedTree S (.multiset ss ts))
    (hw : ExtendedTree S (.whole f ss es ts))
    (hn : 1 + treeSize hm + treeSize hw = n) : Result S (.weak (.marked f g.result ss es) (.head g ts)) := by
  intro q hq
  cases hq with
  | marked hqp hsp hb he =>
    obtain ⟨hm'⟩ := small _ hm (by omega) _ hb
    obtain ⟨hw'⟩ := small _ hw (by omega) _ _ _ (.marked hqp hsp hb he)
    exact ⟨.stat hqp ht heq hm' hw'⟩

theorem case_inHead (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S (.marked g τ ts ds) τ)
    (heq : Equivalent S f g)
    (hm : ExtendedTree S (.matching ss ts))
    (ho : ExtendedTree S (.ordered es ds))
    (hn : 1 + treeSize hm + treeSize ho = n) : Result S (.weak (.marked f τ ss es) (.marked g τ ts ds)) := by
  intro q hq
  cases hq with
  | @marked _ _ qb qe _ _ hqp hsp hb he =>
    have hm' := small _ hm (by omega) _ hb
    have hw' := small _ ho (by omega) f qb qe τ hqp he
    exact ExtraCompressionProof.extraCompression S f g τ qb qe ts ds hqp ht heq hm' hw' 

theorem case_marked1 (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S (.marked g τ ts ds) τ)
    (hpref : Precedes S f g)
    (hb : ExtendedTree S (.whole f ss es ts))
    (he : ExtendedTree S (.whole f ss es ds))
    (hn : 1 + treeSize hb + treeSize he = n) : Result S (.weak (.marked f τ ss es) (.marked g τ ts ds)) := by
  intro q hq
  cases hq with
  | marked hqp hsp hbase hextras =>
    obtain ⟨hb'⟩ := small _ hb (by omega) _ _ _ (.marked hqp hsp hbase hextras)
    obtain ⟨he'⟩ := small _ he (by omega) _ _ _ (.marked hqp hsp hbase hextras)
    exact ⟨.marked1 hqp ht hpref hb' he'⟩

end LogicLineages.PersistentMarking.SharpCases
