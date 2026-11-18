import LogicLineages.PersistentMarking.SharpBinderProof
import LogicLineages.PersistentMarking.RefinementMarkProof
import LogicLineages.PersistentMarking.ExtraCompressionProof
import LogicLineages.PersistentMarking.ExtendedEndpointProof
namespace LogicLineages.PersistentMarking.SharpCases
open Spine NameBridge SharpResults ConservativeListSupport ConservativeOwnerSupport
open ExtendedMeasure

theorem case_var (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : Result S (.weak (.free σ x) (.free σ x)) := by
  intro q hq
  cases hq
  exact ⟨.var⟩

theorem case_abs (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.lam σ s) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ t) (.arrow σ τ))
    (hxs : freeOccurs (σ,x) s = false)
    (hxt : freeOccurs (σ,x) t = false)
    (hc : ExtendedTree S (.weak (openBody σ x s) (openBody σ x t)))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.lam σ s) (.lam σ t)) := by
  exact SharpBinderProof.abstraction S n small σ τ s t x hp ht hxs hxt hc (by omega)

theorem case_funHead (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.head f ss) f.result)
    (ht : PaperTerm S (.head g ts) g.result)
    (heq : Equivalent S f g)
    (htype : f.result = g.result)
    (hm : ExtendedTree S (.matching ss ts))
    (hn : 1 + treeSize hm = n) : Result S (.weak (.head f ss) (.head g ts)) := by
  intro q hq
  cases hq with
  | head hqp hsp hb =>
    obtain ⟨hm'⟩ := small _ hm (by omega) _ hb
    exact ⟨.funHead hqp ht heq htype hm'⟩

theorem case_put (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.head f ss) f.result)
    (ht : PaperTerm S t f.result)
    (hc : ExtendedTree S (.weak (.marked f f.result ss .nil) t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.head f ss) t) := by
  intro q hq
  cases hq with
  | head hqp hsp hb =>
    obtain ⟨r,hm,href⟩ := RefinementMarkProof.refinementMarkReflection S _ _ _ ⟨.head hqp hsp hb⟩ rfl
    simp only [Spine.mark,Option.some.injEq] at hm
    subst r
    obtain ⟨hr⟩ := href
    obtain ⟨hc'⟩ := small _ hc (by omega) _ hr
    exact ⟨.put hqp ht hc'⟩

theorem case_select (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S t τ)
    (ha : (At ss i q ∨ At es i q))
    (hq : Typed EmptyContext q (ArrowPrefix domains τ))
    (hcall : apply q (ownerCopies f ss es domains) = some r)
    (hc : ExtendedTree S (.weak r t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f τ ss es) t) := by
  intro p href
  cases href with
  | @marked _ _ qb qe _ _ hpp hps hb he =>
    exact SharpSelectionProof.selectCase S f τ ss es qb qe t q r domains (ownerCopies f ss es domains) hp ht (.marked hpp hps hb he) ha hq (wholeTuple f ss es domains) hcall
      (fun p hr => by obtain ⟨hr⟩ := hr; exact small _ hc (by omega) p hr)

end LogicLineages.PersistentMarking.SharpCases
