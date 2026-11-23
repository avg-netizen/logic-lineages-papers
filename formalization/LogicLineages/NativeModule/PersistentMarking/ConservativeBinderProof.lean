module

public import LogicLineages.NativeModule.PersistentMarking.ConservativeResults

@[expose] public section

namespace LogicLineages.PersistentMarking.ConservativeBinderProof
open Spine NameBridge ConservativeResults ConservativeListSupport OpeningFoundationProof

theorem abstraction (S : Signature) (n : Nat) (small : Smaller S n) (σ τ : Ty) (s t : Expr) (x : Nat)
    (hp : PaperTerm S (.lam σ s) (.arrow σ τ)) (ht : PaperTerm S (.lam σ t) (.arrow σ τ))
    (hxs : freeOccurs (σ,x) s = false) (hxt : freeOccurs (σ,x) t = false)
    (hc : ExtendedWeakTree S (openBody σ x s) (openBody σ x t)) (hsize : ExtendedMeasure.treeSize hc < n) :
    Result S (.weak (.lam σ s) (.lam σ t)) := by
  intro q hq ho
  cases hq with
  | @abs _ p ρ _ y hpp hps hyp hys hbody =>
    let z := max (maxFreeName p) (max (maxFreeName s) (maxFreeName t)) + 1
    have hzp : freeOccurs (σ,z) p = false := aboveFresh σ z p (by dsimp [z]; omega)
    have hzs : freeOccurs (σ,z) s = false := aboveFresh σ z s (by dsimp [z]; omega)
    have hzt : freeOccurs (σ,z) t = false := aboveFresh σ z t (by dsimp [z]; omega)
    have href : RefinementTree S (.lam σ p) (.lam σ s) := .abs hpp hps hyp hys hbody
    have hp' := refiningPaper href hp
    obtain ⟨hr⟩ := RefinementFreshOpeningProof.opening S σ p s z ⟨href⟩ hzp hzs
    obtain ⟨hc',he⟩ := ExtendedOpeningProof.absSynchronize S σ x z s t hxs hxt hzs hzt hc
    have hlt : ExtendedMeasure.treeSize hc' < n := by omega
    have hweak := small _ hc' hlt _ hr (ElementarySupportProof.openOrdinary σ z 0 t ho)
    exact .abs hp' ht hzp hzt hweak

theorem functional (S : Signature) (n : Nat) (small : Smaller S n) (f : Head) (σ τ : Ty) (base extras : Args) (body : Expr) (x : Nat)
    (hp : PaperTerm S (.marked f (.arrow σ τ) base extras) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ body) (.arrow σ τ))
    (hxo : freeOccurs (σ,x) (.marked f (.arrow σ τ) base extras) = false) (hxb : freeOccurs (σ,x) body = false)
    (hc : ExtendedWeakTree S (.marked f τ base (extras.append (.cons (.free σ x) .nil))) (openBody σ x body))
    (hsize : ExtendedMeasure.treeSize hc < n) : Result S (.weak (.marked f (.arrow σ τ) base extras) (.lam σ body)) := by
  intro q hq ho
  cases hq with
  | @marked _ _ qb qe _ _ hpp hps hb he =>
    let z := max (maxFreeName (.marked f (.arrow σ τ) qb qe)) (max (maxFreeName (.marked f (.arrow σ τ) base extras)) (maxFreeName body)) + 1
    have hzq : freeOccurs (σ,z) (.marked f (.arrow σ τ) qb qe) = false := aboveFresh σ z _ (by dsimp [z]; omega)
    have hzo : freeOccurs (σ,z) (.marked f (.arrow σ τ) base extras) = false := aboveFresh σ z _ (by dsimp [z]; omega)
    have hzb : freeOccurs (σ,z) body = false := aboveFresh σ z body (by dsimp [z]; omega)
    have href : Refines S (.marked f (.arrow σ τ) qb qe) (.marked f (.arrow σ τ) base extras) := ⟨.marked hpp hps hb he⟩
    obtain ⟨hr⟩ := RefinementAppendProof.markedAppend S f (.arrow σ τ) τ qb qe base extras (.cons (.free σ z) .nil) (.cons (.free σ z) .nil) href ⟨.cons .var .nil⟩
    obtain ⟨hc',hcount⟩ := ExtendedOpeningProof.fabsSynchronize S f σ τ base extras body x z hxo hxb hzo hzb hc
    have hlt : ExtendedMeasure.treeSize hc' < n := by omega
    have hweak := small _ hc' hlt _ hr (ElementarySupportProof.openOrdinary σ z 0 body ho)
    exact .fabs hpp ht hzq hzb hweak
end LogicLineages.PersistentMarking.ConservativeBinderProof
