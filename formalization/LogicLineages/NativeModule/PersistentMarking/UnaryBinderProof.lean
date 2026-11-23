module

public import LogicLineages.NativeModule.PersistentMarking.UnaryTransportResults

@[expose] public section

namespace LogicLineages.PersistentMarking.UnaryBinderProof
open Spine NameBridge UnaryTransportSupport UnaryTransportResults

theorem arrowArgument {σ υ τ : Ty} {a : Expr}
    (h : CallTyped EmptyContext (.arrow σ υ) (.cons a .nil) τ) : Typed EmptyContext a σ ∧ τ = υ := by
  cases h with
  | cons ha hr => cases hr; exact ⟨ha,rfl⟩

theorem abstraction (S : Signature) (σ : Ty) (s t : Expr) (x : Nat)
    (hxs : freeOccurs (σ,x) s = false) (hxt : freeOccurs (σ,x) t = false)
    (hc : ExtendedWeakTree S (openBody σ x s) (openBody σ x t)) : Unary S (.lam σ s) (.lam σ t) := by
  intro a b τ r hab hqa hsb hr
  have ha := lamArgument hqa
  have hb := lamArgument hsb
  have hout := TwoEnvironmentProof.weak S (RefinementCallMapProof.replace σ x a) (RefinementCallMapProof.replace σ x b)
    (RefinementCallMapProof.typed σ x a ha) (RefinementCallMapProof.typed σ x b hb) (replaceRelated S σ x a b hab) _ _ ⟨hc⟩
  have heq : substitute (.cons b .nil) 0 t = r := Option.some.inj ((lamCall hsb).symm.trans hr)
  subst r
  refine ⟨_,lamCall hqa,?_⟩
  simpa only [openedReplace σ x a s hxs,openedReplace σ x b t hxt] using hout

theorem functional (S : Signature) (f : Head) (σ υ : Ty) (base extras : Args) (body : Expr) (x : Nat)
    (hxo : freeOccurs (σ,x) (.marked f (.arrow σ υ) base extras) = false) (hxb : freeOccurs (σ,x) body = false)
    (hc : ExtendedWeakTree S (.marked f υ base (extras.append (.cons (.free σ x) .nil))) (openBody σ x body)) :
    Unary S (.marked f (.arrow σ υ) base extras) (.lam σ body) := by
  intro a b τ r hab hqa hsb hr
  have ha := (arrowArgument hqa).1
  have he := (arrowArgument hqa).2
  subst τ
  have hb := lamArgument hsb
  have hout := TwoEnvironmentProof.weak S (RefinementCallMapProof.replace σ x a) (RefinementCallMapProof.replace σ x b)
    (RefinementCallMapProof.typed σ x a ha) (RefinementCallMapProof.typed σ x b hb) (replaceRelated S σ x a b hab) _ _ ⟨hc⟩
  have hparts : freeOccursArgs (σ,x) base = false ∧ freeOccursArgs (σ,x) extras = false := by
    simpa only [freeOccurs,Bool.or_eq_false_iff] using hxo
  have heq : substitute (.cons b .nil) 0 body = r := Option.some.inj ((lamCall hsb).symm.trans hr)
  subst r
  refine ⟨_,markedCall hqa,?_⟩
  simpa only [freeSub,FreeCompositionProof.mapAppend,freeSubArgs,RefinementCallMapProof.replace,ite_true,
    SubstitutionProof.shiftZero,RefinementCallMapProof.absentArgs σ x a 0 base hparts.1,
    RefinementCallMapProof.absentArgs σ x a 0 extras hparts.2,openedReplace σ x b body hxb] using hout
end LogicLineages.PersistentMarking.UnaryBinderProof
