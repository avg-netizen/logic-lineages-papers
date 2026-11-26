module

public import LogicLineages.NativeModule.PersistentMarking.TwoEnvironmentSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.TwoEnvironmentBinderProof
open Spine NameBridge TwoEnvironmentSupport RefinementSubstitutionSupport OpeningFoundationProof

theorem abstraction (S : Signature) (n : Nat) (small : Smaller S n) (σ τ : Ty) (s t : Expr) (x : Nat)
    (hp : PaperTerm S (.lam σ s) (.arrow σ τ)) (ht : PaperTerm S (.lam σ t) (.arrow σ τ))
    (hxs : freeOccurs (σ,x) s = false) (hxt : freeOccurs (σ,x) t = false)
    (hc : ExtendedWeakTree S (openBody σ x s) (openBody σ x t)) (hsize : ExtendedMeasure.treeSize hc < n)
    (γ δ : FreeMap) (hg : FreeMapTyped EmptyContext γ) (hd : FreeMapTyped EmptyContext δ) (he : Related S γ δ) :
    Result S γ δ (.weak (.lam σ s) (.lam σ t)) := by
  let z := max (maxFreeName s) (max (maxFreeName t) (max (imageBound γ s) (imageBound δ t))) + 1
  have hzs : freeOccurs (σ,z) s = false := aboveFresh σ z s (by dsimp [z]; omega)
  have hzt : freeOccurs (σ,z) t = false := aboveFresh σ z t (by dsimp [z]; omega)
  have hzg : freeOccurs (σ,z) (freeSub γ 1 s) = false := imageFresh γ σ z 1 s (by dsimp [z]; omega)
  have hzd : freeOccurs (σ,z) (freeSub δ 1 t) = false := imageFresh δ σ z 1 t (by dsimp [z]; omega)
  obtain ⟨hc',heq⟩ := ExtendedOpeningProof.absSynchronize S σ x z s t hxs hxt hzs hzt hc
  have hlt : ExtendedMeasure.treeSize hc' < n := by omega
  obtain ⟨out⟩ := small _ hc' hlt (mask γ σ z) (mask δ σ z) (maskTyped γ σ z hg) (maskTyped δ σ z hd) (maskRelated S γ δ σ z he)
  have hout : ExtendedWeakTree S (openBody σ z (freeSub γ 1 s)) (openBody σ z (freeSub δ 1 t)) := by
    simpa only [maskedOpening γ σ z s hzs,maskedOpening δ σ z t hzt] using out
  exact ⟨.abs (subPaper S γ hg (leftValid he) _ _ hp) (subPaper S δ hd (rightValid he) _ _ ht) hzg hzd hout⟩

theorem functional (S : Signature) (n : Nat) (small : Smaller S n) (f : Head) (σ τ : Ty) (base extras : Args) (body : Expr) (x : Nat)
    (hp : PaperTerm S (.marked f (.arrow σ τ) base extras) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ body) (.arrow σ τ))
    (hxo : freeOccurs (σ,x) (.marked f (.arrow σ τ) base extras) = false) (hxb : freeOccurs (σ,x) body = false)
    (hc : ExtendedWeakTree S (.marked f τ base (extras.append (.cons (.free σ x) .nil))) (openBody σ x body))
    (hsize : ExtendedMeasure.treeSize hc < n)
    (γ δ : FreeMap) (hg : FreeMapTyped EmptyContext γ) (hd : FreeMapTyped EmptyContext δ) (he : Related S γ δ) :
    Result S γ δ (.weak (.marked f (.arrow σ τ) base extras) (.lam σ body)) := by
  let owner := Expr.marked f (.arrow σ τ) base extras
  let z := max (maxFreeName owner) (max (maxFreeName body) (max (imageBound γ owner) (imageBound δ body))) + 1
  have hzo : freeOccurs (σ,z) owner = false := aboveFresh σ z owner (by dsimp [z]; omega)
  have hzb : freeOccurs (σ,z) body = false := aboveFresh σ z body (by dsimp [z]; omega)
  have hzg : freeOccurs (σ,z) (freeSub γ 0 owner) = false := imageFresh γ σ z 0 owner (by dsimp [z]; omega)
  have hzd : freeOccurs (σ,z) (freeSub δ 1 body) = false := imageFresh δ σ z 1 body (by dsimp [z]; omega)
  have hparts : freeOccursArgs (σ,z) base = false ∧ freeOccursArgs (σ,z) extras = false := by
    simpa only [owner,freeOccurs,Bool.or_eq_false_iff] using hzo
  obtain ⟨hc',heq⟩ := ExtendedOpeningProof.fabsSynchronize S f σ τ base extras body x z hxo hxb hzo hzb hc
  have hlt : ExtendedMeasure.treeSize hc' < n := by omega
  obtain ⟨out⟩ := small _ hc' hlt (mask γ σ z) (mask δ σ z) (maskTyped γ σ z hg) (maskTyped δ σ z hd) (maskRelated S γ δ σ z he)
  have hout : ExtendedWeakTree S
      (.marked f τ (freeSubArgs γ 0 base) ((freeSubArgs γ 0 extras).append (.cons (.free σ z) .nil)))
      (openBody σ z (freeSub δ 1 body)) := by
    simpa only [freeSub,FreeCompositionProof.mapAppend,freeSubArgs,mask,ite_true,shift,
      maskedAbsentArgs γ σ z 0 base hparts.1,maskedAbsentArgs γ σ z 0 extras hparts.2,
      maskedOpening δ σ z body hzb] using out
  exact ⟨.fabs (subPaper S γ hg (leftValid he) _ _ hp) (subPaper S δ hd (rightValid he) _ _ ht) hzg hzd hout⟩
end LogicLineages.PersistentMarking.TwoEnvironmentBinderProof
