import LogicLineages.PersistentMarking.CutCoreSupport
import LogicLineages.PersistentMarking.ExtendedOpeningProof
import LogicLineages.PersistentMarking.UnaryTransportProof
namespace LogicLineages.PersistentMarking.CutBinderProof
open Spine NameBridge OpeningFoundationProof ExtendedMeasure

theorem abstractions (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (σ τ : Ty) (s t u : Expr) (x y : Nat)
    (hs : PaperTerm S (.lam σ s) (.arrow σ τ)) (hu : PaperTerm S (.lam σ u) (.arrow σ τ))
    (hxs : freeOccurs (σ,x) s = false) (hxt : freeOccurs (σ,x) t = false)
    (hyt : freeOccurs (σ,y) t = false) (hyu : freeOccurs (σ,y) u = false)
    (left : ExtendedWeakTree S (openBody σ x s) (openBody σ x t))
    (right : ExtendedWeakTree S (openBody σ y t) (openBody σ y u))
    (hc : treeSize right < n) (ho : Ordinary u) : ExtendedWeak S (.lam σ s) (.lam σ u) := by
  let z := max (maxFreeName s) (max (maxFreeName t) (maxFreeName u)) + 1
  have hzs : freeOccurs (σ,z) s = false := aboveFresh σ z s (by dsimp [z]; omega)
  have hzt : freeOccurs (σ,z) t = false := aboveFresh σ z t (by dsimp [z]; omega)
  have hzu : freeOccurs (σ,z) u = false := aboveFresh σ z u (by dsimp [z]; omega)
  obtain ⟨left',_⟩ := ExtendedOpeningProof.absSynchronize S σ x z s t hxs hxt hzs hzt left
  obtain ⟨right',he⟩ := ExtendedOpeningProof.absSynchronize S σ y z t u hyt hyu hzt hzu right
  obtain ⟨hcut⟩ := below _ _ _ right' (by omega) (ElementarySupportProof.openOrdinary σ z 0 u ho) ⟨left'⟩
  exact ⟨.abs hs hu hzs hzu hcut⟩

theorem functionalAbstraction (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (f : Head) (base extras : Args) (σ τ : Ty) (t u : Expr) (x y : Nat)
    (hs : PaperTerm S (.marked f (.arrow σ τ) base extras) (.arrow σ τ))
    (hu : PaperTerm S (.lam σ u) (.arrow σ τ))
    (hxs : freeOccurs (σ,x) (.marked f (.arrow σ τ) base extras) = false) (hxt : freeOccurs (σ,x) t = false)
    (hyt : freeOccurs (σ,y) t = false) (hyu : freeOccurs (σ,y) u = false)
    (left : ExtendedWeakTree S (.marked f τ base (extras.append (.cons (.free σ x) .nil))) (openBody σ x t))
    (right : ExtendedWeakTree S (openBody σ y t) (openBody σ y u))
    (hc : treeSize right < n) (ho : Ordinary u) :
    ExtendedWeak S (.marked f (.arrow σ τ) base extras) (.lam σ u) := by
  let z := max (maxFreeName (.marked f (.arrow σ τ) base extras)) (max (maxFreeName t) (maxFreeName u)) + 1
  have hzs : freeOccurs (σ,z) (.marked f (.arrow σ τ) base extras) = false := aboveFresh σ z _ (by dsimp [z]; omega)
  have hzt : freeOccurs (σ,z) t = false := aboveFresh σ z t (by dsimp [z]; omega)
  have hzu : freeOccurs (σ,z) u = false := aboveFresh σ z u (by dsimp [z]; omega)
  obtain ⟨left',_⟩ := ExtendedOpeningProof.fabsSynchronize S f σ τ base extras t x z hxs hxt hzs hzt left
  obtain ⟨right',he⟩ := ExtendedOpeningProof.absSynchronize S σ y z t u hyt hyu hzt hzu right
  obtain ⟨hcut⟩ := below _ _ _ right' (by omega) (ElementarySupportProof.openOrdinary σ z 0 u ho) ⟨left'⟩
  exact ⟨.fabs hs hu hzs hzu hcut⟩

theorem ownerOpening (S : Signature) (f g : Head) (sb se tb te : Args) (σ τ : Ty) (x : Nat)
    (root : CutOwnerSyntax.Root S f sb se g tb te)
    (hp : PaperTerm S (.marked f (.arrow σ τ) sb se) (.arrow σ τ))
    (ht : PaperTerm S (.marked g (.arrow σ τ) tb te) (.arrow σ τ)) :
    ExtendedWeak S (.marked f τ sb (se.append (.cons (.free σ x) .nil)))
      (.marked g τ tb (te.append (.cons (.free σ x) .nil))) := by
  have he := CutOwnerProof.retyped S f sb se g tb te (.arrow σ τ) root hp ht
  have hsCall : CallTyped EmptyContext (Expr.marked f (.arrow σ τ) sb se).type (.cons (.free σ x) .nil) τ := .cons .free .nil
  have htCall : CallTyped EmptyContext (Expr.marked g (.arrow σ τ) tb te).type (.cons (.free σ x) .nil) τ := .cons .free .nil
  obtain ⟨out,hout,hcompare⟩ := UnaryTransportProof.unaryTransport S _ _ (.free σ x) (.free σ x) τ _ he ⟨.var⟩ hsCall htCall (UnaryTransportSupport.markedCall htCall)
  have heq := Option.some.inj ((UnaryTransportSupport.markedCall hsCall).symm.trans hout)
  subst out
  exact hcompare

theorem ownerFunctional (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (f g : Head) (sb se tb te : Args) (σ τ : Ty) (body : Expr) (x : Nat)
    (root : CutOwnerSyntax.Root S f sb se g tb te)
    (hp : PaperTerm S (.marked f (.arrow σ τ) sb se) (.arrow σ τ))
    (ht : PaperTerm S (.marked g (.arrow σ τ) tb te) (.arrow σ τ))
    (hu : PaperTerm S (.lam σ body) (.arrow σ τ))
    (hxt : freeOccurs (σ,x) (.marked g (.arrow σ τ) tb te) = false)
    (hxu : freeOccurs (σ,x) body = false)
    (right : ExtendedWeakTree S (.marked g τ tb (te.append (.cons (.free σ x) .nil))) (openBody σ x body))
    (hc : treeSize right < n) (ho : Ordinary body) :
    ExtendedWeak S (.marked f (.arrow σ τ) sb se) (.lam σ body) := by
  let z := max (maxFreeName (.marked f (.arrow σ τ) sb se)) (max (maxFreeName (.marked g (.arrow σ τ) tb te)) (maxFreeName body)) + 1
  have hzp : freeOccurs (σ,z) (.marked f (.arrow σ τ) sb se) = false := aboveFresh σ z _ (by dsimp [z]; omega)
  have hzt : freeOccurs (σ,z) (.marked g (.arrow σ τ) tb te) = false := aboveFresh σ z _ (by dsimp [z]; omega)
  have hzu : freeOccurs (σ,z) body = false := aboveFresh σ z body (by dsimp [z]; omega)
  obtain ⟨right',he⟩ := ExtendedOpeningProof.fabsSynchronize S g σ τ tb te body x z hxt hxu hzt hzu right
  have left := ownerOpening S f g sb se tb te σ τ z root hp ht
  obtain ⟨hcut⟩ := below _ _ _ right' (by omega) (ElementarySupportProof.openOrdinary σ z 0 body ho) left
  exact ⟨.fabs hp hu hzp hzu hcut⟩
end LogicLineages.PersistentMarking.CutBinderProof
