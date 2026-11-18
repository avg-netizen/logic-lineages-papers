import LogicLineages.PersistentMarking.MarkedBaseTupleFoundationProof
import LogicLineages.PersistentMarking.HereditaryPartialOrderProof
namespace LogicLineages.PersistentMarking.MarkedBaseTupleOrderProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics MarkedBaseTuples

theorem order : MarkedBaseTupleTargets.TupleOrder := by
  intro E Γ ds hw
  refine ⟨?_,?_,?_⟩
  · intro xs hx
    apply (MarkedBaseTupleFoundationProof.orderExact E Γ ds xs xs hx hx).mpr
    intro i σ a b hd ha hb
    have he : a=b := Option.some.inj (ha.symm.trans hb)
    subst b
    exact (HereditaryPartialOrderProof.partialOrder E σ Γ hw).1 a (hx.2 i σ a hd ha)
  · intro xs ys zs hx hy hz hxy hyz
    have hxy := (MarkedBaseTupleFoundationProof.orderExact E Γ ds xs ys hx hy).mp hxy
    have hyz := (MarkedBaseTupleFoundationProof.orderExact E Γ ds ys zs hy hz).mp hyz
    apply (MarkedBaseTupleFoundationProof.orderExact E Γ ds xs zs hx hz).mpr
    intro i σ a c hd ha hc
    have hi : i < ds.length := (List.getElem?_eq_some_iff.mp hd).1
    have hyl := hy.1
    have hiy : i < ys.length := by omega
    let b := ys[i]'hiy
    have hb : ys[i]? = some b := List.getElem?_eq_some_iff.mpr ⟨hiy,rfl⟩
    exact (HereditaryPartialOrderProof.partialOrder E σ Γ hw).2.1 a b c
      (hx.2 i σ a hd ha) (hy.2 i σ b hd hb) (hz.2 i σ c hd hc)
      (hxy i σ a b hd ha hb) (hyz i σ b c hd hb hc)
  · intro xs ys hx hy hxy hyx
    have hxy := (MarkedBaseTupleFoundationProof.orderExact E Γ ds xs ys hx hy).mp hxy
    have hyx := (MarkedBaseTupleFoundationProof.orderExact E Γ ds ys xs hy hx).mp hyx
    apply List.ext_getElem (hx.1.symm.trans hy.1)
    intro i hix hiy
    have hxl := hx.1
    have hi : i < ds.length := by omega
    let σ := ds[i]'hi
    have hd : ds[i]? = some σ := List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩
    have hxa : xs[i]? = some xs[i] := List.getElem?_eq_some_iff.mpr ⟨hix,rfl⟩
    have hya : ys[i]? = some ys[i] := List.getElem?_eq_some_iff.mpr ⟨hiy,rfl⟩
    exact (HereditaryPartialOrderProof.partialOrder E σ Γ hw).2.2 _ _
      (hx.2 i σ _ hd hxa) (hy.2 i σ _ hd hya)
      (hxy i σ _ _ hd hxa hya) (hyx i σ _ _ hd hya hxa)
end LogicLineages.PersistentMarking.MarkedBaseTupleOrderProof
