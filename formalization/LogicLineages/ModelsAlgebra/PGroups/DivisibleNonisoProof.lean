module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleNonisoTargets
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleCharacteristicProof
public import LogicLineages.ModelsAlgebra.PGroups.PrueferModelProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem divisible_infinite_finite_noniso : Targets.divisibleInfiniteFiniteNoniso := by
  intro R S D E _ _ _ _ p _ _ hr hs hd he h
  obtain ⟨e⟩ := divisible_product_socle_invariant R S D E hr hs hd he p h
  haveI : Finite (pSocle p (⊤ : AddSubgroup D)) := Finite.of_injective e e.injective
  exact not_finite (pSocle p (⊤ : AddSubgroup D))

theorem divisible_finite_pruefer_noniso : Targets.divisibleFinitePrueferNoniso := by
  classical
  intro p _ R D _ _ _ hr hd hiso
  have hprod : GroupDivisible (D×PrueferModel p) := by
    intro n hn x
    obtain ⟨a,ha⟩ := hd n hn x.1
    obtain ⟨b,hb⟩ := (genuine_pruefer_model p).2.1 n hn x.2
    exact ⟨(a,b),Prod.ext ha hb⟩
  obtain ⟨e⟩ := divisible_product_socle_invariant R R D (D×PrueferModel p) hr hr hd hprod p hiso
  let j : pSocle p (⊤ : AddSubgroup D) → pSocle p (⊤ : AddSubgroup (D×PrueferModel p)) :=
    fun x => ⟨((x:D),0),AddSubgroup.mem_top _,Prod.ext x.property.2 (nsmul_zero p)⟩
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : pSocle p (⊤ : AddSubgroup (D×PrueferModel p)) => (z:D×PrueferModel p).1) h)
  have hsur : Function.Surjective (e.symm ∘ j) := Finite.surjective_of_injective (e.symm.injective.comp hj)
  obtain ⟨t,ht,hpt⟩ := (genuine_pruefer_model p).2.2
  let z : pSocle p (⊤ : AddSubgroup (D×PrueferModel p)) :=
    ⟨(0,t),AddSubgroup.mem_top _,Prod.ext (nsmul_zero p) hpt⟩
  obtain ⟨x,hx⟩ := hsur (e.symm z)
  have he : j x = z := e.symm.injective hx
  have hz := congrArg (fun w : pSocle p (⊤ : AddSubgroup (D×PrueferModel p)) => (w:D×PrueferModel p).2) he
  exact ht hz.symm
end LogicLineages.ModelsAlgebra.PGroups
