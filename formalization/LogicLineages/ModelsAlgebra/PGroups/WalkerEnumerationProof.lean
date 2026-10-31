module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerEnumerationTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerOrdinalNodeProof
public import Mathlib.Logic.Equiv.Set
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem walker_ordinal_enumeration : Targets.walkerOrdinalEnumeration := by
  classical
  intro ξ _
  let S := Set.range (walkerOrdinalCode ξ)
  let E : WalkerOrdinalNode ξ ≃ S :=
    Equiv.ofInjective (walkerOrdinalCode ξ) (walker_ordinal_coding ξ).1
  have build {I : Type} [LinearOrder I] (o : I ≃o S) :
      ∃ e : I ≃ WalkerOrdinalNode ξ,
        StrictMono (fun i => walkerOrdinalCode ξ (e i)) ∧ WalkerAncestorEnumeration ξ I e := by
    let e : I ≃ WalkerOrdinalNode ξ := o.toEquiv.trans E.symm
    have hc (i : I) : walkerOrdinalCode ξ (e i) = (o i).val :=
      Equiv.apply_ofInjective_symm (walker_ordinal_coding ξ).1 (o i)
    have hm : StrictMono (fun i => walkerOrdinalCode ξ (e i)) := by
      intro i j hij
      change walkerOrdinalCode ξ (e i) < walkerOrdinalCode ξ (e j)
      rw [hc i, hc j]
      exact o.strictMono hij
    refine ⟨e, hm, ?_⟩
    intro i j hparent
    exact hm.lt_iff_lt.mp ((walker_ordinal_coding ξ).2.2 (e i) (e j) hparent)
  rcases finite_or_infinite S with hf | hi
  · letI := hf
    letI := Fintype.ofFinite S
    obtain ⟨e, hm, he⟩ := build (Fintype.orderIsoFinOfCardEq S rfl)
    exact Or.inl ⟨Fintype.card S, e, hm, he⟩
  · letI := hi
    obtain ⟨e, hm, he⟩ := build (Nat.Subtype.orderIsoOfNat S)
    exact Or.inr ⟨e, hm, he⟩

end LogicLineages.ModelsAlgebra.PGroups
