module

public import LogicLineages.ModelsAlgebra.Forests.AgeNecessaryTargets
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Denumerable

/-! Finite unions inside an actual countable forest give JEP. Unbounded finite
members force the carrier to be infinite and hence genuinely equivalent to Nat. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.AgeNecessaryProof

open AgeConstruction

theorem realizedForestAgeHasJEP : Targets.RealizedForestAgeHasJEP := by
  classical
  intro K A hAge F G hF hG
  obtain ⟨f⟩ := (hAge F).mp hF
  obtain ⟨g⟩ := (hAge G).mp hG
  let S : Set A.Carrier := Set.range f ∪ Set.range g
  have hf : (Set.range f).Finite := Set.toFinite _
  have hg : (Set.range g).Finite := Set.toFinite _
  letI : Fintype S := (hf.union hg).fintype
  let H : FiniteOrderForest := {
    Carrier := S
    carrierFintype := inferInstance
    carrierPartialOrder := inferInstance
    forest := fun {x y z} hx hy => A.forest hx hy }
  let ef : F.Carrier ↪o H.Carrier := {
    toFun := fun x => ⟨f x, Or.inl ⟨x, rfl⟩⟩
    inj' := fun _ _ h => f.injective (congrArg Subtype.val h)
    map_rel_iff' := fun {_ _} => f.le_iff_le }
  let eg : G.Carrier ↪o H.Carrier := {
    toFun := fun x => ⟨g x, Or.inr ⟨x, rfl⟩⟩
    inj' := fun _ _ h => g.injective (congrArg Subtype.val h)
    map_rel_iff' := fun {_ _} => g.le_iff_le }
  exact ⟨H, (hAge H).mpr ⟨OrderEmbedding.subtype S⟩, ⟨ef⟩, ⟨eg⟩⟩

theorem unboundedForestAgeInfinite : Targets.UnboundedForestAgeInfinite := by
  classical
  intro K A hAge hUnbounded
  by_contra h
  letI : Finite A.Carrier := Finite.of_not_infinite h
  letI : Fintype A.Carrier := Fintype.ofFinite _
  obtain ⟨F, hF, hlarge⟩ := hUnbounded (Fintype.card A.Carrier)
  obtain ⟨e⟩ := (hAge F).mp hF
  exact (not_lt_of_ge (Fintype.card_le_of_injective e e.injective)) hlarge

theorem unboundedForestAgeCountablyInfinite : Targets.UnboundedForestAgeCountablyInfinite := by
  intro K A hAge hUnbounded
  letI : Infinite A.Carrier := unboundedForestAgeInfinite K A hAge hUnbounded
  infer_instance

end LogicLineages.ModelsAlgebra.Forests.AgeNecessaryProof
