module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerEnumerationDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.WalkerPresentedDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.WalkerLimitDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

/-- The actual source parent transported through an ancestor enumeration.
Out-of-range entries after a finite presentation are irrelevant roots. -/
noncomputable def walkerFiniteOrdinalParent (ξ : Ordinal.{0}) (n : ℕ)
    (e : Fin n ≃ WalkerOrdinalNode ξ) (he : WalkerAncestorEnumeration ξ (Fin n) e) :
    WalkerParentSequence := fun k =>
  if hk : k < n then
    match h : walkerOrdinalParent ξ (e ⟨k, hk⟩) with
    | none => none
    | some t => some ⟨(e.symm t).val, he ⟨k, hk⟩ (e.symm t) (by simpa using h)⟩
  else none

noncomputable def walkerInfiniteOrdinalParent (ξ : Ordinal.{0})
    (e : ℕ ≃ WalkerOrdinalNode ξ) (he : WalkerAncestorEnumeration ξ ℕ e) :
    WalkerParentSequence := fun k =>
  match h : walkerOrdinalParent ξ (e k) with
  | none => none
  | some t => some ⟨e.symm t, he k (e.symm t) (by simpa using h)⟩

end LogicLineages.ModelsAlgebra.PGroups
