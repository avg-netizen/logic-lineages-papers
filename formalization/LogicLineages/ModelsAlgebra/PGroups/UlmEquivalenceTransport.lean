module
public import LogicLineages.ModelsAlgebra.PGroups.UlmIsomorphismTargets
public import LogicLineages.ModelsAlgebra.PGroups.UlmTransport
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem isomorphism_finite_filtration : Targets.groupIsomorphismFiniteFiltration := by
  intro G H _ _ e p j
  ext x
  constructor
  · rintro ⟨g,hg,rfl⟩
    obtain ⟨w,hw⟩ := (finite_filtration_multiple_image G p j).le hg
    apply (finite_filtration_multiple_image H p j).ge
    refine ⟨e w, ?_⟩
    change p ^ j • e w = e g
    change p ^ j • w = g at hw
    rw [← map_nsmul, hw]
  · intro hx
    obtain ⟨w,hw⟩ := (finite_filtration_multiple_image H p j).le hx
    obtain ⟨v,rfl⟩ := e.surjective w
    refine ⟨p ^ j • v, (finite_filtration_multiple_image G p j).ge ⟨v,rfl⟩, ?_⟩
    change e (p ^ j • v) = x
    rw [map_nsmul]
    exact hw

theorem isomorphism_ulm_rank : Targets.groupIsomorphismUlmRank := by
  intro G H _ _ e p j
  have he := injective_ulm_isomorphism G H p (finiteFiltration p j) e.toAddMonoidHom e.injective
  rw [isomorphism_finite_filtration G H e p j] at he
  obtain ⟨q⟩ := he
  exact q.rank_eq

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
