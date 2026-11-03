module
public import LogicLineages.OrdinalComparison.CanonicalAnnotationBuilderCodeSemanticProof
public import LogicLineages.OrdinalComparison.CanonicalAnnotationBuilderCodePrimitiveProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.CanonicalAnnotationBuilderCode.Proof

theorem rawChecked : Targets.RawChecked := by
  intro Γ tracked n u d h
  rw [buildCode.eq_def] at h
  dsimp only at h
  obtain ⟨τ,hτ,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨arity,harity,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u',hu',h⟩ := Option.bind_eq_some_iff.mp h
  have he : u' = u := by
    split at h
    · exact congrArg Prod.fst (Option.some.inj h)
    · split at h
      · split at h
        · exact congrArg Prod.fst (Option.some.inj h)
        · contradiction
      · split at h
        · split at h
          · obtain ⟨a,ha,h⟩ := Option.bind_eq_some_iff.mp h
            split at h
            · obtain ⟨f,hf,h⟩ := Option.bind_eq_some_iff.mp h
              obtain ⟨a,ha,h⟩ := Option.bind_eq_some_iff.mp h
              exact congrArg Prod.fst (Option.some.inj h)
            · contradiction
          · split at h
            · obtain ⟨body,hbody,h⟩ := Option.bind_eq_some_iff.mp h
              obtain ⟨data,hdata,h⟩ := Option.bind_eq_some_iff.mp h
              exact congrArg Prod.fst (Option.some.inj h)
            · contradiction
        · contradiction
  exact ⟨τ,arity,hτ,harity,he ▸ hu'⟩
end LogicLineages.OrdinalComparison.Source.CanonicalAnnotationBuilderCode.Proof
