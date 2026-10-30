module
public import LogicLineages.ModelsAlgebra.PGroups.FreshCombineDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

noncomputable def absorptionMap (A C T : Type) [AddCommGroup A] [AddCommGroup C] [AddCommGroup T]
    (M : ℕ) (j : T →+ (ℕ →₀ C)) : ((A × (ℕ →₀ C)) × T) →+ (A × (ℕ →₀ C)) := by
  let a := (AddMonoidHom.fst A (ℕ →₀ C)).comp (AddMonoidHom.fst (A × (ℕ →₀ C)) T)
  let high := (AddMonoidHom.snd A (ℕ →₀ C)).comp (AddMonoidHom.fst (A × (ℕ →₀ C)) T)
  let low := j.comp (AddMonoidHom.snd (A × (ℕ →₀ C)) T)
  exact a.prod ((freshCombine C C M (AddMonoidHom.id C)).comp (low.prod high))

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
