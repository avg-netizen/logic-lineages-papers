module
public import LogicLineages.ModelsAlgebra.PGroups.SourceAbsorptionTargets
public import LogicLineages.ModelsAlgebra.PGroups.AbsorptionMap
public import LogicLineages.ModelsAlgebra.PGroups.AbsorptionLogic
public import LogicLineages.ModelsAlgebra.PGroups.SingleReservoirExtraction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem absorption_tuple_transport : Targets.groupAbsorptionTupleTransport := by
  intro p _ K A T _ _ _ _ k e hT m a
  obtain ⟨f,hf,hfix⟩ := bounded_absorption_tuple_fixing p A T k hT m (fun j => e (a j))
  let ep := e.prodCongr (AddEquiv.refl T)
  refine ⟨e.symm.toAddMonoidHom.comp (f.comp ep.toAddMonoidHom),
    e.symm.injective.comp (hf.comp ep.injective), ?_⟩
  intro j
  change e.symm (f (e (a j),0)) = a j
  rw [hfix j, e.symm_apply_apply]

theorem source_factor_absorption : Targets.groupSourceFactorAbsorption := by
  intro p _ K A T _ _ _ _ _ k N e _ hT
  let i : K →+ K × T := (AddMonoidHom.id K).prod 0
  have hi : Function.Injective i := by
    intro x y h
    exact congrArg Prod.fst h
  have hfix := absorption_tuple_transport p K A T k e hT
  exact ⟨tuple_fixing_sigma_one (K × T) K i hi hfix,
    tuple_fixing_backforth_two (K × T) K i hi hfix⟩

theorem source_bounded_absorption : Targets.groupSourceBoundedAbsorption := by
  intro p _ K T _ _ _ _ N a hK ha hT
  obtain ⟨A, inst, hcount, ⟨e⟩⟩ := single_reservoir_extraction p K N a hK ha
  letI := inst
  exact source_factor_absorption p K A T (a.val+1) N e hK hT

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
