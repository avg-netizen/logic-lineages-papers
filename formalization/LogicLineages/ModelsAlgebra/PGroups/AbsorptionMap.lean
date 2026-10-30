module
public import LogicLineages.ModelsAlgebra.PGroups.AbsorptionMapTargets
public import LogicLineages.ModelsAlgebra.PGroups.BoundedReservoirEmbedding
public import LogicLineages.ModelsAlgebra.PGroups.FreshCombine
public import Mathlib.Data.Finset.Lattice.Fold
public meta import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem absorption_map_injective : Targets.groupAbsorptionMapInjective := by
  intro A C T _ _ _ M j hj x y h
  have ha := congrArg (fun z : A × (ℕ →₀ C) => z.1) h
  have hh := congrArg (fun z : A × (ℕ →₀ C) => z.2) h
  have he : (j x.2,x.1.2) = (j y.2,y.1.2) :=
    fresh_combine_injective C C M (AddMonoidHom.id C) Function.injective_id hh
  have hlow := congrArg (fun z : (ℕ →₀ C) × (ℕ →₀ C) => z.1) he
  have hhigh := congrArg (fun z : (ℕ →₀ C) × (ℕ →₀ C) => z.2) he
  apply Prod.ext
  · apply Prod.ext
    · exact ha
    · exact hhigh
  · exact hj hlow

theorem absorption_map_fixes : Targets.groupAbsorptionMapFixes := by
  intro A C T _ _ _ M j x hx
  apply Prod.ext
  · rfl
  · change freshCombine C C M (AddMonoidHom.id C) (j 0,x.2) = x.2
    rw [map_zero]
    exact fresh_combine_fixes C C M (AddMonoidHom.id C) x.2 hx

theorem bounded_absorption_tuple_fixing : Targets.groupBoundedAbsorptionTupleFixing := by
  classical
  intro p _ A T _ _ _ k hk m a
  obtain ⟨j,hj⟩ := bounded_reservoir_embedding p T k hk
  let support := Finset.univ.biUnion (fun n : Fin m => (a n).2.support)
  let M := support.sup id + 1
  refine ⟨absorptionMap A (ZMod (p^k)) T M j, absorption_map_injective A _ T M j hj, ?_⟩
  intro n
  apply absorption_map_fixes A _ T M j (a n)
  intro l hl
  have hs : l ∈ support := Finset.mem_biUnion.mpr ⟨n,Finset.mem_univ n,hl⟩
  have hb : l ≤ support.sup id := Finset.le_sup (f := id) hs
  dsimp [M]
  omega

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
