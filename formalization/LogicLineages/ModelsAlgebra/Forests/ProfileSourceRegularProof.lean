module
public import LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegularTargets
public import LogicLineages.ModelsAlgebra.Forests.ProfileAutomatonEncodingProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegular.Proof
open RankedParse RankedGraphImage ProfileAutomatonEncoding ForestParseRepresentation

def rawPathIso : rawGraph pathInput ≃g GraphBridge.fourPath where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    intro x y
    simp [rawGraph, pathInput, GraphBridge.fourPath, SimpleGraph.fromRel, Equiv.refl_apply] <;> intro _ <;> rfl

def rawCycleIso : rawGraph cycleInput ≃g GraphBridge.fourCycle where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    intro x y
    simp [rawGraph, cycleInput, GraphBridge.fourCycle, SimpleGraph.fromRel, Equiv.refl_apply] <;> intro _ <;> rfl

theorem sourceMachineCorrect : Targets.SourceMachineCorrect := by
  intro F t
  change (machine (pathInput :: cycleInput :: F)).accept
    (machineRun (machine (pathInput :: cycleInput :: F)) t) = true ↔ _
  rw [ProfileAutomatonEncoding.Proof.machineCorrect]
  change RawAvoids (pathInput :: cycleInput :: F) t ↔
    (¬ Nonempty (GraphBridge.fourPath ↪g graph t) ∧
      ¬ Nonempty (GraphBridge.fourCycle ↪g graph t) ∧
      ∀ H ∈ F.map rawFinite, ¬ Embeds H (evalFinite t))
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨e⟩
      exact h pathInput (by simp) ⟨e.comp rawPathIso.toEmbedding⟩
    · rintro ⟨e⟩
      exact h cycleInput (by simp) ⟨e.comp rawCycleIso.toEmbedding⟩
    · intro H hH
      obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hH
      exact h A (by simp [hA])
  · rintro ⟨hp, hc, h⟩ A hA
    rcases List.mem_cons.mp hA with hA | hA
    · subst A
      rintro ⟨e⟩
      exact hp ⟨e.comp rawPathIso.symm.toEmbedding⟩
    · rcases List.mem_cons.mp hA with hA | hA
      · subst A
        rintro ⟨e⟩
        exact hc ⟨e.comp rawCycleIso.symm.toEmbedding⟩
      · exact h (rawFinite A) (List.mem_map.mpr ⟨A, hA, rfl⟩)

theorem generalForbiddenRegular : Targets.GeneralForbiddenRegular := by
  intro B
  obtain ⟨F, hF⟩ := ProfileAutomatonEncoding.Proof.arbitraryFiniteFamilyRegular (sourceFamily B)
  have hs : ∀ t, (machine F).accept (machineRun (machine F) t) = true ↔
      GeneralForbiddenLanguage B t := by
    intro t
    simpa [sourceFamily, GeneralForbiddenLanguage, GeneralForbiddenClass,
      evalFinite, Embeds] using hF t
  refine ⟨⟨F, hs⟩, ?_⟩
  intro s t hst ht
  apply (hs s).mp
  apply (ProfileAutomatonEncoding.Proof.machineCorrect F s).mpr
  apply ProfileAutomatonEncoding.Proof.rawAvoidanceDownward F s t hst
  exact (ProfileAutomatonEncoding.Proof.machineCorrect F t).mp ((hs t).mpr ht)

end LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegular.Proof
