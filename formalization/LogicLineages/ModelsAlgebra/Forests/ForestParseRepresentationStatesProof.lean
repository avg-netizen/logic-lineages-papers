module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStatesTargets
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinaryStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarShapeStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStates.Proof
open RankedParse ForestParseRepresentationCotree ForestParseRepresentationBinary ProfileAutomatonEncoding

theorem stateSetMem (M : Machine) (C : Cotree) (q : M.State) :
    q ∈ stateSet M C ↔ ∃ t, Expansion t C ∧ machineRun M t = q := by
  classical
  simp [stateSet]

theorem stateSetLeaf : Targets.StateSetLeaf := by
  intro M
  classical
  ext q
  rw [stateSetMem]
  constructor
  · rintro ⟨t, h, he⟩
    cases h
    simpa [machineRun] using he.symm
  · intro h
    have he : q = M.leaf := Finset.mem_singleton.mp h
    exact ⟨.atom, Expansion.atom, he.symm⟩

theorem stateSetGraphExact : Targets.StateSetGraphExact := by
  intro M C hC q
  rw [stateSetMem]
  constructor
  · rintro ⟨t, ht, hr⟩
    exact ⟨t, ForestParseRepresentationBinary.Proof.expansionSound _ _ ht, hr⟩
  · rintro ⟨t, ht, hr⟩
    exact ⟨t, (ForestParseRepresentationBinary.Proof.binaryCharacterization t C hC).mp ht, hr⟩

theorem stateSetNodeExact : Targets.StateSetNodeExact := by
  intro M o n c q
  rw [stateSetMem]
  constructor
  · rintro ⟨t, ht, hr⟩
    cases ht with
    | node r s hc hb =>
      refine ⟨s, fun i => machineRun M (r i), hb, ?_, ?_⟩
      · intro i; exact (stateSetMem _ _ _).mpr ⟨r i, hc i, rfl⟩
      · exact (CotreeGrammarShape.Proof.graftRunExact M o _ r s).symm.trans hr
  · rintro ⟨s, v, hb, hv, he⟩
    classical
    have hrep : ∀ i, ∃ t, Expansion t (c i) ∧ machineRun M t = v i :=
      fun i => (stateSetMem _ _ _).mp (hv i)
    let r : Fin (n + 2) → Term := fun i => Classical.choose (hrep i)
    have hc : ∀ i, Expansion (r i) (c i) := fun i => (Classical.choose_spec (hrep i)).1
    have hr : machineRun M ∘ r = v := funext (fun i => (Classical.choose_spec (hrep i)).2)
    refine ⟨graft o r s, Expansion.node r s hc hb, ?_⟩
    rw [CotreeGrammarShape.Proof.graftRunExact, hr]
    exact he

theorem stateSetAcceptExact : Targets.StateSetAcceptExact := by
  intro M C hC
  constructor
  · rintro ⟨q, hq, ha⟩
    obtain ⟨t, ht, hr⟩ := (stateSetGraphExact M C hC q).mp hq
    exact ⟨t, ht, hr ▸ ha⟩
  · rintro ⟨t, ht, ha⟩
    exact ⟨machineRun M t, (stateSetGraphExact M C hC _).mpr ⟨t, ht, rfl⟩, ha⟩

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStates.Proof
