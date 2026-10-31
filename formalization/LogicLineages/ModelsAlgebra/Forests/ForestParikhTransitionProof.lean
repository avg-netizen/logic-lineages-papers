module
public import LogicLineages.ModelsAlgebra.Forests.ForestParikhTransitionTargets
public import LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikhStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParikhTransition.Proof
open FirstOrder Language RankedParse ProfileAutomatonEncoding ForestParseRepresentationCotree
open ForestParseRepresentationStates ForestParseRepresentationCounts CotreeMachineParikh

theorem stateSetTransport : Targets.StateSetTransport := by
  intro M k e C
  apply Finset.ext
  intro j
  change j ∈ stateSet (numberMachine M e).toMachine C ↔ j ∈ (stateSet M C).map e.toEmbedding
  constructor
  · intro hj
    have hq : e.symm j ∈ stateSet M C :=
      (CotreeMachineParikh.Proof.stateEncoding M e C (e.symm j)).mpr (by exact (e.apply_symm_apply j).symm ▸ hj)
    exact Finset.mem_map.mpr ⟨e.symm j, hq, e.apply_symm_apply j⟩
  · intro hj
    obtain ⟨q, hq, he⟩ := Finset.mem_map.mp hj
    have h := (CotreeMachineParikh.Proof.stateEncoding M e C q).mp hq
    change e q = j at he
    exact he ▸ h

theorem childCountTransport : Targets.ChildCountTransport := by
  intro M k e n c B
  classical
  unfold childCounts
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have ht := stateSetTransport M k e (c i)
  constructor
  · intro h
    exact e.finsetCongr.apply_eq_iff_eq_symm_apply.mp (ht.symm.trans h)
  · intro h
    exact ht.trans ((congrArg e.finsetCongr h).trans (e.finsetCongr.apply_symm_apply B))

theorem numberedParikhExact : Targets.NumberedParikhExact := by
  intro M k e o n c q
  have hc : childCounts (numberMachine M e).toMachine c =
      (childCounts M c) ∘ e.finsetCongr.symm :=
    funext (fun B => childCountTransport M k e (n + 2) c B)
  have hf := CotreeMachineParikh.StatementChecks.numberedTransitionExact M k e o n c q
  rw [hc] at hf
  exact hf.trans Formula.realize_relabel.symm

theorem semanticCompleteness : Targets.SemanticCompleteness := by
  intro M
  classical
  refine ⟨Fintype.card M.State, Fintype.equivFin M.State, ?_⟩
  exact numberedParikhExact M _ _

end LogicLineages.ModelsAlgebra.Forests.ForestParikhTransition.Proof
