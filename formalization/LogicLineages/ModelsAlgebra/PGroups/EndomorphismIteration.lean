module

public import LogicLineages.ModelsAlgebra.PGroups.EndomorphismIterationTargets

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u

theorem iteration_transition_identity : Targets.groupIterationTransitionIdentity.{u} := by
  intro G _ f i x
  change (f : G → G)^[i - i] x = x
  simp

theorem iteration_transition_composition : Targets.groupIterationTransitionComposition.{u} := by
  intro G _ f i j k hij hjk x
  change (f : G → G)^[k - j] ((f : G → G)^[j - i] x) = (f : G → G)^[k - i] x
  have hn : k - j + (j - i) = k - i := by omega
  rw [← Function.iterate_add_apply, hn]

theorem iteration_transition_injective : Targets.groupIterationTransitionInjective.{u} := by
  intro G _ f hf i j hij
  change Function.Injective ((f : G → G)^[j - i])
  exact hf.iterate _

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
