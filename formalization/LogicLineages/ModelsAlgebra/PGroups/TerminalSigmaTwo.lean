module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalSigmaTwoTargets
public import LogicLineages.ModelsAlgebra.PGroups.Relativized
public import LogicLineages.ModelsAlgebra.PGroups.CoherentTerminal
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth
universe u v

private theorem empty_map {A B : Type u} (f : A → B) :
    (fun j : Fin 0 => f (Fin.elim0 j)) = (Fin.elim0 : Fin 0 → B) := by
  funext j
  exact Fin.elim0 j

theorem terminal_sigma_two_transfer : Targets.groupTerminalSigmaTwoTransfer.{u,v} := by
  intro G _ p δ K T hH hKT hBF φ hφ ht
  let H := (transfiniteFiltration p δ : AddSubgroup G)
  let QH := (transfiniteFiltration p δ : AddSubgroup (G ⧸ T))
  obtain ⟨e,_⟩ := coherent_terminal_quotient G p δ K T hH hKT
  have hQ : φ.Realize (Fin.elim0 : Fin 0 → QH) := by
    apply (relativized_subgroup_agreement (G ⧸ T) QH 0 φ Fin.elim0).mp
    simpa only [empty_map] using ht
  have hc : BackAndForth (2 : Ordinal.{v}) (Fin.elim0 : Fin 0 → K) (Fin.elim0 : Fin 0 → QH) := by
    simpa only [empty_map] using comparison_isomorphism (2 : Ordinal.{v}) K QH e 0 Fin.elim0
  have hK := (truth_transfer (2 : Ordinal.{v}) K QH 0 Fin.elim0 Fin.elim0 hc).2 φ hφ hQ
  have hG := (truth_transfer (2 : Ordinal.{v}) H K 0 Fin.elim0 Fin.elim0 hBF).2 φ hφ hK
  simpa only [empty_map] using (relativized_subgroup_agreement G H 0 φ Fin.elim0).mpr hG

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
