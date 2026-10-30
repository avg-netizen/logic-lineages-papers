module
public import LogicLineages.ModelsAlgebra.PGroups.RawGuardTargets
public import LogicLineages.ModelsAlgebra.PGroups.RawConjunction
public import LogicLineages.ModelsAlgebra.PGroups.RawGroupAxioms
public import LogicLineages.ModelsAlgebra.PGroups.PiConjunction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u

theorem raw_guard_pi_realization : Targets.groupRawGuardPiRealization.{u} := by
  intro G R φ
  unfold guardPi
  rw [raw_pi_conjunction 0 abelianGroupAxioms φ G R Fin.elim0,
    raw_axioms_realization G R]

theorem raw_guard_difference_realization : Targets.groupRawGuardDifferenceRealization.{u} := by
  intro G R d
  change (d.sigmaPart.RawRealize R Fin.elim0 ∧ (guardPi d.piPart).RawRealize R Fin.elim0) ↔ _
  rw [raw_guard_pi_realization G R d.piPart]
  exact ⟨fun h => ⟨h.2.1,h.1,h.2.2⟩, fun h => ⟨h.2.1,h.1,h.2.2⟩⟩

theorem raw_guard_pi_complexity : Targets.groupRawGuardPiComplexity := by
  intro α hα φ hφ
  have hpos : α ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hα)
  exact pi_conjunction_complexity α hpos 0 abelianGroupAxioms φ
    (positive_complexity_monotone .pi 1 α 0 abelianGroupAxioms one_ne_zero hα raw_axioms_complexity) hφ

theorem raw_guard_difference_complexity : Targets.groupRawGuardDifferenceComplexity := by
  intro α hα d hd
  exact ⟨hd.1, raw_guard_pi_complexity α hα d.piPart hd.2⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
