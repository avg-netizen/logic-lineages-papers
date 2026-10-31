module
public import LogicLineages.ModelsAlgebra.PGroups.StableTailCategoricityTargets
public import LogicLineages.ModelsAlgebra.PGroups.StableStageProof
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryUlmClassificationProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem stable_tail_categoricity : Targets.stableTailCategoricity := by
  intro G H _ _ _ _ p _ hG hH α hsG hsH hu hd
  have g := primary_stable_stage G p hG α hsG
  have h := primary_stable_stage H p hH α hsH
  apply (countable_primary_ulm_classification G H p hG hH).mpr
  constructor
  · intro β
    rcases lt_or_ge β α with hb | hb
    · exact hu β hb
    · exact (g.2.2 β hb).2.trans (h.2.2 β hb).2.symm
  · change Module.rank (ZMod p) (pSocle p (divisiblePart G)) =
      Module.rank (ZMod p) (pSocle p (divisiblePart H))
    rw [g.2.1,h.2.1] at hd
    exact hd
end LogicLineages.ModelsAlgebra.PGroups
