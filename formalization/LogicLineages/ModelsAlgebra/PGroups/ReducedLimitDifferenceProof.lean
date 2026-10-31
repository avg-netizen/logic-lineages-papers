module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLimitDifferenceTargets
public import LogicLineages.ModelsAlgebra.PGroups.ReducedPrueferComparisonProof
public import LogicLineages.ModelsAlgebra.PGroups.ReducedPrueferReverseProof
public import LogicLineages.ModelsAlgebra.PGroups.Infinitary
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary

theorem reduced_limit_no_difference : Targets.reducedLimitNoDifference := by
  intro G _ _ p _ hG hr γ _ hl d hc hs
  let Q := G×PrueferModel p
  letI : Countable Q := (pruefer_enlargement_data G p hG).1
  have hf := reduced_pruefer_comparison G p hG hr γ hl 0 Fin.elim0
  have hb := reduced_pruefer_reverse G p hG hr γ hl 0 Fin.elim0
  have hn : (fun i:Fin 0=>(Fin.elim0 i,(0:PrueferModel p)))=(Fin.elim0:Fin 0→Q) := by
    funext i; exact Fin.elim0 i
  rw [hn] at hf hb
  have hσ := (truth_transfer (2*γ) Q G 0 Fin.elim0 Fin.elim0 hb).2 d.sigmaPart hc.1 hs.1.1
  have hπ := (truth_transfer (2*γ) G Q 0 Fin.elim0 Fin.elim0 hf).1 d.piPart hc.2 hs.1.2
  exact reduced_pruefer_enlargement_noniso G p hr (hs.2 Q ⟨hσ,hπ⟩)

theorem reduced_limit_no_raw_difference : Targets.reducedLimitNoRawDifference := by
  intro G _ _ p _ hG hr γ hγ hl d hc hs
  exact reduced_limit_no_difference G p hG hr γ hγ hl d hc (raw_difference_scott_restriction G d hs)
end LogicLineages.ModelsAlgebra.PGroups
