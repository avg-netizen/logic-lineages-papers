module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.ComparisonProof
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.Targets

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.Proof
open ComparisonProof

theorem booleanGuardsCorrect : Targets.BooleanGuardsCorrect := by
  intro tie desired value hd
  rw [guardAt_makeGuards tie desired hd]
  constructor
  · rintro ⟨sign,hmem,hatom⟩
    have hs := (signAtom_iff sign value).mp hatom
    have h := (signFormula_mem tie desired sign).mp hmem
    simpa only [hs] using h.2
  · intro h
    exact ⟨orderInt value 0,(signFormula_mem tie desired _).mpr
      ⟨orderInt_bound value 0,h⟩,(signAtom_iff _ _).mpr rfl⟩

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.Proof
