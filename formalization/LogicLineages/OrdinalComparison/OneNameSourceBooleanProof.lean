module
public import LogicLineages.OrdinalComparison.OneNameSourceBooleanProgramProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OneNameSourceBoolean

theorem source_value : Targets.ActualOneNameSourceBooleanValue := by
  intro source x hx
  obtain ⟨formula,hValid,hCode,hValue⟩ := formula_realization source
  unfold encodedOneNameSourceBooleanValue
  rw [hCode,OneInputBoolean.source_value formula hValid x]
  exact hValue x hx

theorem closures_correct (source : OneNameSourceBooleanExpr) :
    ((encodedOneNameSourceBooleanClosures (oneNameSourceBooleanCompile source)).1=true ↔
      ∃ x : Nat,0<x ∧ actualOneNameSourceBooleanValue source x=true) ∧
    ((encodedOneNameSourceBooleanClosures (oneNameSourceBooleanCompile source)).2=true ↔
      ∀ x : Nat,0<x → actualOneNameSourceBooleanValue source x=true) := by
  obtain ⟨formula,hValid,hCode,hValue⟩ := formula_realization source
  unfold encodedOneNameSourceBooleanClosures
  rw [hCode]
  have hs := OneInputBoolean.closures_correct formula hValid
  constructor
  · rw [hs.1]
    constructor
    · rintro ⟨x,hx,h⟩
      exact ⟨x,hx,(hValue x hx) ▸ h⟩
    · rintro ⟨x,hx,h⟩
      exact ⟨x,hx,(hValue x hx).symm ▸ h⟩
  · rw [hs.2]
    constructor
    · intro h x hx
      rw [←hValue x hx]
      exact h x hx
    · intro h x hx
      rw [hValue x hx]
      exact h x hx

theorem full : Targets.FullActualOneNameSourceBooleanClosures := ⟨programs,source_value,closures_correct⟩

end LogicLineages.OrdinalComparison.OneNameSourceBoolean
