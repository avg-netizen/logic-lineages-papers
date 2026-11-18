module
public import LogicLineages.StandardControlCurrent.PolicyOneNameProgramsProof
public import LogicLineages.StandardControlCurrent.PolicyOneNameDomainProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyOneName.Proof
open OrdinalComparison

theorem source_value : PolicyOneNameTargets.NumericValue := by
  intro p source x hx
  obtain ⟨formula,hValid,hCode,hValue⟩ := formula_realization p source
  unfold encodedOneNameSourceBooleanValue
  rw [hCode,OneInputBoolean.source_value formula hValid x]
  exact hValue x hx

theorem numeric_closures (p : Source.AdmissibleSum.Policy) (source : OneNameSourceBooleanExpr) :
    ((encodedOneNameSourceBooleanClosures p (oneNameSourceBooleanCompile source)).1=true ↔
      ∃ x : Nat,0<x ∧ actualOneNameSourceBooleanValue p source x=true) ∧
    ((encodedOneNameSourceBooleanClosures p (oneNameSourceBooleanCompile source)).2=true ↔
      ∀ x : Nat,0<x → actualOneNameSourceBooleanValue p source x=true) := by
  obtain ⟨formula,hValid,hCode,hValue⟩ := formula_realization p source
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

theorem closures : PolicyOneNameTargets.Closures := by
  intro p formula
  have hn := numeric_closures p formula
  constructor
  · rw [hn.1]
    constructor
    · rintro ⟨x,hx,h⟩
      obtain ⟨s,hs⟩ := positive_original x hx
      exact ⟨s,(original_value p formula s x hs).trans h⟩
    · rintro ⟨s,h⟩
      obtain ⟨x,hx,hs⟩ := original_positive s
      exact ⟨x,hx,(original_value p formula s x hs).symm.trans h⟩
  · rw [hn.2]
    constructor
    · intro h s
      obtain ⟨x,hx,hs⟩ := original_positive s
      exact (original_value p formula s x hs).trans (h x hx)
    · intro h x hx
      obtain ⟨s,hs⟩ := positive_original x hx
      exact (original_value p formula s x hs).symm.trans (h s)

theorem full : PolicyOneNameTargets.Full := ⟨programs,source_value,original_value,closures⟩
end LogicLineages.StandardControlCurrent.PolicyOneName.Proof
