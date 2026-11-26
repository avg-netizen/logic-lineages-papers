module
public import LogicLineages.PermittedControl.FixedHeadCollapseGraphTargets
import LogicLineages.PermittedControl.FixedHeadCollapseGraphFieldsProof
import LogicLineages.PermittedControl.CountProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section
namespace LogicLineages.PermittedControl.FixedHeadCollapseGraph
open OrdinalComparison

theorem sourceGraph : ExactSourceGraph := by
  intro f B selected p
  let lam := (rawNoteDecode p.1).repr
  let value := headCollapse f lam p.2
  have realized (h : domain p) : read f p = some value := by
    let l : NONote := ⟨rawNoteDecode p.1,h.1⟩
    have decomposition := (count_endpoint_facts f B selected lam p.2
      (normalRepresentationSound l) h.2.1 h.2.2).2.1
    change read f p = some (headCollapse f lam p.2)
    rw [decomposition]
    exact congrArg (fun hit => hit.map (fun v : Nat × Nat => v.1 + v.2))
      ((terminalFields f p).2 h)
  have exactValue (y : Nat) : read f p = some y ↔ domain p ∧ y = value := by
    by_cases h : domain p
    · constructor
      · intro result
        exact ⟨h,(Option.some.inj ((realized h).symm.trans result)).symm⟩
      · rintro ⟨_,rfl⟩
        exact realized h
    · have rejected := (terminalFields f p).1.mpr h
      simp [read,rejected,h]
  refine ⟨exactValue,?_,?_⟩
  · constructor
    · rintro ⟨y,result,_⟩
      exact ((exactValue y).mp result).1
    · intro h
      exact ⟨value,realized h,fun y result => ((exactValue y).mp result).2⟩
  · intro test
    constructor
    · rintro ⟨y,result,negative⟩
      rcases (exactValue y).mp result with ⟨h,rfl⟩
      exact ⟨h,negative⟩
    · rintro ⟨h,negative⟩
      exact ⟨value,realized h,negative⟩

end LogicLineages.PermittedControl.FixedHeadCollapseGraph
