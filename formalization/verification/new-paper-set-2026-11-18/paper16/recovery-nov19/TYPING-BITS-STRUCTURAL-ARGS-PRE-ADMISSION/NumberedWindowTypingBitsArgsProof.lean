import LogicLineages.PersistentMarking.NumberedWindowTypingBitsTargets
import LogicLineages.PersistentMarking.NumberedWindowApplicationDomainProof

namespace LogicLineages.PersistentMarking.NumberedWindowTypingBitsArgsProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowTypingBits
open NumberedWindowApplicationDomainProof (annotation)

theorem baseShape {C : Spine.BoundContext} {qs : NArgs} {types : List Ty}
    (h : BaseTyped C qs types) : annotationList qs = types ∧ ExtrasTyped C qs := by
  induction qs generalizing types with
  | nil =>
    cases h
    exact ⟨rfl,.nil⟩
  | cons Q qs ih =>
    cases h with
    | cons hq hs =>
      obtain ⟨e,he⟩ := ih hs
      refine ⟨?_,.cons hq he⟩
      change Q.type :: annotationList qs = _
      rw [annotation hq,e]

theorem extrasBase {C : Spine.BoundContext} {qs : NArgs} (h : ExtrasTyped C qs) :
    BaseTyped C qs (annotationList qs) := by
  induction qs with
  | nil => exact .nil
  | cons Q qs ih =>
    cases h with
    | cons hq hs => exact .cons ((annotation hq).symm ▸ hq) (ih hs)

end LogicLineages.PersistentMarking.NumberedWindowTypingBitsArgsProof
