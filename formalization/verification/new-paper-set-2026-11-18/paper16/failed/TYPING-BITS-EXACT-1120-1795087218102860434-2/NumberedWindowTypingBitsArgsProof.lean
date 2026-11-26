import LogicLineages.PersistentMarking.NumberedWindowTypingBitsTargets
import LogicLineages.PersistentMarking.NumberedWindowApplicationDomainProof

namespace LogicLineages.PersistentMarking.NumberedWindowTypingBitsArgsProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowTypingBits
open NumberedWindowApplicationDomainProof (annotation)

private theorem baseShapeFixed (C : Spine.BoundContext) (qs : NArgs) (types : List Ty)
    (h : BaseTyped C qs types) : annotationList qs = types ∧ ExtrasTyped C qs := by
  cases qs with
  | nil =>
    cases h
    exact ⟨rfl,.nil⟩
  | cons Q qs =>
    cases h with
    | cons hq hs =>
      obtain ⟨e,he⟩ := baseShapeFixed C qs _ hs
      refine ⟨?_,.cons hq he⟩
      change Q.type :: annotationList qs = _
      rw [annotation hq,e]
termination_by structural qs

theorem baseShape {C : Spine.BoundContext} {qs : NArgs} {types : List Ty}
    (h : BaseTyped C qs types) : annotationList qs = types ∧ ExtrasTyped C qs :=
  baseShapeFixed C qs types h

private theorem extrasBaseFixed (C : Spine.BoundContext) (qs : NArgs)
    (h : ExtrasTyped C qs) : BaseTyped C qs (annotationList qs) := by
  cases qs with
  | nil => exact .nil
  | cons Q qs =>
    cases h with
    | cons hq hs => exact .cons ((annotation hq).symm ▸ hq) (extrasBaseFixed C qs hs)
termination_by structural qs

theorem extrasBase {C : Spine.BoundContext} {qs : NArgs} (h : ExtrasTyped C qs) :
    BaseTyped C qs (annotationList qs) :=
  extrasBaseFixed C qs h

end LogicLineages.PersistentMarking.NumberedWindowTypingBitsArgsProof
