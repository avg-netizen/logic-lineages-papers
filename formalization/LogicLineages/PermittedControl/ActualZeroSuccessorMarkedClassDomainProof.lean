module
public import LogicLineages.PermittedControl.ActualZeroSuccessorMarkedClassTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroSuccessorMarkedClass
open MixedSameRankResidue (WeightedOperand)
open ActualFullValueLabels (labels activeLabel)

theorem exactDecorationDomain : ExactDecorationDomain := by
  intro ts
  induction ts with
  | nil =>
      intro bs
      cases bs with
      | nil =>
          refine ⟨by simp [decorate,labels],?_⟩
          intro ms h
          have same : ms = [] := (Option.some.inj h).symm
          simp [same]
      | cons b bs =>
          refine ⟨by simp [decorate,labels],?_⟩
          intro ms h
          cases h
  | cons t ts ih =>
      intro bs
      cases hl : activeLabel t with
      | none =>
          have head : decorate (t::ts) bs = (decorate ts bs).map (List.cons (t,false)) := by
            cases bs <;> simp [decorate,hl]
          refine ⟨?_,?_⟩
          · rw [head]
            simpa [labels,hl] using (ih bs).1
          · intro ms h
            rw [head] at h
            cases ht : decorate ts bs with
            | none => simp [ht] at h
            | some tail =>
                have eq : (t,false) :: tail = ms := Option.some.inj (by simpa [ht] using h)
                rw [← eq,List.map_cons,(ih bs).2 tail ht]
      | some lab =>
          cases bs with
          | nil =>
              refine ⟨by simp [decorate,labels,hl],?_⟩
              intro ms h
              have no : decorate (t::ts) [] = none := by simp [decorate,hl]
              rw [no] at h
              cases h
          | cons b bs =>
              have head : decorate (t::ts) (b::bs) = (decorate ts bs).map (List.cons (t,b)) := by
                simp [decorate,hl]
              refine ⟨?_,?_⟩
              · rw [head]
                simpa [labels,hl] using (ih bs).1
              · intro ms h
                rw [head] at h
                cases ht : decorate ts bs with
                | none => simp [ht] at h
                | some tail =>
                    have eq : (t,b) :: tail = ms := Option.some.inj (by simpa [ht] using h)
                    rw [← eq,List.map_cons,(ih bs).2 tail ht]

end LogicLineages.PermittedControl.ActualZeroSuccessorMarkedClass
