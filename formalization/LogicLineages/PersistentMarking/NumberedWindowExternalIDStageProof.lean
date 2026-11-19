import LogicLineages.PersistentMarking.NumberedWindowExternalIDTagProof

namespace LogicLineages.PersistentMarking.NumberedWindowExternalIDStageProof
open NumberedWindowExternalIDOperators NumberedWindowExternalIDStages
open NumberedWindowExternalIDOperatorTargets NumberedWindowExternalIDTagProof
universe u

theorem stageEq {ι : Type u} (r : ι → ι → Prop) (wf : WellFounded r)
    (F : Operator) (a : ι) :
    stage r wf F a = F (fun n => ∃ b, ∃ _ : r b a, stage r wf F b n) := by
  exact WellFounded.fix_eq wf _ a

private theorem stageFiber {ι : Type u} (r : ι → ι → Prop) (wf : WellFounded r)
    (F A : Operator) (tag : Nat → Nat)
    (proj : ∀ P n, F P (tag n) ↔ A (fun d => P (tag d)) n) (a : ι) :
    ∀ n, stage r wf F a (tag n) ↔ stage r wf A a n := by
  refine wf.induction (C := fun i => ∀ n,
    stage r wf F i (tag n) ↔ stage r wf A i n) a ?_
  intro a ih n
  rw [stageEq r wf F a,stageEq r wf A a,proj]
  have hPrior :
      (fun d => ∃ b, ∃ _ : r b a, stage r wf F b (tag d)) =
        (fun d => ∃ b, ∃ _ : r b a, stage r wf A b d) := by
    funext d
    apply propext
    constructor
    · rintro ⟨b,hb,h⟩
      exact ⟨b,hb,(ih b hb d).mp h⟩
    · rintro ⟨b,hb,h⟩
      exact ⟨b,hb,(ih b hb d).mpr h⟩
  rw [hPrior]

theorem actual : ActualStageTagProjection.{u} := by
  intro ι r wf S K a n
  exact ⟨stageFiber r wf _ _ _ (scalarAt S K) a n,
    stageFiber r wf _ _ _ (multisetAt S K) a n⟩

theorem starts : StageStartsAtOperatorEmpty.{u} := by
  intro ι r wf F a noEarlier n
  rw [stageEq r wf F a]
  have hEmpty : (fun d => ∃ b, ∃ _ : r b a, stage r wf F b d) = (fun _ : Nat => False) := by
    funext d
    apply propext
    constructor
    · rintro ⟨b,hb,_⟩
      exact noEarlier b hb
    · intro h
      exact False.elim h
  rw [hEmpty]

end LogicLineages.PersistentMarking.NumberedWindowExternalIDStageProof
