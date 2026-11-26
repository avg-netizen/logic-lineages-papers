module
public import LogicLineages.PermittedControl.ActualFiniteFullValueGuardsTargets
import LogicLineages.PermittedControl.ActualFullLabelPairGuardsProof
import LogicLineages.PermittedControl.ActualPreparedSlotAppendReadProof
import LogicLineages.PermittedControl.ActualPreparedSlotAppendProof
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaShapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteFullValueGuards
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open ActualFullLabelPairGuards (Pair Answer Ready PaidUpdate ActualOutcome packet exactFullLabelPairGuard)
open ActualPreparedSlotAppend (append merge view shiftName exactPreparedAppend exactAppendedReads)
open OriginalMatrixLinearRowFormula (safeTruth)

private theorem viewUpdate (d : Nat) (ν : Nat → Nat) (z : Nat) :
    view d (Function.update ν 0 z) = Function.update (view d ν) 0 z := by
  funext n
  cases n with
  | zero => simp [view,shiftName]
  | succ j =>
      have h₁ : d+(j+1) ≠ 0 := by omega
      have h₂ : j+1 ≠ 0 := Nat.succ_ne_zero j
      simp only [view,shiftName,Function.update_of_ne h₁,Function.update_of_ne h₂]

theorem exactOrderedGuardFold : ExactOrderedGuardFold := by
  intro f B hf ρ top ps
  induction ps with
  | nil =>
      intro as len _
      have empty : as = [] := by
        cases as with
        | nil => rfl
        | cons a tail => cases len
      subst as
      refine ⟨safeTruth [],⟨fun _ => 0,?_⟩,?_⟩
      · intro j hj
        exact False.elim (Nat.not_lt_zero j hj)
      · intro ν _ z _
        exact ⟨fun _ => .nil,fun _ => True.intro⟩
  | cons p ps ih =>
      intro as length ready
      cases as with
      | nil => cases length
      | cons a as =>
          let left := packet top p a
          let right := compile top ps as
          have oldLen : as.length = ps.length := Nat.succ.inj length
          have expected := exactFullLabelPairGuard f B hf ρ top p (ready p List.mem_cons_self) a
          have remaining := ih as oldLen (fun q hq => ready q (List.mem_cons_of_mem _ hq))
          have combined := exactPreparedAppend left right expected.1 remaining.1
          have tieAppend := exactAppendedReads f ρ top left.1 right.1
          obtain ⟨ν₁,tie₁⟩ := expected.2.1
          obtain ⟨ν₂,tie₂⟩ := remaining.2.1
          refine ⟨combined.1,⟨merge left.1.length ν₁ ν₂,tieAppend.2.2.2 ν₁ ν₂ tie₁ tie₂⟩,?_⟩
          intro ν tied z paid
          obtain ⟨lfit,rfit⟩ := (tieAppend.2.2.1 ν).mp tied
          have guardL := expected.2.2 ν lfit z (paid p List.mem_cons_self)
          have guardR := remaining.2.2 (view left.1.length ν) rfit z
            (fun q hq => paid q (List.mem_cons_of_mem _ hq))
          have actual := combined.2.1 (Function.update ν 0 z)
          rw [viewUpdate] at actual
          refine actual.trans ((and_congr guardL guardR).trans ?_)
          constructor
          · rintro ⟨head,tail⟩
            exact .cons head tail
          · intro h
            cases h with
            | cons head tail => exact ⟨head,tail⟩

end LogicLineages.PermittedControl.ActualFiniteFullValueGuards
