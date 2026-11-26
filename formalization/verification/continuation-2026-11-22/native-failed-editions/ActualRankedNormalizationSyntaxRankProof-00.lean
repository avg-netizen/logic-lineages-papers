module
public import LogicLineages.PermittedControl.ActualRankedNormalizationSyntaxTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRankedNormalizationSyntax
open PreparedProjection
open MixedSameRankResidue (WeightedOperand orderedReads)
open ActualFullValueLabels (ActualLabel)

theorem exactOriginalSupportRankExtension : ExactOriginalSupportRankExtension := by
  intro ρ top z lower above
  refine ⟨?_,?_,?_⟩
  · intro i j lt
    by_cases jBelow : j < top
    · have iBelow := lt.trans jBelow
      simpa only [extend,if_pos iBelow,if_pos jBelow] using lower i j lt jBelow
    · by_cases iBelow : i < top
      · have prev := above i iBelow
        simp only [extend,if_pos iBelow,if_neg jBelow]
        omega
      · simp only [extend,if_neg iBelow,if_neg jBelow]
        omega
  · simp [extend]
  · intro i bounded
    rcases bounded.eq_or_lt with eq | lt
    · subst i
      simp [extend]
    · simp only [extend,if_pos lt,Function.update_of_ne (ne_of_lt lt)]

theorem exactOriginalRankReadLocality : ExactOriginalRankReadLocality := by
  intro f ρ σ top agreed
  have opRead (op : LowerOperand) (within : op.rank ≤ top) :
      lowerOperandRead f ρ op = lowerOperandRead f σ op ∧
        ∀ v : Nat, LowerOperandActual f ρ op v ↔ LowerOperandActual f σ op v := by
    have tie := agreed op.rank within
    cases op <;> simp only [LowerOperand.rank] at tie <;>
      simp only [lowerOperandRead,LowerOperandActual,tie] <;>
      exact ⟨rfl,fun _ => Iff.rfl⟩
  refine ⟨opRead,?_,?_,?_⟩
  · intro terms all vs
    induction terms generalizing vs with
    | nil => cases vs <;> rfl
    | cons t terms ih =>
        cases vs with
        | nil => rfl
        | cons v vs =>
            obtain ⟨read,value⟩ := opRead t.2 (all t List.mem_cons_self)
            have tail := ih (fun q hq => all q (List.mem_cons_of_mem _ hq)) vs
            simp only [orderedReads,read,value v,tail]
  · intro l within v
    obtain ⟨read,actual⟩ := opRead (.ordinary l.rank l.field) within
    simp only [ActualLabel,read,actual v]
  · intro ops ν
    constructor
    · intro tied j hj
      obtain ⟨lt,h⟩ := tied j hj
      exact ⟨lt,((opRead ops[j] lt.le).2 _).mp h⟩
    · intro tied j hj
      obtain ⟨lt,h⟩ := tied j hj
      exact ⟨lt,((opRead ops[j] lt.le).2 _).mpr h⟩

end LogicLineages.PermittedControl.ActualRankedNormalizationSyntax
