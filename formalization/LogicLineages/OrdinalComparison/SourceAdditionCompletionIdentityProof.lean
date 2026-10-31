module
public import LogicLineages.OrdinalComparison.SourceAdditionCompletionArithmeticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAdditionCompletion.Proof
open LogicLineages.ComputabilityKnowledge
open WWOrdinalTermSemantics WWOrdinalTermSemanticsProof
open SourceSortCompletion

def identityZeroVector (Γ : List Ty) : OrdinalVector Γ 0 := fun _ =>
  .collapse .one (.add (.add (.add .one .one) .one) .one)

theorem identity_zero_assignment (Γ : List Ty) :
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy
      (.app (identity (Γ := Γ)) .zeroC) = some (identityZeroVector Γ) := by
  apply congrArg some
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp only [Ty.level, List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  simp only [AdmissibleAssignment.application, AdmissibleAssignment.box,
    Ty.level, Fin.val_zero]
  rw [ordinalBoxPositive]
  simp only [show ¬ (1 ≤ 0) by omega, dite_false]
  simp [Fin.cases_zero, identityZeroVector, AdmissibleAssignment.boxTail,
    Ty.level, ordinalVectorAt, ordinalPartialSize, ordinalHeadFree, ordinalHeadOccurs,
    ordinalHeadComponentOccurs, ordinalHeadClosure, ordinalHeadClosureComponent,
    substitute, AdmissibleAssignment.repeated, OrdinalSyntax.defaultPolicy,
    OrdinalSyntax.defaultShape, OrdinalSyntax.leftShape, AdmissibleSum.expand]
  all_goals first | rfl | exact ⟨rfl, rfl⟩


end LogicLineages.OrdinalComparison.Source.SourceAdditionCompletion.Proof
