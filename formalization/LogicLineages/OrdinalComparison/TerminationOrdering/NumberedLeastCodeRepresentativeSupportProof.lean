module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentativeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentativeSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedLeastCodeRepresentative

theorem typeNumberInjective : Function.Injective typeNumber := by
  intro tau
  induction tau with
  | ground => intro other h; cases other <;> simp_all [typeNumber] <;> omega
  | arrow sigma tau ihs iht =>
    intro other h
    cases other <;> simp_all [typeNumber,Nat.pair_eq_pair]
    exact ⟨ihs rfl,iht rfl⟩

theorem typesNumberInjective : Function.Injective typesNumber := by
  intro types
  induction types with
  | nil => intro other h; cases other <;> simp_all [typesNumber] <;> omega
  | cons tau rest ih =>
    intro other h
    cases other with
    | nil => simp [typesNumber] at h
    | cons sigma tail =>
      have hp : typeNumber tau=typeNumber sigma ∧ typesNumber rest=typesNumber tail := by simpa [typesNumber,Nat.pair_eq_pair] using h
      exact congrArg₂ List.cons (typeNumberInjective hp.1) (ih hp.2)

theorem headNumberInjective {n : Nat} : Function.Injective (@headNumber n) := by
  intro f g h
  cases f <;> cases g <;> simp_all [headNumber,Nat.pair_eq_pair,typeNumberInjective.eq_iff,Fin.val_inj]

theorem structuralNumberInjective : NumberedLeastCodeRepresentativeTargets.ActualStructuralNumberInjective := by
  intro n c
  induction c <;> intro other h <;> cases other <;>
    simp_all [codeNumber,Nat.pair_eq_pair,typeNumberInjective.eq_iff,typesNumberInjective.eq_iff,headNumberInjective.eq_iff]
  all_goals aesop

theorem packedNumberInjective : NumberedLeastCodeRepresentativeTargets.ActualPackedNumberInjective := by
  intro n arity Gamma q r h
  have hp := Nat.pair_eq_pair.mp h
  have ht := typeNumberInjective hp.1
  have hc := structuralNumberInjective n hp.2
  exact NumberedAuxiliaryCodingProof.packedCodeInjective (Fin n) arity Gamma (Prod.ext ht hc)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentativeSupportProof
