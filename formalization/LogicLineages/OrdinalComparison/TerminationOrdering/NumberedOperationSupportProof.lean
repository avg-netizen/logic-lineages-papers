module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOperationSupportTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOperationSupportProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedRenamingSupport

theorem actualApplyArgumentsSupport : NumberedOperationSupportTargets.ActualApplyArgumentsSupport := by
  intro Symbol arity Gamma P types tau q args
  induction types with
  | nil => cases args; exact ⟨fun h => ⟨h,trivial⟩,fun h => h.1⟩
  | cons sigma types ih => cases args with
    | cons a rest =>
      simp only [applyArguments,ih,supports,supportsArguments]
      exact and_assoc

theorem actualSelfArgumentsSupport : NumberedOperationSupportTargets.ActualSelfArgumentsSupport := by
  intro Symbol arity Gamma P label f base extraTypes extras types hb he
  induction types with
  | nil => trivial
  | cons tau types ih => exact ⟨⟨hb,he⟩,ih⟩

theorem appendSupport {Symbol : Type} {arity : Symbol → Nat} {Gamma xs ys : List Ty}
    (P : VariablePredicate Gamma) (base : AuxArguments Symbol arity Gamma xs) (extras : AuxArguments Symbol arity Gamma ys) :
    supportsArguments P (appendArguments base extras) ↔ supportsArguments P base ∧ supportsArguments P extras := by
  induction xs with
  | nil => cases base; simp [appendArguments,supportsArguments]
  | cons tau xs ih => cases base with
    | cons q rest =>
      simp only [appendArguments,supportsArguments,ih]
      exact and_assoc.symm

theorem actualOpenNumberedSupport : NumberedOperationSupportTargets.ActualOpenNumberedSupport := by
  intro Symbol arity Gamma P label f sigma tau base extraTypes extras
  simp only [openNumbered,supports,appendSupport]
  rw [NumberedSupportPullbackProof.actualArgumentSupportPullback,
    NumberedSupportPullbackProof.actualArgumentSupportPullback]
  simp only [Renaming.weaken,liftPredicate,supportsArguments,supports,and_true]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOperationSupportProof
