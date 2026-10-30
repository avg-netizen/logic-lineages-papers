module

public import LogicLineages.ModelsAlgebra.PGroups.BackForthCore
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.BackForthCoreStatementChecks

theorem fixed_groupTermHomEvaluation : Targets.groupTermHomEvaluation :=
  GroupBackAndForth.term_hom_evaluation
theorem fixed_groupEmbeddingAtomicAgreement : Targets.groupEmbeddingAtomicAgreement :=
  GroupBackAndForth.embedding_atomic_agreement
theorem fixed_groupBackForthReflexive : Targets.groupBackForthReflexive :=
  GroupBackAndForth.comparison_reflexive
theorem fixed_groupBackForthTransitive : Targets.groupBackForthTransitive :=
  GroupBackAndForth.comparison_transitive
theorem fixed_groupBackForthIsomorphism : Targets.groupBackForthIsomorphism :=
  GroupBackAndForth.comparison_isomorphism

end LogicLineages.ModelsAlgebra.PGroups.BackForthCoreStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
