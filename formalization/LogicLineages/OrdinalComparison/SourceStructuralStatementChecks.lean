module
public import LogicLineages.OrdinalComparison.SourceStructural
public import LogicLineages.OrdinalComparison.SourceTypesProofs
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.CheckedStructural

theorem literal_ground_arity_level : Targets.GroundArityLevel := groundArityLevel

theorem literal_type_subexpression_closure : Targets.TypeSubexpressionClosure :=
  typeSubexpressionClosure

theorem exact_renaming_identity : Targets.IdentityRenaming := identityRenaming

theorem exact_renaming_composition : Targets.ComposedRenaming := composedRenaming

theorem exact_substitution_identity : Targets.IdentitySubstitution := identitySubstitution

end LogicLineages.OrdinalComparison.Source.CheckedStructural

#audit_namespace LogicLineages.OrdinalComparison.Source
