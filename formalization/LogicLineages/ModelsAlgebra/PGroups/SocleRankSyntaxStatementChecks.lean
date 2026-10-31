module
public import LogicLineages.ModelsAlgebra.PGroups.SocleRankSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.SocleRankSyntaxStatementChecks
theorem upper : Targets.socleUpperDimension := socle_upper_dimension
theorem infinite : Targets.socleInfiniteDimension := socle_infinite_dimension
theorem countableBound : Targets.countableSocleRankBound := countable_socle_rank_bound
theorem actualEntry : Targets.socleRankEntryExact := socle_rank_entry_exact
end LogicLineages.ModelsAlgebra.PGroups.SocleRankSyntaxStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.SocleRankSyntaxStatementChecks
