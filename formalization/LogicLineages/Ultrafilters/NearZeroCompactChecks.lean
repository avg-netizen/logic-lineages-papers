module

public import LogicLineages.Ultrafilters.NearZeroCompactProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.Ultrafilters.StatementChecks

theorem fixed_near_zero_compact_semigroup : Targets.NearZeroCompactSemigroup := nearZero_compactSemigroup

end LogicLineages.Ultrafilters.StatementChecks

#audit_namespace LogicLineages.Ultrafilters
