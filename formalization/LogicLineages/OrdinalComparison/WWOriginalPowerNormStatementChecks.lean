module
public import LogicLineages.OrdinalComparison.WWOriginalPowerNormProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualOmegaLeftNormBounds : Source.Targets.ActualOmegaLeftNormBounds :=
  Source.OriginalDomain.actualOmegaLeftNormBounds

theorem fixed_actualBaseTwoPowerNormFormula : Source.Targets.ActualBaseTwoPowerNormFormula :=
  Source.OriginalDomain.actualBaseTwoPowerNormFormula

theorem fixed_actualBaseTwoInverseNorm : Source.Targets.ActualBaseTwoInverseNorm :=
  Source.OriginalDomain.actualBaseTwoInverseNorm

theorem fixed_actualBaseTwoForwardNorm : Source.Targets.ActualBaseTwoForwardNorm :=
  Source.OriginalDomain.actualBaseTwoForwardNorm

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
