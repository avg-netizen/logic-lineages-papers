module
public import LogicLineages.PermittedControl.MixedRankResidueTargets
import LogicLineages.PermittedControl.MixedRankResidueCodeProof
import LogicLineages.PermittedControl.MixedRankResidueSupportProof
import LogicLineages.PermittedControl.MixedRankResidueSemanticProof

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks

theorem fixed_mixedRankResidueCodeExact : MixedRankResidue.CodeExact :=
  MixedRankResidue.codeExact

theorem fixed_mixedRankResidueSupport : MixedRankResidue.RankSupport :=
  MixedRankResidue.rankSupportExact

theorem fixed_actualMultiRankResidue : MixedRankResidue.ActualMultiRankResidue :=
  MixedRankResidue.actualMultiRankResidue

theorem fixed_fullMixedRankResidue : MixedRankResidue.FullMixedRankResidue :=
  ⟨fixed_mixedRankResidueCodeExact,fixed_mixedRankResidueSupport,fixed_actualMultiRankResidue⟩

#print axioms fixed_mixedRankResidueCodeExact
#print axioms fixed_mixedRankResidueSupport
#print axioms fixed_actualMultiRankResidue
#print axioms fixed_fullMixedRankResidue

end LogicLineages.PermittedControl.StatementChecks
