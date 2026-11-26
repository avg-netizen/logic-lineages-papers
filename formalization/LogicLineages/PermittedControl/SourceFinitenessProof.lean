module
public import LogicLineages.PermittedControl.SourceScalarCalibrationProof
public import LogicLineages.PermittedControl.SelectedSourceDomainProof
public import LogicLineages.PermittedControl.LiteralFinitenessStatementChecks
public import LogicLineages.PermittedControl.LiteralCovarianceDeltaProof
public import LogicLineages.PermittedControl.NakedDeltaProgramStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SourceFinitenessProof
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax SelectedSourceDomain
open StandardControlCurrent

 theorem sourcePartial : SourceFinitenessTargets.SourcePartial := by
  intro f B hf Γ σ p hp i t ht
  obtain ⟨v,hv,huniq⟩ := SelectedSourceDomainProof.uniquePartial f Γ σ p i t ht
  refine ⟨v,⟨hv.1,?_,hv.2⟩,?_⟩
  · rw [PolicyPartialStatementChecks.full.2.1 p Γ σ i t,hv.1]
    rfl
  · intro w hw
    exact huniq w ⟨hw.1,hw.2.2⟩

 theorem sourceDelta : SourceFinitenessTargets.SourceDelta := by
  intro f B hf Γ σ p hp m h hh
  obtain ⟨v,hv,huniq⟩ := (SelectedSourceDomainProof.uniqueVectorOperations f Γ σ p m h hh).2.1
  refine ⟨v,⟨hv,?_⟩,?_⟩
  · rw [NakedDeltaSyntaxProof.literal p Γ σ m h,hv]
    rfl
  · intro w hw
    exact huniq w hw.1

 theorem sourceAbstraction : SourceFinitenessTargets.SourceAbstraction := by
  intro f B hf Γ σ p hp m h hh
  obtain ⟨v,hv,huniq⟩ := (SelectedSourceDomainProof.uniqueVectorOperations f Γ σ p m h hh).2.2
  refine ⟨v,⟨hv,?_⟩,?_⟩
  · rw [PolicyAbstractionStatementChecks.full.2.2.1 p Γ σ m h,hv]
    rfl
  · intro w hw
    exact huniq w hw.1

 theorem fullSourceFiniteness : SourceFinitenessTargets.FullSourceFiniteness :=
  ⟨SourceScalarCalibrationProof.scalarCalibration,sourcePartial,sourceDelta,sourceAbstraction,
    PolicyPartialStatementChecks.full.2.2,NakedDeltaProgramsProof.programs,
    PolicyAbstractionStatementChecks.full.2.2.2,LiteralCovarianceProof.fullLiteralCovariance,
    SelectedSourceDomainProof.deltaHighRetention⟩

end LogicLineages.PermittedControl.SourceFinitenessProof
