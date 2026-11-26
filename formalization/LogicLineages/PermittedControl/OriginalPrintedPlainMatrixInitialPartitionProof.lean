module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInitialPartitionTargets
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInitialPartitionFundingProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixSupportLowProof
import LogicLineages.PermittedControl.OriginalMatrixActualHighPacketBranchProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesCoverageProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInitialPartition
open OriginalPrintedPlainMatrixSupportLow (exactOriginalSupportLowAt)
open OriginalMatrixActualHighPacket (exactOriginalPaidBranchPacket)
open ActualFiniteOrderBranches (actualPattern exactActualBranchCoverage)

theorem exactInitialPartition : ExactInitialPartition := by
  intro f B hf θ known gates p plain prior positive
  constructor
  · rintro ⟨pr,source⟩
    rcases (exactThreeStrata B θ known gates p).1 with small | large | empty
    · obtain ⟨name,mem,below⟩ := small
      have low := exactOriginalSupportLowAt f B θ known gates p plain prior positive name mem below
      exact Or.inl ⟨name,mem,below,low.mp ⟨pr,source⟩⟩
    · let branch := actualPattern θ (names known gates p)
      obtain ⟨mem,checked⟩ := exactActualBranchCoverage θ (names known gates p)
      have paid := exactActualRankZeroFunding B θ known gates p large branch mem checked
      have high := exactOriginalPaidBranchPacket f B hf θ known gates p plain prior positive branch mem paid
      obtain ⟨guarded,pr',packet⟩ := high.mp ⟨checked,pr,source⟩
      exact Or.inr (Or.inl ⟨large,branch,mem,guarded,pr',packet⟩)
    · exact Or.inr (Or.inr ⟨empty,pr,source⟩)
  · rintro (⟨name,mem,below,low⟩ | ⟨large,branch,mem,checked,pr,packet⟩ | ⟨_,pr,source⟩)
    · exact (exactOriginalSupportLowAt f B θ known gates p plain prior positive name mem below).mpr low
    · have paid := exactActualRankZeroFunding B θ known gates p large branch mem checked
      have high := exactOriginalPaidBranchPacket f B hf θ known gates p plain prior positive branch mem paid
      exact (high.mpr ⟨checked,pr,packet⟩).2
    · exact ⟨pr,source⟩

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInitialPartition
