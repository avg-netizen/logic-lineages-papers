module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixDecreasingLowTargets
import LogicLineages.PermittedControl.OriginalMatrixLowDimensionProof
import LogicLineages.PermittedControl.OriginalMatrixLowDimensionCodeProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInitialPartitionProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixDecreasingLow
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open OriginalMatrixActualHighPacket (originalFamilyCeiling)
open OriginalMatrixLowDimension (exactLowFamilyDimension)
open OriginalMatrixLowDimensionCode (exactCodedLowFamilyDimension)
open OriginalPrintedPlainMatrixInitialPartition (exactInitialPartition)

theorem exactOriginalDecreasingLowCase : ExactOriginalDecreasingLowCase := by
  intro f B θ known gates p prior positive
  constructor
  · rintro ⟨name,used,below,branch,residual,member,digit,hits,pr,suffix,actual,accepted⟩
    have smaller := exactLowFamilyDimension f name (originalFamilyCeiling B known gates p)
      (matrix known gates p) used branch member residual hits
    exact ⟨name,used,below,branch,residual,member,digit,hits,smaller.1,smaller.2,pr,suffix,actual,accepted⟩
  · rintro ⟨name,used,below,branch,residual,member,digit,hits,_,_,pr,suffix,actual,accepted⟩
    exact ⟨name,used,below,branch,residual,member,digit,hits,pr,suffix,actual,accepted⟩

theorem exactOriginalCodedLowChildren : ExactOriginalCodedLowChildren := by
  intro f B known gates p name used branch member residual hits
  exact (exactCodedLowFamilyDimension.2 f name (originalFamilyCeiling B known gates p)
    (matrix known gates p) used branch member residual hits).2

theorem exactOriginalDecreasingInitialPartition : ExactOriginalDecreasingInitialPartition := by
  intro f B hf θ known gates p plain prior positive
  exact (exactInitialPartition f B hf θ known gates p plain prior positive).trans
    (or_congr (exactOriginalDecreasingLowCase f B θ known gates p prior positive) Iff.rfl)

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixDecreasingLow
