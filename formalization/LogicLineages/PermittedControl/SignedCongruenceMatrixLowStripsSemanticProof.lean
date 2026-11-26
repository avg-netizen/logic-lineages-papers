module
public import LogicLineages.PermittedControl.SignedCongruenceMatrixLowStripsTargets
import LogicLineages.PermittedControl.SignedCongruenceMatrixSliceStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrixLowStrips
open SignedCongruenceMatrix (actualRows)
open SignedCongruenceMatrixSlice (sliceRows)
open StatementChecks (fixed_signedCongruenceMatrixSliceResidualRanks fixed_actualSignedCongruenceMatrixSlice)

theorem residualRanks : ResidualRanks := by
  intro f rank bound rows residual branch member hit
  change branch ∈ (List.range bound).map (fun a => (a,sliceRows f rank a rows)) at member
  obtain ⟨a,_,equal⟩ := List.mem_map.mp member
  subst branch
  exact fixed_signedCongruenceMatrixSliceResidualRanks f rank a rows residual hit

theorem guardedLowMatrix : GuardedLowMatrix := by
  intro f ρ prior rank bound rows positive
  constructor
  · rintro ⟨a,below,guard,original⟩
    let current := Function.update ρ rank a
    have agree : current rank = a := by simp [current]
    obtain ⟨residual,hits,truth⟩ :=
      (fixed_actualSignedCongruenceMatrixSlice f current rank a rows agree positive).mp original
    refine ⟨(a,sliceRows f rank a rows),residual,?_,hits,guard,truth⟩
    exact List.mem_map.mpr ⟨a,List.mem_range.mpr below,rfl⟩
  · rintro ⟨branch,residual,member,hits,guard,truth⟩
    change branch ∈ (List.range bound).map (fun a => (a,sliceRows f rank a rows)) at member
    obtain ⟨a,below,equal⟩ := List.mem_map.mp member
    subst branch
    let current := Function.update ρ rank a
    have agree : current rank = a := by simp [current]
    have original := (fixed_actualSignedCongruenceMatrixSlice f current rank a rows agree positive).mpr
      ⟨residual,hits,truth⟩
    exact ⟨a,List.mem_range.mp below,guard,original⟩

end LogicLineages.PermittedControl.SignedCongruenceMatrixLowStrips
