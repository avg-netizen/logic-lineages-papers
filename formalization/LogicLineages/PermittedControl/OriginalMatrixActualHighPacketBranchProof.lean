module
public import LogicLineages.PermittedControl.OriginalMatrixActualHighPacketTargets
import LogicLineages.PermittedControl.OriginalMatrixActualHighPacketProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixOrderBranchesProof
import LogicLineages.PermittedControl.OriginalMatrixUniformHighBoundProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixActualHighPacket
open ActualFiniteOrderBranches (realized)
open OriginalPrintedPlainMatrixOrderBranches (branches renamed BranchAccepts exactPrintedOrderBranch)
open OriginalMatrixUniformHighBound (foldCeilingBound exactUniformHighBound)

theorem exactOriginalFamilyHighBound : ExactOriginalFamilyHighBound := by
  intro B known gates p branch member
  exact foldCeilingBound (originalBranchCeiling B known gates p) (branches known gates p) branch member

theorem exactOriginalPaidBranchPacket : ExactOriginalPaidBranchPacket := by
  intro f B hf θ known gates p plain prior polarity branch member payment
  have paid := (exactOriginalFamilyHighBound B known gates p branch member).trans payment
  have side (checked : (ActualFiniteOrderBranches.guard branch).eval θ) :
      BranchAccepts f θ known gates p polarity branch ↔ BranchPacket f B θ known gates p polarity branch := by
    obtain ⟨strict,ranked,_⟩ := exactPrintedOrderBranch f θ known gates p plain polarity branch member checked
    have funds := exactUniformHighBound.2 B branch.1 (branch.1-1) (realized θ branch)
      (renamed known gates p branch) strict.monotone paid
    have exactPacket := exactActualHighPacket f B hf (realized θ branch) strict
      branch.1 (branch.1-1) (renamed known gates p branch) ranked funds
    constructor
    · rintro ⟨xs,actual,terminal⟩
      exact ⟨xs,(exactPacket _).mp actual,terminal⟩
    · rintro ⟨xs,packet,terminal⟩
      exact ⟨xs,(exactPacket _).mpr packet,terminal⟩
  constructor
  · rintro ⟨checked,pr,source⟩
    have transfer := (exactPrintedOrderBranch f θ known gates p plain polarity branch member checked).2.2
    exact ⟨checked,pr,(side checked).mp (transfer.mp source)⟩
  · rintro ⟨checked,pr,packet⟩
    have transfer := (exactPrintedOrderBranch f θ known gates p plain polarity branch member checked).2.2
    exact ⟨checked,pr,transfer.mpr ((side checked).mpr packet)⟩

end LogicLineages.PermittedControl.OriginalMatrixActualHighPacket
