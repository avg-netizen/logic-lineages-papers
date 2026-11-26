module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanBranchesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowsFilterStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowRecheckProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanIntroProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanBranchesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept scanLoop)
open NumberedWindowInternalDirectInsertedRowTargets (oneTerm)
open NumberedWindowInternalOpenOriginScanIntroTargets (D)
open NumberedWindowInternalOpenOriginScanIntroProof (exact_OpenOriginScanConsIntro)
open NumberedWindowInternalOriginRowsFilterStepProof (exact_OpenOriginRowStep)
open NumberedWindowInternalOriginRowRecheckProof (exact_OpenRecheckOriginRow)
open NumberedWindowInternalOpenOriginScanBranchesTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem skipped (r : Program 3) (out rest removed : OrdinaryArithmetic.Term α)
    (same : D B Γ (eqn out rest)) (tail : D B Γ (loopAccept r rest removed)) :
    D B Γ (loopAccept r out removed) := by
  obtain ⟨he⟩ := same
  exact headTransport (scanLoop r) oneTerm rest out ![removed] ⟨symm he⟩ tail

theorem exact_OpenOriginScanBranches : ExactOpenOriginScanBranches := by
  intro r B α Γ oldPool oldScratch row target dom cert
    rawLeft rawRight scratchLeft scratchRight tailLeft tailRight outLeft outRight
    old parsedLeft parsedRight leftOK rightOK leftStep rightStep
  have stepLeft := exact_OpenOriginRowStep B α Γ row tailLeft scratchLeft dom outLeft old.dominatorField
  have stepRight := exact_OpenOriginRowStep B α Γ row tailRight scratchLeft dom outRight old.dominatorField
  constructor
  · intro leftMem
    have build := ((stepLeft.1 leftMem).1).mp leftStep
    have skip := ((stepRight.1 leftMem).2).mp rightStep
    have checked := exact_OpenRecheckOriginRow r B α Γ oldPool rawLeft row oldScratch
      scratchLeft target dom cert old parsedLeft leftMem
    have accepted := exact_OpenOriginScanConsIntro r B α Γ outLeft row tailLeft
      rawLeft build checked leftOK
    exact ⟨build, skip, accepted, skipped r outRight tailRight rawRight skip rightOK⟩
  · intro notLeft rightMem
    have skip := ((stepLeft.2 notLeft).1).mp leftStep
    have build := ((stepRight.2 notLeft).2).mp rightStep
    have checked := exact_OpenRecheckOriginRow r B α Γ oldPool rawRight row oldScratch
      scratchRight target dom cert old parsedRight rightMem
    have accepted := exact_OpenOriginScanConsIntro r B α Γ outRight row tailRight
      rawRight build checked rightOK
    exact ⟨skip, build, skipped r outLeft tailLeft rawLeft skip leftOK, accepted⟩

#print axioms exact_OpenOriginScanBranches

end LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanBranchesProof
