module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnContinuationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalAuxOwnContinuationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverChildOwnScopeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedAuxMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxOwnScratchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedMeasureUpdate)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets (refinedSyntax)
open NumberedWindowInternalCoverSharedOwnScratchTargets (ChildOwnInputs)
open NumberedWindowInternalCoverRefinedAuxSyntaxProof (exact_OpenCoverRefinedAuxSyntaxParent)
open NumberedWindowInternalCoverSharedAuxMeasureProof (exact_OpenCoverSharedAuxMeasureParent)
open NumberedWindowInternalStrictAuxWindowParentProof (exact_OpenStrictAuxWindowParent)
open NumberedWindowInternalCoverChildOwnScopeProof (moveLocal)
open NumberedWindowInternalCoverLocalOwnReportRenameProof (moveParent moveTypeMember)
open NumberedWindowInternalCoverLocalAuxOwnContinuationProof (exact_OpenCoverLocalAuxOwnContinuation)
open NumberedWindowInternalCoverLocalOwnContinuationTargets

theorem exact_OpenCoverRefinedAuxOwnScratch : ExactOpenCoverRefinedAuxOwnScratch := by
  intro V TV M B TW s body α Γ p vertices ctx dom cod fn arg parent typed fnIH argIH domain codomain
  let Q := refinedSyntax V TV
  let R := sharedMeasureUpdate M
  let W := strictAuxWindow B TW
  obtain ⟨bits⟩ := exact_OpenCoverRefinedAuxSyntaxParent V TV body α Γ dom cod fn arg parent.valid
  obtain ⟨windows⟩ := exact_OpenStrictAuxWindowParent B TW body α Γ ctx dom cod fn arg typed
  have fnLocal : ChildOwnInputs Q R W s body Γ ctx (rawCons dom cod) fn :=
    ⟨⟨Derivation.conjunctionLeft (Derivation.conjunctionRight bits)⟩,
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight windows)⟩,fnIH⟩
  have argLocal : ChildOwnInputs Q R W s body Γ ctx dom arg :=
    ⟨⟨Derivation.conjunctionRight (Derivation.conjunctionRight bits)⟩,
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight windows)⟩,argIH⟩
  apply exact_OpenCoverSharedAuxMeasureParent M body α Γ dom cod fn arg p _ parent.measured
  intro β j Δ old mf ma df da bf ba keep row
  rw [graphRename,auxiliaryRename]
  have parent' := moveParent Q R s j keep parent
  rw [auxiliaryRename] at parent'
  have f := moveLocal Q R W s j keep fnLocal
  rw [rawConsRename] at f
  have a := moveLocal Q R W s j keep argLocal
  have d := moveTypeMember s j keep domain
  have c := moveTypeMember s j keep codomain
  exact exact_OpenCoverLocalAuxOwnContinuation Q R W s body β Δ
    (p.relabel j) (vertices.relabel j) (ctx.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    mf ma df da bf ba parent' f a row.fnData row.argData row.parentBounds d c

#print axioms exact_OpenCoverRefinedAuxOwnScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxOwnScratchProof
