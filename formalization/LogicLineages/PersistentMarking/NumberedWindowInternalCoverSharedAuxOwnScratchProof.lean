module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedOwnScratchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedAuxOwnScopesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverChildOwnScopeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedAuxSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedAuxMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedAuxOwnScratchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedSyntax sharedMeasureUpdate)
open NumberedWindowInternalCoverSharedAuxSyntaxProof (exact_OpenCoverSharedAuxSyntaxParent)
open NumberedWindowInternalCoverSharedAuxMeasureProof (exact_OpenCoverSharedAuxMeasureParent)
open NumberedWindowInternalStrictAuxWindowParentProof (exact_OpenStrictAuxWindowParent)
open NumberedWindowInternalCoverChildOwnScopeProof (moveLocal)
open NumberedWindowInternalCoverSharedAuxOwnScopesProof (moveAuxInputs fromSharedMeasured)
open NumberedWindowInternalCoverSharedOwnScratchTargets

theorem exact_OpenCoverSharedAuxOwnScratch : ExactOpenCoverSharedAuxOwnScratch := by
  intro V TV M B TW s body α Γ p vertices ctx dom cod fn arg paid
  obtain ⟨valid⟩ := exact_OpenCoverSharedAuxSyntaxParent V TV body α Γ dom cod fn arg paid.valid
  obtain ⟨typed⟩ := exact_OpenStrictAuxWindowParent B TW body α Γ ctx dom cod fn arg paid.typed
  let W := strictAuxWindow B TW
  let R := sharedMeasureUpdate M
  let Q := sharedSyntax V TV
  have fnLocal : ChildOwnInputs Q R W s body Γ ctx (rawCons dom cod) fn :=
    ⟨⟨Derivation.conjunctionLeft (Derivation.conjunctionRight valid)⟩,
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight typed)⟩,paid.fnIH⟩
  have argLocal : ChildOwnInputs Q R W s body Γ ctx dom arg :=
    ⟨⟨Derivation.conjunctionRight (Derivation.conjunctionRight valid)⟩,
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight typed)⟩,paid.argIH⟩
  apply exact_OpenCoverSharedAuxMeasureParent M body α Γ dom cod fn arg p _ paid.measured
  intro β j Δ old mf ma df da bf ba keep row
  rw [graphRename,auxiliaryRename]
  have paid' := moveAuxInputs V TV M B TW s j keep paid
  have fnLocal' := moveLocal Q R W s j keep fnLocal
  have argLocal' := moveLocal Q R W s j keep argLocal
  rw [rawConsRename] at fnLocal'
  exact fromSharedMeasured V TV M B TW s (p.relabel j) (vertices.relabel j) (ctx.relabel j)
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) mf ma df da bf ba paid'
    fnLocal' argLocal' row.fnData row.argData row.parentBounds

#print axioms exact_OpenCoverSharedAuxOwnScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedAuxOwnScratchProof
