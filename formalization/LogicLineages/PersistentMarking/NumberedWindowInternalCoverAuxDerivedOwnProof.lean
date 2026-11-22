module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxDerivedOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxDerivedOwnScopesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxDerivedOwnChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxOpenParentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureParentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxDerivedOwnProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalCoverAuxSyntaxOpenParentProof (exact_OpenCoverAuxSyntaxParent)
open NumberedWindowInternalStrictAuxWindowParentProof (exact_OpenStrictAuxWindowParent)
open NumberedWindowInternalChosenAuxMeasureParentProof (exact_OpenChosenAuxMeasureParent)
open NumberedWindowInternalCoverAuxDerivedOwnChildProof (moveLocal)
open NumberedWindowInternalCoverAuxDerivedOwnScopesProof (moveInputs fromMeasured)
open NumberedWindowInternalCoverAuxDerivedOwnTargets

theorem exact_OpenCoverAuxDerivedOwn : ExactOpenCoverAuxDerivedOwn := by
  intro V TV M B TW s body α Γ p vertices ctx dom cod fn arg paid
  obtain ⟨valid⟩ := exact_OpenCoverAuxSyntaxParent V TV body α Γ dom cod fn arg paid.valid
  obtain ⟨typed⟩ := exact_OpenStrictAuxWindowParent B TW body α Γ ctx dom cod fn arg paid.typed
  have fnLocal : LocalChild V TV M (strictAuxWindow B TW) s body Γ ctx (rawCons dom cod) fn :=
    ⟨⟨Derivation.conjunctionLeft (Derivation.conjunctionRight valid)⟩,
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight typed)⟩,paid.fnIH⟩
  have argLocal : LocalChild V TV M (strictAuxWindow B TW) s body Γ ctx dom arg :=
    ⟨⟨Derivation.conjunctionRight (Derivation.conjunctionRight valid)⟩,
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight typed)⟩,paid.argIH⟩
  apply exact_OpenChosenAuxMeasureParent M body α Γ dom cod fn arg p _ paid.measured
  intro β j Δ mf ma df da bf ba keep fnData argData parentResult
  rw [graphRename,auxiliaryRename]
  have paid' := moveInputs V TV M B TW s j keep paid
  have fnLocal' := moveLocal V TV M (strictAuxWindow B TW) s j keep fnLocal
  have argLocal' := moveLocal V TV M (strictAuxWindow B TW) s j keep argLocal
  rw [rawConsRename] at fnLocal'
  exact fromMeasured V TV M B TW s (p.relabel j) (vertices.relabel j) (ctx.relabel j)
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) mf ma df da bf ba paid'
    fnLocal' argLocal' fnData argData parentResult.combined

#print axioms exact_OpenCoverAuxDerivedOwn

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxDerivedOwnProof
