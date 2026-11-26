module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldThinOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesConstructorProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember)
open NumberedWindowInternalCoverCartesianFoldTargets (flatGraph)
open NumberedWindowInternalCoverCartesianFoldThinOpenProof (exact_OpenCartesianFoldMember)
open NumberedWindowInternalCoverTypeLeavesTargets
open NumberedWindowInternalCoverTypeLeavesOpenDataProof

attribute [local irreducible] programGraph

theorem exact_OpenCoverTypeLeavesConstructor : ExactOpenCoverTypeLeavesConstructor := by
  intro body α Γ out K ty run ht
  apply programCases typeLeafSingleton (unaryTape ty) _
  intro β j Δ one keep actual
  rw [graphRename,termRename]
  rw [oneTapeRename] at actual
  have run' := renameInto run j Δ keep
  rw [reportRename] at run'
  have ht' := renameInto ht j Δ keep
  rw [graphRename] at ht'
  let n := typeLeafTerm (ty.relabel j)
  have cell := singletonCell one (ty.relabel j) actual
  have oneHit := headMember one n z n cell ⟨refl n⟩
  exact exact_OpenCartesianFoldMember (k := 0) typeLeafSingleton body β Δ (K.relabel j)
    (ty.relabel j) one n (out.relabel j) Fin.elim0 ht' actual oneHit run'

#print axioms exact_OpenCoverTypeLeavesConstructor

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesConstructorProof
