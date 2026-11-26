module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldThinOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerConstructorProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverCartesianFoldTargets (flatGraph)
open NumberedWindowInternalCoverCartesianFoldSyntaxProof (flatRename)
open NumberedWindowInternalCoverCartesianFoldThinOpenProof (exact_OpenCartesianFoldMember)
open NumberedWindowInternalCoverLambdaLayerTargets
open NumberedWindowInternalCoverLambdaLayerOpenDataProof
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm singletonLeaf typeBlock)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename singletonMember)
open NumberedWindowInternalCoverArgumentCellsOpenDataProof (unaryTapeRename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem innerHit (row ty child children : OTerm α)
    (run : Nonempty (Derivation body Γ (flatGraph (singletonLeaf 2) row children ![ty])))
    (hchild : Nonempty (Derivation body Γ (memberGraph children child))) :
    Nonempty (Derivation body Γ (memberGraph row (namedTerm 2 ty child))) := by
  apply programCases (singletonLeaf 2) ![child,ty] _
  intro β j Δ one keep singleton
  rw [graphRename,namedRename]
  simp only [binaryInputsRename] at singleton
  have run' := renameInto run j Δ keep
  rw [flatRename,unaryTapeRename] at run'
  have hchild' := renameInto hchild j Δ keep
  rw [graphRename] at hchild'
  let key := namedTerm 2 (ty.relabel j) (child.relabel j)
  have oneHit := singletonMember 2 (ty.relabel j) (child.relabel j) one singleton
  exact exact_OpenCartesianFoldMember (singletonLeaf 2) body β Δ (children.relabel j) (child.relabel j) one key
    (row.relabel j) ![ty.relabel j] hchild' singleton oneHit run'

private theorem outerHit (out K children ty child : OTerm α)
    (run : Nonempty (Derivation body Γ (flatGraph (typeBlock 2) out K ![children])))
    (hty : Nonempty (Derivation body Γ (memberGraph K ty)))
    (hchild : Nonempty (Derivation body Γ (memberGraph children child))) :
    Nonempty (Derivation body Γ (memberGraph out (namedTerm 2 ty child))) := by
  apply programCases (typeBlock 2) ![ty,children] _
  intro β j Δ row keep rowRun
  rw [graphRename,namedRename]
  simp only [binaryInputsRename] at rowRun
  have run' := renameInto run j Δ keep
  rw [flatRename,unaryTapeRename] at run'
  have hty' := renameInto hty j Δ keep
  have hchild' := renameInto hchild j Δ keep
  rw [graphRename] at hty' hchild'
  let key := namedTerm 2 (ty.relabel j) (child.relabel j)
  have actual := innerGraph row (ty.relabel j) (children.relabel j) rowRun
  have hit := innerHit row (ty.relabel j) (child.relabel j) (children.relabel j) actual hchild'
  exact exact_OpenCartesianFoldMember (typeBlock 2) body β Δ (K.relabel j) (ty.relabel j) row key
    (out.relabel j) ![children.relabel j] hty' rowRun hit run'

theorem exact_OpenCoverLambdaLayerConstructor : ExactOpenCoverLambdaLayerConstructor := by
  intro body α Γ out K children ty q actual hty hq
  exact outerHit out K children ty q (outerGraph out K children actual) hty hq

#print axioms exact_OpenCoverLambdaLayerConstructor

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerConstructorProof
