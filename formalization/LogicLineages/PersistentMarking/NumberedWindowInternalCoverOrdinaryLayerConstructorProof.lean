module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldThinOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerConstructorProof
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
open NumberedWindowInternalCoverOrdinaryLayerTargets
open NumberedWindowInternalCoverOrdinaryLayerOpenDataProof
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm singletonLeaf typeBlock)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename singletonMember)
open NumberedWindowInternalCoverArgumentCellsOpenDataProof (unaryTapeRename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem innerHit (tag : Nat) (row ty child children : OTerm α)
    (run : Nonempty (Derivation body Γ (flatGraph (singletonLeaf tag) row children ![ty])))
    (hchild : Nonempty (Derivation body Γ (memberGraph children child))) :
    Nonempty (Derivation body Γ (memberGraph row (namedTerm tag ty child))) := by
  apply programCases (singletonLeaf tag) ![child,ty] _
  intro β j Δ one keep singleton
  rw [graphRename,namedRename]
  simp only [binaryInputsRename] at singleton
  have run' := renameInto run j Δ keep
  rw [flatRename,unaryTapeRename] at run'
  have hchild' := renameInto hchild j Δ keep
  rw [graphRename] at hchild'
  let key := namedTerm tag (ty.relabel j) (child.relabel j)
  have oneHit := singletonMember tag (ty.relabel j) (child.relabel j) one singleton
  exact exact_OpenCartesianFoldMember (singletonLeaf tag) body β Δ (children.relabel j) (child.relabel j) one key
    (row.relabel j) ![ty.relabel j] hchild' singleton oneHit run'

private theorem outerHit (tag : Nat) (out K children ty child : OTerm α)
    (run : Nonempty (Derivation body Γ (flatGraph (typeBlock tag) out K ![children])))
    (hty : Nonempty (Derivation body Γ (memberGraph K ty)))
    (hchild : Nonempty (Derivation body Γ (memberGraph children child))) :
    Nonempty (Derivation body Γ (memberGraph out (namedTerm tag ty child))) := by
  apply programCases (typeBlock tag) ![ty,children] _
  intro β j Δ row keep rowRun
  rw [graphRename,namedRename]
  simp only [binaryInputsRename] at rowRun
  have run' := renameInto run j Δ keep
  rw [flatRename,unaryTapeRename] at run'
  have hty' := renameInto hty j Δ keep
  have hchild' := renameInto hchild j Δ keep
  rw [graphRename] at hty' hchild'
  let key := namedTerm tag (ty.relabel j) (child.relabel j)
  have actual := innerGraph tag row (ty.relabel j) (children.relabel j) rowRun
  have hit := innerHit tag row (ty.relabel j) (child.relabel j) (children.relabel j) actual hchild'
  exact exact_OpenCartesianFoldMember (typeBlock tag) body β Δ (K.relabel j) (ty.relabel j) row key
    (out.relabel j) ![children.relabel j] hty' rowRun hit run'

theorem openTaggedLayerConstructor (tag : Nat) : ExactOpenTaggedLayerConstructor tag := by
  intro body α Γ out K children ty q actual hty hq
  exact outerHit tag out K children ty q (outerGraph tag out K children actual) hty hq

theorem exact_OpenCoverOrdinaryLayerConstructor : ExactOpenCoverOrdinaryLayerConstructor :=
  openTaggedLayerConstructor 4

#print axioms exact_OpenCoverOrdinaryLayerConstructor

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerConstructorProof
