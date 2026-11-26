module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerOriginProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverCartesianFoldOriginTargets (blockHit)
open NumberedWindowInternalCoverCartesianFoldOriginChecks (exact_OpenCartesianFoldOrigin)
open NumberedWindowInternalCoverCartesianFoldOriginWitnessProof (blockMemberOfHit)
open NumberedWindowInternalCoverNamedLeafOriginBindingProof (cartesianCases)
open NumberedWindowInternalCoverLambdaLayerTargets
open NumberedWindowInternalCoverLambdaLayerOpenDataProof
open NumberedWindowInternalCoverNamedLeavesTargets (singletonLeaf typeBlock)
open NumberedWindowInternalCoverNamedLeafOriginDataProof (singletonOrigin)
open NumberedWindowInternalCoverArgumentCellsOpenDataProof (unaryTapeRename)
open NumberedWindowInternalCoverLambdaLayerBindingProof

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atBody (K children key ty child : OTerm α)
    (hty : Nonempty (Derivation body Γ (memberGraph K ty)))
    (hchild : Nonempty (Derivation body Γ (memberGraph children child)))
    (fromSingleton : Nonempty (Derivation body Γ (blockHit (singletonLeaf 2) child key ![ty]))) :
    Nonempty (Derivation body Γ (lambdaOrigin K children key)) := by
  apply programCases (singletonLeaf 2) ![child,ty] _
  intro β j Δ one keep run
  rw [originRename]
  simp only [binaryInputsRename] at run
  have hty' := renameInto hty j Δ keep
  have hchild' := renameInto hchild j Δ keep
  rw [graphRename] at hty' hchild'
  have hit := renameInto fromSingleton j Δ keep
  simp only [blockHit,programRename,consTermRename,unaryTapeRename,sucRelabel,zRelabel] at hit
  have actualHit := blockMemberOfHit (singletonLeaf 2) (child.relabel j) (key.relabel j) one ![ty.relabel j] run hit
  obtain ⟨same⟩ := singletonOrigin 2 (ty.relabel j) (child.relabel j) one (key.relabel j) run actualHit
  obtain ⟨hty'⟩ := hty'
  obtain ⟨hchild'⟩ := hchild'
  exact introduce (K.relabel j) (children.relabel j) (key.relabel j) (ty.relabel j) (child.relabel j)
    ⟨Derivation.conjunctionIntroduction hty' (Derivation.conjunctionIntroduction hchild' same)⟩

private theorem atType (K children key ty : OTerm α)
    (hty : Nonempty (Derivation body Γ (memberGraph K ty)))
    (fromRow : Nonempty (Derivation body Γ (blockHit (typeBlock 2) ty key ![children]))) :
    Nonempty (Derivation body Γ (lambdaOrigin K children key)) := by
  apply programCases (typeBlock 2) ![ty,children] _
  intro β j Δ row keep run
  rw [originRename]
  simp only [binaryInputsRename] at run
  have hty' := renameInto hty j Δ keep
  rw [graphRename] at hty'
  have hit := renameInto fromRow j Δ keep
  simp only [blockHit,programRename,consTermRename,unaryTapeRename,sucRelabel,zRelabel] at hit
  let types := K.relabel j
  let terms := children.relabel j
  let k := key.relabel j
  let pickedType := ty.relabel j
  have actualHit := blockMemberOfHit (typeBlock 2) pickedType k row ![terms] run hit
  have actualFold := innerGraph row pickedType terms run
  have found := exact_OpenCartesianFoldOrigin (singletonLeaf 2) body β Δ terms k row ![pickedType] actualFold actualHit
  apply cartesianCases (singletonLeaf 2) terms k ![pickedType] _ found
  intro γ l Θ child preserve w
  rw [originRename]
  have hty'' := renameInto hty' l Θ preserve
  rw [graphRename] at hty''
  rw [unaryTapeRename] at w
  obtain ⟨w⟩ := w
  exact atBody (types.relabel l) (terms.relabel l) (k.relabel l) (pickedType.relabel l) child hty''
    ⟨Derivation.conjunctionLeft w⟩ ⟨Derivation.conjunctionRight w⟩

private theorem outerOrigin (out K children key : OTerm α)
    (folded : Nonempty (Derivation body Γ (lambdaReport out K children)))
    (hit : Nonempty (Derivation body Γ (memberGraph out key))) :
    Nonempty (Derivation body Γ (lambdaOrigin K children key)) := by
  have run := outerGraph out K children folded
  have found := exact_OpenCartesianFoldOrigin (typeBlock 2) body α Γ K key out ![children] run hit
  apply cartesianCases (typeBlock 2) K key ![children] _ found
  intro β j Δ ty keep w
  rw [originRename]
  rw [unaryTapeRename] at w
  obtain ⟨w⟩ := w
  exact atType (K.relabel j) (children.relabel j) (key.relabel j) ty
    ⟨Derivation.conjunctionLeft w⟩ ⟨Derivation.conjunctionRight w⟩

theorem exact_OpenCoverLambdaLayerOrigin : ExactOpenCoverLambdaLayerOrigin := by
  intro body α Γ out K children key actual hit
  exact outerOrigin out K children key actual hit

#print axioms exact_OpenCoverLambdaLayerOrigin

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerOriginProof
