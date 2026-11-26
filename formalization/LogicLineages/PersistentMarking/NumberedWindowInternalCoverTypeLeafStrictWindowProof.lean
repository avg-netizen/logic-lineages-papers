module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicBaseOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafStrictWindowProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique outputTransport successorValue projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBodyRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalCoverTypeLeavesOpenDataProof (termRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalAuxExchangeMemoStepTargets (binaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowOpenTargets
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalStrictAuxWindowTargets
open NumberedWindowInternalStrictAuxWindowThinTableProof (sameContext exact_OpenContextMemoSuccessor)
open NumberedWindowInternalCoverTypeLeafMeasureTargets (typeLeafPrior)
open NumberedWindowInternalCoverTypeLeafIntrinsicShapeProof (exact_OpenCoverTypeLeafShape)
open NumberedWindowInternalCoverTypeLeafIntrinsicBaseOpenProof (exact_OpenCoverTypeLeafIntrinsicBaseK)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem priorRename {β : Type} (ty : OTerm α) (j : α → β) :
    (typeLeafPrior ty).relabel j = typeLeafPrior (ty.relabel j) := by
  have pairTermRename (x y : OTerm α) :
      (pairTerm x y).relabel j = pairTerm (x.relabel j) (y.relabel j) := by
    simp only [pairTerm,addRelabel,mulRelabel]
  simp only [typeLeafPrior,pairTermRename,packedBodyRename,numeralRename,List.map_cons,List.map_nil]

private theorem atStep (s : Settings) (B : Program 2) (T : Program 1)
    (ctx ty result old : OTerm α)
    (step : Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate (leafIntrinsicBase s B) T) (suc result) (typeLeafPrior ty) old ctx))) :
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) := by
  let base := leafIntrinsicBase s B
  let prior := typeLeafPrior ty
  let raw := typeLeafTerm ty
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  have shape := exact_OpenCoverTypeLeafShape body α Γ ty
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have other := unaryGraph termShape currentKey z raw xs shape.1 key
  have branch := zeroBranchElim shapeCheck (binaryAfter base (.projection 2) currentKey)
    (strictAuxPositive T) (suc result) xs other step
  have actual : Nonempty (Derivation body Γ (programGraph base (suc result) ![ctx,raw])) := by
    apply compositionRecover base ![.projection 2,currentKey] (suc result) xs ![ctx,raw] branch
    intro i
    exact Fin.cases (projectionValue 2 xs) (Fin.cases key (fun j => Fin.elim0 j)) i
  exact exact_OpenCoverTypeLeafIntrinsicBaseK s B body α Γ ctx ty result actual

private theorem atUpdate (s : Settings) (B : Program 2) (T : Program 1)
    (ctx ty result old value : OTerm α)
    (parent : Nonempty (Derivation body Γ (windowGraph (leafStrictWindow s B T) ctx result (typeLeafTerm ty))))
    (table : Nonempty (Derivation body Γ
      (contextTable (strictAuxUpdate (leafIntrinsicBase s B) T) old (typeLeafPrior ty) ctx)))
    (update : Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate (leafIntrinsicBase s B) T) value (typeLeafPrior ty) old ctx))) :
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) := by
  let R := strictAuxUpdate (leafIntrinsicBase s B) T
  let F := selectedIntrinsic R
  let key := typeLeafTerm ty
  let prior := typeLeafPrior ty
  have parentIntrinsic := (exact_OpenIntrinsicQuery F body α Γ ctx result key).mp parent
  have parentRow := (sameContext R (suc result) ctx key).mp parentIntrinsic
  have actual := exact_OpenContextMemoSuccessor R body α Γ value prior old ctx table update
  have agree := valueUnique (scratchRow (constantZero 2) R) value (suc result) ![key,ctx,z] actual parentRow
  have sameOutput := outputTransport R value (suc result) ![prior,old,ctx,z] agree update
  exact atStep s B T ctx ty result old sameOutput

private theorem withTable (s : Settings) (B : Program 2) (T : Program 1)
    (ctx ty result old : OTerm α)
    (parent : Nonempty (Derivation body Γ (windowGraph (leafStrictWindow s B T) ctx result (typeLeafTerm ty))))
    (table : Nonempty (Derivation body Γ
      (contextTable (strictAuxUpdate (leafIntrinsicBase s B) T) old (typeLeafPrior ty) ctx))) :
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) := by
  let R := strictAuxUpdate (leafIntrinsicBase s B) T
  apply programCases R ![typeLeafPrior ty,old,ctx,z] _
  intro β j Δ value keep update
  simp only [quadInputsRename,priorRename,zRelabel] at update
  simp only [graphRename,typesTerm,numeralRename]
  have parent' := renameInto parent j Δ keep
  have table' := renameInto table j Δ keep
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel,termRename] at parent'
  simp only [contextTable,programRename,tripleInputsRename,priorRename,zRelabel] at table'
  exact atUpdate s B T (ctx.relabel j) (ty.relabel j) (result.relabel j) (old.relabel j)
    value parent' table' update

theorem exact_OpenCoverTypeLeafStrictWindowK : ExactOpenCoverTypeLeafStrictWindowK := by
  intro s B T body α Γ ctx ty result parent
  let R := strictAuxUpdate (leafIntrinsicBase s B) T
  apply programCases (scratchTable (constantZero 2) R) ![typeLeafPrior ty,ctx,z] _
  intro β j Δ old keep table
  simp only [tripleInputsRename,priorRename,zRelabel] at table
  simp only [graphRename,typesTerm,numeralRename]
  have parent' := renameInto parent j Δ keep
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel,termRename] at parent'
  exact withTable s B T (ctx.relabel j) (ty.relabel j) (result.relabel j) old parent' table

#print axioms exact_OpenCoverTypeLeafStrictWindowK

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafStrictWindowProof
