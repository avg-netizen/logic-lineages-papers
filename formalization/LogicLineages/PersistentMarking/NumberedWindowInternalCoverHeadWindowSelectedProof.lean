module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowBaseOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowSelectedProof
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
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBodyRename rawConsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalAuxExchangeMemoStepTargets (binaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowOpenTargets
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalStrictAuxWindowTargets
open NumberedWindowInternalStrictAuxWindowThinTableProof (sameContext exact_OpenContextMemoSuccessor)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedPrior)
open NumberedWindowInternalCoverHeadWindowShapeProof (exact_OpenCoverHeadShape)
open NumberedWindowInternalCoverHeadWindowBaseOpenProof (exact_OpenCoverHeadIntrinsic)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (leafIntrinsicBase)
open NumberedWindowInternalCoverFittedInductionDispatchTargets (fittedWindowBase)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm)
open NumberedWindowInternalCoverHeadWindowTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem priorRename {β : Type} (b : Bool) (h : OTerm α) (tail : List (OTerm α))
    (j : α → β) :
    (headPrior b h tail).relabel j = headPrior b (h.relabel j) (tail.map (fun t => t.relabel j)) := by
  have pairTermRename (x y : OTerm α) :
      (pairTerm x y).relabel j = pairTerm (x.relabel j) (y.relabel j) := by
    simp only [pairTerm,addRelabel,mulRelabel]
  simp only [headPrior,pairTermRename,packedBodyRename,numeralRename,List.map_cons]

private theorem keyRename {β : Type} (b : Bool) (h : OTerm α) (tail : List (OTerm α)) (j : α → β) :
    (headKey b h tail).relabel j = headKey b (h.relabel j) (tail.map (fun t => t.relabel j)) := by
  simp only [headKey,rawConsRename,packedBodyRename,numeralRename,List.map_cons]

private theorem lengthRename {β : Type} (b : Bool) (h : OTerm α) (tail : List (OTerm α)) (j : α → β)
    (len : (h::tail).length = headArity b) :
    (h.relabel j :: tail.map (fun t => t.relabel j)).length = headArity b := by
  simpa only [List.length_cons,List.length_map] using len

private theorem atStep (b : Bool) (s : Settings) (B : Program 2) (T : Program 1)
    (ctx h result old : OTerm α) (tail : List (OTerm α)) (len : (h::tail).length = headArity b)
    (step : Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate (fittedWindowBase s (grammarHeadBase s B)) (refitGuard s T))
        (suc result) (headPrior b h tail) old ctx))) :
    Nonempty (Derivation body Γ (memberGraph (headsTerm s α) h)) := by
  let base := fittedWindowBase s (grammarHeadBase s B)
  let prior := headPrior b h tail
  let raw := headKey b h tail
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  have shape := exact_OpenCoverHeadShape b body α Γ h tail len
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have other := unaryGraph termShape currentKey z raw xs shape.notAux key
  have branch := zeroBranchElim shapeCheck (binaryAfter base (.projection 2) currentKey)
    (strictAuxPositive (refitGuard s T)) (suc result) xs other step
  have actual : Nonempty (Derivation body Γ (programGraph base (suc result) ![ctx,raw])) := by
    apply compositionRecover base ![.projection 2,currentKey] (suc result) xs ![ctx,raw] branch
    intro i
    exact Fin.cases (projectionValue 2 xs) (Fin.cases key (fun j => Fin.elim0 j)) i
  exact exact_OpenCoverHeadIntrinsic b s B body α Γ ctx h result tail len actual

private theorem atUpdate (b : Bool) (s : Settings) (B : Program 2) (T : Program 1)
    (ctx h result old value : OTerm α) (tail : List (OTerm α)) (len : (h::tail).length = headArity b)
    (parent : Nonempty (Derivation body Γ (windowGraph (headFittedWindow s B T) ctx result (headKey b h tail))))
    (table : Nonempty (Derivation body Γ (contextTable
      (strictAuxUpdate (fittedWindowBase s (grammarHeadBase s B)) (refitGuard s T)) old (headPrior b h tail) ctx)))
    (update : Nonempty (Derivation body Γ (contextStep
      (strictAuxUpdate (fittedWindowBase s (grammarHeadBase s B)) (refitGuard s T)) value (headPrior b h tail) old ctx))) :
    Nonempty (Derivation body Γ (memberGraph (headsTerm s α) h)) := by
  let R := strictAuxUpdate (fittedWindowBase s (grammarHeadBase s B)) (refitGuard s T)
  let F := selectedIntrinsic R
  let key := headKey b h tail
  let prior := headPrior b h tail
  have parentIntrinsic := (exact_OpenIntrinsicQuery F body α Γ ctx result key).mp parent
  have parentRow := (sameContext R (suc result) ctx key).mp parentIntrinsic
  have actual := exact_OpenContextMemoSuccessor R body α Γ value prior old ctx table update
  have agree := valueUnique (scratchRow (constantZero 2) R) value (suc result) ![key,ctx,z] actual parentRow
  have sameOutput := outputTransport R value (suc result) ![prior,old,ctx,z] agree update
  exact atStep b s B T ctx h result old tail len sameOutput

private theorem withTable (b : Bool) (s : Settings) (B : Program 2) (T : Program 1)
    (ctx h result old : OTerm α) (tail : List (OTerm α)) (len : (h::tail).length = headArity b)
    (parent : Nonempty (Derivation body Γ (windowGraph (headFittedWindow s B T) ctx result (headKey b h tail))))
    (table : Nonempty (Derivation body Γ (contextTable
      (strictAuxUpdate (fittedWindowBase s (grammarHeadBase s B)) (refitGuard s T)) old (headPrior b h tail) ctx))) :
    Nonempty (Derivation body Γ (memberGraph (headsTerm s α) h)) := by
  let R := strictAuxUpdate (fittedWindowBase s (grammarHeadBase s B)) (refitGuard s T)
  apply programCases R ![headPrior b h tail,old,ctx,z] _
  intro β j Δ value keep update
  simp only [quadInputsRename,priorRename,zRelabel] at update
  simp only [graphRename,headsTerm,numeralRename]
  have parent' := renameInto parent j Δ keep
  have table' := renameInto table j Δ keep
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel,keyRename] at parent'
  simp only [contextTable,programRename,tripleInputsRename,priorRename,zRelabel] at table'
  exact atUpdate b s B T (ctx.relabel j) (h.relabel j) (result.relabel j) (old.relabel j)
    value (tail.map (fun t => t.relabel j)) (lengthRename b h tail j len) parent' table' update

theorem exact_OpenCoverHeadFittedWindow : ExactOpenCoverHeadFittedWindow := by
  intro b s B T body α Γ ctx h result tail len parent
  let R := strictAuxUpdate (fittedWindowBase s (grammarHeadBase s B)) (refitGuard s T)
  apply programCases (scratchTable (constantZero 2) R) ![headPrior b h tail,ctx,z] _
  intro β j Δ old keep table
  simp only [tripleInputsRename,priorRename,zRelabel] at table
  simp only [graphRename,headsTerm,numeralRename]
  have parent' := renameInto parent j Δ keep
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel,keyRename] at parent'
  exact withTable b s B T (ctx.relabel j) (h.relabel j) (result.relabel j) old
    (tail.map (fun t => t.relabel j)) (lengthRename b h tail j len) parent' table

#print axioms exact_OpenCoverHeadFittedWindow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowSelectedProof
