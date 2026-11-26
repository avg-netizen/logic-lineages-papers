module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowBaseOpenProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowSelectedProof
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
open NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof (exact_OpenCoverNamedLeafIntrinsicShape)
open NumberedWindowInternalCoverLexicalBoundWindowBaseOpenProof (exact_OpenCoverLexicalBoundBaseSlot)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (leafIntrinsicBase)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (namedGrammarBase)
open NumberedWindowInternalCoverLexicalSlotTargets (slotCheck)
open NumberedWindowInternalCoverLexicalBoundWindowTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem priorRename {β : Type} (ty i : OTerm α) (j : α → β) :
    (namedPrior true ty i).relabel j = namedPrior true (ty.relabel j) (i.relabel j) := by
  have pairTermRename (x y : OTerm α) :
      (pairTerm x y).relabel j = pairTerm (x.relabel j) (y.relabel j) := by
    simp only [pairTerm,addRelabel,mulRelabel]
  simp only [namedPrior,pairTermRename,packedBodyRename,numeralRename,List.map_cons,List.map_nil]

private theorem atStep (s : Settings) (B : Program 2) (T : Program 1)
    (ctx ty i result old : OTerm α)
    (step : Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase B))) T) (suc result) (namedPrior true ty i) old ctx))) :
    Nonempty (Derivation body Γ (programGraph slotCheck (suc z) ![i,ctx,ty])) := by
  let base := leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase B))
  let prior := namedPrior true ty i
  let raw := namedTerm 1 ty i
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  have shape := exact_OpenCoverNamedLeafIntrinsicShape true body α Γ ty i
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have other := unaryGraph termShape currentKey z raw xs shape.1 key
  have branch := zeroBranchElim shapeCheck (binaryAfter base (.projection 2) currentKey)
    (strictAuxPositive T) (suc result) xs other step
  have actual : Nonempty (Derivation body Γ (programGraph base (suc result) ![ctx,raw])) := by
    apply compositionRecover base ![.projection 2,currentKey] (suc result) xs ![ctx,raw] branch
    intro i
    exact Fin.cases (projectionValue 2 xs) (Fin.cases key (fun j => Fin.elim0 j)) i
  exact exact_OpenCoverLexicalBoundBaseSlot s B body α Γ ctx ty i result actual

private theorem atUpdate (s : Settings) (B : Program 2) (T : Program 1)
    (ctx ty i result old value : OTerm α)
    (parent : Nonempty (Derivation body Γ (windowGraph (lexicalNamedWindow s B T) ctx result (namedTerm 1 ty i))))
    (table : Nonempty (Derivation body Γ
      (contextTable (strictAuxUpdate (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase B))) T) old (namedPrior true ty i) ctx)))
    (update : Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase B))) T) value (namedPrior true ty i) old ctx))) :
    Nonempty (Derivation body Γ (programGraph slotCheck (suc z) ![i,ctx,ty])) := by
  let R := strictAuxUpdate (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase B))) T
  let F := selectedIntrinsic R
  let key := namedTerm 1 ty i
  let prior := namedPrior true ty i
  have parentIntrinsic := (exact_OpenIntrinsicQuery F body α Γ ctx result key).mp parent
  have parentRow := (sameContext R (suc result) ctx key).mp parentIntrinsic
  have actual := exact_OpenContextMemoSuccessor R body α Γ value prior old ctx table update
  have agree := valueUnique (scratchRow (constantZero 2) R) value (suc result) ![key,ctx,z] actual parentRow
  have sameOutput := outputTransport R value (suc result) ![prior,old,ctx,z] agree update
  exact atStep s B T ctx ty i result old sameOutput

private theorem withTable (s : Settings) (B : Program 2) (T : Program 1)
    (ctx ty i result old : OTerm α)
    (parent : Nonempty (Derivation body Γ (windowGraph (lexicalNamedWindow s B T) ctx result (namedTerm 1 ty i))))
    (table : Nonempty (Derivation body Γ
      (contextTable (strictAuxUpdate (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase B))) T) old (namedPrior true ty i) ctx))) :
    Nonempty (Derivation body Γ (programGraph slotCheck (suc z) ![i,ctx,ty])) := by
  let R := strictAuxUpdate (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase B))) T
  apply programCases R ![namedPrior true ty i,old,ctx,z] _
  intro β j Δ value keep update
  simp only [quadInputsRename,priorRename,zRelabel] at update
  simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
  have parent' := renameInto parent j Δ keep
  have table' := renameInto table j Δ keep
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel,namedRename] at parent'
  simp only [contextTable,programRename,tripleInputsRename,priorRename,zRelabel] at table'
  exact atUpdate s B T (ctx.relabel j) (ty.relabel j) (i.relabel j) (result.relabel j) (old.relabel j)
    value parent' table' update

theorem exact_OpenCoverLexicalBoundWindowSlot : ExactOpenCoverLexicalBoundWindowSlot := by
  intro s B T body α Γ ctx ty i result parent
  let R := strictAuxUpdate (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase B))) T
  apply programCases (scratchTable (constantZero 2) R) ![namedPrior true ty i,ctx,z] _
  intro β j Δ old keep table
  simp only [tripleInputsRename,priorRename,zRelabel] at table
  simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
  have parent' := renameInto parent j Δ keep
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel,namedRename] at parent'
  exact withTable s B T (ctx.relabel j) (ty.relabel j) (i.relabel j) (result.relabel j) old parent' table

#print axioms exact_OpenCoverLexicalBoundWindowSlot

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowSelectedProof
