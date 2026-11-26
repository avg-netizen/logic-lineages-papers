module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultBaseProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultWindowProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique outputTransport successorValue projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc eqnRelabel zRelabel sucRelabel)
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
open NumberedWindowInternalCoverNamedResultBaseProof (exact_OpenCoverNamedResultBase)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (leafIntrinsicBase)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (namedGrammarBase)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalBoundBase)
open NumberedWindowInternalCoverNamedResultTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem priorRename {β : Type} (b : Bool) (ty i : OTerm α) (j : α → β) :
    (namedPrior b ty i).relabel j = namedPrior b (ty.relabel j) (i.relabel j) := by
  have pairTermRename (x y : OTerm α) :
      (pairTerm x y).relabel j = pairTerm (x.relabel j) (y.relabel j) := by
    simp only [pairTerm,addRelabel,mulRelabel]
  simp only [namedPrior,pairTermRename,packedBodyRename,numeralRename,List.map_cons,List.map_nil]

private theorem atStep (b : Bool) (s : Settings) (B : Program 2) (T : Program 1)
    (ctx ty i result old : OTerm α)
    (step : Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase (namedResultBase B)))) T) (suc result) (namedPrior b ty i) old ctx))) :
    Nonempty (Derivation body Γ (eqn result ty)) := by
  let base := leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase (namedResultBase B)))
  let prior := namedPrior b ty i
  let raw := namedTerm b.toNat ty i
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  have shape := exact_OpenCoverNamedLeafIntrinsicShape b body α Γ ty i
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have other := unaryGraph termShape currentKey z raw xs shape.1 key
  have branch := zeroBranchElim shapeCheck (binaryAfter base (.projection 2) currentKey)
    (strictAuxPositive T) (suc result) xs other step
  have actual : Nonempty (Derivation body Γ (programGraph base (suc result) ![ctx,raw])) := by
    apply compositionRecover base ![.projection 2,currentKey] (suc result) xs ![ctx,raw] branch
    intro i
    exact Fin.cases (projectionValue 2 xs) (Fin.cases key (fun j => Fin.elim0 j)) i
  exact exact_OpenCoverNamedResultBase b s B body α Γ ctx ty i result actual

private theorem atUpdate (b : Bool) (s : Settings) (B : Program 2) (T : Program 1)
    (ctx ty i result old value : OTerm α)
    (parent : Nonempty (Derivation body Γ (windowGraph (namedResultWindow s B T) ctx result (namedTerm b.toNat ty i))))
    (table : Nonempty (Derivation body Γ
      (contextTable (strictAuxUpdate (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase (namedResultBase B)))) T) old (namedPrior b ty i) ctx)))
    (update : Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase (namedResultBase B)))) T) value (namedPrior b ty i) old ctx))) :
    Nonempty (Derivation body Γ (eqn result ty)) := by
  let R := strictAuxUpdate (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase (namedResultBase B)))) T
  let F := selectedIntrinsic R
  let key := namedTerm b.toNat ty i
  let prior := namedPrior b ty i
  have parentIntrinsic := (exact_OpenIntrinsicQuery F body α Γ ctx result key).mp parent
  have parentRow := (sameContext R (suc result) ctx key).mp parentIntrinsic
  have actual := exact_OpenContextMemoSuccessor R body α Γ value prior old ctx table update
  have agree := valueUnique (scratchRow (constantZero 2) R) value (suc result) ![key,ctx,z] actual parentRow
  have sameOutput := outputTransport R value (suc result) ![prior,old,ctx,z] agree update
  exact atStep b s B T ctx ty i result old sameOutput

private theorem withTable (b : Bool) (s : Settings) (B : Program 2) (T : Program 1)
    (ctx ty i result old : OTerm α)
    (parent : Nonempty (Derivation body Γ (windowGraph (namedResultWindow s B T) ctx result (namedTerm b.toNat ty i))))
    (table : Nonempty (Derivation body Γ
      (contextTable (strictAuxUpdate (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase (namedResultBase B)))) T) old (namedPrior b ty i) ctx))) :
    Nonempty (Derivation body Γ (eqn result ty)) := by
  let R := strictAuxUpdate (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase (namedResultBase B)))) T
  apply programCases R ![namedPrior b ty i,old,ctx,z] _
  intro β j Δ value keep update
  simp only [quadInputsRename,priorRename,zRelabel] at update
  rw [eqnRelabel]
  have parent' := renameInto parent j Δ keep
  have table' := renameInto table j Δ keep
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel,namedRename] at parent'
  simp only [contextTable,programRename,tripleInputsRename,priorRename,zRelabel] at table'
  exact atUpdate b s B T (ctx.relabel j) (ty.relabel j) (i.relabel j) (result.relabel j) (old.relabel j)
    value parent' table' update

theorem exact_OpenCoverNamedResultWindow : ExactOpenCoverNamedResultWindow := by
  intro b s B T body α Γ ctx ty i result parent
  let R := strictAuxUpdate (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase (namedResultBase B)))) T
  apply programCases (scratchTable (constantZero 2) R) ![namedPrior b ty i,ctx,z] _
  intro β j Δ old keep table
  simp only [tripleInputsRename,priorRename,zRelabel] at table
  rw [eqnRelabel]
  have parent' := renameInto parent j Δ keep
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel,namedRename] at parent'
  exact withTable b s B T (ctx.relabel j) (ty.relabel j) (i.relabel j) (result.relabel j) old parent' table

#print axioms exact_OpenCoverNamedResultWindow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultWindowProof
