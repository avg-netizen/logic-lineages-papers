module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedMemoStepSelectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowSelectedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBodyRename rawConsRename)
open NumberedWindowInternalCoverTypeLeavesOpenDataProof (termRename)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalAuxExchangeMemoStepTargets (binaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck)
open NumberedWindowInternalAuxWindowOpenTargets (contextStep windowGraph)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow strictAuxUpdate strictAuxPositive)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverHeadWindowTargets (headPrior)
open NumberedWindowInternalCoverHeadWindowShapeProof (exact_OpenCoverHeadShape)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (precedingBase lambdaLexicalBase)
open NumberedWindowInternalCoverFittedMemoStepSelectionProof (exact_OpenSelectedFittedStepCases)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverSingletonTypeArgumentTargets (singletonTypeKey)
open NumberedWindowInternalCoverSingletonTypeWindowBaseProof (actualOrdinarySingletonType)
open NumberedWindowInternalCoverSingletonTypeWindowTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private abbrev prior {α : Type} (h ty : OTerm α) := headPrior false h [singletonTypeKey ty]

private abbrev finalBase (s : Settings) (B : Program 2) (T : Program 1) :=
  precedingBase s (lambdaLexicalBase s (ordinarySingletonKBase s B) T)

private theorem priorRename {β : Type} (h ty : OTerm α) (j : α → β) :
    (prior h ty).relabel j = prior (h.relabel j) (ty.relabel j) := by
  have pairTermRename (x y : OTerm α) :
      (pairTerm x y).relabel j = pairTerm (x.relabel j) (y.relabel j) := by
    simp only [pairTerm,addRelabel,mulRelabel]
  simp only [prior,headPrior,pairTermRename,packedBodyRename,numeralRename,List.map_cons,List.map_nil,
    singletonTypeKey,rawConsRename,termRename,zRelabel]

private theorem atStep (s : Settings) (B : Program 2) (T : Program 1)
    (ctx h ty result old : OTerm α)
    (actual : Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate (finalBase s B T) (refitGuard s T)) (suc result) (prior h ty) old ctx))) :
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) := by
  let before := prior h ty
  let arg := singletonTypeKey ty
  let raw := ordinaryKey h arg
  let xs : Fin 4 → OTerm α := ![before,old,ctx,z]
  let A := finalBase s B T
  have shape := exact_OpenCoverHeadShape false body α Γ h [arg] rfl
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw before xs (successorValue ![before]) (projectionValue 0 xs)
  have noAux := unaryGraph termShape currentKey z raw xs shape.notAux key
  have picked := zeroBranchElim shapeCheck (binaryAfter A (.projection 2) currentKey)
    (strictAuxPositive (refitGuard s T)) (suc result) xs noAux actual
  have base : Nonempty (Derivation body Γ (programGraph A (suc result) ![ctx,raw])) := by
    apply compositionRecover A ![.projection 2,currentKey] (suc result) xs ![ctx,raw] picked
    intro i
    exact Fin.cases (projectionValue 2 xs) (Fin.cases key (fun j => Fin.elim0 j)) i
  exact actualOrdinarySingletonType s B T ctx h ty result base

private theorem storedKGoal (s : Settings) (ty : OTerm α) {β : Type} (j : α → β) :
    (memberGraph (typesTerm s α) ty).relabel j = memberGraph (typesTerm s β) (ty.relabel j) :=
  (graphRename (typesTerm s α) ty j).trans
    (congrArg (fun list => memberGraph list (ty.relabel j)) (numeralRename (Encodable.encode s.types) j))

theorem exact_OpenCoverOrdinarySingletonKWindow : ExactOpenCoverOrdinarySingletonKWindow := by
  intro s B T body α Γ ctx h ty result actual
  let A : Program 2 := finalBase s B T
  let S : Program 1 := refitGuard s T
  let R : Program 4 := strictAuxUpdate A S
  let Q : Formula α := memberGraph (typesTerm s α) ty
  have parent : Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A S) ctx result (suc (prior h ty)))) :=
    actual
  apply exact_OpenSelectedFittedStepCases A S (prior h ty) ctx result Q parent
  intro β j Δ old _ step
  let Fit : OTerm β → Prop := fun before => Nonempty (Derivation body Δ
    (contextStep R (suc (result.relabel j)) before old (ctx.relabel j)))
  have row : Fit (prior (h.relabel j) (ty.relabel j)) := Eq.mp (congrArg Fit (priorRename h ty j)) step
  have hit := atStep s B T (ctx.relabel j) (h.relabel j) (ty.relabel j) (result.relabel j) old row
  let Want : Formula β → Prop := fun f => Nonempty (Derivation body Δ f)
  exact Eq.mpr (congrArg Want (storedKGoal s ty j)) hit

#print axioms exact_OpenCoverOrdinarySingletonKWindow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowSelectedProof
