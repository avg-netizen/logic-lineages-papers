module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedMemoStepSelectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowSelectedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalControlGraphSupportProof (successorValue projectionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
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
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalAuxExchangeMemoStepTargets (binaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck)
open NumberedWindowInternalAuxWindowOpenTargets (contextStep windowGraph)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow strictAuxUpdate strictAuxPositive)
open NumberedWindowInternalCoverFittedInductionDispatchTargets (fittedWindowBase)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverHeadWindowTargets (grammarHeadBase headPrior)
open NumberedWindowInternalCoverHeadWindowShapeProof (exact_OpenCoverHeadShape)
open NumberedWindowInternalCoverNumberedTypeWindowBaseProof (exact_OpenCoverNumberedTypeIntrinsic)
open NumberedWindowInternalCoverFittedMemoStepSelectionProof (exact_OpenSelectedFittedStepCases)
open NumberedWindowInternalCoverNumberedTypeWindowTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem priorRename {β : Type} (h ty k l r : OTerm α) (j : α → β) :
    (numberedTypePrior h ty k l r).relabel j =
      numberedTypePrior (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j) := by
  have pairTermRename (x y : OTerm α) :
      (pairTerm x y).relabel j = pairTerm (x.relabel j) (y.relabel j) := by
    simp only [pairTerm,addRelabel,mulRelabel]
  simp only [numberedTypePrior,headPrior,pairTermRename,packedBodyRename,numeralRename,List.map_cons,List.map_nil]

private abbrev finalBase (s : Settings) (B : Program 2) :=
  fittedWindowBase s (grammarHeadBase s (numberedTypeBase s B))

private theorem atStep (s : Settings) (B : Program 2) (T : Program 1)
    (ctx h ty k l r result old : OTerm α)
    (step : Nonempty (Derivation body Γ
      (contextStep (strictAuxUpdate (finalBase s B) (refitGuard s T))
        (suc result) (numberedTypePrior h ty k l r) old ctx))) :
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) := by
  let prior := numberedTypePrior h ty k l r
  let raw := numberedTerm h ty k l r
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  let A := finalBase s B
  have shape := exact_OpenCoverHeadShape true body α Γ h [ty,k,l,r] rfl
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have noAux := unaryGraph termShape currentKey z raw xs shape.notAux key
  have picked := zeroBranchElim shapeCheck (binaryAfter A (.projection 2) currentKey)
    (strictAuxPositive (refitGuard s T)) (suc result) xs noAux step
  have known : Nonempty (Derivation body Γ (programGraph A (suc result) ![ctx,raw])) := by
    apply compositionRecover A ![.projection 2,currentKey] (suc result) xs ![ctx,raw] picked
    intro i
    exact Fin.cases (projectionValue 2 xs) (Fin.cases key (fun j => Fin.elim0 j)) i
  exact exact_OpenCoverNumberedTypeIntrinsic s B body α Γ ctx h ty k l r result known

private theorem moveTypeGoal (s : Settings) (ty : OTerm α) {β : Type} (j : α → β) :
    (memberGraph (typesTerm s α) ty).relabel j = memberGraph (typesTerm s β) (ty.relabel j) :=
  (graphRename (typesTerm s α) ty j).trans
    (congrArg (fun list => memberGraph list (ty.relabel j)) (numeralRename (Encodable.encode s.types) j))

private theorem closeRow (s : Settings) (B : Program 2) (T : Program 1)
    (ctx h ty k l r result : OTerm α) {β : Type} (j : α → β) (Δ : List (Formula β)) (old : OTerm β)
    (row : Nonempty (Derivation body Δ (contextStep (strictAuxUpdate (finalBase s B) (refitGuard s T))
      (suc (result.relabel j)) ((numberedTypePrior h ty k l r).relabel j) old (ctx.relabel j)))) :
    Nonempty (Derivation body Δ ((memberGraph (typesTerm s α) ty).relabel j)) := by
  let R : Program 4 := strictAuxUpdate (finalBase s B) (refitGuard s T)
  let Fit : OTerm β → Prop :=
    fun prior => Nonempty (Derivation body Δ (contextStep R (suc (result.relabel j)) prior old (ctx.relabel j)))
  have exactPrior := priorRename h ty k l r j
  have step : Fit (numberedTypePrior (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)) :=
    Eq.mp (congrArg Fit exactPrior) row
  have hit : Nonempty (Derivation body Δ (memberGraph (typesTerm s β) (ty.relabel j))) :=
    atStep s B T (ctx.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j)
      (r.relabel j) (result.relabel j) old step
  let Goal : Formula β → Prop := fun f => Nonempty (Derivation body Δ f)
  exact Eq.mpr (congrArg Goal (moveTypeGoal s ty j)) hit

theorem exact_OpenCoverNumberedTypeWindow : ExactOpenCoverNumberedTypeWindow := by
  intro s B T body α Γ ctx h ty k l r result parent
  let A : Program 2 := finalBase s B
  let S : Program 1 := refitGuard s T
  let R : Program 4 := strictAuxUpdate A S
  let prior : OTerm α := numberedTypePrior h ty k l r
  let Q : Formula α := memberGraph (typesTerm s α) ty
  have atParent : Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A S) ctx result (suc prior))) :=
    parent
  have next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (contextStep R (suc (result.relabel j))
        (prior.relabel j) old (ctx.relabel j))) →
      Nonempty (Derivation body Δ (Q.relabel j)) :=
    fun _ j Δ old _ row => closeRow s B T ctx h ty k l r result j Δ old row
  exact exact_OpenSelectedFittedStepCases A S prior ctx result Q atParent next

#print axioms exact_OpenCoverNumberedTypeWindow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowSelectedProof
