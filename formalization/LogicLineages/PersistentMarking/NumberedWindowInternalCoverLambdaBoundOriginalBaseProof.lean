module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundCoherenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundExtraShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBaseCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalPositiveBranchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultLandingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedMemoStepSelectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundOriginalBaseProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim zeroBranchElim)
open ID1Completion.InternalControlGraphSupportProof (successorValue projectionValue)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBodyRename)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalAuxWindowOpenTargets (contextStep windowGraph)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow strictAuxUpdate strictAuxPositive)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck)
open NumberedWindowInternalAuxExchangeMemoStepTargets (binaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedPrior)
open NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof (exact_OpenCoverNamedLeafIntrinsicShape)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeBase numberedTypeGuard numberedTypeWindow)
open NumberedWindowInternalCoverHeadWindowTargets (grammarHeadBase headBaseAt headPositive)
open NumberedWindowInternalCoverNamedResultTargets (namedResultAt namedPositiveResult storedTypeResult)
open NumberedWindowInternalCoverNamedResultLandingProof (exact_OpenNamedResultLanding)
open NumberedWindowInternalCoverFittedMemoStepSelectionProof (exact_OpenSelectedFittedStepCases)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (keepThrough)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (precedingBase)
open NumberedWindowInternalCoverLambdaBoundExtraShapeProof (actualLambdaBoundExtraShape)
open NumberedWindowInternalCoverLambdaLexicalBaseCutProof (liftRawReport)
open NumberedWindowInternalCoverLambdaLexicalPositiveBranchProof (positiveBranchCases)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private abbrev prior {α : Type} (ty i : OTerm α) := namedPrior true ty i

private theorem priorRename {β : Type} (ty i : OTerm α) (j : α → β) :
    (prior ty i).relabel j = prior (ty.relabel j) (i.relabel j) := by
  have pairTermRename (x y : OTerm α) :
      (pairTerm x y).relabel j = pairTerm (x.relabel j) (y.relabel j) := by
    simp only [pairTerm,addRelabel,mulRelabel]
  simp only [prior,namedPrior,pairTermRename,packedBodyRename,numeralRename,List.map_cons,List.map_nil]

private theorem resultPositiveAtStep (s : Settings) (B : Program 2) (T : Program 1)
    (ctx ty i result old : OTerm α)
    (step : Nonempty (Derivation body Γ (contextStep (strictAuxUpdate (precedingBase s B) (refitGuard s T))
      (suc result) (prior ty i) old ctx))) :
    Nonempty (Derivation body Γ (programGraph (namedPositiveResult (grammarHeadBase s (numberedTypeBase s B)))
      (suc result) ![ctx,namedTerm 1 ty i])) := by
  let A := precedingBase s B
  let N := grammarHeadBase s (numberedTypeBase s B)
  let raw := namedTerm 1 ty i
  let before := prior ty i
  let xs : Fin 4 → OTerm α := ![before,old,ctx,z]
  have shape := exact_OpenCoverNamedLeafIntrinsicShape true body α Γ ty i
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw before xs (successorValue ![before]) (projectionValue 0 xs)
  have notAux := unaryGraph termShape currentKey z raw xs shape.1 key
  have branch := zeroBranchElim shapeCheck (binaryAfter A (.projection 2) currentKey)
    (strictAuxPositive (refitGuard s T)) (suc result) xs notAux step
  have actualBase : Nonempty (Derivation body Γ (programGraph A (suc result) ![ctx,raw])) := by
    apply compositionRecover A ![.projection 2,currentKey] (suc result) xs ![ctx,raw] branch
    intro k
    exact Fin.cases (projectionValue 2 xs) (Fin.cases key (fun j => Fin.elim0 j)) k
  have returned := exact_OpenNamedResultLanding true s N ctx ty i result actualBase
  have taken := zeroBranchElim (onRaw (header 0 2)) (namedResultAt true N)
    (namedPositiveResult (namedResultAt true N)) (suc result) ![ctx,raw]
    (liftRawReport (header 0 2) ctx raw z (shape.2.2.2.2.2 rfl)) returned
  exact successorBranchElim (onRaw (header 1 2)) N (namedPositiveResult N) (suc result) z ![ctx,raw]
    (liftRawReport (header 1 2) ctx raw (suc z) shape.2.2.1) taken

private theorem peelOldBase (s : Settings) (B : Program 2) (ctx ty i v : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph (grammarHeadBase s (numberedTypeBase s B))
      (suc v) ![ctx,namedTerm 1 ty i]))) :
    Nonempty (Derivation body Γ (programGraph B (suc v) ![ctx,namedTerm 1 ty i])) := by
  let raw := namedTerm 1 ty i
  let N := numberedTypeBase s B
  have shape := actualLambdaBoundExtraShape (body := body) (Γ := Γ) ty i
  have tag4 := liftRawReport (header 4 2) ctx raw z shape.ordinaryZero
  have tag5 := liftRawReport (header 5 5) ctx raw z shape.numberedZero
  have passed := zeroBranchElim (onRaw (header 4 2)) (headBaseAt true s N)
    (headPositive s (headBaseAt true s N)) (suc v) ![ctx,raw] tag4 actual
  have got := zeroBranchElim (onRaw (header 5 5)) N (headPositive s N) (suc v) ![ctx,raw] tag5 passed
  exact zeroBranchElim (onRaw (header 5 5)) B (numberedTypeGuard s B) (suc v) ![ctx,raw] tag5 got

private theorem fromStep (s : Settings) (B : Program 2) (T : Program 1) (ctx ty i result old : OTerm α)
    (Q : Formula α)
    (step : Nonempty (Derivation body Γ (contextStep (strictAuxUpdate (precedingBase s B) (refitGuard s T))
      (suc result) (prior ty i) old ctx)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (v : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (programGraph B (suc v) ![ctx.relabel j,namedTerm 1 (ty.relabel j) (i.relabel j)])) →
      Nonempty (Derivation body Δ (Q.relabel j))) : Nonempty (Derivation body Γ Q) := by
  let C := grammarHeadBase s (numberedTypeBase s B)
  have taken := resultPositiveAtStep s B T ctx ty i result old step
  apply positiveBranchCases C storedTypeResult ctx (namedTerm 1 ty i) result Q taken
  intro β j Δ v keep actual _
  rw [namedRename] at actual
  exact next β j Δ v keep (peelOldBase s B (ctx.relabel j) (ty.relabel j) (i.relabel j) v actual)

theorem exact_OpenBoundOriginalBaseCases (s : Settings) (B : Program 2) (T : Program 1)
    (ctx ty i result : OTerm α) (Q : Formula α)
    (oldWin : Nonempty (Derivation body Γ (windowGraph (numberedTypeWindow s B T) ctx result (namedTerm 1 ty i))))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (v : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (programGraph B (suc v) ![ctx.relabel j,namedTerm 1 (ty.relabel j) (i.relabel j)])) →
      Nonempty (Derivation body Δ (Q.relabel j))) : Nonempty (Derivation body Γ Q) := by
  let A : Program 2 := precedingBase s B
  let S : Program 1 := refitGuard s T
  let R := strictAuxUpdate A S
  have physical : Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A S) ctx result (suc (prior ty i)))) := oldWin
  apply exact_OpenSelectedFittedStepCases A S (prior ty i) ctx result Q physical
  intro β j Δ old keep step
  let Fit : OTerm β → Prop :=
    fun prior => Nonempty (Derivation body Δ (contextStep R (suc (result.relabel j)) prior old (ctx.relabel j)))
  have row : Fit (prior (ty.relabel j) (i.relabel j)) := Eq.mp (congrArg Fit (priorRename ty i j)) step
  apply fromStep s B T (ctx.relabel j) (ty.relabel j) (i.relabel j) (result.relabel j) old (Q.relabel j) row
  intro γ g Ξ v retain actual
  have both := keepThrough j g keep retain
  simp only [Term.relabel_relabel] at actual
  rw [formulaRelabelComposition j g Q]
  exact next γ (g ∘ j) Ξ v both actual

#print axioms exact_OpenBoundOriginalBaseCases

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundOriginalBaseProof
