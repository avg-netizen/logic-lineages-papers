module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaControlTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBaseCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalPositiveBranchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedMemoStepSelectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedLambdaSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaControlProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (successorValue projectionValue)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalAuxWindowOpenTargets (contextStep windowGraph)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow strictAuxUpdate strictAuxPositive)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck)
open NumberedWindowInternalAuxExchangeMemoStepTargets (binaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaPrior)
open NumberedWindowInternalCoverSharedLambdaSyntaxProof (lambdaPriorRename)
open NumberedWindowInternalCoverFittedMemoStepSelectionProof (exact_OpenSelectedFittedStepCases)
open NumberedWindowInternalCoverLambdaLexicalShapeProof (actualLambdaLexicalShape)
open NumberedWindowInternalCoverLambdaLexicalBaseCutProof (actualLambdaPositive)
open NumberedWindowInternalCoverLambdaLexicalPositiveBranchProof (positiveBranchCases)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof (lambdaRename)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (keepThrough)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets
open NumberedWindowInternalCoverLambdaControlTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private abbrev finalBase (s : Settings) (B : Program 2) (T : Program 1) :=
  precedingBase s (lambdaLexicalBase s B T)

private theorem positiveAtStep (s : Settings) (B : Program 2) (T : Program 1)
    (ctx ty q res old : OTerm α)
    (step : Nonempty (Derivation body Γ (contextStep (strictAuxUpdate (finalBase s B T) (refitGuard s T))
      (suc res) (lambdaPrior ty q) old ctx))) :
    Nonempty (Derivation body Γ (programGraph (lambdaPositive s B T) (suc res) ![ctx,lambdaTerm ty q])) := by
  let prior := lambdaPrior ty q
  let raw := lambdaTerm ty q
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  let A := finalBase s B T
  have shape := actualLambdaLexicalShape (body := body) (Γ := Γ) ty q
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have noAux := unaryGraph termShape currentKey z raw xs shape.auxZero key
  have picked := zeroBranchElim shapeCheck (binaryAfter A (.projection 2) currentKey)
    (strictAuxPositive (refitGuard s T)) (suc res) xs noAux step
  have base : Nonempty (Derivation body Γ (programGraph A (suc res) ![ctx,raw])) := by
    apply compositionRecover A ![.projection 2,currentKey] (suc res) xs ![ctx,raw] picked
    intro i
    exact Fin.cases (projectionValue 2 xs) (Fin.cases key (fun j => Fin.elim0 j)) i
  exact actualLambdaPositive s B T ctx ty q res base

private theorem openAtRenamedStep (s : Settings) (B : Program 2) (T : Program 1)
    (ctx ty q res : OTerm α) {β : Type} (j : α → β) (Δ : List (Formula β)) (old : OTerm β)
    (step : Nonempty (Derivation body Δ (contextStep (strictAuxUpdate (finalBase s B T) (refitGuard s T))
      (suc (res.relabel j)) ((lambdaPrior ty q).relabel j) old (ctx.relabel j)))) :
    Nonempty (Derivation body Δ (programGraph (lambdaPositive s B T)
      (suc (res.relabel j)) ![ctx.relabel j,lambdaTerm (ty.relabel j) (q.relabel j)])) := by
  let R : Program 4 := strictAuxUpdate (finalBase s B T) (refitGuard s T)
  let Fit : OTerm β → Prop := fun prior => Nonempty (Derivation body Δ
    (contextStep R (suc (res.relabel j)) prior old (ctx.relabel j)))
  have row : Fit (lambdaPrior (ty.relabel j) (q.relabel j)) :=
    Eq.mp (congrArg Fit (lambdaPriorRename ty q j)) step
  exact positiveAtStep s B T (ctx.relabel j) (ty.relabel j) (q.relabel j) (res.relabel j) old row

theorem exact_OpenCoverLambdaPositiveControl : ExactOpenCoverLambdaPositiveControl := by
  intro s B T body α Γ ctx ty q res Q parent next
  let A : Program 2 := finalBase s B T
  let S : Program 1 := refitGuard s T
  let prior : OTerm α := lambdaPrior ty q
  have physical : Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A S) ctx res (suc prior))) := parent
  apply exact_OpenSelectedFittedStepCases A S prior ctx res Q physical
  intro β j Δ old keep step
  have positive := openAtRenamedStep s B T ctx ty q res j Δ old step
  apply positiveBranchCases B (lambdaCheckedDomain s B T) (ctx.relabel j)
    (lambdaTerm (ty.relabel j) (q.relabel j)) (res.relabel j) (Q.relabel j) positive
  intro γ k Ξ out retain control _
  rw [lambdaRename] at control
  have actual : Nonempty (Derivation body Ξ (programGraph B (suc out)
      ![ctx.relabel (k ∘ j),lambdaTerm (ty.relabel (k ∘ j)) (q.relabel (k ∘ j))])) := by
    simpa only [Term.relabel_relabel] using control
  rw [formulaRelabelComposition j k Q]
  exact next γ (k ∘ j) Ξ out (keepThrough j k keep retain) actual

#print axioms exact_OpenCoverLambdaPositiveControl

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaControlProof
