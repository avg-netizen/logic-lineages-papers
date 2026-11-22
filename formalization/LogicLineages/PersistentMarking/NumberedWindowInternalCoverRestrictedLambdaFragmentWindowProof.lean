module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedLambdaFragmentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedLambdaFragmentBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedMemoStepSelectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBaseCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedLambdaSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedLambdaFragmentWindowProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph contextStep)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxUpdate strictAuxWindow strictAuxPositive)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck)
open NumberedWindowInternalAuxExchangeMemoStepTargets (binaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaPrior)
open NumberedWindowInternalCoverSharedLambdaSyntaxProof (lambdaPriorRename)
open NumberedWindowInternalCoverAuxFragmentGuardTargets (fragmentGuard)
open NumberedWindowInternalCoverFittedMemoStepSelectionProof (exact_OpenSelectedFittedStepCases)
open NumberedWindowInternalCoverLambdaLexicalShapeProof (actualLambdaLexicalShape)
open NumberedWindowInternalCoverLambdaLexicalBaseCutProof (actualLambdaPositive)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (precedingBase lambdaLexicalBase)
open NumberedWindowInternalCoverRestrictedLambdaFragmentBaseProof (guardAtPositiveLambda)
open NumberedWindowInternalCoverRestrictedLambdaFragmentTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private abbrev physicalBase (s : Settings) (B : Program 2) (T : Program 1) :=
  precedingBase s (lambdaLexicalBase s (lambdaFragmentBase B) T)

private theorem atStep (s : Settings) (B : Program 2) (T : Program 1) (ctx dom q out old : OTerm α)
    (step : Nonempty (Derivation body Γ (contextStep (strictAuxUpdate (physicalBase s B T) (refitGuard s T))
      (suc out) (lambdaPrior dom q) old ctx))) :
    Nonempty (Derivation body Γ (unary fragmentGuard (suc z) q)) := by
  let prior := lambdaPrior dom q
  let raw := lambdaTerm dom q
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  let A : Program 2 := physicalBase s B T
  let S : Program 1 := refitGuard s T
  have shape := actualLambdaLexicalShape (body := body) (Γ := Γ) dom q
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have noAux := unaryGraph termShape currentKey z raw xs shape.auxZero key
  have choice := zeroBranchElim shapeCheck (binaryAfter A (.projection 2) currentKey)
    (strictAuxPositive S) (suc out) xs noAux step
  have base : Nonempty (Derivation body Γ (programGraph A (suc out) ![ctx,raw])) := by
    apply compositionRecover A ![.projection 2,currentKey] (suc out) xs ![ctx,raw] choice
    intro i
    exact Fin.cases (projectionValue 2 xs) (Fin.cases key (fun j => Fin.elim0 j)) i
  have selected := actualLambdaPositive s (lambdaFragmentBase B) T ctx dom q out base
  exact guardAtPositiveLambda s B T ctx dom q out selected

private theorem consumeRenamed (s : Settings) (B : Program 2) (T : Program 1)
    (ctx dom q out : OTerm α) {β : Type} (j : α → β) (Δ : List (Formula β)) (old : OTerm β)
    (step : Nonempty (Derivation body Δ (contextStep (strictAuxUpdate (physicalBase s B T) (refitGuard s T))
      (suc (out.relabel j)) ((lambdaPrior dom q).relabel j) old (ctx.relabel j)))) :
    Nonempty (Derivation body Δ ((unary fragmentGuard (suc z) q).relabel j)) := by
  let R : Program 4 := strictAuxUpdate (physicalBase s B T) (refitGuard s T)
  let Fit : OTerm β → Prop := fun prior => Nonempty (Derivation body Δ
    (contextStep R (suc (out.relabel j)) prior old (ctx.relabel j)))
  have same : (lambdaPrior dom q).relabel j = lambdaPrior (dom.relabel j) (q.relabel j) :=
    lambdaPriorRename dom q j
  have row : Fit (lambdaPrior (dom.relabel j) (q.relabel j)) := Eq.mp (congrArg Fit same) step
  have guard := atStep s B T (ctx.relabel j) (dom.relabel j) (q.relabel j) (out.relabel j) old row
  simpa only [unaryRename,sucRelabel,zRelabel] using guard

theorem exact_OpenCoverRestrictedLambdaFragmentWindow : ExactOpenCoverRestrictedLambdaFragmentWindow := by
  intro s B T body α Γ ctx dom q out actual
  let A : Program 2 := physicalBase s B T
  let S : Program 1 := refitGuard s T
  let R : Program 4 := strictAuxUpdate A S
  let prior : OTerm α := lambdaPrior dom q
  let Z : Formula α := unary fragmentGuard (suc z) q
  have parent : Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A S) ctx out (suc prior))) :=
    actual
  have finish : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (contextStep R (suc (out.relabel j))
        (prior.relabel j) old (ctx.relabel j))) →
      Nonempty (Derivation body Δ (Z.relabel j)) :=
    fun _ j Δ old _ step => consumeRenamed s B T ctx dom q out j Δ old step
  exact exact_OpenSelectedFittedStepCases A S prior ctx out Z parent finish

#print axioms exact_OpenCoverRestrictedLambdaFragmentWindow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedLambdaFragmentWindowProof
