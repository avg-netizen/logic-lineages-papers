module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoRowSupportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedBaseTapeForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedMemoStepSelectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverInstallNonAuxWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalGraphForwardBasicsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowSelectedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSealedWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedLambdaChildWindowProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro zeroBranchIntro zeroBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalControlGraphSupportProof (compositionValue programRename projectionValue successorValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparseFieldParser (scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck)
open NumberedWindowInternalAuxExchangeMemoStepTargets (binaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (binaryGraph unaryGraph)
open NumberedWindowInternalAuxWindowOpenTargets (contextStep windowGraph)
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeWindow)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (ActualPrecedingLambdaChild lambdaLexicalBase precedingBase)
open NumberedWindowInternalCoverLambdaLexicalShapeProof (actualLambdaLexicalShape)
open NumberedWindowInternalCoverLambdaLexicalWindowSelectedProof (exact_OpenCoverLambdaLexicalWindow)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaPrior)
open NumberedWindowInternalCoverFittedBaseTapeForwardProof (exact_OpenCoverFittedBaseTapeForward)
open NumberedWindowInternalCoverFittedMemoStepSelectionProof (exact_OpenSelectedFittedStepCases)
open NumberedWindowInternalCoverInstallNonAuxWindowProof (exact_OpenCoverInstallNonAuxWindow)
open NumberedWindowInternalCoverLocalGraphForwardBasicsProof (applyTape)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxPositive strictAuxUpdate strictAuxWindow)
open NumberedWindowInternalStrictAuxWindowThinTableProof (exact_OpenContextMemoSuccessor sameContext)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalLiteralSyntaxMemoWindow (syntaxAtKey update)
open NumberedWindowInternalLiteralCoveredMemo (contextPresent coverageAtKey coveredIntrinsic coveredMemoWindow coveredUpdate ownSeed)
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralSealedWindowProof (exact_OpenSealedWindow)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
  (exact_OpenJoinedAuxiliaryWindow joinedAuxiliaryWindow)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem baseValueAtNonAuxStep (base : Program 2) (G : Program 1)
    (ctx prior ty old : OTerm α)
    (notAux : D B Γ (unary termShape z (suc prior)))
    (step : D B Γ (contextStep (strictAuxUpdate base G) (suc ty) prior old ctx)) :
    D B Γ (programGraph base (suc ty) ![ctx,suc prior]) := by
  let raw := suc prior
  let tape : Fin 4 → OTerm α := ![prior,old,ctx,z]
  have key : D B Γ (programGraph currentKey raw tape) :=
    unaryGraph .succ (.projection 0) raw prior tape (successorValue ![prior]) (projectionValue 0 tape)
  have rejected := unaryGraph termShape currentKey z raw tape notAux key
  have picked := zeroBranchElim shapeCheck (binaryAfter base (.projection 2) currentKey)
    (strictAuxPositive G) (suc ty) tape rejected step
  apply compositionRecover base ![.projection 2,currentKey] (suc ty) tape ![ctx,raw] picked
  intro i
  exact Fin.cases (projectionValue 2 tape) (Fin.cases key (fun k => Fin.elim0 k)) i

private theorem baseValueAtNonAuxWindow (base : Program 2) (G : Program 1)
    (ctx prior ty : OTerm α)
    (notAux : D B Γ (unary termShape z (suc prior)))
    (held : D B Γ (windowAt (strictAuxWindow base G) ctx ty (suc prior))) :
    D B Γ (programGraph base (suc ty) ![ctx,suc prior]) := by
  let goal := programGraph base (suc ty) ![ctx,suc prior]
  apply exact_OpenSelectedFittedStepCases base G prior ctx ty goal held
  intro β j Δ old keep step
  simp only [goal,programRename,binaryInputsRename,sucRelabel]
  have noAux := renameInto notAux j Δ keep
  simp only [unaryRename,zRelabel,sucRelabel] at noAux
  exact baseValueAtNonAuxStep base G (ctx.relabel j) (prior.relabel j) (ty.relabel j) old noAux step

private theorem coveredStep (C : Program 3) (s : Settings) (base : Program 2) (G Va : Program 1)
    (ctx prior ty old : OTerm α)
    (notAux : D B Γ (unary termShape z (suc prior)))
    (computed : D B Γ (programGraph base (suc ty) ![ctx,suc prior]))
    (covered : D B Γ (coverageReport C s ctx (suc prior)))
    (syntaxReport : D B Γ (unary Va (suc z) (suc prior))) :
    D B Γ (contextStep (coveredUpdate C s base G Va) (suc ty) prior old ctx) := by
  let raw := suc prior
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  let verifier := conjunction contextPresent (ownSeed C s)
  have key : D B Γ (programGraph currentKey raw xs) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have atCover : D B Γ (programGraph (coverageAtKey C s) (suc z) xs) := by
    apply compositionValue verifier ![.projection 2,constantZero 4,currentKey] (suc z) xs ![ctx,z,raw] covered
    intro i
    exact Fin.cases (projectionValue 2 xs)
      (Fin.cases (zeroConstantValue xs) (Fin.cases key (fun j => Fin.elim0 j))) i
  have atSyntax : D B Γ (programGraph (syntaxAtKey Va) (suc z) xs) :=
    unaryGraph Va currentKey (suc z) raw xs syntaxReport key
  have noAux := unaryGraph termShape currentKey z raw xs notAux key
  have localValue := binaryGraph base (.projection 2) currentKey (suc ty) ctx raw xs computed
    (projectionValue 2 xs) key
  have strict : D B Γ (programGraph (strictAuxUpdate base G) (suc ty) xs) :=
    zeroBranchIntro shapeCheck (binaryAfter base (.projection 2) currentKey) (strictAuxPositive G)
      (suc ty) xs noAux localValue
  have checked : D B Γ (programGraph (update base G Va) (suc ty) xs) :=
    successorBranchIntro (normalize (syntaxAtKey Va)) (constantZero 4) (strictAuxUpdate base G)
      (suc ty) z xs (normalizeAccept (syntaxAtKey Va) xs atSyntax) strict
  exact successorBranchIntro (normalize (coverageAtKey C s)) (constantZero 4) (update base G Va)
    (suc ty) z xs (normalizeAccept (coverageAtKey C s) xs atCover) checked

private theorem coveredWindowOfNonAux (C : Program 3) (s : Settings) (base : Program 2) (G Va : Program 1)
    (ctx prior ty : OTerm α)
    (notAux : D B Γ (unary termShape z (suc prior)))
    (computed : D B Γ (programGraph base (suc ty) ![ctx,suc prior]))
    (covered : D B Γ (coverageReport C s ctx (suc prior)))
    (syntaxReport : D B Γ (unary Va (suc z) (suc prior))) :
    D B Γ (windowAt (coveredMemoWindow C s base G Va) ctx ty (suc prior)) := by
  let R := coveredUpdate C s base G Va
  apply programCases (scratchTable (constantZero 2) R) ![prior,ctx,z] _
  intro β j Δ old keep table
  simp only [tripleInputsRename,zRelabel] at table
  simp only [windowRename,sucRelabel]
  have off := renameInto notAux j Δ keep
  have code := renameInto computed j Δ keep
  have cover := renameInto covered j Δ keep
  have wellFormed := renameInto syntaxReport j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at off wellFormed
  simp only [programRename,binaryInputsRename,sucRelabel] at code
  simp only [coverageReport,programRename,tripleInputsRename,sucRelabel,zRelabel] at cover
  let c := ctx.relabel j
  let p := prior.relabel j
  let t := ty.relabel j
  have step := coveredStep C s base G Va c p t old off code cover wellFormed
  have row := exact_OpenContextMemoSuccessor R B β Δ (suc t) p old c table step
  have intrinsic := (sameContext R (suc t) c (suc p)).mpr row
  exact (exact_OpenIntrinsicQuery (coveredIntrinsic C s base G Va) B β Δ c t (suc p)).mpr intrinsic

private theorem joinedNonAux (s : Settings) (base : Program 2) (G V TV baseM : Program 1)
    (ctx prior ty : OTerm α)
    (notAux : D B Γ (unary termShape z (suc prior)))
    (computed : D B Γ (programGraph base (suc ty) ![ctx,suc prior]))
    (covered : D B Γ (coverageReport (measuredStrictCover V TV baseM) s ctx (suc prior)))
    (syntaxReport : D B Γ (unary (unitAuxSyntax V TV) (suc z) (suc prior))) :
    D B Γ (windowAt (joinedAuxiliaryWindow s base G V TV baseM) ctx ty (suc prior)) := by
  let C := measuredStrictCover V TV baseM
  have strict := exact_OpenCoverInstallNonAuxWindow base G B α Γ ctx prior ty notAux computed
  have sealed := (exact_OpenSealedWindow C s (strictAuxWindow base G) ctx ty (suc prior)).2 strict covered
  have memo := coveredWindowOfNonAux C s base G (unitAuxSyntax V TV)
    ctx prior ty notAux computed covered syntaxReport
  exact (exact_OpenJoinedAuxiliaryWindow s base G V TV baseM ctx ty (suc prior)).mpr ⟨sealed,memo⟩

/-- If both the lambda and auxiliary selectors reject the child, its
earlier lexical report and local guards give the exact decorated joined
window at the same pushed context and type. -/
theorem exact_OpenJoinedLambdaNonRecursiveChildWindow (s : Settings) (seed : Program 2)
    (T G V TV baseM : Program 1) (ctx prior ty : OTerm α)
    (notLambda : D B Γ (unary (header 2 2) z (suc prior)))
    (notAux : D B Γ (unary termShape z (suc prior)))
    (earlier : D B Γ (windowAt (numberedTypeWindow s seed T) ctx ty (suc prior)))
    (covered : D B Γ (coverageReport (measuredStrictCover V TV baseM) s ctx (suc prior)))
    (syntaxReport : D B Γ (unary (unitAuxSyntax V TV) (suc z) (suc prior))) :
    D B Γ (windowAt (joinedAuxiliaryWindow s (precedingBase s (lambdaLexicalBase s seed T)) G V TV baseM)
      ctx ty (suc prior)) := by
  let previous := precedingBase s seed
  let decorated := precedingBase s (lambdaLexicalBase s seed T)
  let H := refitGuard s T
  let goal := windowAt (joinedAuxiliaryWindow s decorated G V TV baseM) ctx ty (suc prior)
  apply exact_OpenSelectedFittedStepCases previous H prior ctx ty goal earlier
  intro β j Δ old keep step
  simp only [goal,windowRename,sucRelabel]
  have noLambda := renameInto notLambda j Δ keep
  have noAux := renameInto notAux j Δ keep
  have cover := renameInto covered j Δ keep
  have wellFormed := renameInto syntaxReport j Δ keep
  simp only [unaryRename,zRelabel,sucRelabel] at noLambda noAux wellFormed
  simp only [coverageReport,programRename,tripleInputsRename,sucRelabel,zRelabel] at cover
  let c := ctx.relabel j
  let p := prior.relabel j
  let t := ty.relabel j
  let raw := suc p
  have rawValue := baseValueAtNonAuxStep previous H c p t old noAux step
  have retape := exact_OpenCoverFittedBaseTapeForward s seed T B β Δ c raw noLambda
  have newValue : D B Δ (programGraph decorated (suc t) ![c,raw]) :=
    applyTape previous decorated ![c,raw] (suc t) retape rawValue
  exact joinedNonAux s decorated G V TV baseM c p t noAux newValue cover wellFormed

/-- Open the actual decorated joined parent with its installed outer
guard. At the literal lambda key the strict row takes the base branch,
which exposes the earlier lexical report. -/
theorem exact_OpenJoinedLambdaChildEarlier (s : Settings) (seed : Program 2)
    (T G V TV baseM : Program 1) (ctx dom q result : OTerm α) (goal : Formula α)
    (held : D B Γ (windowAt (joinedAuxiliaryWindow s (precedingBase s (lambdaLexicalBase s seed T)) G V TV baseM)
      ctx result (lambdaTerm dom q)))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (cod : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      ActualPrecedingLambdaChild s seed T B Δ (ctx.relabel j) (dom.relabel j) (q.relabel j)
        (result.relabel j) cod → D B Δ (goal.relabel j)) : D B Γ goal := by
  let base := precedingBase s (lambdaLexicalBase s seed T)
  let C := measuredStrictCover V TV baseM
  let raw := lambdaTerm dom q
  let prior := lambdaPrior dom q
  obtain ⟨sealed,_⟩ := (exact_OpenJoinedAuxiliaryWindow s base G V TV baseM ctx result raw).mp held
  obtain ⟨strict,_⟩ := (exact_OpenSealedWindow C s (strictAuxWindow base G) ctx result raw).1 sealed
  have notAux : D B Γ (unary termShape z (suc prior)) :=
    (actualLambdaLexicalShape (body := B) (Γ := Γ) dom q).auxZero
  have computed := baseValueAtNonAuxWindow base G ctx prior result notAux strict
  have lexical := exact_OpenCoverInstallNonAuxWindow base (refitGuard s T) B α Γ ctx prior result notAux computed
  exact exact_OpenCoverLambdaLexicalWindow s seed T B α Γ ctx dom q result goal lexical use

/-- For a child whose lambda and auxiliary selectors reject, the actual
decorated joined parent plus the child’s coverage and syntax reports
give descent on the very same joined window. -/
theorem exact_OpenJoinedLambdaNonRecursiveDescent (s : Settings) (seed : Program 2)
    (T G V TV baseM : Program 1) (ctx dom prior result : OTerm α) (goal : Formula α) :
    let Q := joinedAuxiliaryWindow s (precedingBase s (lambdaLexicalBase s seed T)) G V TV baseM
    D B Γ (windowAt Q ctx result (lambdaTerm dom (suc prior))) →
    D B Γ (unary (header 2 2) z (suc prior)) →
    D B Γ (unary termShape z (suc prior)) →
    D B Γ (coverageReport (measuredStrictCover V TV baseM) s (rawCons dom ctx) (suc prior)) →
    D B Γ (unary (unitAuxSyntax V TV) (suc z) (suc prior)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (cod : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (result.relabel j) (rawCons (dom.relabel j) cod)) →
      D B Δ (windowAt Q (rawCons (dom.relabel j) (ctx.relabel j)) cod (suc (prior.relabel j))) →
      D B Δ (goal.relabel j)) → D B Γ goal := by
  intro Q held notLambda notAux covered syntaxReport use
  apply exact_OpenJoinedLambdaChildEarlier s seed T G V TV baseM ctx dom (suc prior) result goal held
  intro β j Δ cod keep lexical
  have noLambda := renameInto notLambda j Δ keep
  have noAux := renameInto notAux j Δ keep
  have cover := renameInto covered j Δ keep
  have wellFormed := renameInto syntaxReport j Δ keep
  simp only [unaryRename,zRelabel,sucRelabel] at noLambda noAux wellFormed
  simp only [coverageReport,programRename,tripleInputsRename,sucRelabel,zRelabel,rawConsRename] at cover
  have earlier := lexical.pastWindow
  rw [sucRelabel] at earlier
  have child := exact_OpenJoinedLambdaNonRecursiveChildWindow s seed T G V TV baseM
    (rawCons (dom.relabel j) (ctx.relabel j)) (prior.relabel j) cod noLambda noAux earlier cover wellFormed
  exact use β j Δ cod keep lexical.resultArrow child

#print axioms exact_OpenJoinedLambdaNonRecursiveChildWindow
#print axioms exact_OpenJoinedLambdaChildEarlier
#print axioms exact_OpenJoinedLambdaNonRecursiveDescent
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedLambdaChildWindowProof
