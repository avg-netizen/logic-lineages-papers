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
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

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
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
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

/-- Functionality aligns the selected successor at the given predecessor,
without opening the shape of that predecessor or of the requested goal. -/
private theorem alignStep (A : Program 2) (T : Program 1) (prior ctx result old value : OTerm α)
    (parent : Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A T) ctx result (suc prior))))
    (table : Nonempty (Derivation body Γ (contextTable (strictAuxUpdate A T) old prior ctx)))
    (update : Nonempty (Derivation body Γ (contextStep (strictAuxUpdate A T) value prior old ctx))) :
    Nonempty (Derivation body Γ (contextStep (strictAuxUpdate A T) (suc result) prior old ctx)) := by
  let R := strictAuxUpdate A T
  let F := selectedIntrinsic R
  let key := suc prior
  have parentIntrinsic := (exact_OpenIntrinsicQuery F body α Γ ctx result key).mp parent
  have parentRow := (sameContext R (suc result) ctx key).mp parentIntrinsic
  have actual := exact_OpenContextMemoSuccessor R body α Γ value prior old ctx table update
  have agree := valueUnique (scratchRow (constantZero 2) R) value (suc result) ![key,ctx,z] actual parentRow
  exact outputTransport R value (suc result) ![prior,old,ctx,z] agree update

private theorem moveParent (A : Program 2) (T : Program 1) (prior ctx result : OTerm α)
    {β : Type} (j : α → β) (Δ : List (Formula β)) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (parent : Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A T) ctx result (suc prior)))) :
    Nonempty (Derivation body Δ
      (windowGraph (strictAuxWindow A T) (ctx.relabel j) (result.relabel j) (suc (prior.relabel j)))) := by
  have lifted := renameInto parent j Δ keep
  simpa only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel] using lifted

/-- The two object binders work with an arbitrary predecessor term and an
arbitrary object goal. Thus no packed-list or head-formula normalization
occurs during program totality or graph renaming. -/
private theorem withStep (A : Program 2) (T : Program 1) (prior ctx result old : OTerm α)
    (Q : Formula α)
    (parent : Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A T) ctx result (suc prior))))
    (table : Nonempty (Derivation body Γ (contextTable (strictAuxUpdate A T) old prior ctx)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (contextStep (strictAuxUpdate A T) (suc (result.relabel j))
        (prior.relabel j) (old.relabel j) (ctx.relabel j))) →
      Nonempty (Derivation body Δ (Q.relabel j))) :
    Nonempty (Derivation body Γ Q) := by
  let R := strictAuxUpdate A T
  refine programCases R ![prior,old,ctx,z] Q ?_
  intro β j Δ value keep update
  simp only [quadInputsRename,zRelabel] at update
  have liftTable := renameInto table j Δ keep
  simp only [contextTable,programRename,tripleInputsRename,zRelabel] at liftTable
  have liftParent := moveParent A T prior ctx result j Δ keep parent
  exact next β j Δ keep (alignStep A T (prior.relabel j) (ctx.relabel j) (result.relabel j)
    (old.relabel j) value liftParent liftTable update)

private theorem selectedStepCases (A : Program 2) (T : Program 1) (prior ctx result : OTerm α)
    (Q : Formula α)
    (parent : Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A T) ctx result (suc prior))))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (contextStep (strictAuxUpdate A T) (suc (result.relabel j))
        (prior.relabel j) old (ctx.relabel j))) →
      Nonempty (Derivation body Δ (Q.relabel j))) :
    Nonempty (Derivation body Γ Q) := by
  let R := strictAuxUpdate A T
  refine programCases (scratchTable (constantZero 2) R) ![prior,ctx,z] Q ?_
  intro β j Δ old keep table
  simp only [tripleInputsRename,zRelabel] at table
  have liftParent := moveParent A T prior ctx result j Δ keep parent
  refine withStep A T (prior.relabel j) (ctx.relabel j) (result.relabel j) old (Q.relabel j) liftParent table ?_
  intro γ k Ξ retain step
  have preserved : ∀ f ∈ Γ, f.relabel (k ∘ j) ∈ Ξ := by
    intro f hf
    rw [← formulaRelabelComposition j k f]
    exact retain (f.relabel j) (keep f hf)
  simp only [Term.relabel_relabel] at step
  rw [formulaRelabelComposition j k Q]
  exact next γ (k ∘ j) Ξ (old.relabel k) preserved step

private theorem moveHeadGoal (s : Settings) (h : OTerm α) {β : Type} (j : α → β) :
    (memberGraph (headsTerm s α) h).relabel j = memberGraph (headsTerm s β) (h.relabel j) :=
  (graphRename (headsTerm s α) h j).trans
    (congrArg (fun list => memberGraph list (h.relabel j)) (numeralRename (Encodable.encode s.window.2) j))

private theorem consumeRenamedHeadRow (b : Bool) (s : Settings) (B : Program 2) (T : Program 1)
    (ctx h result : OTerm α) (tail : List (OTerm α)) (len : (h::tail).length = headArity b)
    {β : Type} (j : α → β) (Δ : List (Formula β)) (old : OTerm β)
    (row : Nonempty (Derivation body Δ (contextStep
       (strictAuxUpdate (fittedWindowBase s (grammarHeadBase s B)) (refitGuard s T))
       (suc (result.relabel j)) ((headPrior b h tail).relabel j) old (ctx.relabel j)))) :
    Nonempty (Derivation body Δ ((memberGraph (headsTerm s α) h).relabel j)) := by
  let A : Program 2 := fittedWindowBase s (grammarHeadBase s B)
  let S : Program 1 := refitGuard s T
  let R : Program 4 := strictAuxUpdate A S
  let fs : List (OTerm β) := tail.map (fun t => t.relabel j)
  let Fit : OTerm β → Prop :=
    fun prior => Nonempty (Derivation body Δ
      (contextStep R (suc (result.relabel j)) prior old (ctx.relabel j)))
  have pEq : (headPrior b h tail).relabel j = headPrior b (h.relabel j) fs :=
    priorRename b h tail j
  have step : Fit (headPrior b (h.relabel j) fs) := Eq.mp (congrArg Fit pEq) row
  have hit : Nonempty (Derivation body Δ (memberGraph (headsTerm s β) (h.relabel j))) :=
    atStep b s B T (ctx.relabel j) (h.relabel j) (result.relabel j) old fs (lengthRename b h tail j len) step
  let Goal : Formula β → Prop := fun f => Nonempty (Derivation body Δ f)
  exact Eq.mpr (congrArg Goal (moveHeadGoal s h j)) hit

theorem exact_OpenCoverHeadFittedWindow : ExactOpenCoverHeadFittedWindow := by
  intro b s B T body α Γ ctx h result tail len parent
  let A : Program 2 := fittedWindowBase s (grammarHeadBase s B)
  let S : Program 1 := refitGuard s T
  let R : Program 4 := strictAuxUpdate A S
  let prior : OTerm α := headPrior b h tail
  let Q : Formula α := memberGraph (headsTerm s α) h
  have atParent : Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A S) ctx result (suc prior))) :=
    parent
  have close : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (contextStep R (suc (result.relabel j))
        (prior.relabel j) old (ctx.relabel j))) →
      Nonempty (Derivation body Δ (Q.relabel j)) :=
    fun _ j Δ old _ row => consumeRenamedHeadRow b s B T ctx h result tail len j Δ old row
  exact selectedStepCases A S prior ctx result Q atParent close

#print axioms exact_OpenCoverHeadFittedWindow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowSelectedProof
