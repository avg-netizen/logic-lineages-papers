module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoLiftTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedDirectedXProjectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinLookupChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinSuccessorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedDirectedXGapProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename headTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc eqnRelabel zRelabel sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseFieldParser (scratchTable scratchRow)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoLiftTargets
open NumberedWindowInternalAuxExchangeMemoOpenStepChecks (exact_OpenAuxMemoStepAtGap)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (readRow tableAt)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXProjectionProof (exact_OpenSelectedMemoProjection)
open NumberedWindowInternalScratchMemoThinLookupChecks (exact_OpenThinScratchMemoLookup)
open NumberedWindowInternalScratchMemoThinSuccessorProof (exact_OpenSelectedMemoSuccessor)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem pairRelabel {β : Type} (a b : OTerm α) (j : α → β) :
    (pairTerm a b).relabel j = pairTerm (a.relabel j) (b.relabel j) := by
  simp only [pairTerm,addRelabel,mulRelabel]

theorem atGap (base : Program 2) (V : Program 1) (dom cod fn fn' arg gap : OTerm α)
    (keyEq : Nonempty (Derivation body Γ (eqn (suc (OrdinaryArithmetic.addTerm (pairTerm fn fn') gap))
      (pairTerm (auxiliaryTerm dom cod fn arg) (auxiliaryTerm dom cod fn' arg)))))
    (child : Nonempty (Derivation body Γ (accepts base V fn fn')))
    (checkSrc : Nonempty (Derivation body Γ (syntaxOne V (auxiliaryTerm dom cod fn arg))))
    (checkDst : Nonempty (Derivation body Γ (syntaxOne V (auxiliaryTerm dom cod fn' arg)))) :
    Nonempty (Derivation body Γ (accepts base V (auxiliaryTerm dom cod fn arg) (auxiliaryTerm dom cod fn' arg))) := by
  let R := step base V
  let prior := OrdinaryArithmetic.addTerm (pairTerm fn fn') gap
  apply programCases (scratchTable (constantZero 2) R) ![prior,z,z] _
  intro β j Δ old hJ table
  simp only [accepts,programRename,binaryInputsRename,sucRelabel,zRelabel,auxiliaryRename]
  have raw := renameInto child j Δ hJ
  have src := renameInto checkSrc j Δ hJ
  have dst := renameInto checkDst j Δ hJ
  have key := renameInto keyEq j Δ hJ
  simp only [accepts,programRename,binaryInputsRename,sucRelabel,zRelabel] at raw
  change Nonempty (Derivation body Δ ((unary V (suc z) (auxiliaryTerm dom cod fn arg)).relabel j)) at src
  change Nonempty (Derivation body Δ ((unary V (suc z) (auxiliaryTerm dom cod fn' arg)).relabel j)) at dst
  simp only [unaryRename,sucRelabel,zRelabel,auxiliaryRename] at src dst
  simp only [eqnRelabel,sucRelabel,addRelabel,pairRelabel,auxiliaryRename] at key
  simp only [tripleInputsRename,zRelabel,prior,addRelabel,pairRelabel] at table
  let a := auxiliaryTerm (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
  let b := auxiliaryTerm (dom.relabel j) (cod.relabel j) (fn'.relabel j) (arg.relabel j)
  let childKey := pairTerm (fn.relabel j) (fn'.relabel j)
  let before := OrdinaryArithmetic.addTerm childKey (gap.relabel j)
  have row := (exact_OpenSelectedMemoProjection R body β Δ (suc z) (fn.relabel j) (fn'.relabel j)).mp raw
  have lookup := exact_OpenThinScratchMemoLookup R body β Δ (suc z) childKey (gap.relabel j) old row table
  have updated := exact_OpenAuxMemoStepAtGap base V body β Δ (dom.relabel j) (cod.relabel j)
    (fn.relabel j) (fn'.relabel j) (arg.relabel j) (gap.relabel j) old key src dst lookup
  have rowNext := exact_OpenSelectedMemoSuccessor R body β Δ (suc z) before old table updated
  have atParent : Nonempty (Derivation body Δ (readRow R (suc z) (pairTerm a b))) :=
    headTransport (scratchRow (constantZero 2) R) (suc z) (suc before) (pairTerm a b) ![z,z] key rowNext
  exact (exact_OpenSelectedMemoProjection R body β Δ (suc z) a b).mpr atParent

#print axioms atGap

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedDirectedXGapProof
