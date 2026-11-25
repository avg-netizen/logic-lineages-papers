module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicFallbackDecoderProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxDescendingDecoderProof

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxDescendingDecoderProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFuelInductionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRunChildProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxGeneralOwnFuelProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (addSucc symm cancelSuc trans)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF addRelabel)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.InternalOriginalOrderProof (orderCases)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename)
open NumberedWindowInternalSparseRawRun (ownRun iterateState)
open NumberedWindowInternalSparseRawRunLiftOwnProof (initialTerm witnessStrict)
open NumberedWindowInternalLiteralFunctionRunPeelProof (functionRemaining)
open NumberedWindowInternalLiteralAuxRunChildProof (ChildTerminal)
open NumberedWindowInternalLiteralAuxFallback (auxiliaryFallback)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralAuxDescendingDecoderProof (exact_OpenAuxiliaryDecoderWith)
open NumberedWindowInternalLiteralDescendingFirstTickProof (FrameDecoder fallbackDecoder)
open NumberedWindowInternalLiteralAtomicTickNumericProof (atomicFallback)
open NumberedWindowInternalLiteralAtomicFallbackDecoderProof (exact_OpenAtomicFallbackDecoder)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralFuelInductionProof (exact_OpenTrimmedOwnRunWith)
open NumberedWindowInternalLiteralExcessTerminalProof (LitRun TerminalOne runRename)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem remainingRename {β : Type} (child : OTerm α) (j : α → β) :
    (functionRemaining child).relabel j = functionRemaining (child.relabel j) := by
  simp only [functionRemaining,pairTerm,rawConsRename,addRelabel,mulRelabel,numeralRename,zRelabel]

/-- This is the actual open own-fuel converse for a decoded function
child. It uses the physically selected descending fallback and the
original strong induction derivation, not numerical truth reflection. -/
theorem exact_OpenFunctionChildOwnFuelWith (p other : Program 3) (decode : FrameDecoder other) (q child r : OTerm α)
    (actual : D B Γ (ChildTerminal p other q child r)) :
    D B Γ (bit (ownRun p (auxiliaryFallback other)) ![q,child,r]) := by
  let F := auxiliaryFallback other
  let goal := bit (ownRun p F) ![q,child,r]
  have enough : D B Γ (ltF child (suc (functionRemaining child))) := witnessStrict child
  apply orderCases Γ child (suc (functionRemaining child)) goal enough
  intro β j Δ gap keep e
  let s := q.relabel j
  let w := child.relabel j
  let t := r.relabel j
  rw [sucRelabel,remainingRename] at e
  obtain ⟨d⟩ := e
  have shift : D B Δ (eqn (functionRemaining w) (add w gap)) :=
    ⟨symm (cancelSuc (trans (symm (addSucc w gap)) d))⟩
  have retained := renameInto (show D B Γ (LitRun p F TerminalOne (functionRemaining child) q child r) from actual)
    j Δ keep
  simp only [runRename,remainingRename,stateRename,sucRelabel,zRelabel] at retained
  have h : D B Δ (LitRun p F TerminalOne (add w gap) s w t) :=
    headTransport (iterateState p F) TerminalOne (functionRemaining w) (add w gap)
      ![initialTerm (![s,w,t])] shift retained
  simp only [goal,bit,programRename,tripleInputsRename,sucRelabel,zRelabel]
  exact exact_OpenTrimmedOwnRunWith p F (exact_OpenAuxiliaryDecoderWith other decode) s w t gap h

/-- The exact descendant has its own fuel on the actual inner atom
fallback, not a numerically interchangeable callback. -/
theorem exact_OpenAtomicFunctionChildOwnFuel (p other : Program 3) (q child r : OTerm α)
    (actual : D B Γ (ChildTerminal p (atomicFallback (fallback other)) q child r)) :
    D B Γ (bit (ownRun p (auxiliaryFallback (atomicFallback (fallback other)))) ![q,child,r]) :=
  exact_OpenFunctionChildOwnFuelWith p (atomicFallback (fallback other))
    (exact_OpenAtomicFallbackDecoder (fallback other) (fallbackDecoder other)) q child r actual

#print axioms exact_OpenFunctionChildOwnFuelWith
#print axioms exact_OpenAtomicFunctionChildOwnFuel
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxGeneralOwnFuelProof
