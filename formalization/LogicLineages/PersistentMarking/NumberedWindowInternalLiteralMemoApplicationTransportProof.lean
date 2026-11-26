module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoApplicationTransportCoreProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoVaryingParentProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationSelectedProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoParentIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoApplicationTransportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSupportProof (refl cancelSuc)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse)
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof (AuxRow)
open NumberedWindowInternalLiteralTypedAuxEdgeOpenProof (childAlternatives)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalLiteralTypedMemoParentIntroProof (exact_OpenTypedMemoAuxiliaryIntro)
open NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof
open NumberedWindowInternalLiteralMemoRoundApplicationSelectedProof (exact_OpenMemoSelectedApplication)
open NumberedWindowInternalLiteralPackedLeastOnProof (leastOnGraph packedLeastOn)
open NumberedWindowInternalLiteralRoundObserverTargets (observe Preserves)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)

open NumberedWindowInternalLiteralMemoVaryingParentProof
open NumberedWindowInternalLiteralMemoApplicationTransportCoreProof

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Reduce an application-image comparison to an actual original base
edge in each parent frame. All iterations are the exact selected
physical rounds, not a comparison of external result numerals. -/
theorem exact_OpenTypedMemoApplicationTransport (C : Program 3) (Base : Program 4) (s : Settings)
    (reverse : CanReverse Base)
    (stable : Preserves (recursiveTypedMemo Base) (packedLeastOn C (recursiveTypedMemo Base) s))
    (v : Bool) (ctx dom cod seed selected fixed m : OTerm α)
    (lift : BaseApplicationLiftAt Base v B Γ ctx dom cod fixed)
    (child : D B Γ (leastOnGraph C (recursiveTypedMemo Base) s ctx
      (varyingOperandType v dom cod) seed selected))
    (parent : D B Γ (leastOnGraph C (recursiveTypedMemo Base) s ctx cod
      (varyAuxiliary v dom cod seed fixed) m)) :
    D B Γ (leastOnGraph C (recursiveTypedMemo Base) s ctx cod
      (varyAuxiliary v dom cod selected fixed) m) := by
  have parentEdge : SelectedParentEdgesAt (recursiveTypedMemo Base) v B Γ ctx dom cod fixed := by
    intro β j Δ q r keep edge
    exact exact_OpenTypedMemoVaryingParent Base reverse v (ctx.relabel j) (dom.relabel j) (cod.relabel j) q r
      (fixed.relabel j) (lift β j Δ q r keep edge) edge
  exact exact_OpenSelectedParentRoundTransport C (recursiveTypedMemo Base) s stable v
    ctx dom cod seed selected fixed m parentEdge child parent

#print axioms exact_OpenTypedMemoApplicationTransport
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoApplicationTransportProof
