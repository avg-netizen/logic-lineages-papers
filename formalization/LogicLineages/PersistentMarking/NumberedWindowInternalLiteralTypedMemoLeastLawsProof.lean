module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoUnfoldingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedCanonicalChildProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoLeastLawsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (CoveredEndpoints WindowEndpoints exact_OpenLeastOnPreserves)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse)
open NumberedWindowInternalLiteralEdgeOnCoverProof (KeepsCover)
open NumberedWindowInternalLiteralChildGuardEdgeProof (childGuardObservers)
open NumberedWindowInternalLiteralAuxProfileObserversProof (unaryObserver)
open NumberedWindowInternalLiteralTypedRecursiveLeastStabilityProof (exact_OpenRecursiveDiagonalFromRounds)
open NumberedWindowInternalLiteralTypedMemoStageProof (typedMemoStage)
open NumberedWindowInternalLiteralTypedDualMemoProof
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (fullAuxiliaryDecorator)
open NumberedWindowInternalThinRoundExhaustionTargets (CountLengthBound)
open NumberedWindowInternalThinUncoveredCountTargets (InternalStrictDecrease)

def memoFilteredLeast (C : Program 3) (Base : Program 4) (s : Settings) : Program 3 :=
  guardedLeast (headerLeast (fullAuxiliaryDecorator (packedLeastOn C (recursiveTypedMemo Base) s)))

def MemoSelectedReports (C : Program 3) (s : Settings) (Base : Program 4) : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty q k : OTerm α),
    D B Γ (leastOnGraph C (recursiveTypedMemo Base) s ctx ty q k) →
    D B Γ (programGraph (memoFilteredLeast C Base s) (suc k) ![ctx,ty,q])

/-- The same selected memo supplies ordinary window endpoints, stable
primitive least values, and the full physical least report including the
original child-class checks at every nested auxiliary. -/
theorem exact_OpenTypedMemoLeastLaws (count : CountLengthBound) (strict : InternalStrictDecrease)
    (C W : Program 3) (s : Settings) (Base : Program 4)
    (guards : ∀ O ∈ childGuardObservers, Preserves Base O)
    (reverse : CanReverse Base) (cover : KeepsCover C s Base)
    (endpoints : CoveredEndpoints C s Base) (windows : WindowEndpoints W Base) :
    WindowEndpoints W (recursiveTypedMemo Base) ∧
    Preserves (recursiveTypedMemo Base) (packedLeastOn C (recursiveTypedMemo Base) s) ∧
    MemoSelectedReports C s Base := by
  let R := typedMemoStage Base
  let E := recursiveTypedMemo Base
  have original := exact_OpenDualContextMemoBase Base R
  have win : WindowEndpoints W E := by
    intro B α Γ ctx ty q r edge
    exact windows B α Γ ctx ty q r (original B α Γ ctx ty q r edge)
  have cv : CoveredEndpoints C s E := by
    intro B α Γ ctx ty q r edge
    exact endpoints B α Γ ctx ty q r (original B α Γ ctx ty q r edge)
  have back := exact_OpenDualContextMemoReverse Base R reverse
  have same := exact_OpenDualContextMemoCover C s Base R cover
  have shape := guards (unaryObserver termShape) (by simp [childGuardObservers])
  have unfolds := exact_OpenRecursiveTypedMemoUnfolds Base shape
  refine ⟨win,exact_OpenLeastOnPreserves count strict C E s back same cv,?_⟩
  intro B α Γ ctx ty q k actual
  exact exact_OpenRecursiveDiagonalFromRounds count strict C Base E s unfolds guards back same cv ctx ty q k actual

#print axioms exact_OpenTypedMemoLeastLaws
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoLeastLawsProof
