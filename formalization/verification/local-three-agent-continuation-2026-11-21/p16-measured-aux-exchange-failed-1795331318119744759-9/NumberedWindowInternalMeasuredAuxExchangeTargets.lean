module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoGuardedTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxExchangeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalEqualityTest (equalityTest)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated factoredCover)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalAuxExchangeMemoLiftTargets (syntaxOne)
open NumberedWindowInternalAuxExchangeMemoGuardedTargets (accepted)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseSymmetricExchangeTargets (pairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)

def atSlot (M : Program 1) (i : Fin 2) : Program 2 :=
  .composition M (fun _ : Fin 1 => .projection i)

def compareMeasurements (M : Program 1) : Program 2 :=
  .composition equalityTest ![atSlot M 0,atSlot M 1]

def measuredExchange (M : Program 1) (X : Program 2) : Program 2 :=
  conjunction X (compareMeasurements M)

/-- The selected symmetric/cover-guarded wrapper remains on the outside. -/
def measuredFactoredExchange (s : Settings) (baseX : Program 2) (V baseM : Program 1)
    (P : Program 2) (G : Program 3) : Program 2 :=
  let M := selectedMeasure (measureUpdate baseM P)
  let C := factoredCover V M G
  guardedExchange C s (pairedExchange (measuredExchange M (selected (step baseX V))))

def ExactMeasuredExchangeCalibration : Prop :=
  ∀ (s : Settings) (M : Program 1) (X : Program 2),
    TermMeasureCalibrated M → ActualTermExchange s X → ActualTermExchange s (measuredExchange M X)

/-- The parent's cover comparison and measure comparison are derived inside
the calculus. The two parent syntax reports are the only added premises. -/
def ExactOpenMeasuredFactoredAuxLift : Prop :=
  ∀ (s : Settings) (baseX : Program 2) (V baseM : Program 1) (P : Program 2) (G : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (dom cod fn fn' arg : OTerm α),
    let X := measuredFactoredExchange s baseX V baseM P G
    let a := auxiliaryTerm dom cod fn arg
    let b := auxiliaryTerm dom cod fn' arg
    Nonempty (Derivation body Γ
      ((accepted X fn fn' ⊓ (syntaxOne V a ⊓ syntaxOne V b)).imp (accepted X a b)))

end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxExchangeTargets
