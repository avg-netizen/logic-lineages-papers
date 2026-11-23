module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaFrameTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaRun
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawLambdaFrame
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalSparseRawTick (chosenTick)
open NumberedWindowInternalSparseRawTickTargets (ActualFallback stateTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)

def lambdaTest : Program 3 := onRaw witnessShape 1

/-- Install just the exposed literal tag-one branch in the same physical
fallback slot; other original raw contexts remain in the supplied callback. -/
def lambdaFallback (other : Program 3) : Program 3 := branch lambdaTest other chosenFrame

def ExactLambdaFallbackFit : Prop :=
  ∀ other : Program 3, ActualFallback other → ActualFallback (lambdaFallback other)

def ExactOpenLambdaContextTick : Prop :=
  ∀ (B : Positive (Fin 1)) (p other : Program 3) (α : Type) (Γ : List (Formula α))
    (flag dom src child dst : OTerm α),
    let tape := liftedTape dom src child dst
    let initial := stateTerm flag (frameValueTerm (tape 0) (tape 1) (tape 2))
    let final := stateTerm z (frameValueTerm src child dst)
    Nonempty (Derivation B Γ (programGraph (chosenTick p (lambdaFallback other)) final ![initial]))

def ExactOpenLambdaOwnRunLift : Prop :=
  ∀ (B : Positive (Fin 1)) (p other : Program 3) (α : Type) (Γ : List (Formula α))
    (dom src child dst k : OTerm α),
    let run := ownRun p (lambdaFallback other)
    Nonempty (Derivation B Γ (programGraph run (suc k) ![src,child,dst])) →
    Nonempty (Derivation B Γ (programGraph run (suc k) (liftedTape dom src child dst)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaRun
