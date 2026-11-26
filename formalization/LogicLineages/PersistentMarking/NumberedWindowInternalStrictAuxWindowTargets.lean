module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureMemoTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalRawListRecursion (lookup)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalAuxExchangeMemoStepTargets (binaryAfter currentKey)
open NumberedWindowInternalAuxMeasureStepTargets (certain shapeCheck)
open NumberedWindowInternalAuxWindowMemoTargets (intrinsicWindow IntrinsicWindowCalibrated selectedIntrinsic)
open NumberedWindowInternalAuxWindowStepTargets (admittedChildren resultCode intrinsicQuery TypeGuardCalibrated)
open NumberedWindowInternalAuxWindowOpenTargets
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)

def strictAuxPositive (T : Program 1) : Program 4 :=
  branch (conjunction certain (admittedChildren T)) (constantZero 4) resultCode

/-- A new selected intrinsic row. Only the literal original aux header
gets the strict zero fallback; outside tag six, keep the same old
base callback at the same physical lexical context and raw key. -/
def strictAuxUpdate (base : Program 2) (T : Program 1) : Program 4 :=
  branch shapeCheck (binaryAfter base (.projection 2) currentKey) (strictAuxPositive T)

def strictAuxIntrinsic (base : Program 2) (T : Program 1) : Program 2 :=
  selectedIntrinsic (strictAuxUpdate base T)

def strictAuxWindow (base : Program 2) (T : Program 1) : Program 3 :=
  intrinsicQuery (strictAuxIntrinsic base T)

def ExactStrictAuxWindowStepCalibration : Prop :=
  ∀ (s : Settings) (base : Program 2) (T : Program 1),
    IntrinsicWindowCalibrated s base → TypeGuardCalibrated s T →
    ∀ (i old ctx : Nat),
      (∀ n, n < i+1 → evaluate lookup ((i-n) ::ᵥ old ::ᵥ nil) = intrinsicWindow s ctx n) →
      evaluate (strictAuxUpdate base T) (i ::ᵥ old ::ᵥ ctx ::ᵥ 0 ::ᵥ nil) = intrinsicWindow s ctx (i+1)

def ExactStrictAuxIntrinsicCalibration : Prop :=
  ∀ (s : Settings) (base : Program 2) (T : Program 1),
    IntrinsicWindowCalibrated s base → TypeGuardCalibrated s T →
    IntrinsicWindowCalibrated s (strictAuxIntrinsic base T)

def ExactStrictAuxWindowCalibration : Prop :=
  ∀ (s : Settings) (base : Program 2) (T : Program 1),
    IntrinsicWindowCalibrated s base → TypeGuardCalibrated s T →
    ActualPackedWindow s (strictAuxWindow base T)

/-- The two child windows are at the same genuine lexical context,
not a fresh/protected-port extension. -/
def strictAuxChildren {α : Type} (base : Program 2) (T : Program 1)
    (ctx dom cod fn arg : OTerm α) : Formula α :=
  (unary T (suc z) dom ⊓ unary T (suc z) cod) ⊓
    (windowGraph (strictAuxWindow base T) ctx (rawCons dom cod) fn ⊓
      windowGraph (strictAuxWindow base T) ctx dom arg)

def ExactOpenStrictAuxWindowRow : Prop :=
  ∀ (base : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx dom cod fn arg old : OTerm α),
    let R := strictAuxUpdate base T
    let prior := memoPrior dom cod fn arg
    Nonempty (Derivation body Γ (contextTable R old prior ctx)) →
    Nonempty (Derivation body Γ (contextStep R (suc cod) prior old ctx)) →
    Nonempty (Derivation body Γ (strictAuxChildren base T ctx dom cod fn arg))

end LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowTargets
