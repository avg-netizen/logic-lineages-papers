module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundLeastTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowFunctionalGraphTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalControlGraph (programGraph)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings canonical)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowFunctionalGraphTargets (someValue)
open NumberedWindowInternalSparsePositiveOutputTargets (equivalent)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePositiveWindowTargets (AdvanceWindows)
open NumberedWindowInternalSparseCoveredWindowTargets (coveredWindow)
open NumberedWindowInternalSparseSymmetricExchangeTargets (pairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)

def fixedValue (least : Program 3) : Program 3 := .composition equalityTest ![least,someValue]

def canonicalCoordinates (W least : Program 3) : Program 3 := conjunction W (fixedValue least)

/-- Test canonicality on original packed context, type and raw class coordinates. -/
def ExactCoordinateCalibration : Prop :=
  ∀ (s : Settings) (W least : Program 3), ActualPackedWindow s W → ActualLeastCalibration s least →
    ∀ ctx ty k, evaluate (canonicalCoordinates W least) (ctx ::ᵥ ty ::ᵥ k ::ᵥ nil) =
      ((unpack ctx).any (fun g => canonical s (g,ty,k))).toNat

def ExactOpenCoordinateTest : Prop :=
  ∀ (W least : Program 3) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty k : OTerm α),
    Nonempty (Derivation body Γ (equivalent (windowAt (canonicalCoordinates W least) ctx ty k)
      (windowAt W ctx ty k ⊓ programGraph least (suc k) ![ctx,ty,k])))

def ExactCanonicalAdvance : Prop :=
  ∀ (C : Program 3) (s : Settings) (baseX : Program 2) (baseW root other : Program 3) (syntaxProg : Program 1),
    let W := coveredWindow C s baseW
    let X := guardedExchange C s (pairedExchange baseX)
    let least := packedLeastProgram C X W s
    AdvanceWindows (typedRaw5 root other W syntaxProg) least (canonicalCoordinates W least)

/-- A nonempty accepted scalar path has two canonical class states in the
same packed context and type, in the original calculus with free terms. -/
def ExactCanonicalPositive : Prop :=
  ∀ (C : Program 3) (s : Settings) (baseX : Program 2) (baseW root other : Program 3) (syntaxProg : Program 1)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty a cert b : OTerm α),
    let W := coveredWindow C s baseW
    let X := guardedExchange C s (pairedExchange baseX)
    let least := packedLeastProgram C X W s
    let raw := typedRaw5 root other W syntaxProg
    Nonempty (Derivation body Γ ((positiveAt raw least ctx ty a cert b).imp
      (windowAt (canonicalCoordinates W least) ctx ty a ⊓ windowAt (canonicalCoordinates W least) ctx ty b)))
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesTargets
