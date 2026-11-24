module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveCalibrationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowFunctionalGraphTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressThinDefinitions
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalEqualityTest (equalityTest)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings canonical)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowFunctionalGraphTargets (someValue)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePositiveOutputTargets (equivalent)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets (ActualContextGuard ActualTypeGuard)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)

-- Literal AST transcription without the unneeded whole round/reachability
-- theorem dependencies. Exact calibration is checked independently below.
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

def shapeChecks (cv tv : Program 1) : Program 1 :=
  conjunction addressGood (conjunction (applyUnary cv rawContext) (applyUnary tv rawResult))

def coordinateCall (W least : Program 3) : Program 1 :=
  .composition (canonicalCoordinates W least) ![rawContext,rawResult,rawLeast]

def addressScalar (cv tv : Program 1) (W least : Program 3) : Program 1 :=
  conjunction (shapeChecks cv tv) (coordinateCall W least)

def ExactAddressScalarCalibration : Prop :=
  ∀ (s : Settings) (cv tv : Program 1) (W least : Program 3), ActualContextGuard cv → ActualTypeGuard tv →
    ActualPackedWindow s W → ActualLeastCalibration s least → ActualScalarCalibration s (addressScalar cv tv W least)

/-- On the supplied literal tag-three fields, unit acceptance is exactly the
two original validity calls and coordinate canonicality, in the same calculus. -/
def ExactReportedAddressScalar : Prop :=
  ∀ (cv tv : Program 1) (W least : Program 3) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (q ctx ty k : OTerm α), let checks := unary cv (suc z) ctx ⊓
      (unary tv (suc z) ty ⊓ windowAt (canonicalCoordinates W least) ctx ty k)
    Nonempty (Derivation body Γ ((addressReport q ctx ty k).imp
      (equivalent (unary (addressScalar cv tv W least) (suc z) q) checks)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressThinDefinitions
