module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveCalibrationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseCanonicalCoordinatesTargets (canonicalCoordinates)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets (ActualContextGuard ActualTypeGuard)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparsePositiveOutputTargets (equivalent)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseCoveredWindowTargets (coveredWindow)
open NumberedWindowInternalSparseSymmetricExchangeTargets (pairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)

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

/-- The original full three-address-slot positive program itself supplies
both full unary carriers without supplying any fields or validity hypotheses. -/
def ExactPositiveAddressCarriers : Prop :=
  ∀ (C : Program 3) (s : Settings) (baseX : Program 2) (baseW root other : Program 3) (syntaxProg cv tv : Program 1)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (a cert b : OTerm α),
    let W := coveredWindow C s baseW
    let X := guardedExchange C s (pairedExchange baseX)
    let least := packedLeastProgram C X W s
    let raw := typedRaw5 root other W syntaxProg
    let i := addressScalar cv tv W least
    Nonempty (Derivation body Γ ((programGraph (addressPositive cv tv raw least) (suc z) ![a,cert,b]).imp
      (unary i (suc z) a ⊓ unary i (suc z) b)))
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressTargets
