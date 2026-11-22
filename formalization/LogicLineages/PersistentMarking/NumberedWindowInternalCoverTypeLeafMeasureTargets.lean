module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasureTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalPairing (pairing)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalCoverSharedRecursionTargets (lambdaDispatch sharedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (certain)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)

/-- Original standard (depth, width) encoding, not a fresh surrogate constant. -/
def leafPair10 : Program 1 := .composition pairing ![literal 1 1,constantZero 1]

/-- Only the canonical original tag-three header changes the literal base
callback. Use the original callback M at the same key outside this branch. -/
def leafMeasureBase (M : Program 1) : Program 1 := branch (header 3 1) M leafPair10

/-- Keep the actual existing shared lambda/auxiliary recursion, changing
only its explicitly selected base callback. -/
abbrev typeLeafSharedMeasure (M : Program 1) : Program 1 := sharedMeasure (leafMeasureBase M)

def ExactCoverTypeLeafMeasureBase : Prop :=
  ∀ M : Program 1, TermMeasureCalibrated M → TermMeasureCalibrated (leafMeasureBase M)

def ExactCoverTypeLeafSharedMeasure : Prop :=
  ∀ M : Program 1, TermMeasureCalibrated M → TermMeasureCalibrated (typeLeafSharedMeasure M)

/-- Rejection occurs on the actual literal type-only current tape, not
on an external numeric classification. The old table is entirely open. -/
abbrev typeLeafPrior {α : Type} (ty : OTerm α) : OTerm α :=
  NumberedWindowInternalSparsePair.pairTerm
    (SourceComputabilityFormulaSupportProof.numeral 3)
    (NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof.packedBody [ty])

def ExactOpenCoverTypeLeafMeasureDispatch : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ty old : OTerm α),
    let xs : Fin 4 → OTerm α := ![typeLeafPrior ty,old,z,z]
    Nonempty (Derivation body Γ (programGraph lambdaDispatch z xs)) ∧
    Nonempty (Derivation body Γ (programGraph certain z xs)) ∧
    Nonempty (Derivation body Γ (unary (header 3 1) (suc z) (typeLeafTerm ty)))

/-- One actual selected report at the literal type-only key gives its
original successor depth and width zero on that same code p. -/
def ExactOpenCoverTypeLeafSharedMeasure : Prop :=
  ∀ (M : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ty p : OTerm α),
    Nonempty (Derivation body Γ (unary (typeLeafSharedMeasure M) p (typeLeafTerm ty))) →
    Nonempty (Derivation body Γ (codePair p (suc z) z))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasureTargets
