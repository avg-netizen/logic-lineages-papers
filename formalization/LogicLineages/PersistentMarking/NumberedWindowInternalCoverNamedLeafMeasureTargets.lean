module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasureTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasureTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalPairing (pairing)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverSharedRecursionTargets (lambdaDispatch)
open NumberedWindowInternalAuxMeasureStepTargets (certain)
open NumberedWindowInternalCoverTypeLeafMeasureTargets (typeLeafSharedMeasure)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)

/-- Original standard pair, with width read from original sparse field 1. -/
def namedMeasurePair : Program 1 := .composition pairing ![literal 1 1,field 1]

def namedMeasureBase (M : Program 1) : Program 1 :=
  branch (header 0 2) (branch (header 1 2) M namedMeasurePair) namedMeasurePair

/-- Keep exactly the previously paid tag-three and λ/auxiliary dispatchers:
specialize their original base fallback, not their accepted graph. -/
abbrev namedSharedMeasure (M : Program 1) : Program 1 := typeLeafSharedMeasure (namedMeasureBase M)

def ExactCoverNamedLeafMeasureBase : Prop :=
  ∀ M : Program 1, TermMeasureCalibrated M → TermMeasureCalibrated (namedMeasureBase M)

def ExactCoverNamedLeafSharedMeasure : Prop :=
  ∀ M : Program 1, TermMeasureCalibrated M → TermMeasureCalibrated (namedSharedMeasure M)

abbrev namedPrior {α : Type} (b : Bool) (ty i : OTerm α) : OTerm α :=
  NumberedWindowInternalSparsePair.pairTerm (numeral b.toNat) (packedBody [ty,i])

/-- The current physical row bypasses λ and auxiliary recursion, passes
the true corresponding named header, and physically reports the original
index at field 1. A bound name additionally rejects the earlier free header. -/
def ExactOpenCoverNamedLeafMeasureDispatch : Prop :=
  ∀ (b : Bool) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ty i old : OTerm α),
    let raw := namedTerm b.toNat ty i
    let xs : Fin 4 → OTerm α := ![namedPrior b ty i,old,z,z]
    Nonempty (Derivation body Γ (programGraph lambdaDispatch z xs)) ∧
    Nonempty (Derivation body Γ (programGraph certain z xs)) ∧
    Nonempty (Derivation body Γ (unary (header 3 1) z raw)) ∧
    Nonempty (Derivation body Γ (unary (header b.toNat 2) (suc z) raw)) ∧
    Nonempty (Derivation body Γ (unary (field 1) i raw)) ∧
    (b = true → Nonempty (Derivation body Γ (unary (header 0 2) z raw)))

def ExactOpenCoverNamedLeafSharedMeasure : Prop :=
  ∀ (b : Bool) (M : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ty i p : OTerm α),
    Nonempty (Derivation body Γ (unary (namedSharedMeasure M) p (namedTerm b.toNat ty i))) →
    Nonempty (Derivation body Γ (codePair p (suc z) i)) ∧
    Nonempty (Derivation body Γ (ltF i (suc i)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasureTargets
