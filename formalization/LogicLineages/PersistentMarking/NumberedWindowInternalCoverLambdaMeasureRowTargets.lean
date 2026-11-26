module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalRawListRecursion (lookup)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowCoverBoundsAlgorithm (bounds)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt)
open NumberedWindowInternalAuxMeasureStepTargets (earlierAt measureAt)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalChosenAuxMeasureCombine (callOne callTwo)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaPrior lambdaTape lambdaGuard)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)

def successorDepth : Program 1 := callOne .succ ID1Completion.InternalUnpair.left

/-- The child's original standard pair is unshifted. Increment its left
(depth) coordinate only and re-pair with the unchanged right numeral. -/
def lambdaBump : Program 1 :=
  callTwo ID1Completion.InternalPairing.pairing successorDepth ID1Completion.InternalUnpair.right

def lambdaMeasureUpdate (M : Program 1) : Program 4 :=
  branch lambdaGuard (unaryAfter M currentKey) (unaryAfter lambdaBump (measureAt 1))

def lambdaMeasure (M : Program 1) : Program 1 := selectedMeasure (lambdaMeasureUpdate M)

def ExactCoverLambdaBumpCalibration : Prop :=
  ∀ d w : Nat, run lambdaBump (Encodable.encode (d,w)) = Encodable.encode (d+1,w)

def ExactCoverLambdaMeasureStepCalibration : Prop :=
  ∀ (M : Program 1), TermMeasureCalibrated M →
  ∀ (i old : Nat),
    (∀ n, n < i+1 → evaluate lookup ((i-n) ::ᵥ old ::ᵥ nil) = Encodable.encode (bounds n).1) →
    evaluate (lambdaMeasureUpdate M) (i ::ᵥ old ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) = Encodable.encode (bounds (i+1)).1

def ExactCoverLambdaMeasureCalibration : Prop :=
  ∀ (M : Program 1), TermMeasureCalibrated M → TermMeasureCalibrated (lambdaMeasure M)

def ExactOpenCoverLambdaBumpPair : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (p mc d w : OTerm α),
    Nonempty (Derivation body Γ (codePair mc d w)) →
    Nonempty (Derivation body Γ (unary lambdaBump p mc)) →
    Nonempty (Derivation body Γ (codePair p (suc d) w))

def lambdaMeasureRecovered {α : Type} (M : Program 1) (ty q old mc p d w : OTerm α) : Formula α :=
  unary (lambdaMeasure M) p (lambdaTerm ty q) ⊓
    (codePair p (suc d) w ⊓
      (programGraph (earlierAt 1) (suc z) (lambdaTape ty q old) ⊓
       programGraph (measureAt 1) mc (lambdaTape ty q old)))

/-- The one actual same-table parent step returns a real parent measure
with the original tag-two coordinates. No supplied bump output report. -/
def ExactOpenCoverLambdaMeasureRow : Prop :=
  ∀ (M : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ty q old mc p d w : OTerm α),
    Nonempty (Derivation body Γ (tableAt (lambdaMeasureUpdate M) old (lambdaPrior ty q))) →
    Nonempty (Derivation body Γ (programGraph (lambdaMeasureUpdate M) p (lambdaTape ty q old))) →
    Nonempty (Derivation body Γ (unary (lambdaMeasure M) mc q)) →
    Nonempty (Derivation body Γ (codePair mc d w)) →
    Nonempty (Derivation body Γ (lambdaMeasureRecovered M ty q old mc p d w))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowTargets
