module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityCompletion.BottomParameter
open SourceComputabilityCompletion.BottomRepresentative (bottomGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Both original validator calibrations hold on ALL raw values and paired
parameters, including malformed Context/type codes and every Gamma code.
No subtype-closure, validWindow or source-validity premise is supplied. -/
def ActualOriginalBottomParameterCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  InternalOriginalUniformDescentSelection.Calibrated n arity (baseData data)

/-- Literal AST wiring pays the symbolic-Gamma slice. The context-only
parameter is supplied through the SAME original pair graph; neither Context
nor Gamma decoding is assumed. Later closed-context computations can consume
this rule without reflecting a symbolic evaluation calibration. -/
def ActualParameterizedBottomLeafSlice : Prop :=
  ∀ (body : Positive (Fin 1)) (old : Program 2) (α : Type)
    (Delta : List (Formula α))
    (out value parameter context gamma contextOnly : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((graph2 InternalPairing.pairing parameter context gamma ⊓
      graph2 InternalPairing.pairing contextOnly context OrdinaryArithmetic.zeroTerm).imp
      ((bottomGraph InternalOriginalStepGuard.one value).imp
        ((graph2 (normalized old) out value parameter).iff
          (graph2 old out value contextOnly)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterTargets
