module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityFormulaSupportProof
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityCompletion.BottomSource
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Source-specific INTERNAL bottom typing at an arbitrary runtime Gamma
code. The same globally selected Data/window precede every source window.
The only internal antecedent is the ORIGINAL parameter pairing: no source,
type, shape, fixedness or symbolic calibration premise is supplied. Closed
leaf computations must be represented by actual original proof trees. -/
def ActualOriginalUniformBottomTyping : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data) (window : Program 1),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  (∀ v, evaluate window v = GuardCalibration.validWindowValue n v) →
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  ∀ (tau : Ty), tau ∈ S →
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (parameter gamma : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((graph2 InternalPairing.pairing parameter
      (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) gamma).imp
      (typedBottom data window tau parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceTargets
