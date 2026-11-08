module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationStepPeel InternalApplicationStepChecker
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All-input calibration of the particular frozen repeat-then-old-checker
AST to the ORIGINAL numericStepTest. Both supplied programs are calibrated
on all their natural inputs. No decode success, subtype closure, certificate
validity or successful transition is assumed. -/
def ActualOriginalCheckerCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (endpoint : Program 5) (oldChecker : Program 3),
  EndpointCalibrated n arity symbols S Gamma endpoint →
  StepCalibrated n arity symbols S Gamma table oldChecker →
  ∀ v : List.Vector Nat 3,
    evaluate (InternalApplicationStepPeel.checker endpoint oldChecker) v =
      (NumberedNumericStep.numericStepTest n arity symbols S Gamma table
        (v.get 0) (v.get 1) (v.get 2)).toNat

/-- Full-output equivalence for the SAME concrete normalized checker at
original and lifted source/target/certificate terms. The old checker and leaf
are arbitrary original Program ASTs; no calibration hypothesis appears.
Actual constructor, outer-tag and endpoint-leaf graphs are explicit premises.
Every symbolic original certificate is allowed, including malformed suffixes.
This does not identify arbitrary semantically equivalent checker programs. -/
def ActualOriginalLiftedChecker : Prop :=
  ∀ (body : Positive (Fin 1)) (endpoint : Program 5) (oldChecker : Program 3)
    (α : Type) (d e arrow s t a k s' t' k' out : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((liftedCheckerPremises endpoint d e arrow s t a k s' t' k').imp
      ((graph3 (InternalApplicationStepPeel.checker endpoint oldChecker) out s' t' k').iff
        (graph3 (InternalApplicationStepPeel.checker endpoint oldChecker) out s t k))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerTargets
