module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepChecker
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The old checker is calibrated to the unchanged original numeric step
checker on EVERY natural triple. This external equation is not an internal
proof rule and is not a premise of the lifted graph target. -/
def StepCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (oldChecker : Program 3) : Prop :=
  ∀ v : List.Vector Nat 3, evaluate oldChecker v =
    (NumberedNumericStep.numericStepTest n arity symbols S Gamma table
      (v.get 0) (v.get 1) (v.get 2)).toNat

/-- Actual original graph witnesses, not semantic typing assertions. The
original raw application constructor discards outer tags, so those tags are
explicit. The same argument and type codes are used at both endpoints.
The endpoint leaf retains its actual output-one graph as a separate obligation.
No state-normalization or checker-equivalence conclusion is assumed here. -/
def liftedCheckerPremises {α : Type} (endpoint : Program 5)
    (d e arrow s t a k s' t' k' : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 InternalListCodec.consCode arrow d e ⊓
    (graph1 InternalUnpair.left arrow s ⊓
      (graph1 InternalUnpair.left arrow t ⊓
        (graph1 InternalUnpair.left d a ⊓
          (graph5 endpoint (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) d e s t a ⊓
            (graph4 application s' d e s a ⊓
              (graph4 application t' d e t a ⊓ graph1 stepLift k' k))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepChecker
