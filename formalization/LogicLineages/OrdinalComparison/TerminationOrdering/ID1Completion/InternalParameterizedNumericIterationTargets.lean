module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationDefinitions
public import Mathlib.Logic.Function.Iterate
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedNumericIteration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- All natural inputs, including count zero and every parameter. P is one
actual binary AST, not a family selected after the parameter is supplied.
This separate evaluation theorem does not imply any internal derivation. -/
def ExactParameterizedNumericIterationEvaluation : Prop :=
  ∀ (P : Program 2) (count value parameter : Nat),
  evaluate (repeatP P) (count ::ᵥ value ::ᵥ parameter ::ᵥ List.Vector.nil) =
    Nat.iterate
      (fun x => evaluate P (x ::ᵥ parameter ::ᵥ List.Vector.nil)) count value

/-- Both states are constrained by the ACTUAL original pairing graphs.
Under those graphs, one carried step is equivalent to the actual P graph
at [value, parameter], with arbitrary full output and arbitrary context. -/
def ActualOriginalParameterizedNumericIterationCarryStep : Prop :=
  ∀ (body : Positive (Fin 1)) (P : Program 2) (α : Type)
    (Gamma : List (Formula α))
    (state nextState value next parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((programGraph InternalPairing.pairing state
        (Fin.cons parameter (Fin.cons value Fin.elim0)) ⊓
      programGraph InternalPairing.pairing nextState
        (Fin.cons parameter (Fin.cons next Fin.elim0))).imp
      ((carryGraph P nextState state).iff
        (programGraph P next (Fin.cons value (Fin.cons parameter Fin.elim0))))))

/-- The original numeric iterator preserves the actual left-coordinate
graph at every symbolic count and every raw initial state. No standard
model equality, decoder, generated-state, or canonicality premise occurs. -/
def ActualOriginalParameterizedNumericIterationParameterPreservation : Prop :=
  ∀ (body : Positive (Fin 1)) (P : Program 2) (α : Type)
    (Gamma : List (Formula α))
    (out count state parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((programGraph InternalUnpair.left parameter (Fin.cons state Fin.elim0) ⊓
      InternalNumericIteration.repeatGraph (carryP P) out count state).imp
      (programGraph InternalUnpair.left parameter (Fin.cons out Fin.elim0))))

/-- Zero returns the arbitrary original symbolic value at the same
symbolic parameter, in the unchanged internal calculus and context. -/
def ActualOriginalParameterizedNumericIterationZero : Prop :=
  ∀ (body : Positive (Fin 1)) (P : Program 2) (α : Type)
    (Gamma : List (Formula α))
    (out value parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((repeatGraph P out OrdinaryArithmetic.zeroTerm value parameter).iff
      (equal out value)))

/-- A front successor uses the actual graph of the SAME P at the SAME
symbolic parameter. The successor is the original arithmetic term. -/
def ActualOriginalParameterizedNumericIterationFrontSuccessor : Prop :=
  ∀ (body : Positive (Fin 1)) (P : Program 2) (α : Type)
    (Gamma : List (Formula α))
    (out count value next parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((programGraph P next (Fin.cons value (Fin.cons parameter Fin.elim0))).imp
      ((repeatGraph P out (OrdinaryArithmetic.succTerm count) value parameter).iff
        (repeatGraph P out count next parameter))))

/-- Perform first iterations, then second iterations from their actual
intermediate output, preserving one parameter throughout. The count uses
the original addTerm, not an external sum or a new counting program. -/
def ActualOriginalParameterizedNumericIterationAdditionFusion : Prop :=
  ∀ (body : Positive (Fin 1)) (P : Program 2) (α : Type)
    (Gamma : List (Formula α))
    (out first second value intermediate parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((repeatGraph P intermediate first value parameter).imp
      ((repeatGraph P out (OrdinaryArithmetic.addTerm first second) value parameter).iff
        (repeatGraph P out second intermediate parameter))))

/-- An actual P(fixed,[fixed,parameter]) graph fixes the full returned
value at EVERY symbolic count. This is not output-one acceptance, and the
parameter is the identical symbolic term in the premise and conclusion. -/
def ActualOriginalParameterizedNumericIterationFixedPoint : Prop :=
  ∀ (body : Positive (Fin 1)) (P : Program 2) (α : Type)
    (Gamma : List (Formula α))
    (out count fixed parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((programGraph P fixed (Fin.cons fixed (Fin.cons parameter Fin.elim0))).imp
      ((repeatGraph P out count fixed parameter).iff (equal out fixed))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationTargets
