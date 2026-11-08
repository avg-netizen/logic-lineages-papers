module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStack
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact original decoder identities for every raw payload and every type
code. No successful-decode or well-typed-input hypothesis is allowed. Source
retains its result-type membership test; target has no universe restriction. -/
def ActualOriginalApplicationDecoderEquations : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (d e fp ap : Nat),
  InternalOriginalStepGuard.targetValidityValue n arity Gamma (applicationValue d e fp ap) =
    (if InternalOriginalStepGuard.targetValidityValue n arity Gamma (functionValue d e fp) = 1 ∧
      InternalOriginalStepGuard.targetValidityValue n arity Gamma (argumentValue d ap) = 1
      then 1 else 0) ∧
  InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma (applicationValue d e fp ap) =
    (if InternalStructuralEndpointGuard.membershipValue S e = 1 ∧
      InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma (functionValue d e fp) = 1 ∧
      InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma (argumentValue d ap) = 1
      then 1 else 0)

/-- All raw states and arbitrary actual Program leaves. This is calibration
of the exposed one-step AST, not a semantic-to-internal reflection principle. -/
def ActualOriginalStackTransitionCalibration : Prop :=
  ∀ (node leaf : Program 1) (value : Nat),
  evaluate (transition node leaf) (List.Vector.ofFn ![value]) =
    transitionValue (fun x => evaluate node (List.Vector.ofFn ![x]))
      (fun x => evaluate leaf (List.Vector.ofFn ![x])) value

/-- Exact state encoding compatibility, including every non-one status.
The original natural-list codec is not replaced or restricted. -/
def ActualOriginalEncodedStackTransition : Prop :=
  ∀ (node leaf : Nat → Nat) (state : State),
  transitionValue node leaf (encodeState state) = encodeState (stateStep node leaf state)

/-- The invariant names the ORIGINAL semantic tests themselves. Neither
direction may assume that a node is valid, a decoder succeeds, or S is closed. -/
def ActualOriginalStackValidityInvariant : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (state : State),
  (stateValid (InternalOriginalStepGuard.targetValidityValue n arity Gamma)
      (stateStep (fun _ => 1) (InternalOriginalStepGuard.targetValidityValue n arity Gamma) state) ↔
    stateValid (InternalOriginalStepGuard.targetValidityValue n arity Gamma) state) ∧
  (stateValid (InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma)
      (stateStep (InternalStructuralEndpointGuard.membershipValue S)
        (InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma) state) ↔
    stateValid (InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma) state)

/-- Every nonempty live worklist loses at least one unit, for arbitrary leaf
functions, even when a guard rejects. The measure is on term payloads, NOT
packed values or reconstructed arrow type codes. -/
def ActualOriginalStackWorkDecrease : Prop :=
  ∀ (node leaf : Nat → Nat) (state : State),
  state.status = 1 → state.work ≠ [] →
    workWeight (stateStep node leaf state).work < workWeight state.work

/-- A genuine internal full-output constructor equation. The only accepted
guard is the actual node Program graph at the SAME result-type term. Function
and argument payloads, stack suffix, state and output remain arbitrary terms.
The old leaf is arbitrary and is not inspected at an application node. -/
def ActualOriginalApplicationStackPush : Prop :=
  ∀ (body : Positive (Fin 1)) (node leaf : Program 1) (α : Type)
    (d e fp ap tail state out : OTerm α),
  Nonempty (Derivation body []
    ((InternalApplicationStepPeel.graph5 applicationFrame state d e fp ap tail ⊓
      graph1 node InternalOriginalStepGuard.one e).imp
      ((graph1 (transition node leaf) out state).iff
        (InternalApplicationStepPeel.graph5 expandedFrame out d e fp ap tail))))

/-- Source-to-target acceptance is syntactic even before recursive calibration
is proved. No old leaf calibration or external natural-number truth is used. -/
def ActualOriginalRecursiveSourceTarget : Prop :=
  ∀ (body : Positive (Fin 1)) (old : InternalOriginalStepGuard.Data) (member : Program 1)
    (α : Type) (value : OTerm α),
  Nonempty (Derivation body []
    ((graph1 (recursiveData old member).sourceValid InternalOriginalStepGuard.one value).imp
      (graph1 (recursiveData old member).targetValid InternalOriginalStepGuard.one value)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackTargets
