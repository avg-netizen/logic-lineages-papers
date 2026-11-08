module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalParameterizedApplicationResultStack
open InternalApplicationResultStackReturnSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Separate standard-model calibration on EVERY raw numeric state and
parameter. Its right side is the unchanged ORIGINAL transitionValue, with
callbacks sliced at p in exactly their displayed coordinate order. This
external equality supplies no internal derivability or validity hypothesis. -/
def ExactParameterizedApplicationResultStackTransitionEvaluation : Prop :=
  ∀ (guard leaf : Program 2) (combine : Program 5) (state parameter : Nat),
  evaluate (transitionP guard leaf combine) (List.Vector.ofFn ![state,parameter]) =
    InternalApplicationResultStack.transitionValue
      (fun value => evaluate guard (List.Vector.ofFn ![value,parameter]))
      (fun value => evaluate leaf (List.Vector.ofFn ![value,parameter]))
      (fun d e f a => evaluate combine (List.Vector.ofFn ![d,e,f,a,parameter])) state

/-- Unary weakening factors through the actual original unary graph, in
every context and at the same arbitrary symbolic parameter. -/
def ActualOriginalParameterizedApplicationResultStackLift : Prop :=
  ∀ (body : Positive (Fin 1)) (P : Program 1) (α : Type) (Gamma : List (Formula α))
    (out value parameter : OTerm α),
  Nonempty (Derivation body Gamma
    ((graph2 (liftP P) out value parameter).iff (graph1 P out value)))

/-- Literal finite composition/reindexing. The hypotheses are already-derived
actual selector graphs, not external evaluations or assumed correctness of
any callback. The final coordinate is the identical symbolic parameter. -/
def ActualOriginalParameterizedApplicationResultStackWiring : Prop :=
  ∀ (body : Positive (Fin 1)) (n : Nat) (P : Program (n+1))
    (selectors : Fin n → Program 1) (α : Type) (Gamma : List (Formula α))
    (out state parameter : OTerm α) (values : Fin n → OTerm α),
  (∀ i, Nonempty (Derivation body Gamma (graph1 (selectors i) (values i) state))) →
  Nonempty (Derivation body Gamma
    ((graph2 (wireP P selectors) out state parameter).iff
      (programGraph P out (appendParameter values parameter))))

/-- Opening uses the ACTUAL original packed application and visit-state
constructors, together with G(value,p)=1. The expanded state and all raw
suffix codes are unchanged, independent of p, L and C. -/
def ActualOriginalParameterizedApplicationResultStackVisit : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 2) (combine : Program 5) (α : Type)
    (Gamma : List (Formula α)) (d e fp ap value work results state out parameter : OTerm α),
  Nonempty (Derivation body Gamma
    ((graph4 packedApplication value d e fp ap ⊓
      (graph3 InternalApplicationResultStack.visitState state value work results ⊓
        graph2 guard InternalOriginalStepGuard.one value parameter)).imp
      ((graph2 (transitionP guard leaf combine) out state parameter).iff
        (InternalApplicationResultStack.graph6 InternalApplicationResultStack.expandedState
          out d e fp ap work results))))

/-- Fallback requires the actual zero graph of the exact opening guard.
The original arity-generic returned relation internally quantifies L's
output and pushes it through the original returnState at [value,p]. -/
def ActualOriginalParameterizedApplicationResultStackLeaf : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 2) (combine : Program 5) (α : Type)
    (Gamma : List (Formula α)) (value work results state out parameter : OTerm α),
  Nonempty (Derivation body Gamma
    ((graph3 InternalApplicationResultStack.visitState state value work results ⊓
      graph2 (openGuardP guard) OrdinaryArithmetic.zeroTerm value parameter).imp
      ((graph2 (transitionP guard leaf combine) out state parameter).iff
        (returned leaf out (Fin.cons value (Fin.cons parameter Fin.elim0)) work results))))

/-- Only the original finish-state constructor is assumed. The arbitrary
prior outputs reach C in [domain,codomain,function,argument,p] order, and
its internally quantified output is pushed onto the original result suffix. -/
def ActualOriginalParameterizedApplicationResultStackFinish : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 2) (combine : Program 5) (α : Type)
    (Gamma : List (Formula α)) (d e work argument function results state out parameter : OTerm α),
  Nonempty (Derivation body Gamma
    ((InternalApplicationResultStack.graph6 InternalApplicationResultStack.finishState
        state d e work argument function results).imp
      ((graph2 (transitionP guard leaf combine) out state parameter).iff
        (returned combine out
          (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argument (Fin.cons parameter Fin.elim0)))))
          work results))))

/-- Empty work fixes the ENTIRE original state, including an arbitrary
whole result stack. The parameter is neither the output nor a new state field. -/
def ActualOriginalParameterizedApplicationResultStackEmpty : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 2) (combine : Program 5) (α : Type)
    (Gamma : List (Formula α)) (results state out parameter : OTerm α),
  Nonempty (Derivation body Gamma
    ((graph1 InternalApplicationResultStack.emptyState state results).imp
      ((graph2 (transitionP guard leaf combine) out state parameter).iff (equal out state))))

/-- Every symbolic iteration count, including zero, preserves the SAME
terminal original state at the SAME parameter. This is the local empty-step
law plus the actual parameterized iterator fixed-point law, not a claim
that every initial run finishes or that arbitrary worklists can be framed. -/
def ActualOriginalParameterizedApplicationResultStackTerminalIteration : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 2) (combine : Program 5) (α : Type)
    (Gamma : List (Formula α)) (results state out count parameter : OTerm α),
  Nonempty (Derivation body Gamma
    ((graph1 InternalApplicationResultStack.emptyState state results).imp
      ((graph3 (iterateP guard leaf combine) out count state parameter).iff (equal out state))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackTargets
