module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalApplicationResultStack
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Every raw numeric state, not merely states reached from a canonical input.
The guard and leaf receive the original packed value; combine receives its
four specified coordinates. No semantic or internal-correctness field occurs. -/
def ActualOriginalResultStackTransitionCalibration : Prop :=
  ∀ (guard leaf : Program 1) (combine : Program 4) (value : Nat),
  evaluate (transition guard leaf combine) (List.Vector.ofFn ![value]) =
    transitionValue (fun x => evaluate guard (List.Vector.ofFn ![x]))
      (fun x => evaluate leaf (List.Vector.ofFn ![x]))
      (fun d e f a => evaluate combine (List.Vector.ofFn ![d,e,f,a])) value

/-- Exact original state/list encoding, including malformed numeric frames,
non-one status and short result stacks. No new source term codec is used. -/
def ActualOriginalEncodedResultStackTransition : Prop :=
  ∀ (guard leaf : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat) (state : State),
  transitionValue guard leaf combine (encodeState state) =
    encodeState (stateStep guard leaf combine state)

/-- Output size is unrestricted and contributes nothing to this measure.
Every nonempty live worklist decreases, including rejected malformed frames. -/
def ActualOriginalResultStackWorkDecrease : Prop :=
  ∀ (guard leaf : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat) (state : State),
  state.status = 1 → state.work ≠ [] →
    workWeight (stateStep guard leaf combine state).work < workWeight state.work

/-- The exact exposed bound is 2*original payload+1. Opening and finishing
each cost one; the two child budgets use their original payloads, irrespective
of reconstructed type sizes or computed results. This is only fuel algebra,
not a completed-run, recursive-fold or representative-calibration claim. -/
def ActualOriginalResultStackFuelBounds : Prop :=
  (∀ value : Nat,
    evaluate fuel (List.Vector.ofFn ![value]) = fuelValue value ∧
    workWeight [visitValue value] = fuelValue value) ∧
  (∀ d e fp ap : Nat,
    1 + fuelValue (InternalApplicationValidityStack.functionValue d e fp) +
        fuelValue (InternalApplicationValidityStack.argumentValue d ap) + 1 ≤
      fuelValue (InternalApplicationValidityStack.applicationValue d e fp ap))

/-- The opening rule uses ACTUAL constructor, state and root-guard graphs.
The source-validity graph is never inferred from external calibration. Neither
the arbitrary leaf nor combine is inspected by this transition branch. -/
def ActualOriginalResultStackVisit : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 1) (combine : Program 4) (α : Type)
    (d e fp ap value work results state out : OTerm α),
  Nonempty (Derivation body []
    ((graph4 packedApplication value d e fp ap ⊓
      (graph3 visitState state value work results ⊓
        graph1 guard InternalOriginalStepGuard.one value)).imp
      ((graph1 (transition guard leaf combine) out state).iff
        (graph6 expandedState out d e fp ap work results))))

/-- Fallback uses an actual zero graph for the exact opening test. It applies
both to nonapplications and to applications whose root guard rejects. The
leaf output is internally quantified, with no supplied semantic value. -/
def ActualOriginalResultStackLeaf : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 1) (combine : Program 4) (α : Type)
    (value work results state out : OTerm α),
  Nonempty (Derivation body []
    ((graph3 visitState state value work results ⊓
      graph1 (openGuard guard) OrdinaryArithmetic.zeroTerm value).imp
      ((graph1 (transition guard leaf combine) out state).iff
        (leafResult leaf out value work results))))

/-- The concrete frame/result constructors are the only hypotheses. In
particular, nothing assumes the two prior results are representatives or have
the expected type tags. Combine is applied in function/argument order. -/
def ActualOriginalResultStackFinish : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 1) (combine : Program 4) (α : Type)
    (d e work argument function results state out : OTerm α),
  Nonempty (Derivation body []
    ((graph6 finishState state d e work argument function results).imp
      ((graph1 (transition guard leaf combine) out state).iff
        (finishResult combine out d e work argument function results))))

/-- Exhausted work is a fixed point preserving the ENTIRE arbitrary result
stack, not merely a Boolean success status or its top output. This local law
does not assert the pending output-preserving continuation theorem. -/
def ActualOriginalResultStackEmpty : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 1) (combine : Program 4) (α : Type)
    (results state out : OTerm α),
  Nonempty (Derivation body []
    ((graph1 emptyState state results).imp
      ((graph1 (transition guard leaf combine) out state).iff (equal out state))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackTargets
