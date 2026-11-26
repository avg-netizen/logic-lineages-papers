module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalRecurrence
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact full-output equations for the explicit proof-support weight AST.
The cons equation uses only original constructor/selector graphs. -/
def ActualOriginalHereditaryInternalWorkFuelEquations : Prop :=
  (∀ (body : Positive (Fin 1)) (alpha : Type) (out : OTerm alpha),
    Nonempty (Derivation body []
      ((WorkFuelGraph out OrdinaryArithmetic.zeroTerm).iff
        (equal out OrdinaryArithmetic.zeroTerm)))) ∧
  (∀ (body : Positive (Fin 1)) (alpha : Type)
    (workCode frame raw parameter restCode payload tailFuel out : OTerm alpha),
    Nonempty (Derivation body []
      ((WorkCons workCode frame restCode ⊓
        (FrameGraph frame raw parameter ⊓
          (graph1 InternalUnpair.right payload raw ⊓ WorkFuelGraph tailFuel restCode))).imp
        ((WorkFuelGraph out workCode).iff
          (equal out (OrdinaryArithmetic.addTerm
            (OrdinaryArithmetic.succTerm payload) tailFuel))))))

/-- No nonempty raw worklist has zero payload weight. -/
def ActualOriginalHereditaryInternalWorkFuelZero : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (count workCode : OTerm alpha),
  Nonempty (Derivation body []
    ((WorkFuelGraph count workCode).imp
      ((equal count OrdinaryArithmetic.zeroTerm).iff
        (equal workCode OrdinaryArithmetic.zeroTerm))))

/-- Actual raw-list append, with exact additive payload fuel. All frame
codes and per-frame parameters remain arbitrary. -/
def ActualOriginalHereditaryInternalWorkFuelAppend : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type)
    (front suffix joined first second out : OTerm alpha),
  Nonempty (Derivation body []
    ((graph2 InternalApplicationValidityStackAppend.append joined front suffix ⊓
      (WorkFuelGraph first front ⊓ WorkFuelGraph second suffix)).imp
      ((WorkFuelGraph out joined).iff
        (equal out (OrdinaryArithmetic.addTerm first second)))))

/-- INTERNAL counterpart of the native work decrease, proved afresh from
the exact framed transition and original pairing arithmetic. An arbitrary
transition output is classified, including rejection and all raw tags. -/
def ActualOriginalHereditaryInternalWorkDecrease : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type)
    (state workCode frame raw parameter restCode previousFuel out : OTerm alpha),
  Nonempty (Derivation body []
    ((StateFrame state workCode frame raw parameter restCode ⊓
      WorkFuelGraph previousFuel workCode).imp
      ((graph1 (transition oldSource oldTarget member) out state).imp
        (DecreasedOrFailed out previousFuel))))

/-- Sufficient fuel is PROVED internally for every raw worklist, not
assumed. The endpoint and its completed run are constructed in the
conclusion; either literal failure or literal success is allowed. -/
def ActualOriginalHereditaryInternalSufficientFuel : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type) (workCode required count : OTerm alpha),
  Nonempty (Derivation body []
    ((WorkFuelGraph required workCode ⊓
      InternalPairingSumBounds.weakBound required count).imp
      (TerminatedWork oldSource oldTarget member count workCode)))

/-- After the proved sufficient threshold, acceptance is exactly acceptance
at the worklist's OWN payload sum. No success premise or chosen terminal
endpoint is supplied. This pays removal as well as addition of spare fuel. -/
def ActualOriginalHereditaryInternalFuelSaturation : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type) (workCode required count : OTerm alpha),
  Nonempty (Derivation body []
    ((WorkFuelGraph required workCode ⊓
      InternalPairingSumBounds.weakBound required count).imp
      ((SuccessfulWork oldSource oldTarget member count workCode).iff
        (WorkAccepted oldSource oldTarget member workCode))))

/-- BOTH directions of sequential acceptance for the SAME framed machine.
Each side uses its own internally computed sum of original payload+1
counts. This is an equivalence to be proved, not a successful-prefix/suffix
premise, an equality at an intermediate count, or a unary-machine shortcut. -/
def ActualOriginalHereditaryInternalWorkAppend : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type) (front suffix joined : OTerm alpha),
  Nonempty (Derivation body []
    ((graph2 InternalApplicationValidityStackAppend.append joined front suffix).imp
      ((WorkAccepted oldSource oldTarget member joined).iff
        (WorkAccepted oldSource oldTarget member front ⊓
          WorkAccepted oldSource oldTarget member suffix))))

/-- The proof-support work predicate is identified with the EXISTING
validator on a singleton. Both the initial-state code and exact original
payload+1 fuel are recovered internally from the original frame graphs. -/
def ActualOriginalHereditaryInternalSingletonValidator : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type) (workCode frame raw parameter : OTerm alpha),
  Nonempty (Derivation body []
    ((WorkCons workCode frame OrdinaryArithmetic.zeroTerm ⊓
      FrameGraph frame raw parameter).imp
      ((WorkAccepted oldSource oldTarget member workCode).iff
        (graph2 (validator oldSource oldTarget member) (numeral 1) raw parameter))))

/-- Bounded VALIDATOR acceptance supplies the exact original node factors.
Unlike the earlier initial-node theorem, no accepted node, initial-state
graph, selector witness or successful-run hypothesis is supplied. -/
def ActualOriginalHereditaryInternalAcceptanceNode : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type) (raw parameter : OTerm alpha),
  Nonempty (Derivation body []
    ((graph2 (validator oldSource oldTarget member) (numeral 1) raw parameter).imp
      (NodeFactors oldSource oldTarget member raw parameter)))

/-- Exact INDEPENDENT INTERNAL recurrence for every raw value/parameter
and arbitrary binary Program leaves, including non-Boolean outputs. Every
child invokes the same frozen validator at its own original payload+1 fuel.
No native calibration, typed-source, completed-run, child-validity, or
fuel-success assumption occurs. This statement is pending until proved. -/
def ActualOriginalHereditaryInternalValidatorRecurrence : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type) (raw parameter : OTerm alpha),
  Nonempty (Derivation body []
    ((graph2 (validator oldSource oldTarget member) (numeral 1) raw parameter).iff
      (RecurrenceFactors oldSource oldTarget member raw parameter)))

/-- Full-output graph recurrence, including exact zero rejection. No output
is assumed Boolean, and no leaf is required to be Boolean or calibrated. -/
def ActualOriginalHereditaryInternalValidatorOutput : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type) (out raw parameter : OTerm alpha),
  Nonempty (Derivation body []
    ((graph2 (validator oldSource oldTarget member) out raw parameter).iff
      (ValidatorOutputFactors oldSource oldTarget member out raw parameter)))

/-- Accepted literal lambdas internally supply acceptance of the actual
body at the actual extended-Gamma parameter, with the same validator and
the child's OWN payload+1 fuel. No body, parameter extension, initial state,
child acceptance or successful residual run is an external premise.
This is not yet closure of the eventual selected source Program. -/
def ActualOriginalHereditaryInternalLambdaChildClosure : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2)
    (alpha : Type) (raw parameter : OTerm alpha),
  Nonempty (Derivation body []
    ((graph2 (validator oldSource oldTarget member) (numeral 1) raw parameter ⊓
      graph1 OriginalLambdaConstructor.tag (numeral 1) raw).imp
      (RootLambdaChild oldSource oldTarget member raw parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceTargets
