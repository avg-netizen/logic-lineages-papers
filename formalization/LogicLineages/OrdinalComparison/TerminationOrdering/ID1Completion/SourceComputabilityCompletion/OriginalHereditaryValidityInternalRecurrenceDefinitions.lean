module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrence
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A proof-support measure on the ORIGINAL pair-coded frame. Only the raw
term payload contributes: neither its type nor its own parameter contributes.
This auxiliary AST does not replace or occur in the frozen validator. -/
def frameFuel : Program 1 :=
  .composition .succ (fun _ : Fin 1 => rightOf (leftOf (.projection 0)))

/-- Inputs [original frame, recursively computed tail weight]. -/
def workFuelStep : Program 2 :=
  .composition InternalArithmeticPrograms.addition
    ![.composition frameFuel (fun _ : Fin 1 => .projection 0), .projection 1]

/-- Explicit raw-list recursion sums payload+1 over all pending frames.
Every raw list code is covered by the unchanged successor/pair codec.
No native weight, successful traversal, or semantic validity is consulted. -/
def workFuel : Program 1 := InternalRawListRecursion.listRec .zero workFuelStep

def WorkFuelGraph {alpha : Type} (count workCode : OTerm alpha) : Formula alpha :=
  graph1 workFuel count workCode

/-- The actual original success state is pair 1 0, the numeral TWO. -/
def Terminal {alpha : Type} (state : OTerm alpha) : Formula alpha :=
  equal state OrdinaryArithmetic.zeroTerm ⊔ equal state (numeral 2)

/-- Execution of the UNCHANGED framed iterator from status one and the
given raw worklist. Its initial state is constructed internally. -/
def WorkRun {alpha : Type} (oldSource oldTarget member : Program 2)
    (out count workCode : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 1)
    (StateGraph (.var (.inr (0 : Fin 1))) (numeral 1) (workCode.relabel Sum.inl) ⊓
      graph2 (iterate oldSource oldTarget member) (out.relabel Sum.inl)
        (count.relabel Sum.inl) (.var (.inr (0 : Fin 1))))

def SuccessfulWork {alpha : Type} (oldSource oldTarget member : Program 2)
    (count workCode : OTerm alpha) : Formula alpha :=
  WorkRun oldSource oldTarget member (numeral 2) count workCode

/-- The output and the completed run are CONCLUSIONS inside this formula.
Sufficient-fuel targets never require a supplied terminal or successful run. -/
def TerminatedWork {alpha : Type} (oldSource oldTarget member : Program 2)
    (count workCode : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 1)
    (WorkRun oldSource oldTarget member (.var (.inr (0 : Fin 1)))
        (count.relabel Sum.inl) (workCode.relabel Sum.inl) ⊓
      Terminal (.var (.inr (0 : Fin 1))))

/-- A proof intermediary using the EXISTING iterator at exactly the sum of
the original pending payload+1 counts. The weight is an internal graph
witness, not a caller-chosen fuel bound or a replacement source predicate. -/
def WorkAccepted {alpha : Type} (oldSource oldTarget member : Program 2)
    (workCode : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 1)
    (WorkFuelGraph (.var (.inr (0 : Fin 1))) (workCode.relabel Sum.inl) ⊓
      SuccessfulWork oldSource oldTarget member (.var (.inr (0 : Fin 1)))
        (workCode.relabel Sum.inl))

/-- A live nonempty transition either rejects literally or constructs a
live state with strictly smaller payload work. New work/weight witnesses
are internal; no next-state validity or termination premise is supplied. -/
def DecreasedOrFailed {alpha : Type} (out previousFuel : OTerm alpha) : Formula alpha :=
  equal out OrdinaryArithmetic.zeroTerm ⊔
    InternalFiniteBlocks.block (k := 2)
      (StateGraph (out.relabel Sum.inl) (numeral 1) (.var (.inr (0 : Fin 2))) ⊓
        (WorkFuelGraph (.var (.inr (1 : Fin 2))) (.var (.inr (0 : Fin 2))) ⊓
          InternalLessThan.strictLess (.var (.inr (1 : Fin 2)))
            (previousFuel.relabel Sum.inl)))

/-- Both children come from the ACTUAL selectors at the same original
singleton initial state. Each invokes the IDENTICAL bounded validator with
its own payload+1 fuel and the unchanged parent parameter. -/
def RootApplicationChildren {alpha : Type} (oldSource oldTarget member : Program 2)
    (raw parameter : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 3)
    (graph2 initial (.var (.inr (0 : Fin 3)))
        (raw.relabel Sum.inl) (parameter.relabel Sum.inl) ⊓
      (graph1 currentFunction (.var (.inr (1 : Fin 3))) (.var (.inr (0 : Fin 3))) ⊓
        (graph1 currentArgument (.var (.inr (2 : Fin 3))) (.var (.inr (0 : Fin 3))) ⊓
          (graph2 (validator oldSource oldTarget member) (numeral 1)
              (.var (.inr (1 : Fin 3))) (parameter.relabel Sum.inl)) ⊓
            graph2 (validator oldSource oldTarget member) (numeral 1)
              (.var (.inr (2 : Fin 3))) (parameter.relabel Sum.inl))))

/-- The body is the ACTUAL repacked currentBody. Its parameter is BOTH the
actual childParameter selector and the original domain/Gamma extension,
retaining the same outer context. The child invokes the IDENTICAL validator
at its own payload+1 fuel. All three witnesses are generated internally. -/
def RootLambdaChild {alpha : Type} (oldSource oldTarget member : Program 2)
    (raw parameter : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 3)
    (graph2 initial (.var (.inr (0 : Fin 3)))
        (raw.relabel Sum.inl) (parameter.relabel Sum.inl) ⊓
      (graph1 currentBody (.var (.inr (1 : Fin 3))) (.var (.inr (0 : Fin 3))) ⊓
        (ExtendedParameter (raw.relabel Sum.inl) (parameter.relabel Sum.inl)
            (.var (.inr (2 : Fin 3)))) ⊓
          (graph1 childParameter (.var (.inr (2 : Fin 3))) (.var (.inr (0 : Fin 3))) ⊓
            graph2 (validator oldSource oldTarget member) (numeral 1)
              (.var (.inr (1 : Fin 3))) (.var (.inr (2 : Fin 3))))))

/-- Exact arithmetic recurrence factors for ALL original raw values.
Literal tag two requires both application children; literal tag one requires
the extended-Gamma lambda child; every other tag requires only the original
node factors. These are graphs of the unchanged programs, not native truth
or a recursively defined substitute for the original source relation. -/
def RecurrenceFactors {alpha : Type} (oldSource oldTarget member : Program 2)
    (raw parameter : OTerm alpha) : Formula alpha :=
  NodeFactors oldSource oldTarget member raw parameter ⊓
    InternalFiniteBlocks.block (k := 1)
      (graph1 OriginalLambdaConstructor.tag (.var (.inr (0 : Fin 1)))
          (raw.relabel Sum.inl) ⊓
        (((equal (.var (.inr (0 : Fin 1))) (numeral 2)).imp
            (RootApplicationChildren oldSource oldTarget member
              (raw.relabel Sum.inl) (parameter.relabel Sum.inl))) ⊓
          ((equal (.var (.inr (0 : Fin 1))) (numeral 1)).imp
            (RootLambdaChild oldSource oldTarget member
              (raw.relabel Sum.inl) (parameter.relabel Sum.inl)))))

/-- Full output, including every rejection and every non-Boolean leaf.
The validator itself remains Boolean, with rejection exactly the negation
of the same acceptance recurrence. -/
def ValidatorOutputFactors {alpha : Type} (oldSource oldTarget member : Program 2)
    (out raw parameter : OTerm alpha) : Formula alpha :=
  (equal out (numeral 1) ⊓ RecurrenceFactors oldSource oldTarget member raw parameter) ⊔
    (equal out OrdinaryArithmetic.zeroTerm ⊓
      (RecurrenceFactors oldSource oldTarget member raw parameter).not)

/- FROZEN INTERNAL RECURRENCE SPECIFICATION, NOT A PROOF.

Dependency plan:
1. Use original raw-list recursion graph equations for workFuel zero/cons,
   zero reflection and append additivity. Parameters never enter the measure.
2. Combine the independent one-step Internal packet with ORIGINAL internal
   pairing-sum bounds for application/lambda payloads to prove strict work
   decrease. Use object-language arithmetic induction for sufficient fuel,
   then the actual failure/empty fixed points for fuel saturation.
3. Prove BOTH directions of bounded append factorization for this framed
   machine, preserving every frame's own parameter. The older unary-machine
   append proof is a template, not an instantiable closure theorem here.
4. Identify singleton WorkAccepted with the unchanged payload+1 validator.
   Combine append, one-step graph laws and internal fuel bounds to establish
   the exact acceptance/full-output recurrence and constructor child closure.
   Acceptance-to-node can be paid earlier from first-step rejection and
   failure absorption, without waiting for the work-measure induction.

No native recurrence, evaluation theorem or semantic-to-internal reflection
is imported. No final-source transport, hereditary bottom-parameter
invariance, calibrated global Package or paper06 completion is claimed. -/

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrence
