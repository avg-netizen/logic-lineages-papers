module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuel
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Proof-support measure on the ORIGINAL request code. Only its original
raw field plus one contributes; mode, Gamma, type and H never contribute. -/
def requestFuel : Program 1 :=
  .composition .succ (fun _ : Fin 1 => rightOf (rightOf (rightOf (.projection 0))))

/-- Inputs [original request, recursively computed suffix weight]. -/
def workFuelStep : Program 2 :=
  .composition InternalArithmeticPrograms.addition
    ![.composition requestFuel (fun _ : Fin 1 => .projection 0), .projection 1]

/-- A literal PR AST summing raw+1 through the original nil/cons codec.
This auxiliary program does not replace or alter any frozen decoder AST. -/
def workFuel : Program 1 := InternalRawListRecursion.listRec .zero workFuelStep

def WorkFuelGraph {alpha : Type} (count workCode : OTerm alpha) : Formula alpha :=
  graph1 workFuel count workCode

/-- Original failure and original live-empty state, pair 1 0 = TWO. -/
def Terminal {alpha : Type} (state : OTerm alpha) : Formula alpha :=
  equal state OrdinaryArithmetic.zeroTerm ⊔ equal state (numeral 2)

/-- The SAME original iterator; its original live initial state is an
internal witness rather than a caller-supplied successful execution. -/
def WorkRun {alpha : Type} (H : Program 1)
    (out count workCode : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 1)
    (StepLive (.var (.inr (0 : Fin 1))) (workCode.relabel Sum.inl) ⊓
      graph2 (OriginalTypedDecoder.iterate H) (out.relabel Sum.inl)
        (count.relabel Sum.inl) (.var (.inr (0 : Fin 1))))

def SuccessfulWork {alpha : Type} (H : Program 1)
    (count workCode : OTerm alpha) : Formula alpha :=
  WorkRun H (numeral 2) count workCode

/-- Both endpoint and completed run are generated in the conclusion. -/
def TerminatedWork {alpha : Type} (H : Program 1)
    (count workCode : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 1)
    (WorkRun H (.var (.inr (0 : Fin 1))) (count.relabel Sum.inl)
        (workCode.relabel Sum.inl) ⊓
      Terminal (.var (.inr (0 : Fin 1))))

/-- Acceptance by the unchanged iterator at precisely the internally
computed original raw work weight, not a substituted source relation. -/
def WorkAccepted {alpha : Type} (H : Program 1) (workCode : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 1)
    (WorkFuelGraph (.var (.inr (0 : Fin 1))) (workCode.relabel Sum.inl) ⊓
      SuccessfulWork H (.var (.inr (0 : Fin 1))) (workCode.relabel Sum.inl))

/-- Literal failure, or internally generated live work and strictly smaller
weight. No validity, successful traversal or next-weight premise is added. -/
def DecreasedOrFailed {alpha : Type} (out previousFuel : OTerm alpha) : Formula alpha :=
  equal out OrdinaryArithmetic.zeroTerm ⊔
    InternalFiniteBlocks.block (k := 2)
      (StepLive (out.relabel Sum.inl) (.var (.inr (0 : Fin 2))) ⊓
        (WorkFuelGraph (.var (.inr (1 : Fin 2))) (.var (.inr (0 : Fin 2))) ⊓
          InternalLessThan.strictLess (.var (.inr (1 : Fin 2)))
            (previousFuel.relabel Sum.inl)))

/- Frozen internal fuel specification. Prove fresh arithmetic Derivations
from original pair/list graphs and the independent one-step theorem. Native
calibration and native numeric weights are not proof suppliers. Every raw
input and arbitrary unary H are retained; no fuel increase is introduced.
This packet does not yet assert erasure/shift transport or insertion laws. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuel
