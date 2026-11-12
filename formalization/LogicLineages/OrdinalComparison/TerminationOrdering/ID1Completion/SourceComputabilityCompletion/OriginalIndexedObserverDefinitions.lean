module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Proof-side context length is exactly original length after original right
projection. It is not inserted into any runtime traversal Program. -/
def contextLength : Program 1 :=
  .composition OriginalContextInsertion.length (fun _ : Fin 1 => InternalUnpair.right)

/-- Actual finite context range, with its length witness bound internally. -/
def rangeMatrix {alpha : Type} (cutoff parameter : OrdinaryArithmetic.Term alpha) : Formula (alpha ⊕ Fin 1) :=
  graph1 contextLength (.var (.inr 0)) (parameter.relabel Sum.inl) ⊓
    OriginalContextInsertion.Below (cutoff.relabel Sum.inl) (.var (.inr 0))
def ActualRange {alpha : Type} (cutoff parameter : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  SourceComputabilityFormulaSupportProof.existsOne (rangeMatrix cutoff parameter)

/-- A cutoff-indexed observer on the original packed object and parameter. -/
def observations {alpha : Type} (K : Program 3) (out input parameter mark cutoff : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  (graph3 K mark cutoff out parameter).iff
    (graph3 K mark cutoff input parameter)

abbrev premises := @OriginalLambdaTraversalOutput.premises

/-- The cutoff, mark, input, type, output and runtime parameter all remain internally
universal. Lambda visits may therefore use their own actual child Gamma. -/
def payloadMatrix {alpha : Type} (data : Data) (window : Program 1) (K : Program 3)
    (payload : OrdinaryArithmetic.Term alpha) : Formula (alpha ⊕ Fin 6) :=
  let input : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 0)
  let typ : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 1)
  let out : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 2)
  let parameter : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 3)
  let mark : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 4)
  let cutoff : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 5)
  (graph1 InternalUnpair.right (payload.relabel Sum.inl) input).imp
    ((premises data window out input typ parameter).imp
      ((ActualRange cutoff parameter).imp (observations K out input parameter mark cutoff)))

def atPayload {alpha : Type} (data : Data) (window : Program 1) (K : Program 3)
    (payload : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (payloadMatrix data window K payload)

def payloadPredicate (data : Data) (window : Program 1) (K : Program 3) {alpha : Type} : Formula (alpha ⊕ Fin 1) :=
  atPayload data window K (.var (.inr 0))

def belowPayload {alpha : Type} (data : Data) (window : Program 1) (K : Program 3)
    (payload : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  InternalStrongInduction.below (payloadPredicate data window K) payload

/-- Constructor suppliers are independently discharged, not Program fields. -/
def ApplicationLaw (data : Data) (window : Program 1) (K : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input out typ parameter arrow d e fn arg fnOut argOut fValue aValue mark cutoff : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta (ActualRange cutoff parameter)) →
  Nonempty (Derivation body Delta (premises data window out input typ parameter)) →
  Nonempty (Derivation body Delta (premises data window fnOut fn arrow parameter)) →
  Nonempty (Derivation body Delta (premises data window argOut arg d parameter)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow d e)) →
  Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.ApplicationFields input d e fn arg)) →
  Nonempty (Derivation body Delta (graph4 application input d e fn arg)) →
  Nonempty (Derivation body Delta (graph4 application out d e fnOut argOut)) →
  Nonempty (Derivation body Delta (graph3 K fValue cutoff fn parameter)) →
  Nonempty (Derivation body Delta (graph3 K fValue cutoff fnOut parameter)) →
  Nonempty (Derivation body Delta (graph3 K aValue cutoff arg parameter)) →
  Nonempty (Derivation body Delta (graph3 K aValue cutoff argOut parameter)) →
  Nonempty (Derivation body Delta (observations K out input parameter mark cutoff))

def LambdaLaw (data : Data) (window : Program 1) (K : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input out typ parameter mark d e child childParameter childOut value cutoff : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta (ActualRange cutoff parameter)) →
  Nonempty (Derivation body Delta (premises data window out input typ parameter)) →
  Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields input d e child parameter childParameter)) →
  Nonempty (Derivation body Delta (graph2 (OriginalLambdaTraversalSelection.canonical data window) childOut child childParameter)) →
  Nonempty (Derivation body Delta (graph3 K value (InternalTagArithmeticSyntaxProof.suc cutoff) child childParameter)) →
  Nonempty (Derivation body Delta (graph3 K value (InternalTagArithmeticSyntaxProof.suc cutoff) childOut childParameter)) →
  Nonempty (Derivation body Delta (observations K out input parameter mark cutoff))

def OtherLaw (data : Data) (window : Program 1) (K : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter mark cutoff : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta (ActualRange cutoff parameter)) →
  Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)) →
  Nonempty (Derivation body Delta (InternalParameterizedCanonicalResultFold.sourcePremises
    (OriginalLambdaTraversalSelection.leafData data window) input typ parameter)) →
  Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one input)) →
  Nonempty (Derivation body Delta (graph2 (OriginalLambdaTraversalSelection.leaf data window) out input parameter)) →
  Nonempty (Derivation body Delta (observations K out input parameter mark cutoff))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverDefinitions
