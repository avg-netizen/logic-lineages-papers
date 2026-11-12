module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyPayloadDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Binary key observation retains the actual runtime parameter. -/
def observations {alpha : Type} (K : Program 2) (out input parameter mark : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  (graph2 K mark out parameter).iff
    (graph2 K mark input parameter)

abbrev premises := @OriginalLambdaTraversalOutput.premises

/-- The mark, input, type, output and runtime parameter all remain internally
universal. Lambda visits may therefore use their own actual child Gamma. -/
def payloadMatrix {alpha : Type} (data : Data) (window : Program 1) (K : Program 2)
    (payload : OrdinaryArithmetic.Term alpha) : Formula (alpha ⊕ Fin 5) :=
  let input : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 0)
  let typ : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 1)
  let out : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 2)
  let parameter : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 3)
  let mark : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 4)
  (graph1 InternalUnpair.right (payload.relabel Sum.inl) input).imp
    ((premises data window out input typ parameter).imp (observations K out input parameter mark))

def atPayload {alpha : Type} (data : Data) (window : Program 1) (K : Program 2)
    (payload : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (payloadMatrix data window K payload)

def payloadPredicate (data : Data) (window : Program 1) (K : Program 2) {alpha : Type} : Formula (alpha ⊕ Fin 1) :=
  atPayload data window K (.var (.inr 0))

def belowPayload {alpha : Type} (data : Data) (window : Program 1) (K : Program 2)
    (payload : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  InternalStrongInduction.below (payloadPredicate data window K) payload

/-- Constructor suppliers are independently discharged, not Program fields. -/
def ApplicationLaw (data : Data) (window : Program 1) (K : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input out typ parameter arrow d e fn arg fnOut argOut fValue aValue mark : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta (premises data window out input typ parameter)) →
  Nonempty (Derivation body Delta (premises data window fnOut fn arrow parameter)) →
  Nonempty (Derivation body Delta (premises data window argOut arg d parameter)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow d e)) →
  Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.ApplicationFields input d e fn arg)) →
  Nonempty (Derivation body Delta (graph4 application input d e fn arg)) →
  Nonempty (Derivation body Delta (graph4 application out d e fnOut argOut)) →
  Nonempty (Derivation body Delta (graph2 K fValue fn parameter)) →
  Nonempty (Derivation body Delta (graph2 K fValue fnOut parameter)) →
  Nonempty (Derivation body Delta (graph2 K aValue arg parameter)) →
  Nonempty (Derivation body Delta (graph2 K aValue argOut parameter)) →
  Nonempty (Derivation body Delta (observations K out input parameter mark))

def LambdaLaw (data : Data) (window : Program 1) (K : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input out typ parameter mark d e child childParameter childOut value : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta (premises data window out input typ parameter)) →
  Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields input d e child parameter childParameter)) →
  Nonempty (Derivation body Delta (graph2 (OriginalLambdaTraversalSelection.canonical data window) childOut child childParameter)) →
  Nonempty (Derivation body Delta (graph2 K value child childParameter)) →
  Nonempty (Derivation body Delta (graph2 K value childOut childParameter)) →
  Nonempty (Derivation body Delta (observations K out input parameter mark))

def OtherLaw (data : Data) (window : Program 1) (K : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter mark : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)) →
  Nonempty (Derivation body Delta (InternalParameterizedCanonicalResultFold.sourcePremises
    (OriginalLambdaTraversalSelection.leafData data window) input typ parameter)) →
  Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one input)) →
  Nonempty (Derivation body Delta (graph2 (OriginalLambdaTraversalSelection.leaf data window) out input parameter)) →
  Nonempty (Derivation body Delta (observations K out input parameter mark))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyPayloadDefinitions
