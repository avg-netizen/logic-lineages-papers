module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootProjectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalFiniteBlocks (block)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- The actual unchanged runtime state's result-stack head, and its first
coordinate. These are total original primitive projections on every code. -/
def rootValue : Program 1 := .composition InternalListCodec.headCode
 (fun _ : Fin 1 => rightOf (.projection 0))
def rootOfState : Program 1 := leftOf rootValue
def fields {alpha : Type} (R : Program 2)
 (packed parameter output stack value old root tail : OTerm alpha) : Formula alpha :=
 graph2 InternalPairing.pairing output (numeral 0) stack ⊓
 (graph2 InternalListCodec.consCode stack value old ⊓
 (graph2 InternalPairing.pairing value root tail ⊓
  graph2 (OriginalRootObservation.rootObservation R) root packed parameter))
def matrix {alpha : Type} (R : Program 2) (packed parameter output : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
 fields R (packed.relabel Sum.inl) (parameter.relabel Sum.inl) (output.relabel Sum.inl)
   (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))
/-- Internally constructed actual final pair/cons/value-pair geometry. The
old suffix and second value coordinate are not assumed to be semantically
correct or empty. -/
def Shape {alpha : Type} (R : Program 2) (packed parameter output : OTerm alpha) : Formula alpha :=
 block (matrix R packed parameter output)
/-- CPS exposure of the genuine final root return, retaining its original
packed source and parameter. This is a proof-side existential eliminator. -/
def ReturnConsumer (R : Program 2) (body : Positive (Fin 1)) {alpha : Type}
 (Delta : List (Formula alpha)) (packed parameter output : OTerm alpha) (psi : Formula alpha) : Prop :=
 ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (input work results frame payload : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing input work results)) →
   Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode work frame (numeral 0))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
   Nonempty (Derivation body Theta (graph1 OriginalHereditaryReturnStep.role (numeral 0) input)) →
   Nonempty (Derivation body Theta (graph1 OriginalHereditaryReturnStep.packed (packed.relabel j) input)) →
   Nonempty (Derivation body Theta (graph1 OriginalHereditaryReturnStep.parameter (parameter.relabel j) input)) →
   Nonempty (Derivation body Theta (graph1 (OriginalHereditaryReturnStep.step R) (output.relabel j) input)) →
   Nonempty (Derivation body Theta (psi.relabel j))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultDefinitions
