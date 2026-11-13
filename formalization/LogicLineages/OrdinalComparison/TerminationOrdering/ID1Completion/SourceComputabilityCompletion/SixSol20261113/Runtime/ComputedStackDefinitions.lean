module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalFiniteBlocks (block)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Literal final state contains exactly one value and no residual stack suffix.
The value is also the output of the unchanged computed-fuel evaluator. -/
def fields {alpha : Type} (R : Program 2) (packed parameter output stack value : OTerm alpha) : Formula alpha :=
 graph2 InternalPairing.pairing output (numeral 0) stack ⊓
 (graph2 InternalListCodec.consCode stack value (numeral 0) ⊓
  graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) value packed parameter)
def matrix {alpha : Type} (R : Program 2) (packed parameter output : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
 fields R (packed.relabel Sum.inl) (parameter.relabel Sum.inl) (output.relabel Sum.inl)
   (.var (.inr 0)) (.var (.inr 1))
def SingletonResult {alpha : Type} (R : Program 2) (packed parameter output : OTerm alpha) : Formula alpha :=
 block (matrix R packed parameter output)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackDefinitions
