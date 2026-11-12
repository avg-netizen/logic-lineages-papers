module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelProgramDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant)
/-- Inputs [packed term, original parameter]. No decoding is used to define this AST. -/
def job : Program 2 := pairOf (constant 2 0)
 (pairOf (leftOf (.projection 0)) (pairOf (rightOf (.projection 0)) (.projection 1)))
def initial : Program 2 := pairOf (consOf (pairOf (constant 2 0) job) (constant 2 0)) (constant 2 0)
def computedFuel : Program 2 := .composition OriginalHereditaryFuelProgram.fuel (fun _ : Fin 1 => job)
def completed (R : Program 2) : Program 2 :=
 .composition (OriginalHereditaryRuntimeIterationDefinitions.run R) ![computedFuel,initial]
/-- Literal total projection on malformed inputs, without a semantic guarantee. -/
def evaluator (R : Program 2) : Program 2 :=
 .composition InternalListCodec.headCode (fun _ : Fin 1 => rightOf (completed R))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorDefinitions
