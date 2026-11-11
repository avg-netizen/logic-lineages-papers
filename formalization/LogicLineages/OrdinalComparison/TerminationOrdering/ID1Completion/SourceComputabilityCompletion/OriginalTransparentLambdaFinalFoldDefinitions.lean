module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFold
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof
open InternalParameterizedApplicationCertifiedResultFoldClosure
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A common output of the unchanged actual certified fold and an arbitrary
comparison program. This auxiliary invariant does not change either machine. -/
def commonFoldP {α : Type} (guard leaf valid : Program 2) (combine : Program 5)
    (out input parameter : OrdinaryArithmetic.Term α) : Formula α :=
  certifiedFoldP guard leaf combine out input parameter ⊓ graph2 valid out input parameter

/-- One genuine object-language existential binds the output of BOTH actual
graphs in commonFoldP. Zero is allowed, and neither graph is a premise. -/
def hasCertifiedOutputP {α : Type} (guard leaf valid : Program 2) (combine : Program 5)
    (input parameter : OrdinaryArithmetic.Term α) : Formula α :=
  existsOne (commonFoldP guard leaf valid combine (.var (.inr 0))
    (input.relabel Sum.inl) (parameter.relabel Sum.inl))

/-- At each induction payload quantify EVERY original packed input AND
parameter inside the predicate. The input's raw type/tag is unrestricted;
there is no separately fixed input, validity, requested-type or member guard.
Only the actual right-selector graph links that input to the payload. -/
def payloadMatrixP {α : Type} (guard leaf valid : Program 2) (combine : Program 5)
    (payload : OrdinaryArithmetic.Term α) : Formula (α ⊕ Fin 2) :=
  let input : OrdinaryArithmetic.Term (α ⊕ Fin 2) := .var (.inr 0)
  let parameter : OrdinaryArithmetic.Term (α ⊕ Fin 2) := .var (.inr 1)
  (graph1 InternalUnpair.right (payload.relabel Sum.inl) input).imp
    (hasCertifiedOutputP guard leaf valid combine input parameter)

/-- The existing internal finite universal block. Strong induction is on
only the original payload. Child packed codes, raw types, parameters and
callback outputs need not be bounded by their parent payload. -/
def atPayloadP {α : Type} (guard leaf valid : Program 2) (combine : Program 5)
    (payload : OrdinaryArithmetic.Term α) : Formula α :=
  InternalClosedPrograms.allBlock (payloadMatrixP guard leaf valid combine payload)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFold
