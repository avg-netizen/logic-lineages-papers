module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoder
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original drop AST, with inputs [requested type, variable index, original
Encodable context code]. The type input is deliberately retained. -/
def rest : Program 3 :=
  .composition InternalRawListRecursion.drop
    (Fin.cons (.projection 1) (Fin.cons (.projection 2) Fin.elim0))

def head : Program 3 :=
  .composition InternalListCodec.headCode (fun _ : Fin 1 => rest)

def matches : Program 3 :=
  .composition InternalEqualityTest.equalityTest
    (Fin.cons (.projection 0) (Fin.cons head Fin.elim0))

/-- Concrete realization of the ORIGINAL variable-decoder success test.
The nonempty guard is essential: the total head operation maps nil to zero,
which must not falsely accept a ground-type variable in an empty context.
The existing branch takes control, zero branch, then nonzero branch. -/
def check : Program 3 :=
  InternalAcceptance.branch rest (InternalAcceptance.constantZero 3) matches

def graph {alpha : Type} (out typ index gamma : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  programGraph check out (Fin.cons typ (Fin.cons index (Fin.cons gamma Fin.elim0)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoder
