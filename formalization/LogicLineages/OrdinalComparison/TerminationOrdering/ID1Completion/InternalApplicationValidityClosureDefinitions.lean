module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosure
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors

/-- Exact original constructor graphs with SHARED raw type and payload terms.
The function has the original arrow tag, the argument has the domain tag, and
the parent is packedApplication at those same two term payloads. These are
object-language graphs, not successful decodes or semantic equalities. -/
def applicationConstructors {α : Type}
    (arrow d e fp ap fn arg parent : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 InternalListCodec.consCode arrow d e ⊓
    (graph2 InternalPairing.pairing fn arrow fp ⊓
      (graph2 InternalPairing.pairing arg d ap ⊓
        graph4 packedApplication parent d e fp ap))

/-- The concrete ORIGINAL endpoint accepts the recursive validity Programs.
The sole separate type witness is the original arrow cons graph. Raw source
and target applications use application, which discards outer type fields;
the endpoint itself must therefore supply the original child tag graphs. -/
def endpointApplicationPremises {α : Type}
    (old : InternalOriginalStepGuard.Data)
    (member : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 1)
    (arrow d e s t a sourceApp targetApp : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 InternalListCodec.consCode arrow d e ⊓
    (InternalStructuralEndpointGuard.accepted
        (InternalApplicationValidityStack.recursiveData old member) member d e s t a ⊓
      (graph4 application sourceApp d e s a ⊓
        graph4 application targetApp d e t a))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosure
