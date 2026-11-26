module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseConstructQueriesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def kept : Program 3 := consOf (.projection 1) (.projection 2)
def paired : Program 3 := pairOf (.projection 0) kept
def queries : Fin 2 → Program 3 := ![kept,paired]

theorem recover (bit head rest : OTerm alpha) (ys : Fin 2 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries i) (ys i) ![bit,head,rest]))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode (ys 0) head rest)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 1) bit (ys 0))) := by
  constructor
  · exact binaryRecover InternalListCodec.consCode (.projection 1) (.projection 2) (ys 0) head rest ![bit,head,rest]
      (hq 0) (projectionValue 1 ![bit,head,rest]) (projectionValue 2 ![bit,head,rest])
  · exact binaryRecover InternalPairing.pairing (.projection 0) kept (ys 1) bit (ys 0) ![bit,head,rest]
      (hq 1) (projectionValue 0 ![bit,head,rest]) (hq 0)

#print axioms recover
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseConstructQueriesProof
