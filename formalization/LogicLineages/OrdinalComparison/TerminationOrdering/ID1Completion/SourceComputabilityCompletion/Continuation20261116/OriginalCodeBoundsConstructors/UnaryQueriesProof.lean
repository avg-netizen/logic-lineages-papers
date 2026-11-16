module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (suc)
open Continuation20261115 OriginalCodeBoundsRecursion OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def size (n : Nat) : Program 1 := leftOf (bounds n)
def label (n : Nat) : Program 1 := rightOf (bounds n)
def next (n : Nat) : Program 1 := pairOf (succOf (size n)) (label n)
def queries (n : Nat) : Fin 4 → Program 1 := ![bounds n,size n,label n,next n]

theorem childPair (n : Nat) (child value s l : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph1 (bounds n) value child)))
    (hs : Nonempty (Derivation body Delta (graph1 (size n) s child)))
    (hl : Nonempty (Derivation body Delta (graph1 (label n) l child))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value s l)) :=
  reconstructPair value s l
    (unaryRecover InternalUnpair.left (bounds n) s value ![child] hs he)
    (unaryRecover InternalUnpair.right (bounds n) l value ![child] hl he)

theorem nextPair (n : Nat) (child s l out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph1 (size n) s child)))
    (hl : Nonempty (Derivation body Delta (graph1 (label n) l child)))
    (ho : Nonempty (Derivation body Delta (graph1 (next n) out child))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc s) l)) := by
  have hsucc := unaryValue .succ (size n) (suc s) s ![child] (successorValue ![s]) hs
  exact binaryRecover InternalPairing.pairing (succOf (size n)) (label n) out (suc s) l ![child] ho hsucc hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryQueriesProof
