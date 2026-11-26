module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseChildQueriesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalListCodecDecompositionSupportProof
open InternalTagArithmeticSyntaxProof (z eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def head : Program 2 := .composition InternalListCodec.headCode (fun _ : Fin 1 => .projection 0)
def tail : Program 2 := .composition InternalListCodec.tailCode (fun _ : Fin 1 => .projection 0)
def child : Program 2 := .composition NumberedWindowInternalLiteralScratchErase.state ![tail,.projection 1]
def queries : Fin 5 → Program 2 := ![head,tail,child,leftOf child,rightOf child]

theorem recover (raw needle : OTerm alpha) (ys : Fin 5 → OTerm alpha)
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries i) (ys i) ![raw,needle]))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw (ys 0) (ys 1))) ∧
    Nonempty (Derivation body Delta (graph2 NumberedWindowInternalLiteralScratchErase.state (ys 2) (ys 1) needle)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 2) (ys 3) (ys 4))) := by
  have hh := unaryRecover InternalListCodec.headCode (.projection 0) (ys 0) raw ![raw,needle]
    (hq 0) (projectionValue 0 ![raw,needle])
  have ht := unaryRecover InternalListCodec.tailCode (.projection 0) (ys 1) raw ![raw,needle]
    (hq 1) (projectionValue 0 ![raw,needle])
  have hc := binaryRecover NumberedWindowInternalLiteralScratchErase.state tail (.projection 1) (ys 2) (ys 1) needle ![raw,needle]
    (hq 2) (hq 1) (projectionValue 1 ![raw,needle])
  have hb := unaryRecover InternalUnpair.left child (ys 3) (ys 2) ![raw,needle] (hq 3) (hq 2)
  have hr := unaryRecover InternalUnpair.right child (ys 4) (ys 2) ![raw,needle] (hq 4) (hq 2)
  exact ⟨reconstructNonzero raw (ys 0) (ys 1) hn hh ht,hc,reconstructPair (ys 2) (ys 3) (ys 4) hb hr⟩

#print axioms recover
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseChildQueriesProof
