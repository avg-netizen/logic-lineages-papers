module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ListsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def unaryQueries : Fin 2 → Program 2 :=
  ![consOf (.projection 0) (OriginalRawSyntaxTransport.constant 2 0),consOf (.projection 1) (OriginalRawSyntaxTransport.constant 2 0)]
def firstTail : Program 4 := consOf (.projection 1) (OriginalRawSyntaxTransport.constant 4 0)
def secondTail : Program 4 := consOf (.projection 3) (OriginalRawSyntaxTransport.constant 4 0)
def binaryQueries : Fin 4 → Program 4 :=
  ![firstTail,consOf (.projection 0) firstTail,secondTail,consOf (.projection 2) secondTail]

theorem unary (a b : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (first second : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode first (a.relabel j) z)) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode second (b.relabel j) z)) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases unaryQueries ![a,b] psi
  intro beta j ys Theta hj hq
  have hx : (fun i => (![a,b] i).relabel j) = ![a.relabel j,b.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hq
  apply next beta j Theta (ys 0) (ys 1) hj
  · exact binaryRecover InternalListCodec.consCode (.projection 0) (OriginalRawSyntaxTransport.constant 2 0)
      (ys 0) (a.relabel j) z ![a.relabel j,b.relabel j] (hq 0)
      (projectionValue 0 ![a.relabel j,b.relabel j]) (constantValue 0 ![a.relabel j,b.relabel j])
  · exact binaryRecover InternalListCodec.consCode (.projection 1) (OriginalRawSyntaxTransport.constant 2 0)
      (ys 1) (b.relabel j) z ![a.relabel j,b.relabel j] (hq 1)
      (projectionValue 1 ![a.relabel j,b.relabel j]) (constantValue 0 ![a.relabel j,b.relabel j])

theorem binary (a b c d : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (rest first valueRest second : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode rest (b.relabel j) z)) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode first (a.relabel j) rest)) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode valueRest (d.relabel j) z)) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode second (c.relabel j) valueRest)) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases binaryQueries ![a,b,c,d] psi
  intro beta j ys Theta hj hq
  have hx : (fun i => (![a,b,c,d] i).relabel j) = ![a.relabel j,b.relabel j,c.relabel j,d.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hq
  apply next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) hj
  · exact binaryRecover InternalListCodec.consCode (.projection 1) (OriginalRawSyntaxTransport.constant 4 0)
      (ys 0) (b.relabel j) z ![a.relabel j,b.relabel j,c.relabel j,d.relabel j] (hq 0)
      (projectionValue 1 ![a.relabel j,b.relabel j,c.relabel j,d.relabel j]) (constantValue 0 ![a.relabel j,b.relabel j,c.relabel j,d.relabel j])
  · exact binaryRecover InternalListCodec.consCode (.projection 0) firstTail
      (ys 1) (a.relabel j) (ys 0) ![a.relabel j,b.relabel j,c.relabel j,d.relabel j] (hq 1)
      (projectionValue 0 ![a.relabel j,b.relabel j,c.relabel j,d.relabel j]) (hq 0)
  · exact binaryRecover InternalListCodec.consCode (.projection 3) (OriginalRawSyntaxTransport.constant 4 0)
      (ys 2) (d.relabel j) z ![a.relabel j,b.relabel j,c.relabel j,d.relabel j] (hq 2)
      (projectionValue 3 ![a.relabel j,b.relabel j,c.relabel j,d.relabel j]) (constantValue 0 ![a.relabel j,b.relabel j,c.relabel j,d.relabel j])
  · exact binaryRecover InternalListCodec.consCode (.projection 2) secondTail
      (ys 3) (c.relabel j) (ys 2) ![a.relabel j,b.relabel j,c.relabel j,d.relabel j] (hq 3)
      (projectionValue 2 ![a.relabel j,b.relabel j,c.relabel j,d.relabel j]) (hq 2)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ListsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ListsProof
