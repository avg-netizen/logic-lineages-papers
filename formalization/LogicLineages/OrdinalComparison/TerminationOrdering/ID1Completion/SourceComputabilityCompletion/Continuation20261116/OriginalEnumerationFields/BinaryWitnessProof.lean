module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.UnaryWitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases)
open InternalTagArithmeticSyntaxProof (z)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def leftKeyQuery : Program 4 := pairOf (.projection 0) (.projection 2)
def rightKeyQuery : Program 4 := pairOf (.projection 1) (.projection 2)
def leftValue (n : Nat) : Program 4 := .composition (extract n) ![leftKeyQuery,.projection 3]
def rightValue (n : Nat) : Program 4 := .composition (extract n) ![rightKeyQuery,.projection 3]
def restDeps : Program 4 := consOf rightKeyQuery (constant 4 0)
def deps : Program 4 := consOf leftKeyQuery restDeps
def restValues (n : Nat) : Program 4 := consOf (rightValue n) (constant 4 0)
def values (n : Nat) : Program 4 := consOf (leftValue n) (restValues n)
def queries (n : Nat) : Fin 8 → Program 4 :=
  ![leftKeyQuery,rightKeyQuery,leftValue n,rightValue n,restDeps,deps,restValues n,values n]

theorem cases (n : Nat) (left right bound param : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (leftKey rightKey leftOut rightOut depRest depList valueRest valueList : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing leftKey (left.relabel j) (bound.relabel j))) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing rightKey (right.relabel j) (bound.relabel j))) →
      Nonempty (Derivation body Theta (graph2 (extract n) leftOut leftKey (param.relabel j))) →
      Nonempty (Derivation body Theta (graph2 (extract n) rightOut rightKey (param.relabel j))) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode depRest rightKey z)) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode depList leftKey depRest)) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode valueRest rightOut z)) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode valueList leftOut valueRest)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply queryCases (queries n) ![left,right,bound,param] psi
  intro beta j ys Theta hj hq
  have hx : (fun i => (![left,right,bound,param] i).relabel j) = ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hq
  have h0 : Nonempty (Derivation body Theta (programGraph leftKeyQuery (ys 0) ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j])) := hq 0
  have h1 : Nonempty (Derivation body Theta (programGraph rightKeyQuery (ys 1) ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j])) := hq 1
  have h2 : Nonempty (Derivation body Theta (programGraph (leftValue n) (ys 2) ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j])) := hq 2
  have h3 : Nonempty (Derivation body Theta (programGraph (rightValue n) (ys 3) ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j])) := hq 3
  have h4 : Nonempty (Derivation body Theta (programGraph restDeps (ys 4) ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j])) := hq 4
  have h5 : Nonempty (Derivation body Theta (programGraph deps (ys 5) ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j])) := hq 5
  have h6 : Nonempty (Derivation body Theta (programGraph (restValues n) (ys 6) ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j])) := hq 6
  have h7 : Nonempty (Derivation body Theta (programGraph (values n) (ys 7) ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j])) := hq 7
  apply next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) hj
  · exact binaryRecover InternalPairing.pairing (.projection 0) (.projection 2) (ys 0) (left.relabel j) (bound.relabel j)
      ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j] h0 (projectionValue 0 ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j]) (projectionValue 2 ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j])
  · exact binaryRecover InternalPairing.pairing (.projection 1) (.projection 2) (ys 1) (right.relabel j) (bound.relabel j)
      ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j] h1 (projectionValue 1 ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j]) (projectionValue 2 ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j])
  · exact binaryRecover (extract n) leftKeyQuery (.projection 3) (ys 2) (ys 0) (param.relabel j)
      ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j] h2 h0 (projectionValue 3 ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j])
  · exact binaryRecover (extract n) rightKeyQuery (.projection 3) (ys 3) (ys 1) (param.relabel j)
      ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j] h3 h1 (projectionValue 3 ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j])
  · exact binaryRecover InternalListCodec.consCode rightKeyQuery (constant 4 0) (ys 4) (ys 1) z
      ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j] h4 h1 (constantValue 0 ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j])
  · exact binaryRecover InternalListCodec.consCode leftKeyQuery restDeps (ys 5) (ys 0) (ys 4)
      ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j] h5 h0 h4
  · exact binaryRecover InternalListCodec.consCode (rightValue n) (constant 4 0) (ys 6) (ys 3) z
      ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j] h6 h3 (constantValue 0 ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j])
  · exact binaryRecover InternalListCodec.consCode (leftValue n) (restValues n) (ys 7) (ys 2) (ys 6)
      ![left.relabel j,right.relabel j,bound.relabel j,param.relabel j] h7 h2 h6
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryWitnessProof
