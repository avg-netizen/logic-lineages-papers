module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ListsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinaryQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def leftQuery (n : Nat) : Program 2 := .composition (depth n) (fun _ => .projection 0)
def rightQuery (n : Nat) : Program 2 := .composition (depth n) (fun _ => .projection 1)
def maximumQuery (n : Nat) : Program 2 := .composition OriginalBoundsRecombination.maximum ![leftQuery n,rightQuery n]
def queries (n : Nat) : Fin 3 → Program 2 := ![leftQuery n,rightQuery n,maximumQuery n]

theorem cases (n : Nat) (left right : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (dl dr maximum : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (depth n) dl (left.relabel j))) →
      Nonempty (Derivation body Theta (graph1 (depth n) dr (right.relabel j))) →
      Nonempty (Derivation body Theta (graph2 OriginalBoundsRecombination.maximum maximum dl dr)) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (queries n) ![left,right] psi
  intro beta j ys Theta hj hq
  have hx : (fun i => (![left,right] i).relabel j) = ![left.relabel j,right.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hq
  apply next beta j Theta (ys 0) (ys 1) (ys 2) hj
  · exact unaryRecover (depth n) (.projection 0) (ys 0) (left.relabel j) ![left.relabel j,right.relabel j]
      (hq 0) (projectionValue 0 ![left.relabel j,right.relabel j])
  · exact unaryRecover (depth n) (.projection 1) (ys 1) (right.relabel j) ![left.relabel j,right.relabel j]
      (hq 1) (projectionValue 1 ![left.relabel j,right.relabel j])
  · exact binaryRecover OriginalBoundsRecombination.maximum (leftQuery n) (rightQuery n)
      (ys 2) (ys 0) (ys 1) ![left.relabel j,right.relabel j] (hq 2) (hq 0) (hq 1)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinaryQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinaryQueriesProof
