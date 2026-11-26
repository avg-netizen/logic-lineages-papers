module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildObservationsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (queryCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalControlGraphSupportProof (emptyRename)
open Continuation20261115
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def queries (n : Nat) : Fin 3 → Program 1 :=
  ![OriginalCodeBoundsRecursion.bounds n, OriginalCodeBoundsConstructors.UnaryQueriesProof.size n,
    OriginalCodeBoundsConstructors.UnaryQueriesProof.label n]

theorem cases (n : Nat) (child : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (pair size label : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair (child.relabel j))) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing pair size label)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply queryCases (queries n) (Fin.cons child Fin.elim0) psi
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  have hb : Nonempty (Derivation body Theta
      (graph1 (OriginalCodeBoundsRecursion.bounds n) (ys 0) (child.relabel j))) := hq 0
  have hs : Nonempty (Derivation body Theta
      (graph1 (OriginalCodeBoundsConstructors.UnaryQueriesProof.size n) (ys 1) (child.relabel j))) := hq 1
  have hl : Nonempty (Derivation body Theta
      (graph1 (OriginalCodeBoundsConstructors.UnaryQueriesProof.label n) (ys 2) (child.relabel j))) := hq 2
  exact next beta j Theta (ys 0) (ys 1) (ys 2) hj hb
    (OriginalCodeBoundsConstructors.UnaryQueriesProof.childPair n (child.relabel j) (ys 0) (ys 1) (ys 2) hb hs hl)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildObservationsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildObservationsProof
