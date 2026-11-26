module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rankEquality (n : Nat) (node param left right value : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.accepted n) (suc z) node param)))
    (hr : Nonempty (Derivation body Delta (graph2 (rank n) value node param))) :
    Nonempty (Derivation body Delta (eqn value left)) := by
  have hs := successorBranchElim (OriginalDecodedDependencies.accepted n) (constant 2 0)
    OriginalDecodedDependencies.source value z (Fin.cons node (Fin.cons param Fin.elim0)) ha hr
  exact valueUnique OriginalDecodedDependencies.source value left (Fin.cons node (Fin.cons param Fin.elim0)) hs
    (OriginalDecodedDependencies.SupportProof.sourceAt node param left right hp)

theorem childAccepted (n : Nat) (node param left right : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (hl : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) left)))
    (hr : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) right))) :
    Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.accepted n) (suc z) node param)) :=
  conjunctionAccept (OriginalDecodedDependencies.sourceAccepted n) (OriginalDecodedDependencies.targetAccepted n)
    (Fin.cons node (Fin.cons param Fin.elim0))
    (OriginalDecodedDependencies.SupportProof.sourceAcceptedAt n node param left right (numeral 1) hp hl)
    (OriginalDecodedDependencies.SupportProof.targetAcceptedAt n node param left right (numeral 1) hp hr)

theorem pairCases (node : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (left right : OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (node.relabel j) left right)) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  let qs : Fin 2 → Program 1 := ![InternalUnpair.left,InternalUnpair.right]
  apply queryCases qs (Fin.cons node Fin.elim0) psi
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  exact next beta j Theta (ys 0) (ys 1) hj (reconstructPair (node.relabel j) (ys 0) (ys 1) (hq 0) (hq 1))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
