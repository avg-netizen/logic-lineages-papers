module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalPackedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankPackedQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl symm trans congSuc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal OriginalRawVariableRank
open OriginalRawVariableRankTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Packed raw inputs are split by the actual total inverse of pairing.
The actual transform output is queried on the right component internally. -/
theorem packedTransformCases (p : Program 3) (d k packed : OTerm alpha) (psi : Formula alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (tau raw transformed : OTerm beta),
      (∀ f ∈ Delta, f.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (packed.relabel j) tau raw)) →
      Nonempty (Derivation body Theta (graph3 p transformed (d.relabel j) (k.relabel j) raw)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let qs : Fin 3 → Program 3 := ![leftOf (.projection 2),rightOf (.projection 2),
    .composition p ![.projection 0,.projection 1,rightOf (.projection 2)]]
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons packed Fin.elim0))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  let xs' : Fin 3 → OTerm beta := fun i => (xs i).relabel j
  have hl := unaryRecover InternalUnpair.left (.projection 2) (ys 0) (packed.relabel j) xs'
    (hq 0) (projectionValue 2 xs')
  have hr := unaryRecover InternalUnpair.right (.projection 2) (ys 1) (packed.relabel j) xs'
    (hq 1) (projectionValue 2 xs')
  have hp := reconstructPair (packed.relabel j) (ys 0) (ys 1) hl hr
  have ht : Nonempty (Derivation body Theta (graph3 p (ys 2) (d.relabel j) (k.relabel j) (ys 1))) := by
    apply compositionRecover p ![.projection 0,.projection 1,rightOf (.projection 2)] (ys 2) xs'
      (Fin.cons (d.relabel j) (Fin.cons (k.relabel j) (Fin.cons (ys 1) Fin.elim0))) (hq 2)
    intro i
    exact Fin.cases (projectionValue 0 xs') (Fin.cases (projectionValue 1 xs')
      (Fin.cases (hq 1) (fun q => Fin.elim0 q))) i
  exact step beta j Theta (ys 0) (ys 1) (ys 2) hj hp ht

theorem rankNonincreaseRename {beta : Type} (after before : OTerm alpha) (j : alpha → beta) :
    (RankNonincrease after before).relabel j = RankNonincrease (after.relabel j) (before.relabel j) := by
  change ((InternalOriginalOrderSyntaxProof.ltF before after).relabel j).not = _
  rw [InternalOriginalOrderSyntaxProof.orderRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankPackedQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankPackedQueryProof
