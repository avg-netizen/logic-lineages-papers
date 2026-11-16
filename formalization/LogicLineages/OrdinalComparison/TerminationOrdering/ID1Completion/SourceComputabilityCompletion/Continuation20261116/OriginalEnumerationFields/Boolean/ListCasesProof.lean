module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.HeadRangeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.ListCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel)
open InternalTagArithmeticSupportProof (refl)
open InternalApplicationStepPeelSupportProof (queryCases)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nonzeroCases (list : OTerm alpha) (psi : Formula alpha)
    (hn : Nonempty (Derivation body Delta (eqn list z).not))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (head tail : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode (list.relabel j) head tail)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply queryCases ![InternalListCodec.headCode,InternalListCodec.tailCode] (Fin.cons list Fin.elim0) psi
  intro beta j ys Theta hj hg
  simp only [consTermRename,emptyRename] at hg
  have hnj := renameInto hn j Theta hj
  rw [InternalListCodecDecompositionSupportProof.nonzeroRename] at hnj
  exact next beta j Theta (ys 0) (ys 1) hj
    (InternalListCodecDecompositionSupportProof.reconstructNonzero (list.relabel j) (ys 0) (ys 1) hnj (hg 0) (hg 1))

theorem memberHead (list head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) list head)) := by
  apply TwoSol20261113.CalibratedPrimary.MembershipInternalProof.containsHit list head tail head hc
  rw [InternalControlGraphSupportProof.equalEqn]
  exact ⟨refl head⟩

theorem memberTail (list head tail node : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) tail node))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) list node)) :=
  Continuation20261115.NumericDependencyCross.SupportProof.memberTail list head tail node hc hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.ListCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.ListCasesProof
