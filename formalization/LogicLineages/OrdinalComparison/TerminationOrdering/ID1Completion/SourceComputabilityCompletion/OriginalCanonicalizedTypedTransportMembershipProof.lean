module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionFieldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportMembershipProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformContextMembership
open InternalOriginalUniformContextMembershipInternalProof
open OriginalTransparentDecoderValidatorCollapse
open UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The final pipeline retains exactly the normalized original member AST.
The transparent and once-refined inputs do not replace that original member. -/
theorem selectedMember (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    (selected p H G W).member = normalizedMember p.base.member := by
  change (OriginalLambdaTraversalSelection.finalData (refined p H G W)).member = _
  rw [OriginalLambdaTraversalSelectionFieldProof.sameMember,
    OriginalLambdaTraversalSelectionFieldProof.leafMember]
  rfl

/-- Original membership moves between actual parameter pairs with the same
outer context. The two Gamma codes may be arbitrary and need no window. -/
theorem memberTransport (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (typ parameter otherParameter c gamma otherGamma : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma)))
    (hq : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing otherParameter c otherGamma)))
    (hm : Nonempty (Derivation body Delta
      (graph2 (selected p H G W).member (numeral 1) typ parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (selected p H G W).member (numeral 1) typ otherParameter)) := by
  rw [selectedMember] at hm ⊢
  exact sliceAccept p.base.member (numeral 1) typ otherParameter c otherGamma hq
    (sliceRecover p.base.member (numeral 1) typ parameter c gamma hp hm)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportMembershipProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportMembershipProof
