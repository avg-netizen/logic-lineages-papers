module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.SelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.DependencySupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open InternalTagArithmeticSupportProof (symm)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem zeroImpossible (node param deps child : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R z node param)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child))) :
    Nonempty (Derivation body Delta (⊥ : Formula alpha)) := by
  have hz : Nonempty (Derivation body Delta (graph2 D z node param)) :=
    zeroBranchIntro R (InternalAcceptance.constantZero 2) positiveDependencies z ![node,param]
      hr (InternalAcceptanceConjunctionProof.constantZeroValue ![node,param])
  have he := valueUnique D deps z ![node,param] hd hz
  exact OriginalAscendingRange.SupportProof.nilImpossible child
    (headTransport contains (numeral 1) deps z (Fin.cons child Fin.elim0) he hm)

theorem memberRank (param deps child a c tail f : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps a tail)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail c z)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (ha : Nonempty (Derivation body Delta (graph2 R f a param)))
    (hc : Nonempty (Derivation body Delta (graph2 R f c param))) :
    Nonempty (Derivation body Delta (graph2 R f child param)) := by
  apply formulaCases (eqn a child)
  · have he : Nonempty (Derivation body (eqn a child :: Delta) (eqn a child)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact headTransport R f a child (Fin.cons param Fin.elim0) he (withHyp ha (eqn a child))
  · let A := (eqn a child).not
    have hn : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have htail := Continuation20261114.PrimaryMembership.Proof.missRecover deps a tail child (numeral 1)
      (withHyp hd A) (by simpa only [equalEqn] using hn) (withHyp hm A)
    obtain ⟨he⟩ := OriginalAscendingRange.SupportProof.singletonMember tail c child (withHyp ht A) htail
    exact headTransport R f c child (Fin.cons param Fin.elim0) ⟨symm he⟩ (withHyp hc A)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.DependencySupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.DependencySupportProof
