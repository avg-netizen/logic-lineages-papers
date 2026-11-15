module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof
open OriginalContextInsertionSyntaxProof
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof (containsNil)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rejectedEmpty : Targets.InternalRejectedEmpty := by
  intro n body alpha Delta node param left right hp hz
  have hc : Nonempty (Derivation body Delta (graph2 (accepted n) z node param)) := by
    rcases hz with hz | hz
    · exact SupportProof.rejectLeft n node param (SupportProof.sourceAcceptedAt n node param left right z hp hz)
    · exact SupportProof.rejectRight n node param (SupportProof.targetAcceptedAt n node param left right z hp hz)
  exact zeroBranchIntro (accepted n) (constant 2 0) decodedCross z (Fin.cons node (Fin.cons param Fin.elim0)) hc
    (constantValue 0 (Fin.cons node (Fin.cons param Fin.elim0)))

theorem acceptedDescent (n : Nat) (node param left right out child a b : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (hv : Nonempty (Derivation body Delta (graph2 (dependencies n) out node param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out child)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child a b)))
    (ha : Nonempty (Derivation body Delta (graph2 (accepted n) (suc z) node param))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess a left ⊓ InternalLessThan.strictLess b right)) := by
  have hx := successorBranchElim (accepted n) (constant 2 0) decodedCross out z
    (Fin.cons node (Fin.cons param Fin.elim0)) ha hv
  have hd := binaryRecover NumericDependencyCross.rawDependencies source target out left right
    (Fin.cons node (Fin.cons param Fin.elim0)) hx (SupportProof.sourceAt node param left right hp)
    (SupportProof.targetAt node param left right hp)
  exact NumericDependencyCross.Proof.descent body alpha Delta left right out child a b hd hm hq

theorem rejectedImpossible (n : Nat) (node param out child : OTerm alpha) (psi : Formula alpha)
    (hv : Nonempty (Derivation body Delta (graph2 (dependencies n) out node param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out child)))
    (hn : Nonempty (Derivation body Delta (graph2 (accepted n) (suc z) node param).not)) :
    Nonempty (Derivation body Delta psi) := by
  have hz := OriginalTransparentLambdaValidityInternalBranchSupportProof.conjunctionReject
    (sourceAccepted n) (targetAccepted n) (Fin.cons node (Fin.cons param Fin.elim0)) hn
  have hx := zeroBranchElim (accepted n) (constant 2 0) decodedCross out
    (Fin.cons node (Fin.cons param Fin.elim0)) hz hv
  have he := valueUnique (constant 2 0) out z (Fin.cons node (Fin.cons param Fin.elim0)) hx
    (constantValue 0 (Fin.cons node (Fin.cons param Fin.elim0)))
  have hm0 := headTransport contains (suc z) out z (Fin.cons child Fin.elim0) he hm
  obtain ⟨bad⟩ := valueUnique contains (suc z) z (Fin.cons z (Fin.cons child Fin.elim0)) hm0 (containsNil child)
  exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩

theorem dependencyDescent : Targets.InternalDependencyDescent := by
  intro n body alpha Delta node param left right out child a b hp hv hm hq
  apply formulaCases (graph2 (accepted n) (suc z) node param)
  · exact acceptedDescent n node param left right out child a b
      (withHyp hp _) (withHyp hv _) (withHyp hm _) (withHyp hq _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact rejectedImpossible n node param out child _ (withHyp hv _) (withHyp hm _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.Proof
