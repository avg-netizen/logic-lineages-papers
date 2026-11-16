module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.BaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.CrossProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.CrossIntroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.StepValuesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open Continuation20261114
open InductionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atCons (bound allowed out types len previous rows head tail tailLen : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (row bound)))
    (hp : Nonempty (Derivation body Delta (graph2 OriginalTypeListsEnumeration.enumeration previous bound allowed)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalTypeListsEnumeration.cross rows allowed previous)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out z rows)))
    (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len types)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode types head tail)))
    (htl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph tailLen tail))) :
    Nonempty (Derivation body Delta (result (suc bound) allowed out types len)) := by
  have hi := rowApply bound allowed previous tail tailLen ih (andIntro hp htl)
  have hlen := OriginalContextInsertionLengthProof.lengthConsRecover types head tail len tailLen ht hl htl
  have hn : Nonempty (Derivation body Delta (equal z types).not) := by
    rw [equalEqn]
    obtain ⟨hn⟩ := ArithmeticProof.consNonzero types head tail ht
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination
      (InternalBetaTotalityProof.addHyp hn _) (symm (Derivation.hypothesis List.mem_cons_self)))⟩
  let M := graph2 contains (numeral 1) out types
  let C := condition (suc bound) allowed types len
  have forward : Nonempty (Derivation body Delta (M.imp C)) := by
    have hm : Nonempty (Derivation body (M :: Delta) M) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hmrows := PrimaryMembership.Proof.missRecover out z rows types (numeral 1)
      (withHyp ho M) (withHyp hn M) hm
    have hh := CrossProof.projection allowed previous rows types head tail
      (withHyp hc M) hmrows (withHyp ht M)
    obtain ⟨himp⟩ := andLeft (withHyp hi M)
    obtain ⟨hmem⟩ := andRight hh
    have htail : Nonempty (Derivation body (M :: Delta) (condition bound allowed tail tailLen)) :=
      ⟨Derivation.implicationElimination himp hmem⟩
    have hb := InternalRecursionGraphExtensionSupportProof.successorOrder tailLen (suc bound) (andLeft htail)
    have hb' := InternalOriginalPairingOrderArithmeticProof.strictTransport len (suc (suc bound))
      (suc tailLen) (suc (suc bound)) (withHyp hlen M) ⟨refl _⟩ hb
    have hall := MemberProof.consMembers types head tail allowed (withHyp ht M) (andLeft hh) (andRight htail)
    obtain ⟨h⟩ := andIntro hb' hall
    exact ⟨Derivation.implicationIntroduction h⟩
  have backward : Nonempty (Derivation body Delta (C.imp M)) := by
    have hh : Nonempty (Derivation body (C :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hlen'⟩ := withHyp hlen C
    have hb := InternalOriginalPairingOrderArithmeticProof.strictTransport (suc tailLen) (suc (suc bound))
      len (suc (suc bound)) ⟨symm hlen'⟩ ⟨refl _⟩ (andLeft hh)
    have hsmall := ArithmeticProof.cancelOrder tailLen (suc bound) hb
    have hall := andRight hh
    have hhead := MemberProof.headMember types head tail allowed (withHyp ht C) hall
    have htail := MemberProof.tailMembers types head tail allowed (withHyp ht C) hall
    obtain ⟨hcond⟩ := andIntro hsmall htail
    obtain ⟨himp⟩ := andRight (withHyp hi C)
    have hmem : Nonempty (Derivation body (C :: Delta) (graph2 contains (numeral 1) previous tail)) :=
      ⟨Derivation.implicationElimination himp hcond⟩
    have hrows := CrossIntroProof.introduce allowed previous rows types head tail
      (withHyp hc C) (andIntro hhead hmem) (withHyp ht C)
    obtain ⟨hm⟩ := SupportProof.memberTail out z rows types (withHyp ho C) hrows
    exact ⟨Derivation.implicationIntroduction hm⟩
  exact andIntro forward backward
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.StepValuesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.StepValuesProof
