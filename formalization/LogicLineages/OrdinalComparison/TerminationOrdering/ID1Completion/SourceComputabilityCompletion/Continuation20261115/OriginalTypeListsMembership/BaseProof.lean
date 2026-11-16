module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.ArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.InductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.BaseProof
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
open InductionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nilCondition (bound allowed types len : OTerm alpha)
    (hz : Nonempty (Derivation body Delta (eqn types z)))
    (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len types))) :
    Nonempty (Derivation body Delta (condition bound allowed types len)) := by
  have hl0 := headTransport OriginalContextInsertion.length len types z Fin.elim0 hz hl
  have hlen := OriginalContextInsertionLengthProof.lengthNilRecover len hl0
  have hb := InternalOriginalPairingOrderArithmeticProof.strictTransport len (suc bound) z (suc bound)
    hlen ⟨refl (suc bound)⟩ ⟨InternalQuotientComparisonProof.zeroLessSuccessor bound⟩
  obtain ⟨hz⟩ := hz
  exact andIntro hb (ArithmeticProof.membersTransport z types allowed ⟨symm hz⟩
    (MemberProof.nilMembers allowed))

theorem zeroCore (allowed out types len : OTerm alpha)
    (hg : Nonempty (Derivation body Delta
      (graph2 OriginalTypeListsEnumeration.enumeration out z allowed)))
    (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len types))) :
    Nonempty (Derivation body Delta (result z allowed out types len)) := by
  obtain ⟨he⟩ := valueUnique OriginalTypeListsEnumeration.enumeration out (numeral 1) ![z,allowed]
    hg (OriginalTypeListsEnumeration.StatementChecks.exactZero body alpha Delta allowed)
  have hc := outputTransport InternalListCodec.consCode (numeral 1) out ![z,z]
    ⟨symm he⟩ ArithmeticProof.singletonZero
  let M := graph2 contains (numeral 1) out types
  let C := condition z allowed types len
  have forward : Nonempty (Derivation body Delta (M.imp C)) := by
    have hm : Nonempty (Derivation body (M :: Delta) M) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := OriginalAscendingRange.SupportProof.singletonMember out z types (withHyp hc M) hm
    obtain ⟨h⟩ := nilCondition z allowed types len hz (withHyp hl M)
    exact ⟨Derivation.implicationIntroduction h⟩
  have backward : Nonempty (Derivation body Delta (C.imp M)) := by
    have hh : Nonempty (Derivation body (C :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hlen := ArithmeticProof.belowOne len (andLeft hh)
    have hl0 := outputTransport OriginalContextInsertion.length len z ![types] hlen (withHyp hl C)
    obtain ⟨hz⟩ := OriginalContextInsertionLengthProof.lengthZeroRecover types hl0
    obtain ⟨hm⟩ := containsHit out z z types (withHyp hc C) (by rw [equalEqn]; exact ⟨symm hz⟩)
    exact ⟨Derivation.implicationIntroduction hm⟩
  exact andIntro forward backward
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.BaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.BaseProof
