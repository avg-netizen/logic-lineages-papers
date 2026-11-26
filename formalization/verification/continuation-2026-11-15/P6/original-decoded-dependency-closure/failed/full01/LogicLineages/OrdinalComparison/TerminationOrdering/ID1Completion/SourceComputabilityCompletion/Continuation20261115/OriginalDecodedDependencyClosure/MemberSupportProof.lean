module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.RunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.MemberSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
variable {n : Nat}
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalOriginalPairingOrderArithmeticProof (strictTransport)
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)

theorem zeroCase (raw deps child : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 0) raw)))
    (hd : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) child)) := by
  have hz : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children z raw)) :=
    zeroBranchIntro _ _ _ z (Fin.cons raw Fin.elim0) ha (constantValue 0 (Fin.cons raw Fin.elim0))
  have he := valueUnique ArgumentEntriesChildren.children deps z (Fin.cons raw Fin.elim0) hd hz
  have h0 := headTransport contains (numeral 1) deps z (Fin.cons child Fin.elim0) he hm
  obtain ⟨hb⟩ := valueUnique contains (numeral 1) z ![z,child] h0 (containsNil child)
  exact ⟨Derivation.explosion (sucNeZeroApply hb)⟩

theorem unaryAt (raw deps child first listCode : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 1) raw)))
    (hd : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode first z)))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) child)) := by
  have hg := ArgumentEntriesChildren.InternalProof.unaryList raw first listCode ha hf hc
  have he := valueUnique ArgumentEntriesChildren.children deps listCode (Fin.cons raw Fin.elim0) hd hg
  have hl := headTransport contains (numeral 1) deps listCode (Fin.cons child Fin.elim0) he hm
  have hcf := PrimaryCarrierBound.RunProof.singletonMember listCode first child hc hl
  obtain ⟨he⟩ := hcf
  exact headTransport (OriginalCodeValidityGuard.check n) (numeral 1) first child Fin.elim0 ⟨symm he⟩ hv

theorem binaryAt (raw deps child first second rest listCode : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) raw)))
    (hd : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.secondOf (.projection 0)) second raw)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest second z)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode first rest)))
    (hv1 : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first)))
    (hv2 : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) second))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) child)) := by
  have hg := ArgumentEntriesChildren.InternalProof.binaryList raw first second rest listCode ha hf hs hr hc
  have he := valueUnique ArgumentEntriesChildren.children deps listCode (Fin.cons raw Fin.elim0) hd hg
  have hl := headTransport contains (numeral 1) deps listCode (Fin.cons child Fin.elim0) he hm
  let A := equal first child
  apply formulaCases A
  · have h : Nonempty (Derivation body (A :: Delta) (equal first child)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    rw [equalEqn] at h
    obtain ⟨e⟩ := h
    exact headTransport (OriginalCodeValidityGuard.check n) (numeral 1) first child Fin.elim0 ⟨e⟩ (withHyp hv1 A)
  · have ht := PrimaryMembership.Proof.missRecover listCode first rest child (numeral 1)
      (withHyp hc A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hl A.not)
    have hcs := PrimaryCarrierBound.RunProof.singletonMember rest second child (withHyp hr A.not) ht
    obtain ⟨he⟩ := hcs
    exact headTransport (OriginalCodeValidityGuard.check n) (numeral 1) second child Fin.elim0 ⟨symm he⟩ (withHyp hv2 A.not)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.MemberSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.MemberSupportProof
